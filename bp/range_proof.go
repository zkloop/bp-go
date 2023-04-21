package bp

import (
	"crypto/rand"
	"crypto/sha256"
	"fmt"
	"math/big"
)

type RangeProof struct {
	Comm ECPoint
	A    ECPoint
	S    ECPoint
	T1   ECPoint
	T2   ECPoint
	Tau  *big.Int
	Th   *big.Int
	Mu   *big.Int
	IPP  InnerProdArg
	L    []*big.Int
	R    []*big.Int
	Factor int8
	LR   *big.Int	// <l,r>, might be different than Th (t^) in the case of MPC

	// challenges
	Cy *big.Int
	Cz *big.Int
	Cx *big.Int
	ConsolidatedChallenge bool
}

/*
Delta is a helper function that is used in the range proof

\delta(y, z) = (z-z^2)<1^n, y^n> - z^3<1^n, 2^n>
*/

func Delta(EC *CryptoParams, y []*big.Int, z *big.Int) *big.Int {
	result := big.NewInt(0)

	// (z-z^2)<1^n, y^n>
	z2 := new(big.Int).Mod(new(big.Int).Mul(z, z), EC.N)
	t1 := new(big.Int).Mod(new(big.Int).Sub(z, z2), EC.N)
	t2 := new(big.Int).Mod(new(big.Int).Mul(t1, VectorSum(y, EC.N)), EC.N)

	// z^3<1^n, 2^n>
	z3 := new(big.Int).Mod(new(big.Int).Mul(z2, z), EC.N)
	po2sum := new(big.Int).Sub(new(big.Int).Exp(big.NewInt(2), big.NewInt(int64(EC.V)), EC.N), big.NewInt(1))
	t3 := new(big.Int).Mod(new(big.Int).Mul(z3, po2sum), EC.N)

	result = new(big.Int).Mod(new(big.Int).Sub(t2, t3), EC.N)

	return result
}

// Calculates (aL - z*1^n) + sL*x
func CalculateL(EC *CryptoParams, aL, sL []*big.Int, z, x *big.Int) []*big.Int {
	result := make([]*big.Int, len(aL))

	tmp1 := VectorAddScalar(aL, new(big.Int).Neg(z), EC.N)
	tmp2 := ScalarVectorMul(sL, x, EC.N)

	result = VectorAdd(tmp1, tmp2, EC.N)

	return result
}

func CalculateR(EC *CryptoParams, aR, sR, y, po2 []*big.Int, z, x *big.Int) []*big.Int {
	if len(aR) != len(sR) || len(aR) != len(y) || len(y) != len(po2) {
		fmt.Println("CalculateR: Uh oh! Arrays not of the same length")
		fmt.Printf("len(aR): %d\n", len(aR))
		fmt.Printf("len(sR): %d\n", len(sR))
		fmt.Printf("len(y): %d\n", len(y))
		fmt.Printf("len(po2): %d\n", len(po2))
	}

	result := make([]*big.Int, len(aR))

	z2 := new(big.Int).Exp(z, big.NewInt(2), EC.N)
	tmp11 := VectorAddScalar(aR, z, EC.N)
	tmp12 := ScalarVectorMul(sR, x, EC.N)
	tmp1 := VectorHadamard(y, VectorAdd(tmp11, tmp12, EC.N), EC.N)
	tmp2 := ScalarVectorMul(po2, z2, EC.N)

	result = VectorAdd(tmp1, tmp2, EC.N)

	return result
}

/*
RPProver : Range Proof Prove

Given a value v, provides a range proof that v is inside 0 to 2^64-1
*/

type MPRangeContext struct {
	AL []*big.Int	`asn1:"optional"`
	AR []*big.Int	`asn1:"optional"`
	SL []*big.Int	`asn1:"optional"`
	SR []*big.Int	`asn1:"optional"`
	Alpha *big.Int	`asn1:"optional"`
	Rho *big.Int	`asn1:"optional"`
	V *big.Int	`asn1:"optional"`
	Tau1 *big.Int	`asn1:"optional"`
	Tau2 *big.Int	`asn1:"optional"`
	T0 *big.Int	`asn1:"optional"`
	T1 *big.Int	`asn1:"optional"`
	T2 *big.Int	`asn1:"optional"`
}

func RPProveStep0(ec *CryptoParams, m *MPRangeContext, rpresult *RangeProof, v *big.Int, comm ECPoint) error {
	if v.Cmp(big.NewInt(0)) == -1 {
		return fmt.Errorf("Value is below range! Not proving")
	}

	if v.Cmp(new(big.Int).Exp(big.NewInt(2), big.NewInt(int64(ec.V)), ec.N)) == 1 {
		return fmt.Errorf("Value is above range! Not proving.")
	}

	rpresult.Comm = comm

	// break up v into its bitwise representation
	//aL := 0
	aL := reverse(StrToBigIntArray(PadLeft(fmt.Sprintf("%b", v), "0", ec.V)))
	aR := VectorAddScalar(aL, big.NewInt(-1), ec.N)

	alpha, err := rand.Int(rand.Reader, ec.N)
	if err != nil {
		return err
	}

	A := ec.TwoVectorPCommitWithGens(ec.BPG, ec.BPH, aL, aR).Add(ec.H.Mult(alpha))
	rpresult.A = A

	sL := RandVector(ec.V, ec.N)
	sR := RandVector(ec.V, ec.N)

	rho, err := rand.Int(rand.Reader, ec.N)
	if err != nil {
		return err
	}

	S := ec.TwoVectorPCommitWithGens(ec.BPG, ec.BPH, sL, sR).Add(ec.H.Mult(rho))
	rpresult.S = S

	m.AL = aL
	m.AR = aR
	m.SL = sL
	m.SR = sR
	m.Alpha = alpha
	m.Rho = rho
	m.V = v

	return nil
}

func RPProveStep1(ec *CryptoParams, m *MPRangeContext, rpresult *RangeProof) error {
	aL := m.AL
	aR := m.AR
	sL := m.SL
	sR := m.SR
	v := m.V

	cy := rpresult.Cy
	cz := rpresult.Cz

	PowerOfTwos := PowerVector(ec.V, big.NewInt(2), ec.N)

	z2 := new(big.Int).Exp(cz, big.NewInt(2), ec.N)
	// need to generate l(X), r(X), and t(X)=<l(X),r(X)>

	/*
			Java code on how to calculate t1 and t2

				FieldVector ys = FieldVector.from(VectorX.iterate(n, BigInteger.ONE, y::multiply),q); //powers of y
			    FieldVector l0 = aL.add(z.negate());
		        FieldVector l1 = sL;
		        FieldVector twoTimesZSquared = twos.times(zSquared);
		        FieldVector r0 = ys.hadamard(aR.add(z)).add(twoTimesZSquared);
		        FieldVector r1 = sR.hadamard(ys);
		        BigInteger k = ys.sum().multiply(z.subtract(zSquared)).subtract(zCubed.shiftLeft(n).subtract(zCubed));
		        BigInteger t0 = k.add(zSquared.multiply(number));
		        BigInteger t1 = l1.innerPoduct(r0).add(l0.innerPoduct(r1));
		        BigInteger t2 = l1.innerPoduct(r1);
		   		PolyCommitment<T> polyCommitment = PolyCommitment.from(base, t0, VectorX.of(t1, t2));


	*/
	PowerOfCY := PowerVector(ec.V, cy, ec.N)
	// fmt.Println(PowerOfCY)
	l0 := VectorAddScalar(aL, new(big.Int).Neg(cz), ec.N)
	// l1 := sL
	r0 := VectorAdd(
		VectorHadamard(
			PowerOfCY,
			VectorAddScalar(aR, cz, ec.N), ec.N),
		ScalarVectorMul(
			PowerOfTwos,
			z2, ec.N), ec.N)
	r1 := VectorHadamard(sR, PowerOfCY, ec.N)

	//calculate t0
	t0 := new(big.Int).Mod(new(big.Int).Add(new(big.Int).Mul(v, z2), Delta(ec, PowerOfCY, cz)), ec.N)

	t1 := new(big.Int).Mod(new(big.Int).Add(InnerProduct(sL, r0, ec.N), InnerProduct(l0, r1, ec.N)), ec.N)
	t2 := InnerProduct(sL, r1, ec.N)

	// given the t_i values, we can generate commitments to them
	tau1, err := rand.Int(rand.Reader, ec.N)
	if err != nil {
		return err
	}
	tau2, err := rand.Int(rand.Reader, ec.N)
	if err != nil {
		return err
	}

	T1 := ec.G.Mult(t1).Add(ec.H.Mult(tau1)) //commitment to t1
	T2 := ec.G.Mult(t2).Add(ec.H.Mult(tau2)) //commitment to t2

	rpresult.T1 = T1
	rpresult.T2 = T2

	m.Tau1 = tau1
	m.Tau2 = tau2
	m.T0 = t0
	m.T1 = t1
	m.T2 = t2

	return nil
}

func RPProveStep2(ec *CryptoParams, m *MPRangeContext, rpresult *RangeProof, gamma *big.Int) error {
	alpha := m.Alpha
	rho := m.Rho
	tau1 := m.Tau1
	tau2 := m.Tau2
	aL := m.AL
	aR := m.AR
	sL := m.SL
	sR := m.SR
	t0 := m.T0
	t1 := m.T1
	t2 := m.T2

	cy := rpresult.Cy
	cz := rpresult.Cz
	cx := rpresult.Cx

	PowerOfTwos := PowerVector(ec.V, big.NewInt(2), ec.N)
	PowerOfCY := PowerVector(ec.V, cy, ec.N)
	z2 := new(big.Int).Exp(cz, big.NewInt(2), ec.N)

	left := CalculateL(ec, aL, sL, cz, cx)
	right := CalculateR(ec, aR, sR, PowerOfCY, PowerOfTwos, cz, cx)

	thatPrime := new(big.Int).Mod( // t0 + t1*x + t2*x^2
		new(big.Int).Add(
			t0,
			new(big.Int).Add(
				new(big.Int).Mul(
					t1, cx),
				new(big.Int).Mul(
					new(big.Int).Mul(cx, cx),
					t2))), ec.N)

	that := InnerProduct(left, right, ec.N) // NOTE: BP Java implementation calculates this from the t_i

	// thatPrime and that should be equal
	if thatPrime.Cmp(that) != 0 {
		fmt.Println("Proving -- Uh oh! Two diff ways to compute same value not working")
		fmt.Printf("\tthatPrime = %s\n", thatPrime.String())
		fmt.Printf("\tthat = %s \n", that.String())
	}

	rpresult.Th = thatPrime

	taux1 := new(big.Int).Mod(new(big.Int).Mul(tau2, new(big.Int).Mul(cx, cx)), ec.N)
	taux2 := new(big.Int).Mod(new(big.Int).Mul(tau1, cx), ec.N)
	taux3 := new(big.Int).Mod(new(big.Int).Mul(z2, gamma), ec.N)
	taux := new(big.Int).Mod(new(big.Int).Add(taux1, new(big.Int).Add(taux2, taux3)), ec.N)

	rpresult.Tau = taux

	mu := new(big.Int).Mod(new(big.Int).Add(alpha, new(big.Int).Mul(rho, cx)), ec.N)
	rpresult.Mu = mu

	rpresult.L = left
	rpresult.R = right

	return nil
}

func padding(l, r []*big.Int, G, H []ECPoint) ([]*big.Int, []*big.Int, []ECPoint, []ECPoint) {
	power := 1
	for power < len(G) {
		power *= 2
	}
	if (len(G) < power) {	// padding to 2^n
		for i := power - len(G); i > 0; i-- {
			l = append(l, big.NewInt(0))
			r = append(r, big.NewInt(0))
			G = append(G, NewECPoint(big.NewInt(0), big.NewInt(0)))
			H = append(H, NewECPoint(big.NewInt(0), big.NewInt(0)))
		}
	}
	return l, r, G, H
}

func RPProveStep3(ec *CryptoParams, rpresult *RangeProof) error {
	PowersOfY := expand(PowerVector(ec.V, rpresult.Cy, ec.N), len(ec.BPG))
	HPrime := make([]ECPoint, len(ec.BPH))

	for i := range HPrime {
		HPrime[i] = ec.BPH[i].Mult(new(big.Int).ModInverse(PowersOfY[i], ec.N))
	}

	P := ec.TwoVectorPCommitWithGens(ec.BPG, HPrime, rpresult.L, rpresult.R)

	G := ec.BPG
	left := rpresult.L
	right := rpresult.R

	left, right, G, HPrime = padding(left, right, G, HPrime)
	rpresult.IPP = InnerProductProve(ec, left, right, rpresult.Th, P, ec.U, G, HPrime)

	return nil
}

func RPProve(EC *CryptoParams, v *big.Int, gamma *big.Int, uncompress bool) RangeProof {

	rpresult := RangeProof{}

	PowerOfTwos := PowerVector(EC.V, big.NewInt(2), EC.N)

	if v.Cmp(big.NewInt(0)) == -1 {
		panic("Value is below range! Not proving")
	}

	if v.Cmp(new(big.Int).Exp(big.NewInt(2), big.NewInt(int64(EC.V)), EC.N)) == 1 {
		panic("Value is above range! Not proving.")
	}

	comm := EC.G.Mult(v).Add(EC.H.Mult(gamma))
	rpresult.Comm = comm

	// break up v into its bitwise representation
	//aL := 0
	aL := reverse(StrToBigIntArray(PadLeft(fmt.Sprintf("%b", v), "0", EC.V)))
	aR := VectorAddScalar(aL, big.NewInt(-1), EC.N)

	alpha, err := rand.Int(rand.Reader, EC.N)
	check(err)

	A := EC.TwoVectorPCommitWithGens(EC.BPG, EC.BPH, aL, aR).Add(EC.H.Mult(alpha))
	rpresult.A = A

	sL := RandVector(EC.V, EC.N)
	sR := RandVector(EC.V, EC.N)

	rho, err := rand.Int(rand.Reader, EC.N)
	check(err)

	S := EC.TwoVectorPCommitWithGens(EC.BPG, EC.BPH, sL, sR).Add(EC.H.Mult(rho))
	rpresult.S = S

	h := sha256.New()
	buf := make([]byte, 32)
	comm.X.FillBytes(buf)	// comm
	h.Write(buf)
	h.Write([]byte{byte(EC.V)})	// n
	A.X.FillBytes(buf)	// A.x
	h.Write(buf)
	S.X.FillBytes(buf)	// S.x
	h.Write(buf)
	chal1s256 := h.Sum(nil)
	cy := new(big.Int).SetBytes(chal1s256)

	rpresult.Cy = cy

	h.Reset()
	A.X.FillBytes(buf)		// A.x
	h.Write(buf)
	S.X.FillBytes(buf)		// S.x
	h.Write(buf)
	h.Write(chal1s256)		// y
	chal2s256 := h.Sum(nil)
	cz := new(big.Int).SetBytes(chal2s256)

	rpresult.Cz = cz
	z2 := new(big.Int).Exp(cz, big.NewInt(2), EC.N)
	// need to generate l(X), r(X), and t(X)=<l(X),r(X)>

	/*
			Java code on how to calculate t1 and t2

				FieldVector ys = FieldVector.from(VectorX.iterate(n, BigInteger.ONE, y::multiply),q); //powers of y
			    FieldVector l0 = aL.add(z.negate());
		        FieldVector l1 = sL;
		        FieldVector twoTimesZSquared = twos.times(zSquared);
		        FieldVector r0 = ys.hadamard(aR.add(z)).add(twoTimesZSquared);
		        FieldVector r1 = sR.hadamard(ys);
		        BigInteger k = ys.sum().multiply(z.subtract(zSquared)).subtract(zCubed.shiftLeft(n).subtract(zCubed));
		        BigInteger t0 = k.add(zSquared.multiply(number));
		        BigInteger t1 = l1.innerPoduct(r0).add(l0.innerPoduct(r1));
		        BigInteger t2 = l1.innerPoduct(r1);
		   		PolyCommitment<T> polyCommitment = PolyCommitment.from(base, t0, VectorX.of(t1, t2));


	*/
	PowerOfCY := PowerVector(EC.V, cy, EC.N)
	// fmt.Println(PowerOfCY)
	l0 := VectorAddScalar(aL, new(big.Int).Neg(cz), EC.N)
	// l1 := sL
	r0 := VectorAdd(
		VectorHadamard(
			PowerOfCY,
			VectorAddScalar(aR, cz, EC.N), EC.N),
		ScalarVectorMul(
			PowerOfTwos,
			z2, EC.N), EC.N)
	r1 := VectorHadamard(sR, PowerOfCY, EC.N)

	//calculate t0
	t0 := new(big.Int).Mod(new(big.Int).Add(new(big.Int).Mul(v, z2), Delta(EC, PowerOfCY, cz)), EC.N)

	t1 := new(big.Int).Mod(new(big.Int).Add(InnerProduct(sL, r0, EC.N), InnerProduct(l0, r1, EC.N)), EC.N)
	t2 := InnerProduct(sL, r1, EC.N)

	// given the t_i values, we can generate commitments to them
	tau1, err := rand.Int(rand.Reader, EC.N)
	check(err)
	tau2, err := rand.Int(rand.Reader, EC.N)
	check(err)

	T1 := EC.G.Mult(t1).Add(EC.H.Mult(tau1)) //commitment to t1
	T2 := EC.G.Mult(t2).Add(EC.H.Mult(tau2)) //commitment to t2

	rpresult.T1 = T1
	rpresult.T2 = T2

	h.Reset()
	h.Write(chal2s256)		// z
	T1.X.FillBytes(buf)		// T1.x
	h.Write(buf)
	T2.X.FillBytes(buf)		// T2.x
	h.Write(buf)
	chal3s256 := h.Sum(nil)
	cx := new(big.Int).SetBytes(chal3s256)

	rpresult.Cx = cx

	left := CalculateL(EC, aL, sL, cz, cx)
	right := CalculateR(EC, aR, sR, PowerOfCY, PowerOfTwos, cz, cx)

	thatPrime := new(big.Int).Mod( // t0 + t1*x + t2*x^2
		new(big.Int).Add(
			t0,
			new(big.Int).Add(
				new(big.Int).Mul(
					t1, cx),
				new(big.Int).Mul(
					new(big.Int).Mul(cx, cx),
					t2))), EC.N)

	that := InnerProduct(left, right, EC.N) // NOTE: BP Java implementation calculates this from the t_i

	// thatPrime and that should be equal
	if thatPrime.Cmp(that) != 0 {
		fmt.Println("Proving -- Uh oh! Two diff ways to compute same value not working")
		fmt.Printf("\tthatPrime = %s\n", thatPrime.String())
		fmt.Printf("\tthat = %s \n", that.String())
	}

	rpresult.Th = thatPrime
	rpresult.Factor = 1

	taux1 := new(big.Int).Mod(new(big.Int).Mul(tau2, new(big.Int).Mul(cx, cx)), EC.N)
	taux2 := new(big.Int).Mod(new(big.Int).Mul(tau1, cx), EC.N)
	taux3 := new(big.Int).Mod(new(big.Int).Mul(z2, gamma), EC.N)
	taux := new(big.Int).Mod(new(big.Int).Add(taux1, new(big.Int).Add(taux2, taux3)), EC.N)

	rpresult.Tau = taux

	mu := new(big.Int).Mod(new(big.Int).Add(alpha, new(big.Int).Mul(rho, cx)), EC.N)
	rpresult.Mu = mu

	if uncompress {
		rpresult.L = left
		rpresult.R = right
		return rpresult
	}

	HPrime := make([]ECPoint, len(EC.BPH))

	for i := range HPrime {
		HPrime[i] = EC.BPH[i].Mult(new(big.Int).ModInverse(PowerOfCY[i], EC.N))
	}

	// for testing
	tmp1 := EC.Zero()
	zneg := new(big.Int).Mod(new(big.Int).Neg(cz), EC.N)
	for i := range EC.BPG {
		tmp1 = tmp1.Add(EC.BPG[i].Mult(zneg))
	}

	tmp2 := EC.Zero()
	for i := range HPrime {
		val1 := new(big.Int).Mul(cz, PowerOfCY[i])
		val2 := new(big.Int).Mul(new(big.Int).Mul(cz, cz), PowerOfTwos[i])
		tmp2 = tmp2.Add(HPrime[i].Mult(new(big.Int).Add(val1, val2)))
	}

	//P1 := A.Add(S.Mult(cx)).Add(tmp1).Add(tmp2).Add(EC.U.Mult(that)).Add(EC.H.Mult(mu).Neg())

	P := EC.TwoVectorPCommitWithGens(EC.BPG, HPrime, left, right)
	//fmt.Println(P1)
	//fmt.Println(P2)

	G := EC.BPG
	left, right, G, HPrime = padding(left, right, G, HPrime)
	rpresult.IPP = InnerProductProve(EC, left, right, that, P, EC.U, G, HPrime)

	return rpresult
}

func expand(v []*big.Int, n int) []*big.Int {
	repeat := n / len(v)
	r := make([]*big.Int, n)
	for i, e := range v {
		for j := 0; j < repeat; j++ {
			r[i * repeat + j] = e
		}
	}
	return r
}

func RPVerify(EC *CryptoParams, rp RangeProof) error {
	// verify the challenges
	var cx, cy, cz *big.Int

	if !rp.ConsolidatedChallenge {
		h := sha256.New()
		buf := make([]byte, 32)
		rp.Comm.X.FillBytes(buf)	// comm
		h.Write(buf)
		h.Write([]byte{byte(EC.V)})	// n
		rp.A.X.FillBytes(buf)		// A.x
		h.Write(buf)
		rp.S.X.FillBytes(buf)		// S.x
		h.Write(buf)
		chal1s256 := h.Sum(nil)
		cy = new(big.Int).SetBytes(chal1s256)
		if rp.Cy != nil && cy.Cmp(rp.Cy) != 0 {
			return fmt.Errorf("RPVerify - Challenge Cy failing!")
		}

		h.Reset()
		rp.A.X.FillBytes(buf)		// A.x
		h.Write(buf)
		rp.S.X.FillBytes(buf)		// S.x
		h.Write(buf)
		h.Write(chal1s256)		// y
		chal2s256 := h.Sum(nil)
		cz = new(big.Int).SetBytes(chal2s256)
		if rp.Cz != nil && cz.Cmp(rp.Cz) != 0 {
			return fmt.Errorf("RPVerify - Challenge Cz failing!")
		}

		h.Reset()
		h.Write(chal2s256)		// z
		rp.T1.X.FillBytes(buf)		// T1.x
		h.Write(buf)
		rp.T2.X.FillBytes(buf)		// T2.x
		h.Write(buf)
		chal3s256 := h.Sum(nil)
		cx = new(big.Int).SetBytes(chal3s256)
		if rp.Cx != nil && cx.Cmp(rp.Cx) != 0 {
			return fmt.Errorf("RPVerify - Challenge Cx failing!")
		}
	} else {
		cx = rp.Cx
		cy = rp.Cy
		cz = rp.Cz
	}

	/*
	fmt.Printf("G = (%x, %x)\n", EC.G.X, EC.G.Y);
	fmt.Printf("H = (%x, %x)\n", EC.H.X, EC.H.Y);
	fmt.Printf("V = %x\n", rp.Comm.X)
	fmt.Printf("n = %x\n", EC.V)
	fmt.Printf("A = %x\n", rp.A.X)
	fmt.Printf("S = %x\n", rp.S.X)
	fmt.Printf("y = %x\n", cy)
	fmt.Printf("z = %x\n", cz)
	v := 25
	aL := reverse(StrToBigIntArray(PadLeft(fmt.Sprintf("%b", v), "0", EC.V)))
	aR := VectorAddScalar(aL, big.NewInt(-1), EC.N)
	alpha, _ := new(big.Int).SetString("ade0b876903df1a0e56a5d4028bd8653b819d2bd1aed8da0ccef36a8c70d778b", 16)
	A := EC.TwoVectorPCommitWithGens(EC.BPG, EC.BPH, aL, aR).Add(EC.H.Mult(alpha))
	fmt.Printf("A' = %x\n", A.X)
	for i, p := range EC.BPG {
		fmt.Printf("G[%d]: (%x, %x)\n", i, p.X, p.Y)
		fmt.Printf("H[%d]: (%x, %x)\n", i, EC.BPH[i].X, EC.BPH[i].Y)
	}
	fmt.Printf("T1.x = %x\n", rp.T1.X)
	fmt.Printf("T2.x = %x\n", rp.T2.X)
	fmt.Printf("x = %x\n", cx)
	fmt.Printf("Th = %x\n", rp.Th)
	fmt.Printf("Tau = %x\n", rp.Tau)
	fmt.Printf("Mu = %x\n", rp.Mu)
	*/

	// given challenges are correct, very range proof
	PowersOfY := PowerVector(EC.V, cy, EC.N)

	// t_hat * G + tau * H
	lhs := EC.G.Mult(rp.Th).Add(EC.H.Mult(rp.Tau))

	// z^2 * V + delta(y,z) * G + x * T1 + x^2 * T2
	delta := Delta(EC, PowersOfY, cz)
	delta.Mul(delta, big.NewInt(int64(rp.Factor)))
	/*
	if delta.Cmp(big.NewInt(0)) < 0 {
		for delta.Add(delta, EC.N).Cmp(big.NewInt(0)) < 0 {
		}
	}
	*/
	rhs := rp.Comm.Mult(new(big.Int).Mul(cz, cz)).Add(
		EC.G.Mult(delta)).Add(
		rp.T1.Mult(cx)).Add(
		rp.T2.Mult(new(big.Int).Mul(cx, cx)))

	if !lhs.Equal(rhs) {
		fmt.Printf("rhs = %x\n", rhs)
		fmt.Printf("lhs = %x\n", lhs)
		return fmt.Errorf("RPVerify - Uh oh! Check line (63) of verification")
	}

	tmp1 := EC.Zero()
	zneg := new(big.Int).Mod(new(big.Int).Neg(cz), EC.N)
	for i := range EC.BPG {
		tmp1 = tmp1.Add(EC.BPG[i].Mult(zneg))
	}

	PowerOfTwos := PowerVector(EC.V, big.NewInt(2), EC.N)
	// @@ MPC
	if len(PowerOfTwos) != len(EC.BPG) {
		PowersOfY = expand(PowersOfY, len(EC.BPG))
		PowerOfTwos = expand(PowerOfTwos, len(EC.BPG))
	}
	// @@@
	tmp2 := EC.Zero()
	// generate h'
	HPrime := make([]ECPoint, len(EC.BPH))

	for i := range HPrime {
		mi := new(big.Int).ModInverse(PowersOfY[i], EC.N)
		HPrime[i] = EC.BPH[i].Mult(mi)
	}

	for i := range HPrime {
		val1 := new(big.Int).Mul(cz, PowersOfY[i])
		val2 := new(big.Int).Mul(new(big.Int).Mul(cz, cz), PowerOfTwos[i])
		val3 := new(big.Int).Add(val1, val2)
		tmp2 = tmp2.Add(HPrime[i].Mult(val3))
	}

	// without subtracting this value should equal muCH + l[i]G[i] + r[i]H'[i]
	// we want to make sure that the innerproduct checks out, so we subtract it
	P := rp.A.Add(rp.S.Mult(cx)).Add(tmp1).Add(tmp2).Add(EC.H.Mult(rp.Mu).Neg())
	//fmt.Println(P)

	var result bool
	if rp.IPP.A != nil {
		var th *big.Int
		if rp.LR != nil {
			th = rp.LR
		} else {
			th = rp.Th
		}
		result = InnerProductVerifyFast(EC, th, P, EC.U, EC.BPG, HPrime, rp.IPP)
	} else if rp.L != nil && rp.R != nil {
		result = P.Equal(EC.TwoVectorPCommitWithGens(EC.BPG, HPrime, rp.L, rp.R))
	} else {
		return fmt.Errorf("RPVerify - No proof!")
	}
	if !result {
		return fmt.Errorf("RPVerify - Uh oh! Check line (65) of verification!")
	}

	return nil
}
