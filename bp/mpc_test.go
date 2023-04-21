package bp

import (
	"crypto/rand"
	"math/big"
	"crypto/sha256"
	"testing"
	"fmt"
)

type PoB struct {
	m MPRangeContext
	proof RangeProof
	gamma *big.Int
}

var svals = []int{40, 60}
var dvals = []int{80, 10, 5, 5}

func TestMPC(t *testing.T) {
	ec := NewECPrimeGroupKey(NBITS)

	var srcs []*PoB
	var dsts []*PoB

	var cp RangeProof	// consolidated proof

	//
	// step 0
	//
	for _, v := range svals {
		gamma, err := rand.Int(rand.Reader, ec.N)
		if err != nil {
			t.Fatal(err)
		}
		comm := ec.G.Mult(big.NewInt(int64(v))).Add(ec.H.Mult(gamma))
		pob := &PoB{}
		RPProveStep0(ec, &pob.m, &pob.proof, big.NewInt(int64(v)), comm)
		pob.gamma = gamma
		srcs = append(srcs, pob)
	}
	for _, v := range dvals {
		gamma, err := rand.Int(rand.Reader, ec.N)
		if err != nil {
			t.Fatal(err)
		}
		comm := ec.G.Mult(big.NewInt(int64(v))).Add(ec.H.Mult(gamma))
		pob := &PoB{}
		RPProveStep0(ec, &pob.m, &pob.proof, big.NewInt(int64(v)), comm)
		pob.gamma = gamma
		dsts = append(dsts, pob)
	}

	// calculate y, z
	h := sha256.New()
	buf := make([]byte, 32)
	for _, pob := range srcs {
		cp.Comm = cp.Comm.Add(pob.proof.Comm)
		cp.A = cp.A.Add(pob.proof.A)
		cp.S = cp.S.Add(pob.proof.S)
	}
	for _, pob := range dsts {
		cp.Comm = cp.Comm.Sub(pob.proof.Comm)
		cp.A = cp.A.Add(pob.proof.A)
		cp.S = cp.S.Add(pob.proof.S)
	}
	cp.Comm.X.FillBytes(buf)	// comm
	h.Write(buf)
	h.Write([]byte{byte(ec.V)})	// n
	cp.A.X.FillBytes(buf)	// A.x
	h.Write(buf)
	cp.S.X.FillBytes(buf)	// S.x
	h.Write(buf)
	chal1s256 := h.Sum(nil)
	cy := new(big.Int).SetBytes(chal1s256)
	cp.Cy = cy
	
	h.Reset()
	cp.A.X.FillBytes(buf)	// A.x
	h.Write(buf)
	cp.S.X.FillBytes(buf)	// S.x
	h.Write(buf)
	h.Write(chal1s256)	// y
	chal2s256 := h.Sum(nil)
	cz := new(big.Int).SetBytes(chal2s256)
	cp.Cz = cz

	//
	// step 1
	//
	for _, pob := range append(srcs, dsts...) {
		pob.proof.Cy = cy
		pob.proof.Cz = cz
		RPProveStep1(ec, &pob.m, &pob.proof)
	}

	for _, pob := range srcs {
		cp.T1 = cp.T1.Add(pob.proof.T1)
		cp.T2 = cp.T2.Add(pob.proof.T2)
	}
	for _, pob := range dsts {
		cp.T1 = cp.T1.Sub(pob.proof.T1)
		cp.T2 = cp.T2.Sub(pob.proof.T2)
	}

	// calculate x
	h.Reset()
	h.Write(chal2s256)		// z
	cp.T1.X.FillBytes(buf)		// T1.x
	h.Write(buf)
	cp.T2.X.FillBytes(buf)		// T2.x
	h.Write(buf)
	chal3s256 := h.Sum(nil)
	cx := new(big.Int).SetBytes(chal3s256)
	cp.Cx = cx

	//
	// step 2
	//
	for _, pob := range append(srcs, dsts...) {
		pob.proof.Cx = cx
		pob.proof.Factor = 1
		pob.proof.ConsolidatedChallenge = true
		RPProveStep2(ec, &pob.m, &pob.proof, pob.gamma)
		if err := RPVerify(ec, pob.proof); err != nil {	// can't verify because of challenges
			t.Fatalf("Failed to verify share: %v", err)
		}
	}

	cp.Factor = 0
	cp.Tau = big.NewInt(0)
	cp.Th = big.NewInt(0)
	cp.Mu = big.NewInt(0)
	th := big.NewInt(0)
	n := len(srcs) + len(dsts)
	cp.L = make([]*big.Int, n * ec.V)
	cp.R = make([]*big.Int, n * ec.V)
	b := 0
	for _, pob := range srcs {
		cp.Tau.Mod(cp.Tau.Add(cp.Tau, pob.proof.Tau), ec.N)
		cp.Th.Mod(cp.Th.Add(cp.Th, pob.proof.Th), ec.N)
		cp.Mu.Mod(cp.Mu.Add(cp.Mu, pob.proof.Mu), ec.N)
		for i, l := range pob.proof.L {
			cp.L[i * n + b] = l
		}
		for i, r := range pob.proof.R {
			cp.R[i * n + b] = r
		}
		b += 1
		cp.Factor += 1
		th.Add(th, InnerProduct(pob.proof.L, pob.proof.R, ec.N))
	}
	for _, pob := range dsts {
		cp.Tau.Mod(cp.Tau.Add(cp.Tau, new(big.Int).Sub(ec.N, pob.proof.Tau)), ec.N)
		cp.Th.Mod(cp.Th.Add(cp.Th, new(big.Int).Sub(ec.N, pob.proof.Th)), ec.N)
		cp.Mu.Mod(cp.Mu.Add(cp.Mu, pob.proof.Mu), ec.N)
		for i, l := range pob.proof.L {
			cp.L[i * n + b] = l
		}
		for i, r := range pob.proof.R {
			cp.R[i * n + b] = r
		}
		b += 1
		cp.Factor -= 1
		th.Add(th, new(big.Int).Sub(ec.N, InnerProduct(pob.proof.L, pob.proof.R, ec.N)))
	}
	th.Mod(th, ec.N)

	// interleave g and h
	var iG, iH []ECPoint
	for i := 0; i < len(ec.BPG); i++ {
		for j := 0; j < n; j++ {
			iG = append(iG, ec.BPG[i])
			iH = append(iH, ec.BPH[i])
		}
	}
	ec.BPG = iG
	ec.BPH = iH

	RPProveStep3(ec, &cp)

	//
	// check if \Sum <l,r> ?= t^
	//
	if th.Cmp(cp.Th) != 0 {
		fmt.Println("\\Sum <l,r> != t^")
	}

	cp.LR = InnerProduct(cp.L, cp.R, ec.N)

	//
	// Verify it
	//
	if err := RPVerify(ec, cp); err != nil {
		t.Fatalf("Verification failed: %v", err)
	}

	fmt.Printf("MPC size = %d\n", len(cp.IPP.L) * 2 + 4 + 5)
}
