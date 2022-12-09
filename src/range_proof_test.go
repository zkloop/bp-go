package bp

import (
	"crypto/rand"
	"fmt"
	"math/big"
	"testing"
)

const NBITS = 20
const uncompress = false

func TestRPVerify1(t *testing.T) {
	EC := NewECPrimeGroupKey(NBITS)
	gamma, err := rand.Int(rand.Reader, EC.N)
	check(err)
	// Testing smallest number in range
	if err := RPVerify(EC, RPProve(EC, big.NewInt(0), gamma, uncompress)); err == nil {
		fmt.Println("Range Proof Verification works")
	} else {
		t.Errorf("*****Range Proof FAILURE: %v", err)
	}
}

func TestRPVerify2(t *testing.T) {
	EC := NewECPrimeGroupKey(NBITS)
	gamma, err := rand.Int(rand.Reader, EC.N)
	check(err)
	// Testing largest number in range
	if err := RPVerify(EC, RPProve(EC, new(big.Int).Sub(new(big.Int).Exp(big.NewInt(2), big.NewInt(NBITS - 1), EC.N), big.NewInt(1)), gamma, uncompress)); err == nil {
		fmt.Println("Range Proof Verification works")
	} else {
		t.Errorf("*****Range Proof FAILURE: %v", err)
	}
}

func TestRPVerify3(t *testing.T) {
	EC := NewECPrimeGroupKey(NBITS)
	gamma, err := rand.Int(rand.Reader, EC.N)
	check(err)
	// Testing the value 3
	if err := RPVerify(EC, RPProve(EC, big.NewInt(3), gamma, uncompress)); err == nil {
		fmt.Println("Range Proof Verification works")
	} else {
		t.Errorf("*****Range Proof FAILURE: %v", err)
	}
}

func TestRPVerifyRand(t *testing.T) {
	EC := NewECPrimeGroupKey(NBITS)
	gamma, err := rand.Int(rand.Reader, EC.N)
	check(err)

	ran, err := rand.Int(rand.Reader, new(big.Int).Exp(big.NewInt(2), big.NewInt(NBITS), EC.N))
	check(err)

	// Testing the value 3
	if err := RPVerify(EC, RPProve(EC, ran, gamma, uncompress)); err == nil {
		fmt.Println("Range Proof Verification works")
	} else {
		t.Errorf("*****Range Proof FAILURE: %v", err)
		fmt.Printf("Random Value: %s", ran.String())
	}
}
