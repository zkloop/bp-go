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
	EC = NewECPrimeGroupKey(NBITS)
	gamma, err := rand.Int(rand.Reader, EC.N)
	check(err)
	// Testing smallest number in range
	if RPVerify(RPProve(big.NewInt(0), gamma, uncompress)) {
		fmt.Println("Range Proof Verification works")
	} else {
		t.Error("*****Range Proof FAILURE")
	}
}

func TestRPVerify2(t *testing.T) {
	EC = NewECPrimeGroupKey(NBITS)
	gamma, err := rand.Int(rand.Reader, EC.N)
	check(err)
	// Testing largest number in range
	if RPVerify(RPProve(new(big.Int).Sub(new(big.Int).Exp(big.NewInt(2), big.NewInt(NBITS - 1), EC.N), big.NewInt(1)), gamma, uncompress)) {
		fmt.Println("Range Proof Verification works")
	} else {
		t.Error("*****Range Proof FAILURE")
	}
}

func TestRPVerify3(t *testing.T) {
	EC = NewECPrimeGroupKey(NBITS)
	gamma, err := rand.Int(rand.Reader, EC.N)
	check(err)
	// Testing the value 3
	if RPVerify(RPProve(big.NewInt(3), gamma, uncompress)) {
		fmt.Println("Range Proof Verification works")
	} else {
		t.Error("*****Range Proof FAILURE")
	}
}

func TestRPVerifyRand(t *testing.T) {
	EC = NewECPrimeGroupKey(NBITS)
	gamma, err := rand.Int(rand.Reader, EC.N)
	check(err)

	ran, err := rand.Int(rand.Reader, new(big.Int).Exp(big.NewInt(2), big.NewInt(NBITS), EC.N))
	check(err)

	// Testing the value 3
	if RPVerify(RPProve(ran, gamma, uncompress)) {
		fmt.Println("Range Proof Verification works")
	} else {
		t.Error("*****Range Proof FAILURE")
		fmt.Printf("Random Value: %s", ran.String())
	}
}
