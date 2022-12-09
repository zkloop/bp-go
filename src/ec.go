package bp

import (
	"math/big"
	"crypto/elliptic"
	btcec "github.com/btcsuite/btcd/btcec/v2"
)


// var EC CryptoParams

type ECPoint struct {
	X, Y *big.Int
	C elliptic.Curve
}

func NewECPoint(x, y *big.Int) ECPoint {
	return ECPoint{x, y, btcec.S256()}
}

// Equal returns true if points p (self) and p2 (arg) are the same.
func (p ECPoint) Equal(p2 ECPoint) bool {
	if p.X.Cmp(p2.X) == 0 && p2.Y.Cmp(p2.Y) == 0 {
		return true
	}
	return false
}

// Mult multiplies point p by scalar s and returns the resulting point
func (p ECPoint) Mult(s *big.Int) ECPoint {
	modS := new(big.Int).Mod(s, p.C.Params().N)
	X, Y := p.C.ScalarMult(p.X, p.Y, modS.Bytes())
	return NewECPoint(X, Y)
}

// Add adds points p and p2 and returns the resulting point
func (p ECPoint) Add(p2 ECPoint) ECPoint {
	if (p.X == nil || p.Y == nil) {
		return p2
	}
	X, Y := p.C.Add(p.X, p.Y, p2.X, p2.Y)
	return NewECPoint(X, Y)
}

// Neg returns the additive inverse of point p
func (p ECPoint) Neg() ECPoint {
	negY := new(big.Int).Neg(p.Y)
	modValue := negY.Mod(negY, p.C.Params().P) // mod P is fine here because we're describing a curve point
	return NewECPoint(p.X, modValue)
}

func (p ECPoint) Sub(p2 ECPoint) ECPoint {
	return p.Add(p2.Neg())
}
