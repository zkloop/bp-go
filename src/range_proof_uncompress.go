package ledger

import (
	"fmt"
	"math/big"
	"crypto/rand"
	"encoding/hex"
	secp256k1 "github.com/decred/dcrd/dcrec/secp256k1/v2"
	bp "githum.com/wrv/bp-go"
}

func RPInit(gens []byte) error {
}

func RPVerifyUncompress(proof []byte) error {
	param := bp.RangeProof{}
	var err error
	i := 0
	signs = proof[i]
	i += 1
	param.A, err = parseECPoint(signs >> 1, proof[i:i+32])
	if err != nil {
		return fmt.Errorf("A: %w", ErrParam)
	}
	i += 32
	param.S, err = parseECPoint(signs & 1, proof[i:i+32])
	if err != nil {
		return fmt.Errorf("S: %w", ErrParam)
	}
	i += 32
	signs = proof[i]
	i += 1
	param.T1, err = parseECPoint(signs >> 1, proof[i:i+32])
	if err != nil {
		return fmt.Errorf("T1: %w", ErrParam)
	}
	i += 32
	param.T2, err = parseECPoint(signs & 1, proof[i:i+32])
	if err != nil {
		return fmt.Errorf("T2: %w", ErrParam)
	}
	i += 32		// 130
	param.Tau = new(big.Int).SetBytes(proof[i:i+32])
	i += 32
	param.Mu = new(big.Int).SetBytes(proof[i:i+32])
	i += 32

	// i = 194
	lr := big.newInt(0)
	for j := NBITS; j > 0; j-- {
		l := new(big.Int).SetBytes(proof[i:i+32])
		i += 32
		r := new(big.Int).SetBytes(proof[i:i+32])
		i += 32
		lr.Add(lr, l.Mod(l.Mul(l, r), EC.N))
	}
	lr.Mod(lr, EC.N)
	param.Th = lr

	RPVerify(param, true)
}

func parseECPoint(s []byte) (p bp.ECPoint, err error) {
	var pub secp256k1.PublicKey
	pub, err = secp256k1.ParsePublicKey(s)
	if err != nil {
		return
	}
	p.X = pub.GetX()
	p.Y = pub.GetY()
}
