// Copyright 2020 Consensys Software Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// Code generated by consensys/gnark-crypto DO NOT EDIT

package fft

import (
	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark-crypto/internal/parallel"
	"math/big"
	"math/bits"

	"github.com/consensys/gnark-crypto/ecc/bls12-381/fr"
)

// Decimation is used in the FFT call to select decimation in time or in frequency
type Decimation uint8

const (
	DIT Decimation = iota
	DIF
)

// parallelize threshold for a single butterfly op, if the fft stage is not parallelized already
const butterflyThreshold = 16

// FFT computes (recursively) the discrete Fourier transform of a and stores the result in a
// if decimation == DIT (decimation in time), the input must be in bit-reversed order
// if decimation == DIF (decimation in frequency), the output will be in bit-reversed order
func (domain *Domain) FFT(a []fr.Element, decimation Decimation, opts ...Option) {

	opt := fftOptions(opts...)

	// find the stage where we should stop spawning go routines in our recursive calls
	// (ie when we have as many go routines running as we have available CPUs)
	maxSplits := bits.TrailingZeros64(ecc.NextPowerOfTwo(uint64(opt.nbTasks)))
	if opt.nbTasks == 1 {
		maxSplits = -1
	}

	// if coset != 0, scale by coset table
	if opt.coset {
		if decimation == DIT {
			// scale by coset table (in bit reversed order)
			cosetTable := domain.cosetTable
			if !domain.withPrecompute {
				// we need to build the full table or do a bit reverse dance.
				cosetTable = make([]fr.Element, len(a))
				BuildExpTable(domain.FrMultiplicativeGen, cosetTable)
			}
			parallel.Execute(len(a), func(start, end int) {
				n := uint64(len(a))
				nn := uint64(64 - bits.TrailingZeros64(n))
				for i := start; i < end; i++ {
					irev := int(bits.Reverse64(uint64(i)) >> nn)
					a[i].Mul(&a[i], &cosetTable[irev])
				}
			}, opt.nbTasks)
		} else {
			if domain.withPrecompute {
				parallel.Execute(len(a), func(start, end int) {
					for i := start; i < end; i++ {
						a[i].Mul(&a[i], &domain.cosetTable[i])
					}
				}, opt.nbTasks)
			} else {
				c := domain.FrMultiplicativeGen
				parallel.Execute(len(a), func(start, end int) {
					var at fr.Element
					at.Exp(c, big.NewInt(int64(start)))
					for i := start; i < end; i++ {
						a[i].Mul(&a[i], &at)
						at.Mul(&at, &c)
					}
				}, opt.nbTasks)
			}

		}
	}

	twiddles := domain.twiddles
	twiddlesStartStage := 0
	if !domain.withPrecompute {
		twiddlesStartStage = 3
		nbStages := int(bits.TrailingZeros64(domain.Cardinality))
		twiddles = make([][]fr.Element, nbStages-twiddlesStartStage)
		w := domain.Generator
		w.Exp(w, big.NewInt(int64(1<<twiddlesStartStage)))
		buildTwiddles(twiddles, w, uint64(nbStages-twiddlesStartStage))
	}

	switch decimation {
	case DIF:
		difFFT(a, domain.Generator, twiddles, twiddlesStartStage, 0, maxSplits, nil, opt.nbTasks)
	case DIT:
		ditFFT(a, domain.Generator, twiddles, twiddlesStartStage, 0, maxSplits, nil, opt.nbTasks)
	default:
		panic("not implemented")
	}
}

// FFTInverse computes (recursively) the inverse discrete Fourier transform of a and stores the result in a
// if decimation == DIT (decimation in time), the input must be in bit-reversed order
// if decimation == DIF (decimation in frequency), the output will be in bit-reversed order
// coset sets the shift of the fft (0 = no shift, standard fft)
// len(a) must be a power of 2, and w must be a len(a)th root of unity in field F.
func (domain *Domain) FFTInverse(a []fr.Element, decimation Decimation, opts ...Option) {
	opt := fftOptions(opts...)

	// find the stage where we should stop spawning go routines in our recursive calls
	// (ie when we have as many go routines running as we have available CPUs)
	maxSplits := bits.TrailingZeros64(ecc.NextPowerOfTwo(uint64(opt.nbTasks)))
	if opt.nbTasks == 1 {
		maxSplits = -1
	}

	twiddlesInv := domain.twiddlesInv
	twiddlesStartStage := 0
	if !domain.withPrecompute {
		twiddlesStartStage = 3
		nbStages := int(bits.TrailingZeros64(domain.Cardinality))
		twiddlesInv = make([][]fr.Element, nbStages-twiddlesStartStage)
		w := domain.GeneratorInv
		w.Exp(w, big.NewInt(int64(1<<twiddlesStartStage)))
		buildTwiddles(twiddlesInv, w, uint64(nbStages-twiddlesStartStage))
	}

	switch decimation {
	case DIF:
		difFFT(a, domain.GeneratorInv, twiddlesInv, twiddlesStartStage, 0, maxSplits, nil, opt.nbTasks)
	case DIT:
		ditFFT(a, domain.GeneratorInv, twiddlesInv, twiddlesStartStage, 0, maxSplits, nil, opt.nbTasks)
	default:
		panic("not implemented")
	}

	// scale by CardinalityInv
	if !opt.coset {
		parallel.Execute(len(a), func(start, end int) {
			for i := start; i < end; i++ {
				a[i].Mul(&a[i], &domain.CardinalityInv)
			}
		}, opt.nbTasks)
		return
	}

	if decimation == DIT {
		if domain.withPrecompute {
			parallel.Execute(len(a), func(start, end int) {
				for i := start; i < end; i++ {
					a[i].Mul(&a[i], &domain.cosetTableInv[i]).
						Mul(&a[i], &domain.CardinalityInv)
				}
			}, opt.nbTasks)
		} else {
			c := domain.FrMultiplicativeGenInv
			parallel.Execute(len(a), func(start, end int) {
				var at fr.Element
				at.Exp(c, big.NewInt(int64(start)))
				at.Mul(&at, &domain.CardinalityInv)
				for i := start; i < end; i++ {
					a[i].Mul(&a[i], &at)
					at.Mul(&at, &c)
				}
			}, opt.nbTasks)
		}
		return
	}

	// decimation == DIF, need to access coset table in bit reversed order.
	cosetTableInv := domain.cosetTableInv
	if !domain.withPrecompute {
		// we need to build the full table or do a bit reverse dance.
		cosetTableInv = make([]fr.Element, len(a))
		BuildExpTable(domain.FrMultiplicativeGenInv, cosetTableInv)
	}
	parallel.Execute(len(a), func(start, end int) {
		n := uint64(len(a))
		nn := uint64(64 - bits.TrailingZeros64(n))
		for i := start; i < end; i++ {
			irev := int(bits.Reverse64(uint64(i)) >> nn)
			a[i].Mul(&a[i], &cosetTableInv[irev]).
				Mul(&a[i], &domain.CardinalityInv)
		}
	}, opt.nbTasks)

}

func difFFT(a []fr.Element, w fr.Element, twiddles [][]fr.Element, twiddlesStartStage, stage, maxSplits int, chDone chan struct{}, nbTasks int) {
	if chDone != nil {
		defer close(chDone)
	}

	n := len(a)
	if n == 1 {
		return
	} else if n == 256 && stage >= twiddlesStartStage {
		kerDIFNP_256(a, twiddles, stage-twiddlesStartStage)
		return
	}
	m := n >> 1

	parallelButterfly := (m > butterflyThreshold) && (stage < maxSplits)

	if stage < twiddlesStartStage {
		if parallelButterfly {
			w := w
			parallel.Execute(m, func(start, end int) {
				if start == 0 {
					fr.Butterfly(&a[0], &a[m])
					start++
				}
				var at fr.Element
				at.Exp(w, big.NewInt(int64(start)))
				innerDIFWithoutTwiddles(a, at, w, start, end, m)
			}, nbTasks/(1<<(stage))) // 1 << stage == estimated used CPUs
		} else {
			innerDIFWithoutTwiddles(a, w, w, 0, m, m)
		}
		// compute next twiddle
		w.Square(&w)
	} else {
		if parallelButterfly {
			parallel.Execute(m, func(start, end int) {
				innerDIFWithTwiddles(a, twiddles[stage-twiddlesStartStage], start, end, m)
			}, nbTasks/(1<<(stage)))
		} else {
			innerDIFWithTwiddles(a, twiddles[stage-twiddlesStartStage], 0, m, m)
		}
	}

	if m == 1 {
		return
	}

	nextStage := stage + 1
	if stage < maxSplits {
		chDone := make(chan struct{}, 1)
		go difFFT(a[m:n], w, twiddles, twiddlesStartStage, nextStage, maxSplits, chDone, nbTasks)
		difFFT(a[0:m], w, twiddles, twiddlesStartStage, nextStage, maxSplits, nil, nbTasks)
		<-chDone
	} else {
		difFFT(a[0:m], w, twiddles, twiddlesStartStage, nextStage, maxSplits, nil, nbTasks)
		difFFT(a[m:n], w, twiddles, twiddlesStartStage, nextStage, maxSplits, nil, nbTasks)
	}

}

func innerDIFWithTwiddles(a []fr.Element, twiddles []fr.Element, start, end, m int) {
	if start == 0 {
		fr.Butterfly(&a[0], &a[m])
		start++
	}
	for i := start; i < end; i++ {
		fr.Butterfly(&a[i], &a[i+m])
		a[i+m].Mul(&a[i+m], &twiddles[i])
	}
}

func innerDIFWithoutTwiddles(a []fr.Element, at, w fr.Element, start, end, m int) {
	if start == 0 {
		fr.Butterfly(&a[0], &a[m])
		start++
	}
	for i := start; i < end; i++ {
		fr.Butterfly(&a[i], &a[i+m])
		a[i+m].Mul(&a[i+m], &at)
		at.Mul(&at, &w)
	}
}

func ditFFT(a []fr.Element, w fr.Element, twiddles [][]fr.Element, twiddlesStartStage, stage, maxSplits int, chDone chan struct{}, nbTasks int) {
	if chDone != nil {
		defer close(chDone)
	}
	n := len(a)
	if n == 1 {
		return
	} else if n == 256 && stage >= twiddlesStartStage {
		kerDITNP_256(a, twiddles, stage-twiddlesStartStage)
		return
	}
	m := n >> 1

	nextStage := stage + 1
	nextW := w
	nextW.Square(&nextW)

	if stage < maxSplits {
		// that's the only time we fire go routines
		chDone := make(chan struct{}, 1)
		go ditFFT(a[m:], nextW, twiddles, twiddlesStartStage, nextStage, maxSplits, chDone, nbTasks)
		ditFFT(a[0:m], nextW, twiddles, twiddlesStartStage, nextStage, maxSplits, nil, nbTasks)
		<-chDone
	} else {
		ditFFT(a[0:m], nextW, twiddles, twiddlesStartStage, nextStage, maxSplits, nil, nbTasks)
		ditFFT(a[m:n], nextW, twiddles, twiddlesStartStage, nextStage, maxSplits, nil, nbTasks)
	}

	parallelButterfly := (m > butterflyThreshold) && (stage < maxSplits)

	if stage < twiddlesStartStage {
		// we need to compute the twiddles for this stage on the fly.
		if parallelButterfly {
			w := w
			parallel.Execute(m, func(start, end int) {
				if start == 0 {
					fr.Butterfly(&a[0], &a[m])
					start++
				}
				var at fr.Element
				at.Exp(w, big.NewInt(int64(start)))
				innerDITWithoutTwiddles(a, at, w, start, end, m)
			}, nbTasks/(1<<(stage))) // 1 << stage == estimated used CPUs

		} else {
			innerDITWithoutTwiddles(a, w, w, 0, m, m)
		}
		return
	}
	if parallelButterfly {
		parallel.Execute(m, func(start, end int) {
			innerDITWithTwiddles(a, twiddles[stage-twiddlesStartStage], start, end, m)
		}, nbTasks/(1<<(stage)))
	} else {
		innerDITWithTwiddles(a, twiddles[stage-twiddlesStartStage], 0, m, m)
	}
}

func innerDITWithTwiddles(a []fr.Element, twiddles []fr.Element, start, end, m int) {
	if start == 0 {
		fr.Butterfly(&a[0], &a[m])
		start++
	}
	for i := start; i < end; i++ {
		a[i+m].Mul(&a[i+m], &twiddles[i])
		fr.Butterfly(&a[i], &a[i+m])
	}
}

func innerDITWithoutTwiddles(a []fr.Element, at, w fr.Element, start, end, m int) {
	if start == 0 {
		fr.Butterfly(&a[0], &a[m])
		start++
	}
	for i := start; i < end; i++ {
		a[i+m].Mul(&a[i+m], &at)
		fr.Butterfly(&a[i], &a[i+m])
		at.Mul(&at, &w)
	}
}

func kerDIFNP_256(a []fr.Element, twiddles [][]fr.Element, stage int) {
	// code unrolled & generated by internal/generator/fft/template/fft.go.tmpl

	innerDIFWithTwiddles(a[:256], twiddles[stage+0], 0, 128, 128)
	for offset := 0; offset < 256; offset += 128 {
		innerDIFWithTwiddles(a[offset:offset+128], twiddles[stage+1], 0, 64, 64)
	}
	for offset := 0; offset < 256; offset += 64 {
		innerDIFWithTwiddles(a[offset:offset+64], twiddles[stage+2], 0, 32, 32)
	}
	for offset := 0; offset < 256; offset += 32 {
		innerDIFWithTwiddles(a[offset:offset+32], twiddles[stage+3], 0, 16, 16)
	}
	for offset := 0; offset < 256; offset += 16 {
		innerDIFWithTwiddles(a[offset:offset+16], twiddles[stage+4], 0, 8, 8)
	}
	for offset := 0; offset < 256; offset += 8 {
		innerDIFWithTwiddles(a[offset:offset+8], twiddles[stage+5], 0, 4, 4)
	}
	for offset := 0; offset < 256; offset += 4 {
		innerDIFWithTwiddles(a[offset:offset+4], twiddles[stage+6], 0, 2, 2)
	}
	for offset := 0; offset < 256; offset += 2 {
		fr.Butterfly(&a[offset], &a[offset+1])
	}
}

func kerDITNP_256(a []fr.Element, twiddles [][]fr.Element, stage int) {
	// code unrolled & generated by internal/generator/fft/template/fft.go.tmpl

	for offset := 0; offset < 256; offset += 2 {
		fr.Butterfly(&a[offset], &a[offset+1])
	}
	for offset := 0; offset < 256; offset += 4 {
		innerDITWithTwiddles(a[offset:offset+4], twiddles[stage+6], 0, 2, 2)
	}
	for offset := 0; offset < 256; offset += 8 {
		innerDITWithTwiddles(a[offset:offset+8], twiddles[stage+5], 0, 4, 4)
	}
	for offset := 0; offset < 256; offset += 16 {
		innerDITWithTwiddles(a[offset:offset+16], twiddles[stage+4], 0, 8, 8)
	}
	for offset := 0; offset < 256; offset += 32 {
		innerDITWithTwiddles(a[offset:offset+32], twiddles[stage+3], 0, 16, 16)
	}
	for offset := 0; offset < 256; offset += 64 {
		innerDITWithTwiddles(a[offset:offset+64], twiddles[stage+2], 0, 32, 32)
	}
	for offset := 0; offset < 256; offset += 128 {
		innerDITWithTwiddles(a[offset:offset+128], twiddles[stage+1], 0, 64, 64)
	}
	innerDITWithTwiddles(a[:256], twiddles[stage+0], 0, 128, 128)
}