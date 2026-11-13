# Arbitrary-dimensional raw atomic Gaussian weak convergence

The final source proves the whole-sequence fixed-volume weak limit of actual raw atomic lattice Gaussian probability measures for every positive dimension d and every real target order s>d/2. The target coefficient weight is exactly (1+norm k)^(-2s). The internal source order is (s+d/2)/2 and the gap is positive.

The theorem is `Pphi2Clean.ArbitraryDimContract.sharp_actual_raw_gaussian_weak_convergence` in `SharpContractArbitraryDim.lean`. Its limit is unique and characterized by all continuum Fourier Gaussian finite marginals. The atomic Fourier sum and actual target-lift identities are checked in the same contract. Standard Lean axioms only: propext, Classical.choice, Quot.sound.

The package includes the recursive local source import closure and pinned Lake configuration; dependency packages and build caches are excluded. Use the pinned Lean toolchain and mathlib revision from the included configuration. With matching dependencies available, run:

```sh
python verify_manifest.py
lake build AImathPPhi2Clean.ActualWeakLimitArbitraryDim
lake env lean SharpContractArbitraryDim.lean
lake env lean EndpointContractArbitraryDim.lean
```

`build-sharp.log` and `sharp-contract.log` record the final sharp proof. `endpoint-contract.log` rechecks the original r+1 theorem against the final generalized source. All packaged logs correspond to the packaged final sources.

The original fixed-dimensional source and pinned dependency package contents were used read-only. New Lean modules use the ArbitraryDim namespace/module suffix. No source `sorry` or new axiom declarations occur in the new generic modules or typed contracts.
