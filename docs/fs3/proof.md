# Fixed-volume 3D periodic Gaussian raw atomic weak limit

## Theorem

For fixed `L > 0` and `mass > 0`, set `N = n + 1` and `a = L / N`. The actual three-dimensional finite lattice Gaussian law, pushed forward by the raw atomic Fourier lift with site coefficient `a^3`, converges weakly on the weighted Fourier `H^-4` carrier to the explicit conjugate-symmetric Gaussian target.

The exported Lean endpoint is `Pphi2Clean.Continuum.periodic3DFixedVolume_weak_tendsto_gaussianTarget` in `AImathPPhi2Clean/Periodic3DGaussianWeakLimit.lean`. Its only assumptions are `0 < L` and `0 < mass`; its axiom footprint is `[propext, Classical.choice, Quot.sound]`.

## Proof chain

- `Periodic3DFiniteSourceLift` and `Periodic3DWeightedFiniteSource` define and connect the actual `Fin 3` physical raw atomic source, including the `a^3` coefficient.
- `Periodic3DCarrierEnergy`, `Periodic3DCompactEmbedding`, and `Periodic3DTightness` establish uniform second moments, compact containment from `H^-3` into `H^-4`, and subsequential weak limits.
- `Periodic3DFiniteMarginal`, `Periodic3DAtomicMarginal`, and `Periodic3DCanonicalMarginal` prove convergence of actual finite joint real Fourier families to the 3D periodic-resolvent Gaussian marginals.
- `Periodic3DWeakLimitExistence` obtains full convergence from tightness and uniqueness of subsequential limits; it does not assume the limit.
- `Periodic3DGaussianTarget` constructs the target by restricting the 4D Gaussian Fourier carrier to fourth frequency zero and multiplying by `(sqrt L)^(-1)`. This gives `L^3` scaling while retaining the 3D mass symbol; it is a spectral construction, not a spatial trace.
- `Periodic3DTargetMarginalBridge` and `Periodic3DCanonicalCovariance` identify the joint canonical Gaussian laws with the explicit resolvent marginals. `Periodic3DRealCarrier` proves conjugate-symmetry support and its preservation under weak limits. `Periodic3DGaussianWeakLimit` identifies every limit using canonical coordinates on that real carrier.
- `Periodic3DGaussianFourierMarginals` exports direct target projection interfaces for arbitrary finite Fourier families, including repeated modes and degenerate zero-sine coordinates.

## Normalization and exceptional modes

The zero real coordinate has variance `L^3 / mass^2`; its imaginary coordinate vanishes on the real carrier. Nonzero canonical cosine and sine coordinates have variance `L^3 / (2 * torusMassSymbol 3 L mass k)`. The target scale is checked by `((sqrt L)^(-1))^2 * L^4 = L^3` and the restriction identity for the mass symbol.

Mode-pairing and covariance proofs separate zero modes, use eventual nonaliasing for each fixed finite family, and exclude self-negative Nyquist modes once `N > |2k|`. Exceptional finite meshes are not claimed to have continuum diagonal covariance. Joint covariance and finite-dimensional law equality are proved, rather than inferred from coordinate variances alone.

## Scope and verification

This is fixed-volume, positive-mass, free Gaussian weak convergence in the weighted Fourier `H^-4` realization. It is not convergence in `H^-3`, an interacting or infinite-volume limit, a spatial trace theorem, or OS reconstruction.

Built against the repository's pinned Lean toolchain and Mathlib revision using:

```bash
lake build AImathPPhi2Clean.Periodic3DGaussianWeakLimit AImathPPhi2Clean.Periodic3DGaussianFourierMarginals
```

The final convergence theorem and the two direct Fourier-marginal interfaces have only the foundational axiom footprint `[propext, Classical.choice, Quot.sound]`.
