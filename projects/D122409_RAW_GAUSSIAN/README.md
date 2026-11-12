# Fixed-Dimension 122409 Raw Gaussian Lift Limit

This isolated Lake project proves whole-sequence weak convergence of the actual raw atomic Gaussian lift at the fixed dimension `d = 122409`. Lean is pinned to `v4.34.0-rc2`; Mathlib is pinned in `lake-manifest.json`. The source dependency closure is included, so no repository-specific external Lean project is required.

```sh
lake build AImathPPhi2Clean.ActualWeakLimit122409
lake env lean EndpointContract122409.lean
```

## Endpoint and weighted-space convention

For every `L > 0` and `mass > 0`, `actualTarget_fixedVolume_weak_tendsto_gaussianLimit` proves convergence of the actual target probability laws indexed by `n : ℕ`, with `N = n + 1` and `a = L / N`. Every positive lattice scale is represented. The endpoint has no caller-supplied covariance convergence, tightness, marginal identification, or uniqueness hypothesis.

The target is the weighted Fourier realization of `H^{-61206}` on the fixed-volume periodic space: its frequency index is `Fin 122409 → ℤ` with the Pi sup norm; its weight is `(1 + ‖k‖)^(-2 * 61206)`. `TargetCompletion` is `lp ℂ 2`, and a raw coefficient `c k` is represented by `sqrt(targetWeight k) * c k`. This is the weight convention used by the theorem; no nonperiodic-space equivalence is asserted. The source random field is the actual finite lattice covariance Gaussian configuration, and the included atomic/site identity identifies its raw Fourier lift with the physical cell-weighted atomic measure.

## Checked proof chain

- `ActualTargetGaussianMeasure122409` proves target measurability, the actual Gaussian pushforward probability law, coordinate square integrability and second moments, the integral/series tail identity, and a uniform high-frequency cutoff valid for every scale.
- `TargetTruncation122409` proves finite-truncation continuity and the exact tail norm identity. Stronger `H^{-61205}` energy sublevels are compact in the target space. Tonelli and the actual uniform energy moment bound give tightness through Markov's inequality. Target separability and Prokhorov further-subsequence extraction are proved.
- `TargetCylinder122409` proves Borel generation by finite coordinate cylinders and uniqueness from all finite coordinate laws. It combines the concrete extraction theorem with convergent finite marginals to obtain whole-sequence convergence.
- `TargetFiniteMarginal122409` enumerates a finite set of modes with both real cosine/sine components. It proves that the actual target marginal law equals the continuous reconstruction of the actual physical Fourier family law, including its `sqrt(targetWeight)` normalization. The concrete covariance and finite Gaussian convergence chain is instantiated at `d = 122409`. Each limiting finite marginal is proved Gaussian.
- `ActualWeakLimit122409` obtains the unconditional whole-sequence endpoint, selects the target probability measure on the actual Borel carrier, identifies every finite marginal with its canonical periodic resolvent Gaussian law, and proves uniqueness by those marginals.

The generic finite-family covariance theorem used here has a complete proof from sampled Fourier coefficients, the lattice dispersion limit, and uniform Fourier cutoff estimates. Its inputs are discharged for the periodic cosine/sine tests. Final convergence theorems in this project are instantiated only at dimension `122409`.

## Scope and optional stronger target

The formal target is characterized by all finite coordinate laws, each a continuous real-linear image of the centered canonical periodic resolvent Gaussian. The project does not construct an arbitrary-dimensional convergence theorem or develop a general infinite-dimensional Gaussian theory. It does not assert a joint ultraviolet/infinite-volume limit or an interacting limit.

Real exponents are supported by the existing `Real.rpow` weights. The optional `H^{-61205}` target is feasible at the weight level: `fractionalSourceWeight_summable` checks the stronger exponent `61204.75 > 122409/2`, and `fractionalSource_to_61205_weight_ratio` checks the positive decay gap. This is an assessment of that alternative, not a convergence theorem in `H^{-61205}`. The completed endpoint retains the default `H^{-61206}` target and `H^{-61205}` source energy.

The endpoint contract prints theorem signatures and kernel axiom footprints. Core endpoint, marginal-identification, uniqueness, tightness and subsequence declarations have only `[propext, Classical.choice, Quot.sound]`; no custom axiom or `sorryAx` is used. Pinned verification output is retained under `audit/`.

The separate project directory preserves the main Lean project and server-only files. Build products are not versioned.
