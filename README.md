# Periodic Gaussian Lattice Limits in Lean 4

A Lean 4 development of finite periodic-lattice Gaussian fields and their fixed-volume continuum limits. The repository now includes a parameterized Lean theorem for **every positive integer dimension**; the older two-, three-, four- and five-dimensional results remain available as separate proof releases.

**Start here:** [Architecture and dimensional constructions](#architecture-companion) · [Arbitrary-dimensional theorem](#arbitrary-dimension) · [Lean source and replay](#reproduce-the-arbitrary-dimensional-proof) · [Results index](#results-index) · [Scope and license](#scope-and-license)

## Architecture companion

The new **16-page architecture article** explains how the actual periodic lattice measures are connected to continuum coefficient laws, what can be reused, and where the source-specific mathematical work remains. It is a separate companion, not a replacement for the endpoint theorem paper below.

| Read or reproduce | Artifact |
|---|---|
| Architecture article | [PDF](paper/GAUSSIAN_LATTICE_FORMALIZATION_ARCHITECTURE/main.pdf) |
| Portable source and evidence | [Source archive](deliverables/20261113_gaussian_lattice_formalization_architecture_sources.zip) · [LaTeX, build and audit](paper/GAUSSIAN_LATTICE_FORMALIZATION_ARCHITECTURE/) |
| Review findings and limits | [Audit notes](paper/GAUSSIAN_LATTICE_FORMALIZATION_ARCHITECTURE/audit/AUDIT.md) · [Executed audit result](paper/GAUSSIAN_LATTICE_FORMALIZATION_ARCHITECTURE/audit/result.json) |
| Release downloads | [Architecture release](https://github.com/springoxn/pphi2-clean-finite-lattice/releases/tag/v2026.11.13-architecture) |

The article presents the two-, three-, four- and five-dimensional constructions individually, including their different weights, target measures and proved carrier maps. It then explains five interfaces: actual-source Fourier identities, energy bounds and compactness, finite Gaussian marginal convergence, Borel/cylinder uniqueness, and whole-sequence convergence. Mathematical specialization of the quantified theorem is distinguished from a formally implemented identification of historical laws.

The comparison with Bochner/Minlos, OSforGFF and the wider QFT formalization programme is pinned to inspected sources. In particular, the inspected OSforGFF theorem already treats every dimension at least two, and Bochner's proof itself uses weak-convergence methods. The distinction here is convergence of the specified periodic lattice laws, not arbitrary dimension alone. The broader reflection-positive and interacting-field work is described with its analytical evidence and external inputs separated from Gaussian Lean endpoints and reconstruction.

```sh
cd paper/GAUSSIAN_LATTICE_FORMALIZATION_ARCHITECTURE
python build.py
```

The article was compiled twice deterministically and rebuilt from its source archive in an independent directory with an identical PDF. Its audit checks frozen evidence and rendered output; it does not claim a fresh Lean replay.

## Arbitrary dimension

For every `d : ℕ` with `0 < d`, every real `s > d/2`, and fixed `L > 0` and `mass > 0`, the laws of the **actual raw atomic lattice Gaussian fields** converge weakly as `n → ∞`, with `N = n+1` and lattice spacing `a = L/N`. The target is the weighted Fourier-coefficient completion with weight

```text
w_s(k) = (1 + ‖k‖∞)^(-2s),  k ∈ ℤ^d.
```

The limiting probability measure is uniquely determined by all of its finite real Fourier marginals, whose covariance is the periodic massive Green pairing. The theorem constructs this limit from the lattice laws; it does not assume tightness, convergence, or target identification as an input.

| Read or reproduce | Artifact |
|---|---|
| Article | [PDF](paper/ARBITRARY_DIMENSIONAL_GAUSSIAN_LIMIT/main.pdf) · [LaTeX, build and audit](paper/ARBITRARY_DIMENSIONAL_GAUSSIAN_LIMIT/) |
| Main quantified theorem | [`SharpContractArbitraryDim.lean`](projects/ARBITRARY_DIM_RAW_GAUSSIAN/SharpContractArbitraryDim.lean) |
| Weak-limit construction | [`ActualWeakLimitArbitraryDim.lean`](projects/ARBITRARY_DIM_RAW_GAUSSIAN/AImathPPhi2Clean/ActualWeakLimitArbitraryDim.lean) |
| Pinned source project | [`projects/ARBITRARY_DIM_RAW_GAUSSIAN/`](projects/ARBITRARY_DIM_RAW_GAUSSIAN/) |
| Server build and typed-contract evidence | [Original Lean evidence archive](deliverables/20261112_arbitrary_dim_raw_gaussian.zip) |
| Article and source bundle | [Reproducible source archive](deliverables/20261112_arbitrary_dimensional_gaussian_limit_sources.zip) |

The sufficient range `s > d/2` is required for these unsmoothed atomic approximants; it is not claimed to be the optimal regularity threshold of the continuum field. The Fourier weight uses the sup norm, while the covariance dispersion uses the Euclidean sum of squares. The result is a massive **free-field**, fixed-volume theorem. It does not assert an interacting construction, an infinite-volume limit, Osterwalder--Schrader reconstruction, an isomorphism to an external distribution-space library, or a separate infinite-dimensional `IsGaussian` instance.

### Reproduce the arbitrary-dimensional proof

The standalone project pins Lean `v4.34.0-rc2` and Mathlib commit `852d20a84581aeba8527bd01d0be361d8c0e71c0`. From the repository root:

```sh
cd projects/ARBITRARY_DIM_RAW_GAUSSIAN
python verify_manifest.py
lake exe cache get
lake build AImathPPhi2Clean.ActualWeakLimitArbitraryDim
lake env lean SharpContractArbitraryDim.lean
lake env lean EndpointContractArbitraryDim.lean
```

The source manifest checks the packaged files before replay. The recorded theorem footprint is `{propext, Classical.choice, Quot.sound}`. A fresh Lean replay requires the pinned toolchain and dependencies; the committed logs are evidence of the successful server build and contract runs, not a substitute for replay.

## Results index

| Dimension | Result | Source or release |
|---|---|---|
| Any integer `d ≥ 1` | Actual raw atomic laws converge in weighted Fourier order `s > d/2`; all finite Gaussian marginals and uniqueness are formalized | [Parameterized Lean project](projects/ARBITRARY_DIM_RAW_GAUSSIAN/) · [Article](paper/ARBITRARY_DIMENSIONAL_GAUSSIAN_LIMIT/main.pdf) |
| 5 | Actual-source fixed-volume limit in weighted Fourier `H^-3` | [Pinned project and evidence bundle](paper/PERIODIC_GAUSSIAN_5D_HMINUS3/periodic_gaussian_5d_hminus3_endpoint.zip) · [Scope notes](paper/PERIODIC_GAUSSIAN_5D_HMINUS3/inputs/periodic5d_hminus3_endpoint.md) |
| 4 | Periodic raw-lift weak limit in the concrete weighted Fourier `H^-4` carrier | [Final Lean module](AImathPPhi2Clean/PeriodicFS4DProbeMoment.lean) · [Proof guide](docs/fs4/proof.md) |
| 3 | Actual-source weak limits in the `H^-4` carrier and the stronger `H^-3` endpoint | [H^-3 weak limit](AImathPPhi2Clean/Periodic3DHminusThreeWeakLimit.lean) · [Combined article](paper/PERIODIC_GAUSSIAN_3D_HMINUS3/periodic_gaussian_3d_hminus3_complete.pdf) |
| 2 | Finite-lattice Gaussian construction and periodic `H^-3` weak-limit chain | [Weak-limit module](AImathPPhi2Clean/PeriodicHMinusThreeWeakLimitMarginal.lean) · [Finite-lattice manuscript](docs/pphi2_clean_finite_lattice.pdf) |

For the common two- and four-dimensional proof architecture, see the [dimension-bridge article](paper/PERIODIC_GAUSSIAN_DIMENSION_BRIDGE/periodic_gaussian_dimension_bridge.pdf). Earlier dimensional statements and release snapshots remain documented in their own papers and archives; they should not be confused with the quantified theorem above.

## Verification

The repository-wide manifest and portable audits can be checked without Lean:

```sh
python verify.py
python verify.py --ext --fs4
python audit/check_fs4_release.py --self-test
```

To rebuild the core library and replay its four-dimensional contract, install elan and run `python verify.py --all`. The arbitrary-dimensional project has its own pinned source manifest and replay commands above. The finite numerical probes are supplementary checks; they are not proofs of the infinite-family theorem.

## Scope and license

All continuum limits here are at fixed positive physical volume and mass. The four-dimensional result is free, not interacting. No section of this repository establishes an infinite-volume interacting four-dimensional field or Osterwalder--Schrader reconstruction.

Licensed under Apache-2.0; see [LICENSE](LICENSE) and [NOTICE](NOTICE). The release excludes credentials, local toolchains and compiled dependency caches.
