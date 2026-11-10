# pphi2-clean-finite-lattice

Lean 4 proofs of finite periodic-lattice Gaussian fields and their fixed-volume
continuum limits in **two, three and four dimensions**. The repository name retains
its original two-dimensional history; the four-dimensional result is a massive
**free-field** limit, not an interacting four-dimensional construction.

## Article connecting the two- and four-dimensional proofs

**[Read the PDF](paper/PERIODIC_GAUSSIAN_DIMENSION_BRIDGE/periodic_gaussian_dimension_bridge.pdf)** ·
[LaTeX source and build instructions](paper/PERIODIC_GAUSSIAN_DIMENSION_BRIDGE/) ·
[Download source archive](paper/PERIODIC_GAUSSIAN_DIMENSION_BRIDGE/periodic_gaussian_dimension_bridge_sources.zip)

*Periodic Gaussian lattice limits in two and four dimensions: a common proof
mechanism and its Lean realization* compares the native formal results,
gives a common paper proof, and explains carrier conventions, aliases,
compactness and real-supported measure uniqueness. It includes a newly executed
joint Lean contract for both final theorems and an audit of the compiled PDF.
The article also records and corrects a physical-scale factor in the earlier
four-dimensional proof guide; the Lean sources are unchanged.

## New: the four-dimensional periodic raw-lift limit

For every `L > 0` and `mass > 0`, let `N = n+1`, `a = L/N` and take the centered
Gaussian on `(Z/NZ)^4` with site covariance `a^-4 (mass^2 - Delta_a)^-1`.
The laws of its raw atomic lifts

```text
X_N = a^4 sum_x phi_x delta_[a x]
```

converge weakly on the concrete weighted Fourier `H^-4(T_L^4)` carrier to the
explicit real-supported periodic Gaussian law with covariance symbol

```text
(mass^2 + (2*pi/L)^2 * sum_i k_i^2)^(-1).
```

The final theorem is
[`Pphi2Clean.Continuum.fs4PeriodicFixedVolume_weak_tendsto_free`](AImathPPhi2Clean/PeriodicFS4DProbeMoment.lean).
Its only explicit hypotheses are positivity of `L` and `mass`. It uses the
actual lattice lift laws and a constructed target law, without caller-supplied
tightness, target-marginal or sublimit-identification hypotheses.

| Step | Published Lean source |
|---|---|
| Four-dimensional summable Sobolev weights | [PeriodicFS4DSobolevWeights](AImathPPhi2Clean/PeriodicFS4DSobolevWeights.lean) |
| Weighted Fourier carrier and conjugate-symmetric real support | [PeriodicFS4DWeightedCarrier](AImathPPhi2Clean/PeriodicFS4DWeightedCarrier.lean), [PeriodicFS4DRealCarrier](AImathPPhi2Clean/PeriodicFS4DRealCarrier.lean) |
| Compact `H^-3` balls in `H^-4` | [PeriodicFS4DCompactEmbedding](AImathPPhi2Clean/PeriodicFS4DCompactEmbedding.lean) |
| Actual raw-lift moment bound, explicit Gaussian series, finite marginals, tightness, uniqueness and full weak convergence | [PeriodicFS4DProbeMoment](AImathPPhi2Clean/PeriodicFS4DProbeMoment.lean) |
| Model-matched lattice covariance limit | [PeriodicFourierCovarianceLimit](AImathPPhi2Clean/PeriodicFourierCovarianceLimit.lean) |

The [proof guide](docs/fs4/proof.md) explains the normalization, aliases,
zero/Nyquist modes, real cosine/sine coordinates and theorem assembly. The
[typed contract](audit/fs4_periodic_raw_lift_interface.lean) independently checks
the final statement and queries the signatures and axiom footprints of four
core theorems. The [release evidence](docs/fs4/release_evidence.json) binds the
entire current Lean library, root, toolchain, dependency lock and contract to a
fresh build and its raw [theorem transcript](docs/fs4/theorems.log).

The carrier uses max-norm Fourier weights equivalent to ordinary Sobolev
weights. The covariance symbol uses the Euclidean sum of squares. The norm
equivalence is explained in the proof guide; no separately packaged Lean
isomorphism to a distribution-library Bessel-potential space is asserted.
The stronger exact raw complex mode identities and sharp trace constant are
paper calculations; the formal tightness proof uses its proved all-N bound.

## New: the three-dimensional periodic raw-lift limit

For every `L > 0` and `mass > 0`, let `N = n+1` and `a = L/N`. The actual
centered Gaussian source on `(Z/NZ)^3` is sent to the weighted Fourier carrier
by its raw atomic lift with the physical-volume factor `a^3`. These laws
converge weakly on the concrete weighted Fourier `H^-4(T_L^3)` carrier to the
explicit real-supported periodic Gaussian law.

The exported theorem is
[`Pphi2Clean.Continuum.periodic3DFixedVolume_weak_tendsto_gaussianTarget`](AImathPPhi2Clean/Periodic3DGaussianWeakLimit.lean).
The proof includes the actual three-dimensional source, moment and compactness
estimates, finite real Fourier marginals, subsequential uniqueness and full
weak convergence. The target is built by restricting the existing 4D Gaussian
Fourier carrier to fourth frequency zero and applying the `(sqrt L)^(-1)`
normalization; no 4D raw lattice source is substituted for the 3D source.

The zero-mode variance is `L^3 / mass^2`; nonzero canonical cosine/sine
coordinates have variance `L^3 / (2 * torusMassSymbol 3 L mass k)`. Alias and
Nyquist coincidences are excluded eventually for each fixed finite frequency
family, not asserted away on exceptional finite meshes. The proof guide
[`docs/fs3/proof.md`](docs/fs3/proof.md) records the normalization, exceptional
modes, real support, and theorem scope. The result is a free, fixed-volume
limit in the weighted Fourier `H^-4` realization, not an interacting,
infinite-volume, or OS-reconstruction theorem.

## Preserved two-dimensional development

The earlier finite-lattice and two-dimensional work remains in this same
library and history:

- The discrete Laplacian is self-adjoint and negative semidefinite;
  `Q = -Delta_a + mass^2` is positive definite. A proved eigenbasis and Parseval
  identity produce its inverse square root and the Glimm--Jaffe normalization.
- The finite Gaussian pushforward is measurable and probabilistic, with exact
  sampled covariance and second-moment identities.
- Physical sampling and the spacing-uniform moment bound supply the lift input.
- The periodic two-dimensional `H^-3` Fourier-pushforward weak-limit chain is in
  [PeriodicHMinusThreeWeakLimitMarginal](AImathPPhi2Clean/PeriodicHMinusThreeWeakLimitMarginal.lean),
  including `periodicHMinusThree_fixedVolume_weak_limit_exists_with_expected_cylinders`.

The original [finite-lattice manuscript](docs/pphi2_clean_finite_lattice.pdf),
archive audit logs and historical extension transcript remain available.
They document earlier stages, not the later four-dimensional result.
[PROVENANCE.md](PROVENANCE.md) separates the archive, historical extensions,
later two-dimensional repairs and the current four-dimensional release.

## Reproduce the current release

Install [elan](https://github.com/leanprover/elan), Git and Python 3.10 or newer.
The package pins Lean `leanprover/lean4:v4.34.0-rc2` and the exact upstream
Mathlib revision `852d20a84581aeba8527bd01d0be361d8c0e71c0`; the committed
lockfile also pins inherited dependencies. This exact Mathlib revision is the
one used by the current release evidence; it is not the older tag named by
some historical instructions.

```bash
git clone https://github.com/springoxn/pphi2-clean-finite-lattice.git
cd pphi2-clean-finite-lattice
lake exe cache get
lake build AImathPPhi2Clean
lake env lean audit/fs4_periodic_raw_lift_interface.lean
```

Portable checks without a Lean installation:

```bash
python verify.py --manifest --count --ext --fs4
python audit/check_fs4_release.py --self-test
```

`--ext` checks the historical two-module extension against its preserved
historical source bytes. `--fs4` checks the current source/configuration hashes,
exact theorem signatures, dependency revisions and foundational axiom allowlist.
To rebuild and replay the current contract and legacy gates:

```bash
python verify.py --all
# or replay just the current full build and four-theorem contract:
python audit/check_fs4_release.py --lean
```

Set `LAKE` if the executable is not on PATH. Fresh replay output goes to ignored
build directories or temporary copies; verification preserves published evidence.
The source census is a separate check: zero `sorry` alone is not evidence that
the intended theorem has been proved. The current four core dependency cones
are checked against `{propext, Classical.choice, Quot.sound}`.

Optional bounded exact checks need SymPy:

```bash
python -m pip install sympy
python audit/fs4d_periodic_gaussian_limit_probe.py
```

These finite checks exercise character orthogonality, alias/Nyquist cases,
normalization, dispersion bounds and negative controls. They do not prove the
infinite-family theorem.

## Scope and license

All continuum limits above are at fixed positive physical volume and mass.
This release does not establish an infinite-volume limit, an interacting
four-dimensional field, or Osterwalder--Schrader reconstruction.

Apache-2.0. See [LICENSE](LICENSE) and [NOTICE](NOTICE). No third-party literature
PDFs, local credentials, private checkouts or compiled dependency caches are
part of the release.
