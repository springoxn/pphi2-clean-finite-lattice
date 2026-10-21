# pphi2-clean-finite-lattice

A self-contained Lean 4 development of the **finite periodic-lattice Gaussian
covariance**, the base layer of every constructive construction of
$P(\varphi)_2$.  The covariance is not postulated from a spectral
representation: it is built from the concrete operator
$Q=-\Delta_a+m^2$ on $(\mathbb{Z}/N\mathbb{Z})^d$, whose self-adjointness,
negative semidefiniteness, positive definiteness, Hermitian matrix form and
positive eigenvalues are all proved, and whose eigenbasis then yields the
covariance $Q^{-1/2}$ with the Glimm--Jaffe normalization $a^{-d/2}$.

The development has **zero `sorry`**, **zero project axioms**, and a declared
footprint inside `{propext, Classical.choice, Quot.sound}` — the three standard
axioms of Lean and Mathlib — for every declaration the audit asks Lean about.
The audit that establishes this is in the repository, together with its logs
and a negative control showing that the firewall fires when an axiom is
injected.

## What is proved

| Layer | Result |
|---|---|
| Operator | $\Delta_a$ is self-adjoint; $\langle f,\Delta_a f\rangle=-a^{-2}\sum_i\sum_x(f(x+e_i)-f(x))^2\le0$; $Q=-\Delta_a+m^2$ is positive definite |
| Spectral data | the operator equals its matrix in the delta basis, so the finite-dimensional spectral theorem applies; orthonormal eigenbasis, real eigenvalues $>0$, Parseval, quadratic form $\langle f,Qf\rangle=\sum_k\lambda_k\langle e_k,f\rangle^2$ |
| Covariance | $Tf=\sum_k\lambda_k^{-1/2}\langle e_k,f\rangle e_k$ with $\langle Tf,Tg\rangle=\sum_k\lambda_k^{-1}\langle e_k,f\rangle\langle e_k,g\rangle$; the $a^{-d/2}$ normalization scales the bilinear form by $a^{-d}$ |
| Measure | the pushforward of finitely many independent standard Gaussians into the cylindrical weak dual; a probability measure; measurable; $L^2$; exact covariance $\int\omega(f)\omega(g)=\langle Tf,Tg\rangle$ |
| Exact moments | closed form in the mass eigenbasis, $a^{-d}\sum_k\lambda_k^{-1}\bigl(\sum_x e_k(x)f(x)\bigr)\bigl(\sum_x e_k(x)g(x)\bigr)$; and the same for the lifted configuration $\int(\eta_\omega(f))^2$ with **arbitrary** continuous linear evaluation functionals |
| Representation | an explicit coefficient embedding into $\ell^2(\mathbb{N})$ is an isometry, and under it the factor equals the upstream spectral coefficient formula |
| Interface | the lift to an arbitrary test space is continuous and measurable, equals evaluation on the induced test field, and transports $L^2$ bounds uniformly over a family |

Numbers (recomputed from the sources, never typed by hand): 34 modules,
3701 lines, 211 declarations of which 149 are theorem-level, 64 declarations in
the axiom report, 27 per-module interface certificates, 8878 build jobs in the
archived log.  `PROVENANCE.md` says how each number is obtained.

## One step beyond the pinned archive

The repository also publishes a single step taken *after* the archive was
pinned: the **physical sampling convention** and the **UV-uniform second-moment
bound**.

| Post-pin result | Statement |
|---|---|
| Spectral floor | $m^2\le\lambda_k$ for every eigenvalue of the mass operator, with the *same* $m^2$ for every lattice spacing — constant functions attain it |
| Sampled covariance | $\langle T_{\mathrm{GJ}}\varphi_f,T_{\mathrm{GJ}}\varphi_f\rangle\le m^{-2}\lVert f\rVert_{a,N}^2$ for the Riemann sample $\varphi_f=a^d(f(ax))_{x\in\Lambda}$ |
| Spacing-uniform bound | at fixed physical volume $L=aN$, $\int(\omega f)^2\,\mathrm{d}\mu_{a,N}\le m^{-2}L^d\lVert f\rVert_\infty^2$ — the constant sees neither $a$ nor $N$ |

That is a bound, not a limit: no tightness, no convergence of measures, no
moments beyond the second, no interacting measure.  The two modules introduce 14
declarations (279 lines), all with a footprint inside the same allowlist, and
they are **not** in the audited archive — so they carry their own evidence in
`docs/extension_evidence.log`, a transcript of a build and axiom run on the build
host, which `python verify.py --ext` re-binds to the bytes here (module hashes,
the root's imports, coverage of all 14 declarations, allowlist containment).  The
companion manuscript's §11 states the results and their scope.

## What is *not* claimed

This is a **free**, **finite-volume**, **lattice** object.  The repository
asserts nothing about a continuum limit $a\to0$, an infinite-volume limit
$N\to\infty$, exponential clustering, an interacting measure, or
Osterwalder--Schrader reconstruction; and it does not identify this finite
pushforward law with any infinite-noise Gaussian implementation.  The gates
below are equally explicit about what a machine check cannot establish: it
cannot tell you that a formal statement is the intended one.

## Layout

```
AImathPPhi2Clean.lean                  root module (imports the library)
AImathPPhi2Clean/
  ConcreteLatticeOperator.lean         Δ_a, Q, matrix bridge, spectral data
  ConcreteLatticeCovariance.lean       Q^{-1/2}, Glimm–Jaffe normalization
  ConcreteGaussianMoment.lean          the measure, exact moments, the lift
  NumberedLatticeGaussianMoment.lean   the Fin n (numbered) interface
  LatticeCovarianceRepresentation.lean ℓ² coefficient embedding, isometry
  LatticeGaussianContinuumConsumer.lean consumer interface, L² transfer
  PhysicalLatticeGaussianBound.lean    post-pin: eigenvalue floor, sampled bound
  PhysicalLatticeSampling.lean         post-pin: the sampling convention
  ...                                  further clean interfaces (Wick,
                                       Nelson layer cake, tightness, positivity)
audit/                                 the gates and their logs (the evidence)
docs/                                  companion manuscript, archived README,
                                       the post-pin evidence transcript
verify.py                              portable verification entry point
PROVENANCE.md                          archive hash, delta policy, upstream pin
MANIFEST.sha256                        SHA-256 of every published file
```

Module-level documentation is in each file's header; the finite-lattice
migration begins at `ConcreteLatticeOperator.lean`.

## Build

Toolchain and dependency are pinned:

- Lean `leanprover/lean4:v4.34.0-rc2` (see `lean-toolchain`)
- Mathlib commit `852d20a84581aeba8527bd01d0be361d8c0e71c0` (see `lake-manifest.json`)

```bash
lake build AImathPPhi2Clean
```

Mathlib is a git dependency; the first build fetches and compiles it, which
takes a while.  Nothing else is required — no other dependency, no generated
code.

## Verify

```bash
python verify.py          # every published file against MANIFEST.sha256
python verify.py --ext    # the post-pin extension: hashes, coverage, axioms
python verify.py --count  # the numbers in this README, recomputed
python verify.py --lean   # additionally re-run the axiom gates (needs lake)
```

The full delivered gate, including the textual provenance check against the
upstream commit, is:

```bash
bash audit/run_finite_lattice_checks.sh /path/to/GaussianField
```

where the argument is a checkout of `mrdouglasny/GaussianField` at commit
`d63a28568a75d99f6cb27af1f888a49a69855a66`.  The scripts discover `lake` from
`$LAKE`, then `PATH`, then elan's default location, and the interpreter from
`$PYTHON` or `python3`; nothing is hard-coded to a particular machine.

What each gate establishes, and what it cannot, is documented in the companion
manuscript (in `docs/`), §9, and summarised in `PROVENANCE.md`.

## Provenance

The Lean sources here are **byte-identical** to a registered, audited archive
except for three audit scripts that carried machine-specific absolute paths and
were made portable, plus the library root, which gained two `import` lines for
the post-pin modules.  The exclusions (the upstream axiom-census tooling, which
depends on a private baseline checkout), the two post-pin modules and the full
delta are listed in `PROVENANCE.md`, and `verify.py` re-checks the manifest.
Definitions in `AImathPPhi2Clean/ConcreteLatticeOperator.lean` are adapted from
`mrdouglasny/GaussianField`; the correspondence is checked textually against
the pinned commit.  See `NOTICE`.

## License

Apache-2.0 (`LICENSE`).  Attribution for the adapted definitions: `NOTICE`.
