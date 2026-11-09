# Periodic Gaussian lattice limits in two and four dimensions

A new English article connecting the two-dimensional and four-dimensional
periodic Gaussian continuum-limit proofs. The article uses `amsart` at 11pt.
It is a separate publication snapshot; earlier papers are preserved.

- [Compiled PDF](periodic_gaussian_dimension_bridge.pdf)
- [LaTeX entry point](main.tex)
- [Mathematical sections](sections/)
- [Audit report](audit/AUDIT.md)
- [Executed joint Lean contract](audit/bridge_contract.log)
- [Bound source/dependency provenance](audit/bridge_contract.json)
- [Machine-readable article audit](audit/result.json)

The paper proves the common mathematical theorem for integer `d >= 1` and
`s > d/2`, then explains which fixed instances the Lean library certifies:
`(d,r,s)=(2,2,3)` and `(4,3,4)`. It treats the raw atomic approximation,
not a spectral truncation. The two-dimensional native weight is equivalent
to, but not identical with, the common weight used for exposition.

The PDF also records a correction to an earlier four-dimensional proof guide:
the dispersion error needs the physical factor `L^-4`. This is a paper-guide
correction; the Lean source and final formal theorem are unchanged.

## Build and audit

Requirements: Python 3, `sympy`, `PyMuPDF`, and Tectonic (on `PATH` or specified
with `TECTONIC`). Python's standard library handles the remaining scripts.
The LaTeX bibliography is included directly; no BibTeX invocation is needed.

```sh
python audit/audit.py --source-only
python build.py
python audit/audit.py --repo ../.. --report audit/result.json
python audit/self_test.py
```

For an offline build, seed a Tectonic cache and set `TECTONIC_CACHE_DIR`, then
run `python build.py --offline`. Cache and intermediate build directories are
excluded from publication. The build fixes `SOURCE_DATE_EPOCH`; exact PDF-byte
reproduction also depends on the Tectonic version and font bundle. An online
build may fetch Tectonic resources. No second web server is needed.

When this directory is inside the public repository, `--repo ../..` binds the
joint contract to every current Lean source/configuration hash. Without that
option, the audit still checks query/transcript hashes and the PDF, but does
not claim to compare an installed release source tree. The full library's
separate release verifier remains the authority for its complete build replay.

To rerun the joint contract in a Lean-ready clone, from the repository root:

```sh
lake build AImathPPhi2Clean
lake env lean paper/PERIODIC_GAUSSIAN_DIMENSION_BRIDGE/audit/bridge_contract.lean
```

The supplied transcript was executed against the exported release sources and
the pinned Mathlib revision. The theorem queries and independent typed examples
check both native convergence conclusions. Their only reported axioms are
`propext`, `Classical.choice`, and `Quot.sound`.

## Evidence limits

The paper contains analytic proofs. The finite symbolic and matrix tests
check bounded examples and normalization identities; they do not establish
infinite-dimensional compactness or arbitrary-dimensional Lean theorems.
The PDF audit checks text, references, captions and margins; representative
pages were also rendered and inspected visually.
