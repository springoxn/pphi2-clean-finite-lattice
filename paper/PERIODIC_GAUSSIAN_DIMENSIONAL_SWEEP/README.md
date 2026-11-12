# Periodic raw Gaussian limits across dimensions

This article combines the dimension-uniform Fourier proof for the actual periodic raw atomic Gaussian lift with a precise map of the dimension-specific Lean results released for dimensions 2 through 5 and the fixed dimension 122409.

- PDF: `periodic_gaussian_dimensional_sweep.pdf`
- LaTeX entry point: `main.tex`
- Sections: `sections/`
- Claim-to-evidence ledger: Appendix A
- Source/PDF audit: `audit/audit.py`
- Standalone pinned Lean project for `d = 122409`: `../../projects/D122409_RAW_GAUSSIAN/`

## Build and audit the article

Requirements: Python 3, Tectonic, and PyMuPDF. Set `TECTONIC` if Tectonic is not on `PATH`; an initial online Tectonic bundle fetch may be required. To use a seeded cache, set `TECTONIC_CACHE_DIR` and run `--offline`.

```sh
python build.py
python audit/audit.py --self-test
```

The build compiles from source, rejects TeX layout/font/reference warnings, copies the PDF to this directory, and runs a separate PDF-content/layout audit. The audit exits `1` on failed assertions and `2` on tool errors. Its machine-readable report is `audit/result.json`.

## Reproduce the 122409-dimensional Lean endpoint

Requirements: Lean `v4.34.0-rc2`, as pinned by `lean-toolchain`, and network access to fetch Mathlib at the pinned commit unless the Lake cache is already populated.

```sh
cd ../../projects/D122409_RAW_GAUSSIAN
python audit/verify_manifest.py
lake build AImathPPhi2Clean.ActualWeakLimit122409
lake env lean EndpointContract122409.lean
```

The source manifest records hashes of the endpoint source closure, toolchain configuration, successful build transcript, and typed endpoint/axiom transcript. The standalone project does not require this repository's main Lean package.

## Claim boundary

The all-dimension weak-convergence theorem is proved analytically in the article. Lean verifies distinct fixed-dimensional endpoint theorems at `d = 2, 3, 4, 5, 122409`; it does **not** currently prove one convergence theorem quantified over arbitrary dimension. The generic Lean lemmas in the 122409 project establish weight summability/comparison facts, not the full generic probability-measure convergence argument. All results are fixed-volume, positive-mass free-field limits.
