# Architecture Companion: Build and Evidence

This is a new, standalone architectural companion. It does not modify or replace the earlier arbitrary-dimensional endpoint paper.

## Build

Requirements: Python 3, PyMuPDF (`pip install PyMuPDF`) and Tectonic with its LaTeX bundle available. Set `TECTONIC` to an executable path when it is not on PATH. The Windows fallback in the build script is optional.

```console
python build.py
python audit/audit.py
```

The build compiles twice with a fixed `SOURCE_DATE_EPOCH`, requires byte-identical PDFs, and audits source integrity and the final PDF. It does not execute Lean.

## Layout

- `main.tex` / `main.pdf`: manuscript and compiled article.
- `audit/audit.py`: executable integrity, recorded-evidence and final-PDF checks, with rejecting negative controls.
- `audit/source_manifest.json`: SHA-256 manifest of manuscript/build/audit sources and selected evidence.
- `audit/result.json`: generated audit results, not mathematical proof.
- `evidence/release/`: selected byte-preserved files from public commit `0c082ff7f33ae42876123507b2bb108e1089c2c2`.
- `evidence/release/projects/ARBITRARY_DIM_RAW_GAUSSIAN/`: standalone pinned generic source closure and recorded build/contract transcripts.
- `evidence/release/paper/PERIODIC_GAUSSIAN_5D_HMINUS3/`: separately pinned 5D source archive.
- `evidence/upstream/`: pinned source captures, licenses, bibliographic HTML and upstream CI status; no independent upstream build is claimed.
- `evidence/scope_snapshot.json`: archived selected registry fields, not independent certification or future state authority.
- `evidence/analysis/`: historical analytical notes used to locate the broader programme; these are not newly checked Lean proofs, and may cite inputs outside the package.

The release selection is not a full clone. The historical root `MANIFEST.sha256` does not describe this selected package. Use this article's manifest here. The root-relative historical provenance text is preserved byte-for-byte inside `PROVENANCE_snapshot.zip` so that its links are not mistaken for active package-relative links. Source licenses are preserved at their respective release/upstream locations.

For a full repository hash check, obtain a fresh clone at the fixed public commit and run its `python verify.py`. The paper gives separate Lean replay commands for the pinned generic project. No Lean source has been changed to write this companion.

## Scientific Scope

The central result is convergence of specified periodic finite-volume lattice Gaussian laws, not Gaussian-field existence alone. The manuscript distinguishes mathematical specialization from formal transport between historical carriers. Broader interacting-field and reflection-positive analytical work is explicitly separated from released Gaussian Lean endpoints, and reconstruction remains a literature input. Upstream Bochner/Minlos proofs use weak-convergence methods, and the inspected OSforGFF master theorem covers all dimensions at least two; neither contribution is understated.
