# Arbitrary-dimensional Gaussian limit article

This directory contains the standalone article and its reproducibility audit. The Lean source closure under `lean/` is copied from the server-verified archive; the archive SHA-256 is recorded in `audit/result.json` after building.

Build locally with:

```powershell
python build.py
```

The script uses `D:\Anaconda\envs\latex\Library\bin\tectonic.exe` when available, rejects TeX warnings that indicate unresolved references or missing glyphs, runs the PDF/source audit, and writes `build/main.pdf` plus the published `main.pdf`.

The formal proof was executed on the server. This article audit checks the recorded Lean evidence and byte hashes; it does not replace a fresh Lean kernel replay.
