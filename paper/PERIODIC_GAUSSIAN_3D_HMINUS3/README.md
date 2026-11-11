# Three-dimensional H-minus-three supplement

Run `python build.py` with Python, PyMuPDF and Tectonic installed. Set `TECTONIC` to the executable and `TECTONIC_CACHE_DIR` to an existing offline Tectonic cache if it is not on PATH. In this checkout the build can seed its private cache from the unchanged previous companion cache. The portable bundle does not ship the TeX cache; an installed Tectonic bundle or initial network access is required elsewhere.

The `inputs/` directory contains immutable snapshots: the previously delivered 3D companion PDF and its source archive, the new Lean source overlay, and the proof record. The build asserts the registered input hashes, compiles only the new supplement, appends it after the old PDF and audits page order, extracted text, headings, embedded fonts and page boundaries. It writes the combined PDF and portable source archive to the checkout deliverables directory when available, otherwise to build/. Original source/PDF inputs are never edited.

The new manuscript distinguishes 3D finite lattice source from 4D frequency-slice target; uses the exact sup-norm Fourier weights; states the sufficient verified H-minus-two moment constant 2; identifies compact closures of stronger-energy balls rather than bounded H-minus-three balls; and explicitly limits the formal Gaussianity claim to the unique-lift and joint-marginal results, not a separate IsGaussian predicate.

This build does not rerun Lean. For the recorded pinned Lean commands and base commit, inspect the included endpoint archive and proof record. The old article is retained as a historical snapshot, followed by a separately titled and paginated supplement.
