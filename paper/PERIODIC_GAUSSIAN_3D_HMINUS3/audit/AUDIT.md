# PDF production audit

> status: ACTIVE · owner: PERIODIC3D_GAUSSIAN_RAW_LIFT_LIMIT · asof: 2026-11-11

## Evidence boundary
The mathematical sources are the immutable endpoint Lean overlay and proof record included under inputs/. This production run compiles and validates the manuscript and PDFs, but does not rerun Lean or independently re-audit the entire historical H4 dependency cone.

## Checks
The build fails nonzero on missing inputs, changed input hashes, TeX overfull boxes/missing characters/undefined controls or references, missing mathematical headings or limitation text, blank pages, replacement glyphs, unembedded fonts, text outside page bounds, changed page order or extracted content, or a corrupt source ZIP. The generated result.json records page counts, fonts and SHA-256 values. Boundary/sample pages are rendered for visual inspection. Structural comparison tests compare every old and new page to its corresponding merged page; they are artifact-fidelity checks, not mathematical proofs.

## Production findings and fixes
The first compile correctly failed on an overfull toolchain-name line. It was repaired by giving that identifier a separate ragged-right quote, without weakening the layout check. The initial ZIP included a duplicate audit report entry; the packager was corrected to include each source once. A production-only final paragraph caused a sparse sixth supplement page and was moved out of the manuscript (the same build instructions remain in README). The final supplement has five pages. Boundary pages and the final theorem-map page were rendered and visually inspected; no clipping, missing symbols, or collisions were observed. The artifact comparison script includes a missing-page negative control that must fail. Symbolic checks independently verify the shell count, weight ratio, projection multiplier cancellation, and target volume scaling, while source references are checked against the archived Lean declarations. These checks do not re-execute Lean.

## Findings and qualifications
The supplement corrects the previous topology description without editing the old snapshot. In particular, compactness is asserted for the closure of bounded stronger H-minus-two energy balls viewed in H-minus-three, never for arbitrary H-minus-three balls. The exact carrier weights use a sup-frequency norm, whereas the physical resolvent uses the Euclidean sum of squares. The verified moment has a sufficient factor 2, not the sharper analytic constant 1. The IsGaussian predicate is explicitly not claimed. Global proof-registry orphan/index checks are separate from PDF checks and remain the parent agent's responsibility after registration; do not infer that artifact_lint is green solely from PDF production.
