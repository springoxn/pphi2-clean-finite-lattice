# Audit Record

## Scope

This record distinguishes the article build and PDF checks from the Lean endpoint replay. A successful PDF audit is not evidence that the arbitrary-dimensional analytic argument has been formalized in Lean.

## Confirmed

- `python build.py` compiled the article and finished with `PASS: source audit, PDF pages=8`.
- The source and PDF audit found no missing required claims, theorem labels, bibliography environment, unresolved PDF references, nearly blank pages, or text blocks outside the page bounds.
- The PDF metadata title is `Periodic Raw Atomic Gaussian Limits Across Dimensions`. The PDF contains eight pages; all discoverable font programs were extractable. Its SHA-256 is `58502d4ba4d21e129cbdacc94c2ccea610eb7be90c68c5a899ba83080adccb23`.
- `python audit/audit.py --self-test` passed. Its negative control verifies that absent source anchors cause a nonzero result.
- Pages 1, 4, 5, 6, 7, and 8 were visually inspected for clipped text, overlap, and table fit; none was observed.

## Findings And Corrections

| Status | Finding | Disposition |
|---|---|---|
| FIXED | Early TeX builds rejected raw markup characters and had overfull lines in the evidence ledger and prose. | Reworded the ledger entries and shortened long lines; the final build log has no overfull-box warning. |
| FIXED | The PDF audit reached its PDF branch without initializing its error collection. | Restored the error-list initialization before PDF checks. |
| FIXED | PDF text extraction changes case and may split a word at a line break, so literal source-case anchors failed on valid PDF text. | Normalize extracted text and use a hyphenation-tolerant anchor; the final source/PDF audit passes. |
| QUALIFIED | The analytic theorem is dimension-parameterized, but the released Lean convergence theorems are fixed-dimensional. | The manuscript and evidence ledger state the boundary explicitly; no generic Lean probability-measure convergence theorem is claimed. |
| CONFIRMED ON SERVER | A fresh replay used the dedicated server project with Lean `v4.34.0-rc2` and Mathlib commit `852d20a84581aeba8527bd01d0be361d8c0e71c0`; the endpoint, target-measure and contract source hashes match the published project. | `lake build AImathPPhi2Clean.ActualWeakLimit122409` completed successfully (8903 jobs). `lake env lean EndpointContract122409.lean` exited successfully and printed the weak-limit, uniqueness and finite-marginal contracts with the declared standard axiom footprint. Server-side logs are `publication-build-20261112.log` and `publication-contract-20261112.log`; they are retained on the server, not bundled here. |
| HISTORICAL LOCAL CACHE FAILURE | An earlier local replay failed while reading imported Mathlib `.olean` modules, before reaching the endpoint or contract. | This was a local cache/import failure, not a theorem failure. The fresh server replay above is the current build verification. |

## Reproduction

From this directory, run:

```sh
python build.py
python audit/audit.py --self-test
```

The standalone pinned Lean instructions and their evidence boundary are in `../../projects/D122409_RAW_GAUSSIAN/README.md`. The local TeX environment emitted a nonfatal Fontconfig configuration warning; the PDF build completed and the embedded-font checks passed.
