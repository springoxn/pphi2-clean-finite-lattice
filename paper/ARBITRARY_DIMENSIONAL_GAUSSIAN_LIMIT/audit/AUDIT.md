# Audit report

> status: ACTIVE · owner: CROSS-BRANCH · asof: 2026-11-12

The article records the server-verified arbitrary-dimensional Lean endpoint. The audit is fail-closed: it checks article anchors, source hygiene, recorded successful Lean transcripts, the server archive digest when the archive is available, and PDF text structure using PyMuPDF.

The audit is not a fresh Lean replay. A fresh replay requires the pinned Lean toolchain and dependencies; the server transcripts record successful `ActualWeakLimitArbitraryDim`, `SharpContractArbitraryDim.lean`, and `EndpointContractArbitraryDim.lean` executions. The theorem scope is `d ∈ ℕ`, `d > 0`, `s > d/2`, `L > 0`, and `mass > 0`. The target coefficient coordinates already include the square-root weight. The Fourier weight uses the sup norm, while the covariance dispersion uses the Euclidean sum of squares.

The only known project-wide governance limitation is the pre-existing dangling-reference baseline in unrelated `.worktrees/pphi2-122409` files; it is not an article or Lean-source failure.
