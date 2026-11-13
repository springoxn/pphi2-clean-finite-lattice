# Publication and Lean Execution Rules

## Author

For newly written, explicitly revised, or rebuilt articles, use `YJ ZHENG` as the author in LaTeX, PDF metadata and build checks. Do not use `AIMATH PROJECT` or `AImath Project` as an author placeholder. Frozen historical papers and evidence retain their original attribution unless the user explicitly requests a revision.

## Lean Builds and Replays

Run Lean builds, endpoint/typed-contract replays and `#print axioms` on the Linux server through SSH, using `/home/zhengyj/.elan/bin/lake`. Preserve the exact commands, toolchain and dependency pins, source SHA-256 hashes, complete output and exit codes. Use isolated copies of the pinned release sources to avoid overwriting server-only work. Do not present old transcripts, local execution or a PDF build as a fresh server Lean replay. If the server is unavailable, report the infrastructure blocker; do not substitute a local Lean build without explicit user authorization.

The manuscript and PDF can be built locally. Successful Gaussian endpoint replays do not certify upstream projects, interacting-field arguments or reconstruction results outside the replayed scope.
