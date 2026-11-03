# Integration record — `paper/PPHI2_FIXED_VOLUME_COMPLETE`

> status: ACTIVE · owner: PPHI2_FIXED_VOLUME_FREE_FIELD_MEASURE_LIMIT · asof: 2026-11-02

This file records what the assembler changed after the parallel writers returned, why,
and what is still open. It is a LOG-layer note for the paper directory: it explains
edits, it does not assert state.

## How the paper was produced

Fifteen bounded agents plus the assembler:

| stage | agents | output |
|---|---|---|
| inventory | 2 | `notes/paper_ledger.md` (paper-level proofs), `notes/lean_ledger.md` (declaration and definition ledgers) |
| figures | 1 | `figures/fig_spine.tex`, `figures/fig_atlas.tex`, assets, `PROVENANCE.md` |
| Part I | 8 | `sections/00_abstract` .. `sections/09_main` |
| Part II | 2 | `sections/10_scope` .. `sections/14_reproduction` |
| review | 2 | adversarial mathematics referee; provenance and integrity auditor |

Every writer worked against `notes/CONTRACT.md` (claims and prohibitions, ownership,
frozen preamble, label table, number discipline, citation keys, notation ledger, and
the formal-side traps). Two writers worked from a ledger of 59 lemma-level entries with
`document:line` pointers, which is why the paper can be audited back to the sources.

## Assembler edits to writer-owned files

Each is small, and each is recorded here because the writers' returns claim those files
verbatim.

| file | edit | reason |
|---|---|---|
| `sections/02_setting.tex` | rewrote the "stored coordinate" paragraph | it contradicted `eq:ell2s` and §5: §2 called the carrier entries stored coordinates while §5 calls them Fourier coefficients with an isometric weighted family. Now §2 states the coefficient convention and points at `def:carrier-hminus3`, so the two agree |
| `sections/07_marginals.tex` | `\mathsf{T}` -> `\mathrm{T}` (5 occurrences) | the offline Tectonic cache has no 9pt sans metric; `\mathsf` in a small-font context aborts the build instead of warning |
| `sections/04_covariance.tex` | added `\cite{yosida1980}` at the Riesz step | the key was in `refs.bib` and unused; the Riesz representation is exactly where a reader needs it |
| `sections/10_scope.tex` | added `\cite{gjs1974}` to the $P(\varphi)_2$ branch | same: a real pointer at the position the sentence actually needs |
| `sections/11_lean.tex` | added two rows to the correspondence table (`cor:uniqueness` -> `..._weak_limit_unique`; `lem:subsequence-marginals` gains `..._subsequential_limit_has_expected_cylinder`) | check E requires the paper to quote every ledgered decoration; the table quoted eight of ten |
| `sections/12_contracts.tex` | `\textsf{Mathlib}` -> `\texttt{Mathlib}` | same font-bundle limit as above |

`main.tex` also gained three preamble decisions, each commented in place:
`\pagestyle{plain}` (amsart's running head for a `\part` is 9pt sans and aborts the
offline build); `\renewcommand{\sfdefault}{\rmdefault}` (belt and braces, since this
paper uses no sans typography); and `\renewcommand{\labelenumi}{(\roman{enumi})}` (the
body refers to steps as (i), (ii), (iii)).

## Refactorings made at the tool level

| change | why |
|---|---|
| `\input{generated/bibliography}` instead of `\bibliographystyle`/`\bibliography` | the offline bundle carries **no `.bst` at all**; BibTeX fails and Tectonic *ignores* the error, so the build stays green while every citation prints as `[?]`. `audit/make_bib.py` now renders `refs.bib`; check L fails if the two drift |
| ledger prints module names with plain `\texttt` and declarations with `\detokenize` | `audit/verify_paper.py` reads declaration names out of the appendix by matching `\detokenize`; module names contain no underscores and would otherwise be mistaken for declarations |
| check N accepts a name that exists in the Lean tree, not only in the ledger | the paper legitimately mentions support declarations; a typo is still red because it is in neither place |
| check E now requires transcript == permitted set and body covers every ledgered name | the earlier form compared body names against the ledger and drifted as the ledger was regenerated |
| check L also scans `figures/*.tex` and `main.tex` for labels | `\cref{fig:atlas}` and `\cref{app:ledger}` are real references; they were being reported dangling |
| four bibliography entries dropped (`dlmf`, `conway1990`, `reedsimon1980`, `kuo1975`) | no sentence needed them. `dlmf` in particular has no legitimate home: this paper deliberately has no Bessel kernel. An uncited entry is a claim the paper does not make |

## Two build facts a future maintainer will hit

1. **The seeded Tectonic cache is missing font variants.** `OT1/cmss/m/n/9` (sans at
   9pt, used by amsart's `\part` running head) and `TU/lmr/bx/n/8` (bold at 8pt) are
   both absent. Tectonic *halts* on a missing metric, and the message names the page
   where the font was first needed, not the construct that asked for it — a `\part`
   whose head is typeset on the first page of Part II surfaces as an error in the
   bibliography if Part II happens to start there.
2. **`\scriptsize` plus `\textbf` cannot be used.** Same missing 8pt bold metric.

## Review round: what the two referees found and what was changed

The mathematics referee re-derived the analytic chain independently and confirmed the two gap
closures are real (`lem:trace-constant` closes R1 with all four ingredients, `lem:hC-identification`
closes R2 from the limit rather than from the symbol), then listed five blockers. The provenance
auditor confirmed every claim about reachability, the vacuous wrapper, the negative control and the
ten footprints on disk, and listed four false statements about the paper's own evidence. All nine
were applied:

| finding | fix |
|---|---|
| front matter said "the fixed-volume lattice laws converge ... to a free Gaussian measure" | now names the finite-source Fourier pushforward and "determined by their finite Fourier marginals"; Gaussianity of `mu_free` is nowhere asserted |
| two conventions for a carrier point (§2/§5 coefficient family vs §3/§6/§7 stored family) | new `rem:two-families` in §5 states the rule once, and §2/§6 point at it; the note records that the only available error is applying the weight twice |
| "Seven works are cited ... none of them is used in a proof" | now `\NumCitedWorks` works, with the three used at a point of use (`yosida1980`, `prokhorov1956`, `bogachev1998`) named as such and the seven positional ones listed below |
| Part II said the declarations are "the same statements proved in Part I" | §10 and §11 now state that the finite-family declaration *consumes* the covariance identification as a hypothesis, i.e. the formal conclusion is weaker, not stronger |
| negative control claimed the transcript command was applied to it | now says the control is attested textually: the file is in the tree and its output line is committed beside it, and it is not a transcript |
| `Sigma_F` asserted to be a covariance matrix before PSD was available | `thm:char-function` (ii) now says it is an entrywise limit of the `Sigma_{F,N}`, hence PSD |
| "the faster decay of `w~_2`" | corrected: the `H^{-3}` weight decays faster, the ratio `w_3/w~_2 = ||k||_\infty^{-2}` → 0 |
| covariance limit called dimension-free | corrected: registered for general `d`, written here in `d = 2`, shell count uses `d = 2` |
| `\NumChainTheorems` "results" over a 9-row table | "declarations", with the weaker row marked |
| §14 told a reproducer to expect "either the permitted set or the empty set" | now expects the permitted set |
| §14 misdescribed the gate (names, uncited keys) | text corrected **and** check L now fails on an uncited key, so the rule is enforced rather than described |
| six word-spelled counts (`Eight`, `seven`, `three lines`, `five places`) | became `\NumUnreachableModules` (computed by an import-graph traversal), `\NumMeasureContractTheorems`, `\NumNegativeControlLines`, `\NumCitedWorks` |
| nil: phase at a sampled site | now written with the physical point `t = ax`, `e^{-2pi i k.x/N}` |
| nil: "carrier coordinate" in §6 | "stored coordinate", tied to `rem:two-families` |

Final state (2026-11-02): 41 pages, 4/4 paper checks, 11/11 `artifact_lint`, no undefined
references.  The claim that there was "no overfull box larger than 60pt" was **wrong** and is
corrected by the 2026-11-03 audit: that build had eight overfull boxes, the worst 249pt, which
clipped two declaration names off the printed page in §13.  The cause is recorded and fixed in the
audit report `docs/reports/AUDIT_PPHI2_FIXED_VOLUME_COMPLETE_20261103.md`: the numbers were checked
against the log by hand at one point and never again after §12/§13 were rewritten.

Final state (2026-11-03): see the same audit report §16 for the repaired numbers; `build_all.py`
now fails the build on any overfull box or undefined reference, so this line cannot rot silently
again.

## Still open

- Nothing in this directory is committed to git yet.
- The remaining referee warnings that were *not* applied are editorial: the module column and role
  prose of Appendix A are curated rather than machine-derived (`make_ledger.py` cross-checks only the
  names), and `CONTRACT.md` §7 still lists the four bibliography keys that were pruned.
- `notes/paper_ledger.md` §7 ranks thirteen gaps; seven are closed at paper level
  (`R1`, `R2` in §§6-7) or stated as boundaries (`R3`-`R7`). `R8`-`R13` are the
  referee-visible caveats the text carries (test class of the summable envelope,
  eventual-in-`N` Bessel bound, `H^{-s}` rule proved only for `d=2`, the off-graph
  abstract Gaussian module, heterogeneous source formats, and the dimension
  restriction).
