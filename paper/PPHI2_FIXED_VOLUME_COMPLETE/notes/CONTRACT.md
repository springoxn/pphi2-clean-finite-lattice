# Writing contract — `paper/PPHI2_FIXED_VOLUME_COMPLETE`

> status: ACTIVE · owner: PPHI2_FIXED_VOLUME_FREE_FIELD_MEASURE_LIMIT · asof: 2026-11-02

Every writer on this paper must read this file in full before writing a line, and
must obey it literally. It is the only place where cross-section decisions live.
If this contract and some other document disagree, this contract wins; report the
conflict in your return value instead of silently choosing.

---

## 1. What the paper claims, and what it must never be made to claim

**Central claim (one sentence).** For `L > 0` and mass `m > 0`, the finite
periodic lattice Gaussian free-field laws at fixed physical volume `a·N = L`,
pushed forward to the concrete weighted `ℓ²` carrier that is `H^{-3}(T_L^2)` by
their **explicit finite-source Fourier lift**, form a tight family of Borel
probability laws on that Polish carrier with a uniform `H^{-2}` moment; their
finite Fourier marginals converge to the paired cosine/sine Gaussian laws with
the periodic massive resolvent covariance; consequently the **whole sequence**
converges weakly to a Borel probability measure `μ_free` determined by those
marginals. Separately, at fixed volume, the covariance integrals of the
underlying lattice measures converge to the pairing with the independently
constructed periodic massive variational weak resolvent.

Precision matters here; three words in the sentence above are load-bearing and
must survive every rewording: **finite-source** (which lift), **whole sequence**
(not "a subsequence"), **determined by those marginals** (not "is the Gaussian
measure with covariance operator `(m^2-\Delta)^{-1}`", unless the writer proves
that from the marginals — see `GAP R4` in `notes/paper_ledger.md`).

**What the paper must NOT claim** (these are scope statements of the project,
`proof_graph/scopes/PPHI2_FIXED_VOLUME_FREE_FIELD_MEASURE_LIMIT.yaml`, quoted):

1. no equivalence with a pre-existing distribution-defined Sobolev space, and no
   strong unbounded-Laplacian domain theorem;
2. the *separate* identity theorem for the abstract `physicalGJ` pushforward
   `periodicHMinusThreeLatticeMeasure` remains conditional on a named input
   structure — that condition is **not** a premise of the fixed-volume
   convergence theorem. In particular the paper must not say that "the lattice
   field laws converge": what converges is the finite-source Fourier
   pushforward, and the bridge to a total carrier representative of
   `physicalGJMeasure` is open (`GAP R3`);
3. no interacting ultraviolet limit and no Osterwalder–Schrader reconstruction is
   proved here; the theory constructed is the **free** (Gaussian) one;
4. no rate, no exponential tail, no quantitative modulus: the tightness is
   first-moment Markov only (`GAP R7`);
5. no Bessel-function kernel, no `K_0`, no `1/(2π)` or `1/(4π)` constant and no
   log-divergence discussion: **none of these occur anywhere in the ten proof
   documents** (`notes/paper_ledger.md` §4, last table). The proof is carried out
   entirely in the symbol/Fourier domain. A writer who introduces such a kernel
   is inventing mathematics.

**External inputs (complete list).** The ten proof documents cite no author–year
reference. Their entire external dependency is: elementary analysis (Cauchy–
Schwarz, Young, Parseval, Markov, Riesz representation, `sin t/t → 1`,
`sin t ≥ 2t/π` on `[0,π/2]`, `4π² > 16`, periodic integration by parts,
π-system/Dynkin, finite-dimensional Gaussian existence) plus five named
`Mathlib` facts (torus Fourier basis, Prokhorov extraction,
`Filter.tendsto_of_subseq_tendsto`, `summable_one_div_norm_rpow`, box-integral
Riemann machinery). See `notes/paper_ledger.md` §6.2 for pointers.

**Literature citations are for positioning only.** `ossier1973`, `ossier1975`,
`minlos1959`, `gj1987`, `gjs1974`, `simon1974`, `nelson1973`, `grs1975` may be
cited to say *where this theorem sits in the constructive-QFT programme*, and
`bogachev1998`, `kuo1975`, `billingsley1999`, `prokhorov1956`, `reedsimon1980`,
`yosida1980`, `conway1990`, `dlmf` only where a reader genuinely needs a
background fact. Never write "by [Glimm–Jaffe]" for a step in this proof: the
documents never use that book, and the identifier `GJ` in
`numberedLatticeCovarianceGJ` is a name, not a citation.

**Evidence discipline (mandatory).** Every nontrivial statement in the body must
be identifiable, at the point of use, as exactly one of:

- (M) *mathematics proved in this paper* — give the proof or point to the
  numbered result that does;
- (L) *an external theorem or standard fact* — state it, name it, and use it only
  under its hypotheses;
- (F) *machine-checked* — a Lean declaration, quoted with `\lean{...}`, and
  listed in the generated ledger (Appendix A);
- (H) *a named hypothesis/input of the development* — state it as a `hypothesis`
  environment with a label, and never use a result that depends on it without
  naming it.

There is no fifth category. If a step is none of these, it is a `GAP` and must be
reported, not written into the paper as if it were proved. The seven `GAP` items
`R1`–`R7` are enumerated in `notes/paper_ledger.md` §7; **R1 and R2 must be
closed at paper level inside this article** (assignments: R1 → W06, R2 → W07),
**R3 must be stated as the open boundary**, and **R5/R6 must be resolved by
quoting the post-identification statements** (`D1:232`, `D1:251`, `D10:3-11`),
never by quoting `D1:260` bare.

---

## 2. File ownership (write-disjointness)

Write **only** the files assigned to you. Never edit `main.tex`, `refs.bib`,
`generated/*`, `figures/*`, `audit/*`, `notes/*`, or a file owned by another
writer. Never create a new file outside your assignment.

| Writer | Files | Section | Target words |
|---|---|---|---|
| W01 | `sections/00_abstract.tex`, `sections/01_intro.tex` | Abstract, §1 | 250 + 1400 |
| W02 | `sections/02_setting.tex` | §2 | 1100 |
| W03 | `sections/03_lattice.tex` | §3 | 1300 |
| W04 | `sections/04_covariance.tex` | §4 | 1200 |
| W05 | `sections/05_carrier.tex` | §5 | 1300 |
| W06 | `sections/06_tightness.tex` | §6 | 1200 |
| W07 | `sections/07_marginals.tex` | §7 | 1100 |
| W08 | `sections/08_identification.tex`, `sections/09_main.tex` | §8, §9 | 800 + 700 |
| W09 | `sections/10_scope.tex`, `sections/11_lean.tex` | §10, §11 | 1100 + 900 |
| W10 | `sections/12_contracts.tex`, `sections/13_boundary.tex`, `sections/14_reproduction.tex` | §12–§14 | 800 + 700 + 600 |
| FIG | `figures/fig_spine.tex`, `figures/fig_atlas.tex`, `figures/*.png` | figure blocks | — |

Each `sections/NN_name.tex` contains exactly one `\section{...}` (with
`\label{sec:...}`) and, for W08/W09/W10, two or three sections respectively.
No file contains `\documentclass`, `\begin{document}`, `\end{document}`,
`\title`, `\author`, `\maketitle`, `\bibliography`, or `\appendix`.

---

## 3. Frozen preamble: what you may use

The preamble of `main.tex` is frozen. Do **not** add `\usepackage`, `\newtheorem`,
`\newcommand`, `\def`, `\let`, `\setlength`, `\renewcommand`, or `\DeclareMathOperator`.

Available theorem environments: `theorem`, `lemma`, `proposition`, `corollary`,
`definition`, `hypothesis`, `external`, `remark`. All share one counter, numbered
by section (`theorem` in §4 is 4.1, the next is 4.2, …). Use `\begin{theorem}` …
`\end{theorem}`; never number by hand.

Available macros (use these, do not roll your own):

```
\R \C \N \Z \T \E \dd \ip{}{} \norm{} \abs{} \sS \sSp \supp \ie \eg
\HL{s}        -> H^{-s}
\Torus        -> T_L^2
\Real \esssup
\lean{name}   -> a Lean declaration name, typeset verbatim (only in text)
\Num...       -> the count macros of generated/metrics.tex (see §6)
\LeanToolchain \TectonicVersion
```

Figures: `\input{figures/fig_spine}` and `\input{figures/fig_atlas}`. Each file
already contains the whole `figure` environment, its caption and its label. Do
not write your own `\includegraphics`, do not re-caption. Only W01 may input
`fig:spine` and only W09 may input `fig:atlas`.

**Language.** English, ASCII source only: write Greek letters as math (`$\varphi$`,
`$\mu$`, `$\sigma$`), never as UTF-8 characters; use `--`/`---` for dashes; no
curly quotes; no emoji; no CJK characters anywhere in the `.tex` source.

---

## 4. Labels you own

Every `\section` gets a `\label{sec:...}`. Every `theorem`/`lemma`/`proposition`/
`corollary`/`definition`/`hypothesis` gets a `\label`. Labels must be globally
unique; use exactly the names below for the results listed, and for anything else
you add use the prefix shown for your section.

| Label | Content (one line) | Owner |
|---|---|---|
| `sec:intro` | Introduction | W01 |
| `sec:setting` | Setting: torus, modes, weights, lattice, regime | W02 |
| `def:torus` | The periodic torus and its test space | W02 |
| `def:modes` | Fourier index set and the weight `w_s` | W02 |
| `def:carrier-hs` | The space `ℓ²_s` and `H^{-s}` for `s > 0` | W02 |
| `hyp:volume` | Fixed physical volume `a·N = L` | W02 |
| `sec:lattice` | The lattice free field and its physical-volume law | W03 |
| `def:lattice-laplacian` | The discrete Laplacian `Δ_a` and `Q = -Δ_a + m²` | W03 |
| `prop:operator` | `Δ_a` self-adjoint, `Q` positive definite, eigenbasis exists | W03 |
| `def:gj-measure` | The physical lattice Gaussian law `physicalGJMeasure` | W03 |
| `lem:haar-lebesgue` | Haar-to-physical-Lebesgue normalisation of test coordinates | W03 |
| `sec:covariance` | The physical-volume covariance limit | W04 |
| `lem:resolvent` | The periodic massive resolvent and its symbol | W04 |
| `lem:resolvent-pairing` | Pairing of the lattice covariance with the resolvent | W04 |
| `thm:covariance-limit` | The fixed-volume covariance / mixed-moment limit | W04 |
| `sec:carrier` | The carrier and its Borel structure | W05 |
| `def:carrier-hminus3` | `PeriodicHMinusThreeCompletion` as `ℓ²` of the mode lattice | W05 |
| `prop:completion` | The completion is isometrically `ℓ²`; `H^{-2} ↪ H^{-3}` | W05 |
| `lem:coordinate-embedding` | Continuous and injective coordinate embeddings | W05 |
| `thm:separable` | The carrier is separable | W05 |
| `thm:cylinder-borel` | The cylinder σ-algebra is the Borel σ-algebra | W05 |
| `sec:tightness` | Uniform moment bound and tightness | W06 |
| `thm:uniform-moment` | `sup_N E‖φ_N‖²_{H^{-2}} < ∞`, with the constant | W06 |
| `lem:zero-mode` | The zero-mode term and why it is harmless | W06 |
| `thm:compact-tail` | H⁻²-bounded sets have relatively compact H⁻³ tails | W06 |
| `thm:tightness` | The family of laws is tight on the carrier | W06 |
| `sec:marginals` | Finite Fourier marginals | W07 |
| `def:cylinder-map` | The finite-mode coordinate map | W07 |
| `thm:char-function` | The characteristic function of the finite-mode law | W07 |
| `thm:finite-family` | Convergence for every finite family of test functions | W07 |
| `sec:identification` | Cylinder uniqueness and identification | W08 |
| `thm:cylinder-uniqueness` | Borel probability measures agreeing on cylinders agree | W08 |
| `lem:subsequence-marginals` | A subsequential limit inherits the target marginals | W08 |
| `sec:main` | The main theorem | W08 |
| `thm:main` | Whole-sequence weak convergence to `μ_free` | W08 |
| `cor:uniqueness` | The limit is independent of the subsequence | W08 |
| `sec:scope` | Scope, boundaries, and the wider programme | W09 |
| `sec:lean-overview` | The Lean development: organisation and module map | W09 |
| `sec:lean-contracts` | Statement contracts and the axiom firewall | W10 |
| `sec:lean-boundary` | What is machine-checked and what is not | W10 |
| `sec:lean-reproduction` | Reproduction | W10 |
| `fig:spine` | Proof spine (owner: FIG) | FIG |
| `fig:atlas` | Lean dependency atlas (owner: FIG) | FIG |
| `app:ledger`, `app:axioms` | generated appendices (owner: build) | — |
| `def:weight-supnorm` | The weights use the sup norm on `Fin 2 → ℤ`, not the Euclidean norm | W02 |
| `ext:fourier-basis` | The torus Fourier basis is complete orthonormal (external) | W02 |
| `ext:summability` | `Σ_k ‖k‖^{-4} < ∞` and `Σ_k ‖k‖^{-6} < ∞` (external) | W02 |
| `def:finite-source-lift` | The explicit finite-source Fourier lift and its law | W03 |
| `rem:lattice-input` | The lattice covariance is an input object here, not derived | W03 |
| `ext:boxintegral` | Physical-cell Riemann sums converge (external) | W04 |
| `hyp:lift-input` | The named open input `PeriodicHMinusThreeLiftMeasureInput` | W05 |
| `lem:trace-constant` | The uniform `H^{-2}` trace constant, derived (**closes GAP R1**) | W06 |
| `ext:prokhorov` | Prokhorov extraction (external) | W06 |
| `lem:hC-identification` | The paired cosine/sine covariance entries, derived (**closes GAP R2**) | W07 |
| `ext:subseq` | Subsequence criterion for whole-sequence convergence (external) | W08 |
| `rem:no-bessel` | Why no Bessel kernel appears: the proof is in the symbol domain | W04 |

Prefixes for anything else you add: `eq:` for displayed equations,
`rem:` for remarks, `tab:` for tables, `asm:` for standing assumptions.

---

## 5. Cross-references

Use `\cref{...}` / `\Cref{...}` (cleveref) — never `Section~\ref` by hand. The
labels above are the only guaranteed targets; references to labels owned by other
writers are expected and encouraged (the numbering is resolved by LaTeX). Do not
cite a result that the owning writer might not write: if you need a statement from
another section, use the row of the table above that describes it.

---

## 6. Numbers

**Never type a structural count.** Use the macros of `generated/metrics.tex`:
`\NumCleanModules`, `\NumCleanLines`, `\NumAuditProbes`, `\NumCleanSorry`,
`\NumCleanProjectAxioms`, `\NumRootFiles`, `\NumRootLines`, `\NumContracts`,
`\NumPermittedAxioms`, `\NumChainTheorems`, `\NumProofDocs`, `\NumProbes`,
`\NumFailureCards`, `\LeanToolchain`, `\TectonicVersion`.

A literal copy of one of those values in the prose is a build failure (checked).
Mathematical constants (`1/2`, `2π`, `1/(4π)`, `a^{-d/2}`) are of course free.

---

## 7. Citations

Cite only these keys, all present in `refs.bib`:

`ossier1973`, `ossier1975`, `minlos1959`, `gj1987`, `gjs1974`, `simon1974`,
`nelson1973`, `grs1975`, `bogachev1998`, `kuo1975`, `billingsley1999`,
`prokhorov1956`, `reedsimon1980`, `yosida1980`, `dlmf`, `conway1990`.

Do not invent keys, do not cite a work for a claim it does not support, and do not
cite a work merely because it is famous. Every bib key must be cited at least once
across the paper (checked), so if you use a key, use it for something real.

---

## 8. Style

House style is evidence-led scientific prose (the project's academic-skills
standard): the verb strength must match the evidence.

- Observation before interpretation; never let an interpretation masquerade as a
  proved statement.
- No "novel", "groundbreaking", "first", "unprecedented", "seamless", "powerful".
  Say what was proved.
- Define a symbol at first use, then reuse it exactly; there is a single notation
  ledger (below) and you must not introduce a second spelling.
- One paragraph, one job. First sentence of each paragraph states its claim.
- Proofs: complete and in order; if a step is standard, say which standard fact
  and name it; never write "it is easy to see" for something that is not.
- Prefer short sentences. Avoid nominalisations and stacked subordinate clauses.
- No forward promises ("we will later show that this revolutionises …").

**Notation ledger** (use exactly this):

| Object | Spelling | Never |
|---|---|---|
| torus | `\Torus` (= `T_L^2`), period `L`, volume `V = L^2` | `\mathbb T^2`, `T^2` |
| mode index set | `I_N = (\Z/N\Z)^2` on the lattice, `\Z^2` in the limit | `\Lambda`, `\mathcal I` |
| norm on the mode lattice | `\norm{k}_\infty = \max_i \abs{k_i}` (the Lean weights use this) | silently using `\abs{k}^2 = Σ k_i^2` for the weight |
| Fourier weight | `\widetilde w_s(k) = \norm{k}_\infty^{-2s}` for `k \neq 0`, with the zero-mode convention stated separately: `w_3(0)=1`, `w_2(0)=0`, `\widetilde w_2(0)=1`. So the carrier weight is `\norm{k}_\infty^{-6}` and the energy weight `\norm{k}_\infty^{-4}` | `-s-2` as an exponent (wrong; the exponent is `-2s`), or a Euclidean norm in a weight |
| lattice spacing / size | `a`, `N`, with `aN = L`; the sequence index is `n` with `N = n+1` | `\epsilon`, `M` for the spacing |
| mass | `m > 0` | `m_0`, `\mu` |
| lattice law (finite-source lift) | `\mu_N` | `\nu_N`, `P_N` |
| the other lattice law | `\mu^{\mathrm{GJ}}_N` (only when contrasting, and say it is not what converges) | confusing the two |
| limit law | `\mu_{\mathrm{free}}` | `\mu_f`, `\mu_\infty` |
| carrier | `\HL{3}` completion carries the measures; `\HL{2}` carries the energy/moment | swapping them |
| covariance | `C_m` (torus), `C_N` (lattice) — the lattice covariance is an **input**, not derived | `G`, `S_2` |
| resolvent | `(m^2-\Delta_T)^{-1}`; symbol `\lambda(k) = m^2 + (2\pi/L)^2\abs{k}^2` | sign conventions of `-\Delta+m^2` mixed in |

If you believe a spelling is wrong, write it as a `remark` and report it; do not
change it unilaterally.

---

## 9. Inputs you must read before writing

- `notes/paper_ledger.md` — the paper-level proof skeleton, every lemma with a
  `path:line` pointer. **This is your primary source for Part I.**
- `notes/lean_ledger.md` — the declaration and definition ledger. **This is your
  primary source for Part II and for any `\lean{}` name.**
- `paper/completion/sections/*.tex` — the *style and architecture* reference of
  the sibling paper (Part I mathematics + Part II machine verification, `external`
  theorem environments, honest boundaries). Read the architecture, not the content:
  that paper is about a different theory.
- `proofs/pphi2_hminus3_*.md` and the other documents listed in
  `notes/paper_ledger.md` — the mathematical sources themselves, when you need
  detail beyond the ledger.

If the ledger and a primary source disagree, the primary source wins and you
report the discrepancy.

---

## 10. Return value

After writing your files, return at most 30 lines:

```
FILES: <path> (+byte/line counts)
STATEMENTS ADDED: <label — one line each>
EVIDENCE TAG per statement: (M)/(L)/(F)/(H)
NUMBERS USED: <which \Num* macros>
OPEN GAPS: <anything you could not support — be specific>
CONFLICTS: <contract vs ledger/source, if any>
```

---

## 11. Formal-side traps (binding for Part II, and for anyone who quotes Lean)

The development's own inventory (`notes/lean_ledger.md` §3 and §5.iv) records traps that can damage a
paper sentence. Six are restated here as prohibitions.

1. **`liftedMeasure` is not a construction.** It is a *field* of a generic structure
   (`formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicFreeFieldFinalTheorem.lean:18-21`), constrained
   only by an equation. The object the theorems are about is
   `periodicHMinusThreeFixedVolumeFreeFieldProbabilityMeasure` — a pushforward of the **finite Gaussian
   source**, not of `physicalGJMeasure`. Never write "the lift `liftedMeasure`".
2. **The final-theorem wrapper is vacuous.** `latticeFreeFieldMeasure_tendsto_periodicFreeGaussian`
   concludes its own hypothesis (`exact hfinal`). Part II may *name* it as a contract-shaped interface and
   must then say in the same breath that it is vacuous; it may never be cited as the paper's theorem.
3. **`..._weak_limit_unique` is Hausdorff uniqueness, not identification.** It says two limits of the same
   filter agree. The characterisation of `\mu_{\mathrm{free}}` by its cylinder marginals is a *separate*
   pair of results. Never write "the limit is unique, hence characterised". The evidential chain is:
   tightness -> Prokhorov -> the subsequential limit inherits the marginals -> cylinder uniqueness ->
   whole sequence.
4. **The carrier is two-dimensional only.** Every measure-limit object is hard-wired to `Fin 2 -> Z`, while
   the registered covariance theorems are stated for general `d`. Never present the measure limit in
   dimension `d > 2`; the covariance limit may be stated for general `d`, but then say in the same sentence
   that the measure chain uses `d = 2`.
5. **Periodicity is a hypothesis of the covariance theorems.** `IsFlatTorusPeriodic` is required by the
   covariance limit; the Green-pairing series identity does not need it. Do not restate the covariance limit
   "for every bounded continuous test" — write "bounded continuous periodic".
6. **The spacing enters twice.** `a^d` sits on the test sampling and again inside the per-site lift vector,
   while the GJ covariance carries `(a^d)^{-1/2}` per factor. Say this once, explicitly, where the chain's
   first limit is stated; a reader who silently cancels the two powers gets the constant wrong.

Finally, the package root aggregator `formal/lean/s6/pphi2_clean/AImathPPhi2Clean.lean` imports 57 of the 89
modules directly and reaches 81 transitively; **8 modules are not reachable at all**, among them
`PeriodicHMinusThreeWeakLimitMarginal` (six of the seven registered measure-limit theorems) and
`PeriodicHMinusThreeProkhorovSubsequence`. Part II must say this plainly: the footprints for those theorems
are evidenced by the recorded server-side transcript (Appendix B), not by a local build of the aggregator.
Do not write "the package root builds every module".
