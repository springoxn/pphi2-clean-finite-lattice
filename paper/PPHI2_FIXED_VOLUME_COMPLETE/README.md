# Whole-sequence weak convergence of fixed-volume lattice free fields on a periodic H^{-3} carrier

A standalone, arXiv-style paper (amsart, Tectonic) reporting one theorem of the
AImath project together with its complete Lean 4 formalisation: the
fixed-physical-volume two-dimensional periodic free field converges weakly, as a
**whole sequence**, to a uniquely determined free Gaussian measure on an explicit
weighted `l^2` carrier.

Build entry point: `python build_all.py`. Gate: `python audit/verify_paper.py`.

## What the paper claims

For `L > 0` and mass `m > 0`, the finite-source Fourier pushforwards `mu_N` of the
fixed-volume lattice Gaussian laws (`a N = L`) are tight on the concrete carrier
(an explicit weighted `l^2` space isomorphic to an `H^{-3}` completion), with a
uniform `H^{-2}` moment; their finite Fourier marginals converge to paired
cosine/sine Gaussian laws with the periodic massive resolvent covariance; and
therefore the whole sequence converges weakly to a Borel probability measure
`mu_free` characterised by those marginals. Separately, the covariance integrals
of the underlying lattice measures converge, at fixed volume, to the pairing with
an independently constructed periodic massive resolvent.

## What the paper does not claim

Stated in `sections/10_scope.tex`; the short version:

1. it does not identify `mu_free` with a total carrier-valued representative of
   the physical lattice measure (that bridge is the named, still open input
   `hyp:lift-input`, and it is used nowhere in the chain);
2. it asserts no equivalence with a pre-existing distribution-defined Sobolev
   space and no strong unbounded-Laplacian domain theorem;
3. it constructs no covariance operator on the carrier and asserts no
   operator-level Gaussianity -- only the finite marginals are identified;
4. it claims no rate, no exponential tail, no modulus: the tightness is
   first-moment Markov only;
5. the measure limit is two-dimensional, and no dimensional generalisation of
   the carrier is claimed.

No interacting ultraviolet limit and no Osterwalder--Schrader reconstruction is
proved; the theory constructed here is the free one.

## Layout

| path | what it is |
|---|---|
| `main.tex` | frozen preamble, macros, title, abstract, input order |
| `sections/` | the body: `00_abstract` .. `14_reproduction` |
| `figures/` | the two figures and their provenance (`PROVENANCE.md`) |
| `generated/` | **derived**: counts, declaration ledger, footprint transcript, bibliography |
| `audit/` | the four scripts that derive, gate and register |
| `ext/axiom_transcript.txt` | recorded `#print axioms` transcript, with commands and date |
| `notes/` | the two source ledgers the paper was written from, plus `CONTRACT.md` |
| `build/` | compile output, `main.pdf`, and `LAST_BUILD.txt` (hashes of every source) |

`generated/*.tex` are rewritten on every build and must never be edited by hand.

## The four paper checks (`audit/verify_paper.py`)

Each has a negative control; `--self-test` runs all of them against deliberately
broken inputs, because a checker that cannot fail proves nothing.

- **N** every Lean name quoted in the body is a declaration listed in the
  generated ledger;
- **M** every structural count in the body is a macro of `generated/metrics.tex`,
  and no distinctive count appears literally in the prose;
- **L** labels, cross-references, citations and bibliography keys close, every
  section is labelled, no label is duplicated, and `refs.bib` cannot drift from
  the rendered bibliography;
- **E** the axiom transcripts all equal the permitted set, and the ledger covers
  exactly the names the body quotes.

What they do **not** check: that a paper sentence means what its Lean name says.
That residue is stated in Section 14 and is not closable by a script.

## Two build facts worth knowing

1. **The bibliography is rendered, not compiled.** The offline Tectonic cache the
   project uses contains no `.bst` files, so BibTeX fails and the driver
   *swallows* the error -- the build stays green while every citation prints as
   `[?]`. `audit/make_bib.py` therefore renders `refs.bib` into an explicit
   `thebibliography` environment, and check **L** keeps the two in step.
2. **The counts are computed, not typed.** `audit/count_lean.py` recounts the
   Lean sources and the contract registry on every build, so a structural count
   can only rot in one place, and check **M** refuses a typed copy.

## Reproducing the Lean side

The formalisation is a separate Lake package (`AImathPPhi2Clean`) under
`formal/lean/s6/pphi2_clean/`, on Lean `v4.34.0-rc2`. The footprints transcribed
in `ext/axiom_transcript.txt` were produced by a `lake build` of the module that
declares the main theorem followed by

```
printf '%s\n' 'import AImathPPhi2Clean.PeriodicHMinusThreeWeakLimitMarginal' '#print axioms <NAME>' \
  > /tmp/Check.lean
lake env lean /tmp/Check.lean
```

See Section 14 for the exact commands, and Section 13 for the honest boundary:
the package root does not reach every module, and a green build proves the stated
declarations rather than the mathematics behind their hypotheses.
