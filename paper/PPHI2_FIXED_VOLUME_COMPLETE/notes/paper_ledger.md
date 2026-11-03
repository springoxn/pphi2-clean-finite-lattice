# PPHI2 fixed-volume H^{-3} free field — paper-level proof ledger

> status: ACTIVE · owner: PPHI2_FIXED_VOLUME_FREE_FIELD_MEASURE_LIMIT · asof: 2026-11-02

Purpose: inventory the **human (paper-level) proofs** of one theorem so that a self-contained
arXiv-style article can be assembled without inventing anything. This note is a WORK-PRODUCT. It
adds no state, changes no graph, and does not re-adjudicate governance: wherever the sources record
a status token or register a residual assumption, that is reported as *the source's own statement*
with a pointer, not treated as mathematics.

Pointer convention: `path:line` or `path:lines A-B`, resolved against `E:\study\AImath`. Abbreviations
used below:

| Abbrev | File |
|---|---|
| `D1` | `proofs/pphi2_fixed_volume_fourier_covariance.md` (260 lines) |
| `D2` | `proofs/pphi2_negative_sobolev_carrier_lift.md` (195) |
| `D3` | `proofs/pphi2_infinite_gaussian_measure.md` (99) |
| `D4` | `proofs/pphi2_finite_fourier_coordinate_convergence.md` (120) |
| `D5` | `proofs/pphi2_uniform_negative_sobolev_tightness.md` (46) |
| `D6` | `proofs/pphi2_hminus3_prokhorov_weak_convergence.md` (56) |
| `D7` | `proofs/pphi2_hminus3_cylinder_borel_uniqueness.md` (43) |
| `D8` | `proofs/pphi2_hminus3_topology_borel_boundary.md` (31) |
| `D9` | `proofs/pphi2_hminus3_lattice_measure_lift.md` (39) |
| `D10` | `proofs/pphi2_full_space_weak_convergence.md` (35) |
| `SA` | `proof_graph/scopes/PPHI2_FIXED_VOLUME_COVARIANCE_LIMIT.yaml` |
| `SB` | `proof_graph/scopes/PPHI2_FIXED_VOLUME_FREE_FIELD_MEASURE_LIMIT.yaml` |
| `TG` | `proof_graph/theory_graph.yaml` |
| `LN` | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/` (Lean side; cited only where the paper text is silent) |

Two secondary files were read only to fix the outer boundary and are used nowhere in the proof chain:
`proofs/pphi2_free_field_2d.md` (the 2-D continuum free-field layer, `K_0/(2π)`) and
`proofs/pphi2_exponential_clustering.md` (OS-reconstruction boundary). **No document among `D1`–`D10`
cites either of them** (checked by name and by `FREE_FIELD_2D`: no hit in `D1`–`D10`).

---

## §1 The theorem, stated exactly

### 1.1 Registered statements (verbatim)

**(a) Measure limit — graph node, `TG:4110-4117`:**

> For L > 0 and mass > 0, the concrete fixed-volume periodic lattice free-field probability measures
> (N = n + 1, a = L/N) converge weakly on PeriodicHMinusThreeCompletion = lp ((Fin 2 → ℤ) → ℂ) 2 to a
> uniquely determined Borel probability measure μ_free. The Lean construction extracts an initial
> Prokhorov limit using concrete weighted-lp separability and tightness, identifies its finite Fourier
> marginals by fixed-volume cylinder convergence, and proves every subsequential limit has those same
> marginals by Borel cylinder uniqueness. The candidate is constructed by this theorem, not assumed as
> a pre-existing measure object.

**(b) Measure limit — scope claim, `SB:5-14`:**

> For L > 0 and mass > 0, the Borel probability measures obtained by pushing the finite-dimensional
> lattice covariance Gaussian with N = n + 1 and a = L/(n+1) through the explicit Fourier lift
> converge weakly on the concrete carrier lp ((Fin 2 → ℤ) → ℂ) 2. The lift agrees pointwise with the
> total H^-3 carrier representative on embedded finite lattice configurations. A common limit is
> constructed by Prokhorov extraction, its finite Fourier marginals are identified by cylinder
> convergence, and Borel cylinder uniqueness identifies every subsequential limit, yielding
> whole-sequence convergence. The stronger abstract `PeriodicHMinusThreeLiftMeasureInput` interface for
> arbitrary physicalGJ pushforwards is not a premise of this theorem.

**(c) The paper-side theorem statement, `D10:3-11`:**

> For every `L > 0` and `mass > 0`, Lean proves
> `periodicHMinusThree_fixedVolume_weak_limit_exists_with_expected_cylinders`
> in `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicHMinusThreeWeakLimitMarginal.lean`. It
> constructs a Borel probability measure `mu_free` on `PeriodicHMinusThreeCompletion`, proves that the
> full fixed-volume sequence converges to it, and identifies every finite weighted Fourier-coordinate
> marginal with the corresponding paired cosine/sine periodic-resolvent Gaussian law. The separate
> theorem `periodicHMinusThree_fixedVolume_weak_limit_unique` proves uniqueness of the measure
> satisfying the weak-limit proposition.

**(d) Covariance limit — graph node, `TG:4025-4030`:**

> Fixed physical volume periodic free Gaussian covariance limit: actual physically sampled GJ
> covariance inner products, mixed second moments and centered covariances converge, for positive L and
> mass and periodic bounded continuous real tests, to the real physical-volume pairing with the
> independently constructed periodic massive variational weak resolvent on the completion of genuine
> unweighted trigonometric polynomials and their classical physical-coordinate gradients.

**(e) Covariance limit — scope claim, `SA:5-17`:**

> For positive physical period L and mass m and real bounded continuous L-periodic tests, the actual
> physically sampled GJ covariance inner products, mixed second moments and centered covariance
> integrals converge to the real part of L^d times the complex probability-Haar L2 pairing with the
> independently constructed periodic massive variational weak resolvent. Its periodic H1 space is the
> closed value-gradient graph completion of arbitrary unweighted finite trigonometric polynomials and
> their actual classical physical-coordinate derivatives. The Riesz adjoint construction solves the
> massive weak equation against every completed H1 test with unique physical L2 value. The exact
> Haar-to-Lebesgue coefficient normalization and Parseval identify the existing Fourier Green pairing
> with this operator pairing, without caller-supplied convergence, summability or Green-identification
> assumptions.

### 1.2 What is proved, and what is not

**What is proved (one sentence).** For fixed `L>0`, `mass>0`, the explicit finite-source Fourier
pushforwards of the exact finite-volume lattice Gaussian laws (`N=n+1`, `a=L/(n+1)`, so `aN=L`) form a
sequence of Borel probability laws on the concrete weighted `lp` space
`PeriodicHMinusThreeCompletion` that is tight with a uniform first moment (`D5:5-30`), whose finite
weighted Fourier marginals converge to the paired cosine/sine Gaussian laws with the periodic massive
resolvent covariance (`D4:29-44`, `D10:24-28`), and which therefore converges weakly, as a whole
sequence and not only along a subsequence, to a Borel probability measure `mu_free` that is unique
among measures with those marginals (`D10:24-29`), while the centred covariance integrals of the
underlying lattice measures converge to `Re(V<f_L,Rg_L>_E)` with `R` the independently constructed
periodic massive variational weak resolvent on the closed value-gradient graph completion of finite
trigonometric polynomials (`D1:162-201`, `SA:5-17`).

**What is not proved (one sentence).** The theorem does not identify `mu_free` (nor the sequence laws)
with the pushforward of the *physical* Gaussian measure `physicalGJMeasure` under a total
carrier-valued representative — that bridge is a separately named, still-open input
`PeriodicHMinusThreeLiftMeasureInput` (`D9:29-34`, `SB:18-19`, `D2:120-145`) — and it asserts no
identity of the carrier with any distribution-defined Sobolev space, no interacting/ultraviolet limit,
and no Osterwalder–Schrader reconstruction (`SA:18-22`, `SB:16-21`, `D1:160`, `D1:254`).

---

## §2 Dependency graph of the argument

Legend: `[P#]` proved step (paper-level argument present in the named document); `[I#]` input or
contract — definitions, hypotheses, or an external theorem that the chain *consumes* and does not
prove; `[C#]` conditional step (takes a named hypothesis; not closed).

```text
[I1] lattice operator A_N = m^2 - Delta_a, symbol lambda_N(p) = m^2 + 4a^-2 sum_i sin^2(pi p_i/N)
     and the GJ lattice covariance; Q_N(f,g) = V^-1 sum_p conj(F_N) G_N / lambda_N          D1:9-19
     INNER PRODUCT FORM: inner(C_GJ b, C_GJ c) = a^-d <b, A_N^-1 c>_counting             D1:41-43
                                    |
[I0] finite-volume Gaussian family physicalGJMeasure(d,N,a,m) and its finite Fourier lifts
     (definitions only; the exact zero mean is used)                                    D1:219,D1:226
                                    |
                                    v
[P1] character eigenbasis, orthogonality, finite inversion, finite Parseval + sup-norm bound
     sum_p |F_N(p)|^2 <= V^2 ||f||_infinity^2                                            D1:25-37
                                    |
                                    v
[P2] exact finite bridge: physical covariance = Re Q_N, with the V^-1 factor               D1:43
                                    |
                                    v
[P3] fixed-mode coefficient convergence |F_N(p_N(k)) - F(k)| <= V omega_k(a) -> 0            D1:45-51
     + symbol convergence 4(N/L)^2 sin^2(pi k_i/N) -> (2 pi k_i/L)^2                       D1:53-57
                                    |
      +-----------------------------+------------------------------+
      |                                                            |
      v                                                            v
[P4] discrete uniform tail                                    [P5] continuum summability:
     |Q_N - Q_{N,K}| <= V ||f|| ||g|| / R_K,                    Green series absolutely
     R_K = m^2 + 16 K^2 / L^2, one K for all N                 convergent (Young)         D1:90-95
     (needs lambda_N >= m^2 + 16|k|_inf^2/L^2)      D1:65-80          + sharp tail
                                                                  |Q-Q_K| <= V||f||||g||/D_K
                                                                  D_K = m^2+(2pi/L)^2(K+1)^2  D1:97-105
      +-----------------------------+------------------------------+
                                    |
                                    v
[P6] epsilon/3 assembly: |Re Q_N - Re Q| < eps for one N                             D1:203-211
                                    |
                                    v
[P7] (Q=R): the Green series equals V <f_L, R g_L>_E, R = independent Riesz/energy solver
     (E) energy split; (H1) graph completion; (W) all-H1 weak equation + uniqueness;
     (N) Haar<->Lebesgue normalisation B f_L(k) = V^-1 F(k)                             D1:127-201
                                    |
                                    v
[P8] covariance / mixed-moment / centered-covariance limits for the actual measures      D1:214-232
     = TG:4025-4030 (node PPHI2_FIXED_VOLUME_COVARIANCE_LIMIT)
                                    |
                                    |  (consumed by the marginals step, not by tightness)
                                    v
[C1] finite-family Gaussian law convergence, target periodicResolventTargetProbabilityMeasure,
     GIVEN hinner (pairwise covariance convergence) and hC (entry identification)         D4:29-44
                                    |
[P9] finite cylinder maps are continuous and Borel; finite-source cylinder coordinate is an
     explicit finite linear combination of cosine/sine source coordinates                D4:65-83
                                    |
                                    v
[P10] fixed-volume H^-2 trace bound, uniform in N:
      C = mass^-2 L^2 + 2 mass^-2 L^2 * sum_k periodicHMinusTwoWeight k                 D5:5-22
      (per-mode first moment + zero mode; energy uses periodicHMinusTwoFullWeight)      LNU:10-27
                                    |
                                    v
[P11] uniform first moment on the actual pushforward measures                          D5:24-30
                                    |
                                    v
[P12] tightness in PeriodicHMinusThreeCompletion: Markov tail C/eps + compactness of
      closures of H^-2 sublevels (weight comparison, compact tail)                      D5:32-40, LNU:235-296
                                    |
[P13] separability of the weighted lp carrier => Polish                                D8:10-20
                                    |
                                    v
[P14] Prokhorov: every subsequence has a further subsequence converging to a probability
      measure on the carrier (Mathlib Prokhorov)                                        D6:24-29
                                    |
                                    v
[P15] cylinder convergence transfers to each extracted limit (continuous mapping)        D6:33-38
                                    |
                                    v
[P16] cylinder sigma-algebra = Borel sigma-algebra; finite-marginal uniqueness for Borel
      probability measures (pi-system + Dynkin)                                         D8:16-20, D7:10-20
                                    |
                                    v
[P17] whole-sequence convergence + uniqueness of the limit: Filter.tendsto_of_subseq_tendsto
      (an input from Mathlib's order/filter library)                                    D6:38-47, D10:29
                                    |
                                    v
      THEOREM  TG:4110-4117 / SB:5-14 / D10:3-11

OFF-GRAPH (present in the corpus, NOT used by the chain):
[D3] abstract Gaussian series measure on WeakDual R E (existence only; 5 explicit inputs
     still open, and no identification with the concrete carrier)                        D3:5-65
[D2] carrier/topology contract (weights, H^-2 -> H^-3 inclusion, general H^-s rule,
     and the still-open physical pushforward)                                            D2:42-77,D2:120-145
```

Reading notes on the graph.

- `[I0]` is an input in the strict sense: `physicalGJMeasure` and
  `numberedLatticeCovarianceGJ 2 N a mass` are used, not constructed, in `D1:D5`. Their defining
  properties used downstream are only: probability, exact zero mean (`D1:226`), Gaussian law of each
  coordinate (`D1:226` region), and the covariance identity of `[I1]`.
- `[C1]` is the one conditional step on the covariance side: `D4:42-44` states it holds
  "under the existing pairwise covariance convergence hypothesis `hinner` and its identification with
  the canonical periodic resolvent covariance matrix `hC`". `hC` is *not* a consequence of `[P8]` as
  written there; `[P8]` supplies `hinner` for real probes. See §7 item R2.
- `[P2]` is where the whole `V^{-1}` bookkeeping is fixed; every later factor of `L^d` traces back to
  `D1:43` and to `(N)` at `D1:186-192`.

---

## §3 Lemma-level skeleton per document

Notation in tables: **Hyp** = hypothesis/input with pointer; **St** = statement (one line);
**Pr** = paper-level proof status: `full` = written out in this document; `ref` = referred to another
document/declaration; `cond` = explicitly conditional. Lemma IDs are `D#.k` and are the units counted
in the return summary.

### D1 — `proofs/pphi2_fixed_volume_fourier_covariance.md`

**Purpose.** Fix the finite and continuum definitions, prove the fixed-volume covariance limit for
bounded continuous periodic tests, and construct the continuum limit target (the periodic massive weak
resolvent) independently of the Fourier series that converges to it.

**Hypotheses.**

| H | Statement | Pointer |
|---|---|---|
| H1a | integer `d>=1`, `L>0`, `m>0`, `N>=1`, `a=L/N`, `V=L^d`, sites `(Z/NZ)^d` with physical reps in `[0,L)^d` | `D1:7` |
| H1b | limit is `N->infinity` with `L,m` fixed — "it is not an infinite-volume limit" | `D1:7` |
| H1c | test space = real bounded continuous `L`-periodic lifts, i.e. `C(T_L^d;R)` | `D1:7` |
| H1d | `A_N = m^2 - Delta_a` with periodic nearest-neighbour differences | `D1:9` |
| H1e | integral-normalised coefficients `F_N(p)`, `F(k)` (no `1/V` in the coefficient) | `D1:11-12` |

**Lemmas.**

| ID | Statement | Pr | Pointer |
|---|---|---|---|
| D1.1 | Shifting a site by `±e_i` multiplies `chi_p` by `exp(±2 pi i p_i/N)`, so `Delta_a chi_p = -4a^-2(sum_i sin^2(pi p_i/N)) chi_p`; valid also at `N=1,2`; hence `lambda_N>=m^2>0` | full | `D1:25` |
| D1.2 | `sum_x chi_{-p}(x) chi_q(x) = N^d 1_{p=q}` | full | `D1:27-29` |
| D1.3 | Inverse transform `u(x)=N^-d sum_p (sum_y u(y) chi_{-p}(y)) chi_p(x)`; for real `u`, coefficient at `-p` is the conjugate at `p` (bilinear Parseval via `finiteFourier_bilinear`) | full/ref | `D1:31-35` |
| D1.4 | `sum_p |F_N(p)|^2 = V a^d sum_x |f(ax)|^2 <= V^2 ||f||_infinity^2` | full | `D1:37` |
| D1.5 | `inner(C_GJ b, C_GJ c) = a^-d <b, A_N^-1 c>_counting` (inverse-mass form of the GJ covariance) | ref (`latticeCovarianceGJ_inner_eq_massResolvent`) | `D1:41` |
| D1.6 | The explicit Fourier inverse solves the complexified mass equation; character denominators are nonzero from positivity alone (no trig-form hypothesis) | ref | `D1:43` |
| D1.7 | Sampled vectors `b_x=a^d f(ax)` turn `D1.5` into `a^d <f, A_N^-1 g>`; the numbered, physically sampled covariance equals `Re Q_N` including the exact `V^-1` (`fixedVolumeCovarianceInner_eq_discreteFourierGreenPairing`) | ref | `D1:43` |
| D1.8 | `|F_N(p_N(k)) - F(k)| <= V omega_k(a) -> 0` for fixed `k`, `omega_k` the sup-norm modulus of continuity of `h_k(t)=f(t)exp(-2 pi i k.t/L)` on the compact cell | full | `D1:47-51` |
| D1.9 | `4(N/L)^2 sin^2(pi k_i/N) -> (2 pi k_i/L)^2`, so `lambda_N -> lambda`; on `|k|_inf<=K` the residue map is injective once `N>2K`, so finite sums converge termwise | full | `D1:53-57` |
| D1.10 | Centred representatives `{-floor(N/2),...,ceil(N/2)-1}^d` give `lambda_N(k) >= m^2 + 16|k|_infinity^2/L^2` (concavity/chord bound `sin t >= 2t/pi` on `[0,pi/2]`); includes the even-`N` Nyquist frequency once | full | `D1:65-71` |
| D1.11 | For `R_K=m^2+16K^2/L^2`: `|Q_N - Q_{N,K}| <= (V R_K)^-1 (sum_p|F_N|^2)^{1/2}(sum_p|G_N|^2)^{1/2} <= V||f||_inf||g||_inf/R_K`, uniformly in `N` and `K>=0` | full (Lean: `discreteFourierGreenPairing_sub_cutoff_norm_le`) | `D1:73-80` |
| D1.12 | Continuum finite-box Bessel bound `sum_{k in S_K}|F_N(p_N(k))|^2 <= V^2||f||^2` holds **eventually in N** (for `N>2K`), not for every `N`; passing to finite `S` gives `sum_{k in S}|F(k)|^2 <= V^2||f||^2` and square-summability | full | `D1:82-90` |
| D1.13 | Green series converges absolutely: `|conj(F(k))G(k)/lambda(k)| <= (|F(k)|^2+|G(k)|^2)/m^2` (Young + `lambda>=m^2`); exhaustion by symmetric boxes gives `Q_K -> Q` | full | `D1:90-95` |
| D1.14 | Quantitative continuum tail `|Q - Q_K| <= V||f||_inf||g||_inf / D_K`, `D_K = m^2+(2 pi/L)^2(K+1)^2`, using `lambda(k)>=D_K` outside `S_K` | full | `D1:97-105` |
| D1.15 | Common summable envelope on smooth lifts: with `r=d+1`, `D_r(f)=max_i||partial_i^r f||_inf`, `|F_N(k)| <= V(L/4)^r D_r(f) q^{-r}` and `V^-1|conj(F_N)G_N/lambda_N| <= (V L^2/16)(L/4)^{2r} D_r(f)D_r(g) q^{-2r-2}`, summable since `2r+2>d`; zero mode bounded separately by `m^-2` and `V||f||_inf||g||_inf` | full | `D1:109-123` |
| D1.16 | Physical-volume energy split `(E)`: `<h,v>_H = m^2<jh,jv>_E + sum_i <D_i h, D_i v>_E` for `H=l2(Z^d)`, `w(k)=lambda(k)^{-1/2}`, `Jh=w h`, `B` the Haar-Hilbert-basis isometry, `D_i` the multiplier `i omega_i(k) w(k)` | full | `D1:127-142` |
| D1.17 | The multipliers are genuine classical coordinate derivatives: `partial_{x_i} P_a = sum_{k in S} i omega_i(k) a(k) b_k` with `HasDerivAt` certificates | ref (`hasDerivAt_mFourier_physicalCoordinate`, `hasDerivAt_trigPolynomial_physicalCoordinate`) | `D1:144-154` |
| D1.18 | `(H1)`: `{(jh,(D_i h)_i) : h in H} = closure(G_0)` in `E x E^d`, `G_0` = finite-support polynomials and their gradients; closed range by `(E)`, density of finite support, injectivity of `j` | full | `D1:156-160` |
| D1.19 | `(R)` `h_g = J^* B g`, `Rg = j h_g`; the adjoint identity gives `(W)` `m^2<Rg,jv>_E + sum_i<D_i h_g,D_i v>_E = <g,jv>_E` for every `v in H`; uniqueness by `(E)`; `||Rg||_E <= m^-2 ||g||_E` (sharp) | full | `D1:162-175` |
| D1.20 | `(P)`: `B(Rg)(k) = lambda(k)^-1 Bg(k)` and `<f,Rg>_E = sum_k conj(Bf(k))Bg(k)/lambda(k)`; absolute summability by Cauchy–Schwarz; multiplier formula is a conclusion about the independent solver, not a definition of `Q` | full | `D1:177-184` |
| D1.21 | `(N)` Haar <-> Lebesgue: `B f_L(k) = int_(0,1]^d f(Lz)e^{-2 pi i k.z}dz = L^{-d} int_[0,L]^d f(x)e^{-2 pi i k.x/L}dx = V^{-1}F(k)` (half-open representative; null boundary; Jacobian `L^d`; phases exact for negative `k`) | full | `D1:186-192` |
| D1.22 | `(Q=R)`: `V<f_L,Rg_L>_E = V sum_k conj(V^-1F)V^-1G/lambda = V^-1 sum_k conj(F)G/lambda = Q(f,g)` | full | `D1:194-201` |
| D1.23 | epsilon/3 assembly: pick `K` with both tails `< eps/3`, then `N` with fixed-cutoff error `< eps/3`; `tendsto_of_cutoff_tail`; interface fields are defining equalities, `uniform_tail` and `mode_tendsto` are derived, not stored | full | `D1:203-211` |
| D1.24 | Transfer to measures: `integral omega (omega f)(omega g) dmu_n -> Re Q(f,g)` and the centred version `E[(omega f - E omega f)(omega g - E omega g)] -> Re Q(f,g)`, all means exactly zero at every mesh (`physicalGJMeasure_eval_mean_zero`) | ref (three named declarations) | `D1:214-232` |

**Conclusion.** `D1:232`: the final consequences are the three limits with target
`Re physicalTorusResolventPairing(f,g) = Re(V<f_L,Rg_L>_E)`; verification status is "recorded
separately"; `D1:254` records the machine boundary and states explicitly the four things not obtained
(limiting probability measure, distribution-defined Sobolev equivalence, interacting UV limit, OS
reconstruction).

**Self-reported conditionals / deferrals (quoted).**

- `GAP: D1:61` — "Continuum summability, the continuous K-to-infinity limit and resolvent
  identification remain obligations of the full covariance limit." (Superseded later in the same file
  by `D1:90-105` and `D1:251`; see §7 item R5.)
- `GAP: D1:258-260` — "Continuum completeness and the identification of this series pairing with an
  independently defined periodic resolvent remain obligations; the interface retains `target_green`
  for precisely that target identification. An axiom audit of a conditional target-identification
  theorem does not discharge that remaining field." This paragraph is labelled
  "Previously verified finite and Fourier-series boundary" (`D1:256`), i.e. it describes the *state
  before* `torusFourierGreenPairing_eq_physicalTorusResolventPairing`, which `D1:251` reports as done.
  A paper must not quote `D1:260` as the current boundary, nor `D1:251` as if `D1:260` did not exist.
- `GAP: D1:160` — the completion `(H1)` "does not assert an additional equivalence with a
  pre-existing distribution-defined Sobolev type. Such a comparison, or a strong unbounded Laplacian
  domain theorem, is outside the stated target."
- `GAP: D1:105` — "These estimates require no pointwise Fourier-series convergence and do not assert a
  common summable pointwise envelope for all continuous tests." The envelope exists only for smooth
  tests (`D1:109`, `r=d+1`); the restriction to `C_b` tests has no summable modewise envelope.

### D2 — `proofs/pphi2_negative_sobolev_carrier_lift.md`

**Purpose.** Fix the carrier/topology convention (which space the laws live in, which topology is used
for convergence) and state the lift/pushforward contract for the physical lattice source.

**Hypotheses / definitions with pointers.** concrete case is two-dimensional and indexed by
`Fin 2 → ℤ` (`D2:6-8`); raw sample is a
`WeakDual ℝ (BoundedContinuousFunction (Fin 2 → ℝ) ℝ)` (`D2:10`); zero mode retained with weight
`1` by `periodicHMinusTwoFullWeight`, nonzero modes weighted `‖k‖^(-4:ℝ)` (`D2:18-19`); carrier is the
weighted square-summable set, subtype exposed as `PeriodicHMinusTwoSpace` and used through `Measure.map`
(`D2:22-40`).

| ID | Statement | Pr | Pointer |
|---|---|---|---|
| D2.1 | Carrier/ambient pair: raw Fourier lift lies in the `H^-2` carrier a.e., convergence happens in the weaker `H^-3` topology; `H^-3` weight summable, `H^-2` embeds into `H^-3`, finite-tail compactness retained as an explicit input | full (definitions) + explicit input | `D2:44-62` |
| D2.2 | General rule: for a massive covariance with high-frequency behaviour `|k|^-2` in dimension `d`, Gaussian second-moment summability in `H^-s` requires `s > (d-2)/2`; compactness needs a strictly weaker ambient exponent `r > s`; the 2-D formalisation uses `(s,r)=(2,3)` | full (`d=2` case); `d=4` remark unproved | `D2:64-77` |
| D2.3 | Discrete finite-source lift `periodicHMinusTwoDiscreteCarrierLift` and its per-mode identity `periodicHMinusTwoDiscreteCarrierLift_apply_of_mem` (under the raw carrier hypothesis every Fourier coordinate is the lifted lattice distribution's coordinate); pushforward named `periodicHMinusTwoDiscreteLiftMeasure` = `Measure.map` of the finite Gaussian | ref (declarations named, not proved here) | `D2:79-118` |

**Conclusion.** `D2:58` "raw Fourier lift ∈ H⁻² carrier a.e. → ambient H⁻³ topology"; `D2:195` "No claim
of full infinite-dimensional weak convergence is made by this artifact."

**Self-reported gaps (quoted; these are the honest boundary of D2 and they are load-bearing for §1.2).**

- `GAP: D2:120-124` — "The proposition `PeriodicHMinusTwoDiscreteLiftInput` records the remaining
  source-level proof boundary: raw-lift measurability and almost-everywhere carrier membership under
  the finite lattice Gaussian measure. The total representative is defined without claiming either
  fact. Its use as a genuine Borel pushforward still requires the corresponding `AEMeasurable` proof."
- `GAP: D2:127-132` — "The proposition `PeriodicHMinusTwoLiftInput` deliberately records the two missing
  facts: 1. measurability of the raw sequence-valued map; 2. almost-everywhere membership in
  `periodicHMinusTwoCarrier`."
- `GAP: D2:141-145` — "The existing full weighted trace bound proves the uniform expected weighted
  square sum, but it does not by itself yet provide the Lean theorem converting that expectation into
  the required a.e. carrier membership. That conversion, and the measurable carrier-valued
  representative, remain open inputs rather than hidden assumptions."
- `GAP: D2:147-173` — "Exact next lemma": the monotone-limit bridge
  `(AEMeasurable S) ∧ (∫ S ∂μ < ∞) ⟹ ∀ᵐ ω, S ω < ∞` is *specified* but **not proved**, with the
  caution "a finite expectation cannot be replaced by an unproved pointwise assertion".
- `GAP: D2:185-193` — "Still open: ... proof that the resulting pushforward is the intended Borel
  probability measure on the chosen `H⁻³` completion; replacement of the two-dimensional `Fin 2`
  implementation by a genuinely parameterized `Fin d` construction."

Note for the paper: the monotone bridge quoted at `D2:147-173` is elementary measure theory
(measurable nonnegative series + finite integral implies a.e. finiteness) and is stated with its exact
hypotheses; nothing mathematical is missing there, but it is *asserted as future work*, so a paper
citing `D2` must either prove it in one line or avoid needing it.

### D3 — `proofs/pphi2_infinite_gaussian_measure.md`

**Purpose.** Provide a reusable *abstract* infinite-dimensional Gaussian series measure and state
exactly how far it is from the concrete carrier. **Result: off-graph — nothing in `D4`–`D10` uses it.**

| ID | Statement | Pr | Pointer |
|---|---|---|---|
| D3.1 | `PeriodicInfiniteGaussianSeriesData` (real test space with weak-dual measurable structure, measurable Hilbert realisation, continuous `J`, enumeration `ℕ → (Fin 2 → ℤ)`, coefficient vectors, absolute norm summability) yields a measure `periodicInfiniteGaussianMeasure D` that is exactly `gaussianWeakDualMeasure D.J D.coefficientVector`, sourced from the countable product Gaussian `gaussianNoiseMeasure 1` | ref (interface names; build reported) | `D3:8-34` |
| D3.2 | Probability, measurability, and a.e. `tsum` representation `X_f(ξ) = ∑' n, ξ n * inner (coefficientVector n) (J f)` | ref | `D3:36-51` |
| D3.3 | Finite-family alignment is conditional: given a coefficient/covariance identity, the existing target-measure theorem gives the centred Gaussian law with `periodicResolventCovarianceMatrix` built from `physicalTorusResolventPairing` | cond | `D3:76-94` |

**Conclusion.** `D3:55-56`: "This construction proves existence of a probability measure on the abstract
weak-dual configuration space once the Hilbert-series data are supplied."

**Self-reported gaps (quoted).** `GAP: D3:57-65` — "It does not by itself prove that the abstract `H` is
the concrete completed periodic `H⁻³` Fourier space from Goal 1", with five enumerated remaining inputs
(construction of the `H^-3` completion/Borel realisation; an enumeration covering all Fourier labels;
trace summability; identification of the covariance; transfer to the carrier by a measurable map).
`GAP: D3:96-99` — "No theorem in this section identifies the arbitrary abstract coefficient vectors with
the periodic resolvent coefficient vectors automatically. In particular, finite-dimensional Gaussian-law
alignment and infinite-dimensional measure identification remain separate claims."

### D4 — `proofs/pphi2_finite_fourier_coordinate_convergence.md`

**Purpose.** Turn the pairwise covariance limit into convergence of the *joint* finite-dimensional
Gaussian laws for any finite test family, and build the concrete weighted cylinder maps.

**Hypotheses.**

| H | Statement | Pointer |
|---|---|---|
| H4a | arbitrary finite family `fs : Fin m → BoundedContinuousFunction (Fin d → ℝ) ℝ` (already available in the finite-dimensional theorem) | `D4:5-11` |
| H4b | `hinner` = pairwise lattice covariance convergence for all real probes | `D4:42-44`, `D4:107-108` |
| H4c | `hC` = identification of the selected finite covariance entries with the periodic resolvent matrix | `D4:43-44`, `D4:108-109` |

| ID | Statement | Pr | Pointer |
|---|---|---|---|
| D4.1 | `periodicFourierTestFamily d m L hL modes useSine` builds the explicit cosine/sine family; projections `..._apply_of_sine`, `..._apply_of_cosine` | ref | `D4:18-27` |
| D4.2 | `physicalFamilyEvalProbabilityMeasure_fixedVolume_weak_tendsto_of_any_finite_test_family`: joint finite-dimensional laws converge to `periodicResolventTargetProbabilityMeasure` under `hinner` + `hC`; "a direct specialization of the existing canonical-factor theorem" | cond | `D4:29-44` |
| D4.3 | Zero mean in every finite direction; full quadratic covariance formula for every finite family | ref | `D4:46-50` |
| D4.4 | Concrete completion `PeriodicHMinusThreeCompletion = lp (Fin 2 → ℤ → ℂ) 2`; `periodicHMinusThreeCylinderMap m modes` is continuous coordinatewise and every finite cylinder map is continuous and measurable | ref | `D4:65-71` |
| D4.5 | `periodicHMinusThreeFiniteSourceFourierLift_cylinder_apply` computes each cylinder coordinate as a finite sum of lattice source coordinates against the weighted site Fourier vector; `..._DiscreteCarrierLift_cylinder_eq_finiteSource` identifies the total-carrier-lift cylinder with the same finite-source lift; the finite-source lift is measurable (continuous finite-source coefficient map composed with measurable lattice coordinates) | ref | `D4:72-83` |
| D4.6 | `periodicHMinusThreeCylinderTestFamily`, `periodicHMinusThreeComplexifyCylinder` (combines each real pair as `sqrt(weight k) * (cos + I * sin)`), pointwise identity `..._RawCylinderCoordinate_eq_complexifyFamilyEval` | ref | `D4:88-96` |

**Conclusion.** `D4:101-105`: `periodicHMinusThreeCylinderProbabilityMeasure_tendsto_of_covariance_limits`
applies `D4.2` to the paired family and then continuous mapping, giving convergence of the selected
complex `H^-3` cylinder laws.

**Self-reported conditionals (quoted).** `GAP: D4:97-100` —
"`periodicHMinusThreeCylinderLaw_eq_complexifiedFamilyLaw` identifies the pushforward of the concrete
carrier-valued lattice probability measure with the continuous image of the existing finite real-family
probability measure, **conditional on `PeriodicHMinusThreeLiftMeasureInput`**". `GAP: D4:107-114` —
"The hypotheses remain explicit: `hinner` ... `hC` ... and `PeriodicHMinusThreeLiftMeasureInput`
provides AEMeasurability of the total carrier representative and its a.e. equality with the raw
weighted Fourier coefficients. These results concern only the selected finite cylinder maps and their
finite-dimensional probability laws. They do not construct a limiting probability measure on the entire
completion and do not assert weak convergence of carrier-valued measures." `GAP: D4:116-120` —
"Still unsupported are identification of the raw weighted-series carrier with the `lp` completion,
construction/identification of an infinite-dimensional Gaussian measure on that completion, and the
full-space tightness, Borel generation, and cylinder-uniqueness steps represented by
`PeriodicFullSpaceWeakConvergenceInput`. Those remain named inputs rather than consequences of
finite-family convergence."

**Disagreement to report (do not silently resolve).** `D4:116-120` lists full-space tightness, Borel
generation and cylinder uniqueness as *named inputs*, while `D5:38-40` says the compact-tail/weight
comparison "are implemented in the imported topology/completion modules rather than left as the old
`PeriodicHMinusThreeLpCompactnessInput` assumption", and `D6:24-29` + `D8:16-20` report those steps as
proved. The two readings differ in what is *still* an input. Resolution available in the sources, and
it is a scope difference rather than a contradiction: `D4` describes the state of the *finite-family
bridge module* (`PeriodicHMinusThreeCylinderConvergence.lean`), whose consumers still take the packed
input, whereas `D5`/`D6`/`D8` describe the *assembled* theorem's own modules. The assembled theorem is
the one that matters for the paper (`D10:24-29`), and its statement (`D10:3-11`) carries no packed
input. Pointers for both sides are given; a paper must cite `D10`, not `D4:119`.

### D5 — `proofs/pphi2_uniform_negative_sobolev_tightness.md`

**Purpose.** Produce the exact fixed-volume moment estimate and the tightness of the whole sequence.

**Hypotheses.** `a*N=L` (`D5:19-22`); weights `periodicHMinusTwoWeight(0)=0`,
`periodicHMinusTwoWeight(k)=|k|^{-4}` for `k≠0`, with the zero mode accounted for separately
(`D5:17-19`).

| ID | Statement | Pr | Pointer |
|---|---|---|---|
| D5.1 | Explicit constant `periodicHMinusTwoFixedVolumeTraceConstant L mass` whose value is `mass^{-2} * L^2 + 2 * mass^{-2} * L^2 * sum_k periodicHMinusTwoWeight k` | full (value) / ref (derivation) | `D5:5-22` |
| D5.2 | `periodicHMinusTwo_fixedVolume_trace_bound` proves the trace estimate whenever `a*N=L`; `..._uniform_in_n` specialises to `N=n+1`, `a=L/(n+1)` | ref | `D5:19-22` |
| D5.3 | `periodicHMinusThreeFixedVolumeFreeFieldProbabilityMeasure_energy_bound`: the bound holds for the actual `H^-3` probability law, not just coordinatewise; proof = finite-source lift measurability + pointwise energy identity + integrate the mapped energy + transfer the trace bound. "No physical total-carrier measurability input is needed for this finite-source law." | ref | `D5:24-30` |
| D5.4 | `periodicHMinusThree_fixedVolume_freeField_tight`: tightness of the whole sequence in `PeriodicHMinusThreeCompletion`, via measurable extended `H^-2` energy + Markov + the Fourier tail estimate + compactness of closures of `H^-2` sublevels | ref | `D5:32-40` |

**Conclusion.** `D5:42-46`: step `D5.4` is "the tightness input used by
`periodicHMinusThree_fixedVolume_prokhorov_subsequence`"; "It is specific to the fixed-volume,
two-dimensional periodic family and does not assert a corresponding interacting-field bound."

**Derivation status.** The constant is *stated* and its construction is delegated to Lean
(`PeriodicHMinusTwoUniformTightness.lean`, `PeriodicFullHMinusTwoTrace.lean`,
`PeriodicHMinusTwoFiniteSourceTrace.lean`). The paper-level text supplies only the sentence "the
separate first term accounts for the zero mode" (`D5:19`) — see §4 item A4 and §7 item R1 for the
GAP on the derivation.

### D6 — `proofs/pphi2_hminus3_prokhorov_weak_convergence.md`

**Purpose.** Instantiate tightness and Prokhorov and assemble whole-sequence weak convergence.

| ID | Statement | Pr | Pointer |
|---|---|---|---|
| D6.1 | Concrete sequence: at index `n` the law is the finite-dimensional Gaussian with covariance `numberedLatticeCovarianceGJ 2 (n+1) (L/(n+1)) mass` pushed forward by `periodicHMinusThreeFiniteSourceFourierLift`; "The physical volume is fixed since `(L/(n+1))*(n+1)=L`" | full | `D6:5-11` |
| D6.2 | Uniform bound on the integral of the extended `H^-2` energy over each law, with the explicit constant | ref (`D5`) | `D6:13-19` |
| D6.3 | Tightness of the whole range of laws; deterministic weight comparison and compact-tail argument proved; closures of `H^-2` sublevels compact in the `H^-3` completion | ref | `D6:20-22` |
| D6.4 | `periodicHMinusThreeCompletion_separable`; Mathlib's Prokhorov theorem applied in `periodicHMinusThree_fixedVolume_prokhorov_subsequence`: from every subsequence a further subsequence converging to a Borel probability measure on the carrier; "No externally supplied separability or tightness field is used in the main theorem" | ref | `D6:24-29` |
| D6.5 | Each finite weighted Fourier cylinder converges to the paired cosine/sine periodic-resolvent Gaussian target; continuous mapping transfers the limits to every extracted weak limit; cylinder sigma-algebra = Borel sigma-algebra; finite-marginal uniqueness identifies every extracted measure with the same `mu_free`; `Filter.tendsto_of_subseq_tendsto` gives convergence of the original sequence | ref | `D6:31-40` |
| D6.6 | The assembled public theorem and its uniqueness companion | ref | `D6:42-47` |

**Conclusion.** `D6:44-47`. **Boundary (quoted).** `D6:51-56`: the separate law built from
`physicalGJMeasure` "still takes `PeriodicHMinusThreeLiftMeasureInput` for measurability and
almost-everywhere representative equality. That conditional bridge is not a premise of the
finite-source weak-convergence theorem and should not be conflated with its sequence of measures."

### D7 — `proofs/pphi2_hminus3_cylinder_borel_uniqueness.md`

**Purpose.** Prove that finite coordinate cylinders determine a Borel probability measure on the
carrier.

| ID | Statement | Pr | Pointer |
|---|---|---|---|
| D7.1 | The coordinate inclusion into the ambient product is measurable, since each coordinate is continuous | ref | `D7:10-11` |
| D7.2 | Finite-coordinate cylinders form a pi-system | ref | `D7:12` |
| D7.3 | Every cylinder is Borel, so the generated cylinder sigma-algebra is contained in the carrier Borel sigma-algebra | ref | `D7:13-14` |
| D7.4 | **Conditional form**: given equality of the generated cylinder sigma-algebra with Borel, finite Borel measures agreeing on all finite cylinders and on the whole space are equal | cond | `D7:15-17` |
| D7.5 | Equality of all finite-coordinate pushforward probability laws implies equality of the measures, under that generation equality | cond | `D7:18-20` |
| D7.6 | The generation equality itself is supplied by `D8` (separability + Polish), so `D7.4`/`D7.5` become unconditional in the assembled theorem | ref | `D7:22-31` |

**Conclusion.** `D7:33-39`. **Boundary (quoted).** `D7:41-43`: "This note does not assert the separate
physical-lattice total-carrier measurability bridge from `PeriodicHMinusThreeFourierMeasure.lean`; that
bridge retains its named `PeriodicHMinusThreeLiftMeasureInput`."

Note the *shape* of `D7.4`: it is a finite-measure extension statement (agreement on a pi-system
generating the sigma-algebra, plus agreement on the total mass seen through the whole space). The
corresponding paper proof is a two-line Dynkin argument; `D7` asserts it as a hypothesis-to-conclusion
implication and does not spell out the Dynkin step.

### D8 — `proofs/pphi2_hminus3_topology_borel_boundary.md`

**Purpose.** Fix the carrier's weight and prove separability, hence Polish, hence cylinder generation.

| ID | Statement | Pr | Pointer |
|---|---|---|---|
| D8.1 | `PeriodicHMinusThreeCompletion` is the weighted Fourier `lp` realisation with `w_3(0)=1`, `w_3(k)=|k|^{-6}`; complete normed space; declared measurable structure definitionally its Borel structure | full (definition) | `D8:5-8` |
| D8.2 | `periodicHMinusThreeCompletion_separable`: finite-coordinate truncations from the span of coordinate vectors are dense; hence Polish | ref | `D8:12-16` |
| D8.3 | The coordinate inclusion into the countable product is continuous and injective, hence a measurable embedding; `periodicHMinusThree_cylinder_sigma_eq_borel_of_polish` proves the reverse inclusion, hence equality of generated cylinder sigma-algebra and Borel sigma-algebra. "Neither countable density nor the reverse cylinder-generation inclusion remains an external input." | ref | `D8:16-20` |

**Conclusion.** `D8:22-27`; boundary `D8:29-31` ("It does not identify that carrier with a separately
defined distribution space or establish results in another dimension").

### D9 — `proofs/pphi2_hminus3_lattice_measure_lift.md`

**Purpose.** Separate the two laws that the corpus keeps apart: the finite-source sequence (used by the
theorem) and the physical total-carrier pushforward (conditional).

| ID | Statement | Pr | Pointer |
|---|---|---|---|
| D9.1 | `periodicHMinusThreeFixedVolumeFreeFieldProbabilityMeasure L mass hL hmass n` is the pushforward of the finite-dimensional Gaussian with covariance `numberedLatticeCovarianceGJ 2 N a mass` (`N=n+1`, `a=L/(n+1)`) under `periodicHMinusThreeFiniteSourceFourierLift`; `periodicHMinusThreeFiniteSourceMeasure` is proved equal to this pushforward; the law is a genuine probability measure for every `n` | ref | `D9:5-25` |

**Conclusion.** `D9:20-25`: uniform `H^-2` energy integral, tightness in the concrete `H^-3` carrier,
marginal convergence — feeding the unconditional theorem.

**Self-reported gap (quoted).** `GAP: D9:27-34` — "`PeriodicHMinusThreeFourierMeasure.lean` also defines a
total representative from `physicalGJMeasure` into the carrier. The definition maps points outside the
raw weighted-series carrier to zero. Constructing its probability-valued map requires
`PeriodicHMinusThreeLiftMeasureInput`, which supplies the named measurability and
almost-everywhere representative-equality facts. Its finite-coordinate identity is proved under that
input." And `D9:36-39`: "The whole-carrier convergence theorem neither assumes nor silently discharges
`PeriodicHMinusThreeLiftMeasureInput`."

### D10 — `proofs/pphi2_full_space_weak_convergence.md`

**Purpose.** The paper-level statement of the assembled theorem plus the six-step proof chain.

| ID | Statement | Pr | Pointer |
|---|---|---|---|
| D10.1 | Sequence definition: index `n` is the pushforward under `periodicHMinusThreeFiniteSourceFourierLift` of `finiteCovarianceGaussianMeasure (numberedLatticeCovarianceGJ 2 (n+1) (L/(n+1)) mass ...)`; `N=n+1`, `a_n=L/(n+1)`, volume exactly `L`; "The target is a probability measure on the concrete weighted `lp` completion, not only a family of compatible finite-dimensional laws" | full | `D10:13-20` |
| D10.2 | Steps 1-6 (energy bound with the explicit trace constant; tightness; separability + Prokhorov; cylinder marginal convergence; transfer to extracted limits + cylinder/Borel equality + finite-marginal identification; whole-sequence convergence via `Filter.tendsto_of_subseq_tendsto`) | full (chain, each step pointing at a named declaration) | `D10:22-29` |
| D10.3 | The canonical `H^{-3}` weight is `1` at the zero mode and `|k|^{-6}` elsewhere; the carrier stores `sqrt(weight) * c_hat(k)` as its `lp` coordinate, and the finite cylinder theorem concerns these stored weighted coordinates | full (definition) | `D10:35` |

**Conclusion.** `D10:3-11` + `D10:29`. **Boundary (quoted).** `D10:31-33`: "The main theorem uses the
finite-source Gaussian laws above. It does not assume `PeriodicHMinusThreeLiftMeasureInput`. That input
belongs to the distinct physical-lattice total-carrier pushforward in
`PeriodicHMinusThreeFourierMeasure.lean` ... The paper's `mu_free` is characterized by the finite
weighted Fourier marginals. No identification with a different distribution-space realization,
interacting-field limit, or Osterwalder–Schrader reconstruction is claimed."

---

## §4 The analytic content a paper must present in full

Q = quoted verbatim from the source; **Status** = whether the document proves it, refers to a
declaration, or leaves it to Lean only.

| # | Item | Exact form | Status | Pointer |
|---|---|---|---|---|
| A1 | Lattice symbol / eigenfunction identity | Q: `Delta_a chi_p=-4 a^{-2}(sum_i sin^2(pi p_i/N)) chi_p`; `lambda_N(p)=m^2+4 a^{-2} sum_i sin^2(pi p_i/N)`; `lambda_N >= m^2 > 0` | proved in text | `D1:9-19`, `D1:25` |
| A2 | Finite Parseval and the only place boundedness enters | Q: `sum_p |F_N(p)|^2 = V a^d sum_x |f(ax)|^2 <= V^2 ||f||_infinity^2` | proved | `D1:37` |
| A3 | Complete-square / resolvent pairing of the lattice covariance | Q: `inner(C_GJ b,C_GJ c)=a^{-d} <b,A_N^{-1}c>_counting`, then with `b_x=a^d f(ax)`: `a^d <f,A_N^{-1}g>` | proved from spectral declarations; the `V^{-1}` rewrite is a named declaration | `D1:41-43` |
| A4 | Exact `H^-2` weight and the uniform trace constant | Q (weight): `periodicHMinusTwoWeight(0)=0`, `= |k|^{-4}` for `k!=0`; Q (constant): `mass^{-2} * L^2 + 2 * mass^{-2} * L^2 * sum_k periodicHMinusTwoWeight k` | value stated, derivation **absent** from the paper-level text (see GAP R1) | `D5:11-19`; `LNPeriodicHMinusTwoWeight.lean:5-6`; `LNPeriodicNegativeSobolevTopologyInterfaces.lean:7-21`; `LNPeriodicHMinusTwoUniformTightness.lean:10-16` |
| A5 | The `H^-3` weight and the stored `lp` coordinate | Q: `w_3(0)=1`, `w_3(k)=|k|^{-6}`; "The carrier stores `sqrt(weight) * c_hat(k)` as its `lp` coordinate" | stated | `D8:5-8`, `D10:35`; `LNPeriodicNegativeSobolevCarriers.lean:5-6`; `LNPeriodicHMinusThreeCompletion.lean:18` |
| A6 | Fixed-mode Riemann-sum convergence (no hidden Riemann hypothesis) | Q: `|F_N(p_N(k))-F(k)| <= V omega_k(a) -> 0`, "boundedness alone would not suffice, whereas continuity on the compact cell supplies `omega_k(a)->0`" | proved (Lean: `PhysicalCellRiemann.lean` retagging, `ContinuousOn.hasBoxIntegral`) | `D1:45-51`, `D1:59` |
| A7 | Sinc/dispersion limit | Q: `4(N/L)^2 sin^2(pi k_i/N) -> (2 pi k_i/L)^2`; `lambda(k)=m^2+(2 pi/L)^2 sum_i k_i^2` | proved | `D1:53-57`, `D1:17` |
| A8 | Uniform denominator bound and discrete tail | Q: `lambda_N(k)>=m^2+16 |k|_infinity^2/L^2` with `R_K=m^2+16 K^2/L^2` and `|Q_N-Q_{N,K}| <= V ||f||_infinity ||g||_infinity / R_K` | proved; the constant `16` comes from `sin t >= 2t/pi` on `[0,pi/2]` | `D1:65-80` |
| A9 | Continuum tail | Q: `lambda(k)>=D_K := m^2+(2 pi/L)^2 (K+1)^2`; `|Q-Q_K| <= V ||f||_infinity ||g||_infinity / D_K -> 0`; "`4 pi^2>16` also gives the weaker bound with `R_K`" | proved | `D1:97-105` |
| A10 | Eventual-in-`N` Bessel bound (aliasing caveat) | Q: `sum_{k in S_K} |F_N(p_N(k))|^2 <= V^2 ||f||_infinity^2`, "This bound is eventual in `N`; asserting it for every `N` would be false because small grids alias several integer modes onto the same residue" | proved | `D1:82-88` |
| A11 | Absolute summability of the Green series | Q: `|conj(F(k)) G(k)/lambda(k)| <= (|F(k)|^2+|G(k)|^2)/m^2` | proved (Young) | `D1:90-93` |
| A12 | Smooth-test summable envelope (the only modewise uniform majorant) | Q: `|F_N(k)| <= V (L/4)^r D_r(f) q^{-r}` and `V^{-1} |conj(F_N(k)) G_N(k)/lambda_N(k)| <= V L^2/16 * (L/4)^{2r} D_r(f)D_r(g) q^{-2r-2}` with shell count `(2q+1)^d-(2q-1)^d <= 2d(2q+1)^{d-1}` and `2r+2>d` | proved | `D1:109-123` |
| A13 | Energy identity `(E)` for the continuum target | Q: `<h,v>_H = m^2 <jh,jv>_E + sum_i <D_i h,D_i v>_E`; `||h||_H^2=m^2||jh||_E^2+sum_i||D_i h||_E^2` | proved (mixed sesquilinear form, not just the diagonal) | `D1:138-142` |
| A14 | Graph completion `(H1)` | Q: `{ (jh,(D_i h)_i) : h in H } = closure(G_0)` with `G_0 = { (P_a,(partial_(x_i) P_a)_i) : a has finite support }` | proved | `D1:152-160` |
| A15 | Weak resolvent, uniqueness, norm bound | Q: `(W)` `m^2 <Rg,jv>_E + sum_i <D_i h_g,D_i v>_E = <g,jv>_E` for all `v in H`; `||Rg||_E<=m^(-2)||g||_E` | proved | `D1:162-175` |
| A16 | Fourier coefficient formula for the independent solver | Q: `B(Rg)(k)=lambda(k)^(-1) Bg(k)`, `<f,Rg>_E=sum_k conjugate(Bf(k)) Bg(k)/lambda(k)` | proved | `D1:179-182` |
| A17 | **Haar ↔ physical Lebesgue normalisation** | Q: `Bf_L(k) = integral_(0,1]^d f(Lz) exp(-2 pi i k.z) dz = L^(-d) integral_[0,L]^d f(x) exp(-2 pi i k.x/L) dx = V^(-1) F(k)` | proved; Lean bridge `physicalTorusTestL2_repr` with right side `(L : C)^(-1)^d * torusFourierCoefficient` | `D1:186-192` |
| A18 | The identification `(Q=R)` | Q: `V <f_L,Rg_L>_E = V sum_k conj(V^(-1)F(k)) V^(-1)G(k)/lambda(k) = V^(-1) sum_k conj(F(k))G(k)/lambda(k) = Q(f,g)` | proved; "the existing Fourier Green pairing has exactly the physical factor `L^(-d)`" | `D1:194-201` |
| A19 | epsilson/3 assembly | Q: `|Re Q_N(f,g) - Re Q(f,g)| <= |Re Q_N - Re Q_{N,K}| + |Re Q_{N,K} - Re Q_K| + |Re Q_K - Re Q| < epsilon` | proved; "No caller supplies summability, a tail estimate, or convergence" | `D1:203-211` |
| A20 | Tightness mechanism | Markov on the extended `H^-2` energy with cutoff `C/ε + 1`, plus compactness of `H^-2` sublevel closures in the `H^-3` completion | proved in Lean; paper text summarizes | `D5:32-40`; `LNPeriodicHMinusTwoUniformTightness.lean:235-296` |
| A21 | Zero-mode handling (two different devices) | (i) trace bound: weight `0` at `k=0` and a separate first term `mass^{-2}L^2`; (ii) energy on `H^-3` points: `periodicHMinusTwoEnergyOnHMinusThree` uses `periodicHMinusTwoFullWeight` (=`1` at `0`) so that sublevel sets are *compact*, and the *norm* is also defined with the full weight | stated; consequence "The zero mode is included because `periodicHMinusTwoFullWeight 0 = 1`" | `D5:11-19`; `LNPeriodicHMinusTwoWeight.lean:22-23`; `LNPeriodicNegativeSobolevTopologyInterfaces.lean:12-21`; `LNPeriodicHMinusTwoUniformTightness.lean:10-16` |

Items the brief anticipates that are **not** in this corpus, with the honest status:

| Item | Status |
|---|---|
| Lattice Green function / resolvent *kernel* in closed form | **Absent.** The corpus never writes `G_a(x-y)`; everything is done in the symbol/Fourier domain (`D1:16-19`, `D1:127-133`). No lattice Bessel function, no `K_0`, no `1/(2π)` or `1/(4π)` occurs anywhere in `D1`–`D10` (grep for `4 ?pi`, `2 ?pi`, `K_0`, `Bessel function`: the only hits are the torus phases `2 pi k.x/L`, the symbol `(2 pi/L)^2`, and the *Bessel inequality*, `D1:82`). |
| Log-divergence / large-mass asymptotics | **Absent from `D1`–`D10`.** The only 2-D continuum kernel identity `C_m(x)=(2π)^{-1}K_0(m|x|)` with `K_0(z)=−log(z/2)−γ+O(z²log z)` lives in `proofs/pphi2_free_field_2d.md:41-57` (Definition 1.1, Prop. 1.2, Prop. 1.4, Prop. 1.5), which **no `D1`–`D10` document cites**. A paper that wants those constants must import them explicitly from that file (which itself states at `:190-194` that its Bessel asymptotics are "standard special-function facts" checked numerically only). |
| Compact-embedding / tail estimate | Present in the *sequence* form: `D1:97-105` (continuum tail) and `D5:32-40` + `LN:235-296` (sublevel compactness); no Sobolev-embedding theorem is used or needed, and `D2:53` notes that finite-frequency tail compactness is "retained as an explicit input" at the interface level. |
| Literature constants | None are quoted from literature in `D1`–`D10`; see §6. |

---

## §5 Conventions and traps

| # | Trap | What the sources actually do | Pointer |
|---|---|---|---|
| T1 | Real vs complex Fourier series | Two different normalisations coexist. The lattice/continuum series uses **integral-normalised** coefficients with *no* `1/V` (`F_N(p)=a^d sum_x f(ax) chi_{-p}(x)`, `F(k)=int_[0,L]^d f e^{-2 pi i k.x/L}`) and puts the `V^{-1}` in the *pairing* `Q`. The Haar side uses the **orthonormal** basis `b_k(z)=exp(2 pi i k.z)` on the probability torus, whose coefficient is `V^{-1}F(k)`. Mixing these is the single easiest way to lose a factor `L^d`. | `D1:11-19`, `D1:131`, `D1:186-192` |
| T2 | Sign and symbol of the resolvent | `A_N = m^2 - Delta_a` (a *positive* operator), symbol `lambda_N = m^2 + 4a^{-2}sum sin^2 >= m^2`; the continuum symbol is `lambda(k)=m^2+(2 pi/L)^2 sum_i k_i^2` with `omega_i(k)=2 pi k_i/L`. The resolvent is `(m^2 - Delta_T)^{-1}`; its Green pairing carries `+1/lambda`, never a sign, and never a `-Delta` alone (the mass is what makes `lambda >= m^2` and hence every tail bound uniform). | `D1:9`, `D1:16-19`, `D1:133`, `D1:175` |
| T3 | Which exponent is the carrier, which is the ambient | **`H^{-2}` is the energy/carrier structure and `H^{-3}` is the ambient topology in which weak convergence is asserted.** `H^-2` carries the bounded-energy/tightness; `H^-3` is strictly weaker so that `H^-2`-bounded sets have `H^-3`-small tails. The general rule is `s > (d-2)/2` for second-moment summability plus `r > s` for compactness; `(s,r)=(2,3)` in `d=2`. Do not write "the carrier is `H^-3`" without saying that the *measured* structure is `H^-2`. | `D2:44-77`; `D8:5-8`; `D5:32-40` |
| T4 | The weight is a *seminorm* weight at `k=0`, and two weights exist | `periodicHMinusTwoWeight(0)=0` (so `sum_k w_2 |c_k|^2` is not a norm); `periodicHMinusTwoFullWeight(0)=1` (the honest norm/energy). The tightness energy and the norm both use the **full** weight; the trace constant's first term is the zero-mode contribution added back separately. `periodicHMinusThreeWeight(0)=1` too. | `LNPeriodicHMinusTwoWeight.lean:5-6,22-23`; `LNPeriodicNegativeSobolevTopologyInterfaces.lean:7-21`; `LNPeriodicHMinusTwoUniformTightness.lean:10-16`; `D5:11-19` |
| T5 | The `lp` coordinate is *not* the Fourier coefficient | The carrier stores `sqrt(weight)*c_hat(k)`; the *distribution* coefficients are recovered by dividing by `sqrt(weight)` (`periodicHMinusThreeDistributionCoefficients`). Any energy/moment computation on a carrier point must undo the weight first. | `D10:35`; `LNPeriodicHMinusTwoUniformTightness.lean:12-16,84-100` |
| T6 | `‖k‖` is the **sup norm** on `Fin 2 → ℤ`, not the Euclidean norm | The Lean weights are `‖k‖ ^ (-4)` / `‖k‖ ^ (-6)` on `k : Fin 2 → ℤ`, i.e. `(max_i |k_i|)^{-4}` / `^{-6}`, whereas the *continuum* symbol uses the Euclidean `sum_i k_i^2`. Both give the same convergence thresholds in `d=2`, but the two must not be silently interchanged in a paper, and the covariance document itself switches to the explicit `|k|_infinity` notation for its bounds. | `LNPeriodicHMinusTwoWeight.lean:5-6`; `LNPeriodicNegativeSobolevCarriers.lean:5-6`; `D1:65-71`, `D1:97-99`, `D1:114` |
| T7 | Three different notations for the same carrier | `lp ((Fin 2 → ℤ) → ℂ) 2` (`TG:4112`, `SB:8`), `lp (Fin 2 → ℤ → ℂ) 2` (`D4:65-66`, curried), `lp (fun _ : PeriodicFourierIndex => Complex) 2` (`D7:7`). They denote one object; a paper must fix one notation and say that `Fin 2 → ℤ → ℂ` is the curried form. | `TG:4112`; `SB:8`; `D4:65-66`; `D7:7` |
| T8 | `lp`-summability, i.e. what "square-summable" means here | Membership is `sum_k w(k) |c_k|^2 < infinity` for the relevant weight, with the summability of the *weight itself* proved from Mathlib's Eisenstein-series lemma `summable_one_div_norm_rpow` (`2<4` resp. `2<6`). No `l^2` of the *unweighted* coefficients is asserted anywhere — in `d=2` the unweighted series diverges (the field is a distribution, not an `L^2` function). | `LNPeriodicHMinusTwoWeight.lean:15-21`; `LNPeriodicNegativeSobolevCarriers.lean:15-30`; `D2:67-71` |
| T9 | Topology used for weak convergence | Weak convergence of **Borel probability measures on the Polish space** `PeriodicHMinusThreeCompletion` (separability from finite-coordinate truncations, completeness inherited from `lp`), i.e. `mu_n => mu` against bounded continuous functions; the operational criterion actually used is convergence of **finite weighted Fourier-coordinate (cylinder) marginals** plus cylinder $\Rightarrow$ Borel. No weak-* topology on a dual, no Prokhorov metric, no test-function topology on `C^\infty` is used. | `D8:10-20`; `D6:24-29`; `D7:10-20`; `D10:24-29` |
| T10 | Measurability convention | The carrier subtype's *inherited* measurable space is used and is definitionally its Borel structure (`D8:6-8`); `PeriodicHMinusTwoSpace` is an `abbrev` precisely so that the inherited instance is available to `Measure.map` (`D2:34-40`). The finite-source lift's measurability is proved (`D4:81-83`); the *total* carrier representative's is not, and is the content of `PeriodicHMinusThreeLiftMeasureInput` (`D9:29-34`). Two named inputs must be kept apart: `PeriodicHMinusThreeLiftMeasureInput` (physical total carrier) and the older `PeriodicHMinusTwoDiscreteLiftInput` / `PeriodicHMinusTwoLiftInput` (`D2:120-132`), plus the retired `PeriodicHMinusThreeLpCompactnessInput` (`D5:40`) and `PeriodicFullSpaceWeakConvergenceInput` (`D4:119`). | as cited |
| T11 | `a^{-d/2}` vs `a^{d/2}`: which covariance normalisation is being limited | The corpus never rescales the field. The lattice covariance is used in the **Glimm–Jaffe ("GJ") normalisation** through `numberedLatticeCovarianceGJ` and the identity `inner(C_GJ b, C_GJ c)=a^{-d}<b,A_N^{-1}c>_counting` — i.e. the `a^{-d}` sits in the *pairing form*, and the sampled vectors are `b_x=a^d f(ax)` (`D1:41-43`). Nothing anywhere multiplies the field by `a^{-d/2}` or `a^{d/2}`; the `a`-dependence is absorbed by the fixed-volume constraint `aN=L` (`D6:5-11`, `D10:20`). A paper that introduces the standard `a^{-d/2}` field rescaling must show it cancels. | `D1:41-43`; `D6:10-11`; `D10:20` |
| T12 | Which measure is being pushed forward | Two families exist and only one is used by the theorem: (i) the **finite-source** Fourier lift of the lattice Gaussian (used, `D9:5-25`, `D10:13-20`); (ii) the **total carrier representative of `physicalGJMeasure`**, which needs the named input (`D9:27-34`, `D6:49-56`). The scope sentence's phrase "agrees pointwise with the total H^-3 carrier representative on embedded finite lattice configurations" (`SB:9-10`) is the only bridge between them and is *weaker* than an identity of laws. | `SB:9-10`; `D9:27-39` |
| T13 | The `N=n+1` index convention and `n : ℕ` vs `N : ℕ` | The Lean statements are indexed by `n` with `N=n+1` and `a=L/(n+1)`; the math text of `D1` uses `N` directly (`N->infinity`). The paper should pick one; `D10:13-20` and `D6:5-11` state the dictionary explicitly. | `D10:13-20`; `D6:5-11`; `D1:7` |
| T14 | Dimension | Everything numeric is `d=2` (`Fin 2 → ℤ`); `D1` is written for general `d>=1` and its Lean support explicitly includes `d=0` and `K=0` (`D1:61`). The paper must not present the `d=2` weight exponents as general, and `D2:74-77` notes the `d=4` variant without proving it. | `D1:61`, `D2:6-8`, `D2:74-77` |

---

## §6 Boundary and literature position

### 6.1 What the sources exclude (verbatim `not_included`)

From `SA:18-22`:

> - "No equivalence with a pre-existing distribution-defined Sobolev type or strong unbounded Laplacian
>   domain theorem is asserted." — basis comment: `proofs/pphi2_fixed_volume_fourier_covariance.md:160`.
> - "No limiting probability measure, interacting ultraviolet limit, or OS reconstruction is constructed
>   by this tested-covariance theorem." — basis comment:
>   `proofs/pphi2_fixed_volume_fourier_covariance.md:254`.

From `SB:16-21`:

> - "No equivalence with a pre-existing distribution-defined Sobolev space or strong unbounded Laplacian
>   domain theorem is asserted."
> - "The separate identity theorem for the abstract physicalGJ pushforward
>   `periodicHMinusThreeLatticeMeasure` remains conditional on `PeriodicHMinusThreeLiftMeasureInput`;
>   this condition is not a premise of the fixed-volume Fourier-pushforward convergence theorem." —
>   basis comment quotes `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicHMinusThreeFourierMeasure.lean:436-452`.
> - "No interacting ultraviolet limit or Osterwalder–Schrader reconstruction is proved by this
>   free-field measure limit." — basis comment quotes `proofs/pphi2_exponential_clustering.md:95-102`.

The same three exclusions are restated inside the proof documents at `D1:160`, `D1:254`, `D10:31-33`,
`D8:29-31`, `D2:195`, `D5:44-46`.

OS reconstruction, in the source's own words (`proofs/pphi2_exponential_clustering.md:95-102`): the
residual is `RECONSTRUCTION` / `OS_RECONSTRUCTION` — "Osterwalder–Schrader 重构定理本体", registered in
`A_FS4D.A_PHY_mass1` with `mathematical_status: LITERATURE_ONLY`, `lean_status: IMPORTED_UPSTREAM`; the
upstream formalisation is reported as carrying "1 条具名 `axiom` + 83 个 `sorry`" so that "`lean`
证据既不足以支撑 `FORMALIZED` 也不足以支撑 FUEA". This is a *boundary report*, not mathematics used
in the proof chain.

### 6.2 Every literature / external item the documents actually cite

The ten primary documents cite **no author–year reference at all**. Their entire external dependency is
the following, and the list is complete (greps for author names of the constructive-QFT literature
returned zero hits in `D1`–`D10`):

| Item | What exactly is borrowed | Where cited |
|---|---|---|
| **Mathlib** — multivariate torus Fourier basis | The complete orthonormal basis `b_k(z)=exp(2 pi i k.z)` of the probability-Haar `L2` space is a theorem about the actual space, not an assumed basis | `D1:131` |
| **Mathlib** — Prokhorov's theorem | Extraction of a weakly convergent subsequence from a tight sequence of Borel probability measures on a Polish space | `D6:24-29` |
| **Mathlib** — `EisensteinSeries.summable_one_div_norm_rpow` | Summability of `sum_k |k|^{-4}` and `sum_k |k|^{-6}` on `Z^2` (used for both weights) | `LNPeriodicHMinusTwoWeight.lean:15-21`; `LNPeriodicNegativeSobolevCarriers.lean:15-30` |
| **Mathlib** — `Filter.tendsto_of_subseq_tendsto` | "every subsequence has a further subsequence converging to the same limit" implies whole-sequence convergence | `D10:29`, `D6:38-39` |
| **Mathlib** — Henstock/box-integral machinery (`ContinuousOn.hasBoxIntegral`, unit partition at lower vertices) | The physical-cell Riemann sum convergence, retagged to Lebesgue volume | `D1:59` |
| Elementary analysis, used without attribution | Euler's formula; `sin t/t -> 1`; concavity/chord bound `sin t >= 2t/pi` on `[0,pi/2]`; `4 pi^2 > 16`; Cauchy–Schwarz; Young's inequality; Parseval; Markov's inequality; Riesz representation; iterated fundamental theorem of calculus and periodic integration by parts; pi-system/Dynkin extension; finite-dimensional Gaussian existence | `D1:25`, `D1:53`, `D1:69`, `D1:105`, `D1:73`,`D1:97`, `D1:90`, `D1:35`, `D5:36`, `D1:167`, `D1:114`, `D7:12-20`, `D3:76-94` |

Two labels deserve an explicit warning for the paper.

- **"GJ" in `numberedLatticeCovarianceGJ` / `C_GJ` / `GJFactor`.** The identifier carries the
  Glimm–Jaffe lattice normalisation, but **no document in the corpus cites Glimm–Jaffe**, and nothing in
  `D1`–`D10` is taken from that book. The covariance is *used* as an input object (`D1:41-43`) and its
  two properties used downstream are the exact zero mean (`D1:226`) and the inverse-mass identity
  (`D1:41`). Do not manufacture a Glimm–Jaffe citation on the strength of the name.
- **"Bessel" in `D1:82`, `D1:90`.** This is the Bessel *inequality* (`sum_{k in S}|F(k)|^2 <= V^2||f||^2`),
  proved from finite Parseval — explicitly "no continuous Bessel theorem or Fourier completeness is
  assumed" (`D1:90`). It is not the Bessel *function*; see §4.

If the paper wants the 2-D kernel constants `C_m(x)=K_0(m|x|)/(2π)` and the small-distance expansion
`K_0(z)=-log(z/2)-γ+O(z^2 log z)`, those appear only in `proofs/pphi2_free_field_2d.md:41-57` (Def. 1.1,
Prop. 1.2, 1.3, 1.4, 1.5), where they are labelled "标准特殊函数事实" and checked numerically rather
than proved (`pphi2_free_field_2d.md:190-194`). They should be cited to that file, or to a standard
special-functions reference chosen by the authors — not to any of `D1`–`D10`.

---

## §7 Open / weak points, ranked

Ranked by how much damage a hostile referee can do with the pointer given. `GAP:` items are the seven
substantive ones; the rest are robustness/derivation items that a referee will raise but that do not
break the theorem as stated.

**GAP R1 — the exact trace constant is stated but never derived anywhere at paper level.**
`D5:11-19` gives
`C = mass^{-2} * L^2 + 2 * mass^{-2} * L^2 * sum_k periodicHMinusTwoWeight k` and explains the first term
only as "the separate first term accounts for the zero mode". Missing: (i) the per-mode first-moment
computation (`E|probe_k|^2 <= 2 mass^{-2} L^2`, i.e. two real coordinates each of variance `<= V m^{-2}`
because `lambda >= m^2`), (ii) the exact zero-mode value `V/m^2 = L^2/m^2` (which is `Q_N(1,1)` from
`D1:18-19` with `F_N(0)=V`), (iii) the boundedness/summability of `sum_k w_2(k)` (it is a concrete
constant, `sum_{k != 0 in Z^2} |k|^{-4}`), (iv) why the factor `2` is present. All four are in Lean
(`LNPeriodicFullHMinusTwoTrace.lean:41`, `LNPeriodicHMinusTwoUniformTightness.lean:10-16`) and none is in
the prose. Pointer for the gap: `D5:11-19`.

**GAP R2 — the passage from the proved covariance limit to `hC` (the "paired cosine/sine
periodic-resolvent covariance matrix" identification) is not exhibited.**
`D4:29-44` requires two hypotheses; `[P8]`/`D1:214-232` delivers the *real* pairing limit
`Re Q(f,g) = Re(V<f_L,Rg_L>_E)`. The statement that the covariance matrix of the paired cosine/sine
family equals `periodicResolventCovarianceMatrix` built from `physicalTorusResolventPairing`
(`D3:76-82`) is asserted as available at `D4:43-44` and `D3:76-82`, but no document *derives* the
entry-by-entry identification from `(Q=R)`; a paper must add the short computation (each real probe is a
cosine/sine test, so the entries are `Re Q(cos_k,cos_l)`, `Re Q(cos_k,sin_l)`, ...). Pointers:
`D4:42-44`; `D3:76-82`; `D1:194-201`.

**GAP R3 — the physical-lattice total-carrier bridge is open, and it is the difference between "a
sequence of Fourier pushforwards converges" and "the lattice field laws converge".**
`D9:27-34`, `D2:120-145`, `SB:18-19`. What is missing is precisely: measurability of the total
carrier-valued representative of `physicalGJMeasure`, and a.e. equality of its weighted coefficients with
the raw weighted Fourier coefficients — plus the one-line monotone-limit bridge that `D2:147-173`
specifies but does not prove. The three-lift chain that a paper must draw carefully is
`physicalGJMeasure` → total carrier representative (open) versus lattice Gaussian → finite-source Fourier
lift (proved), with only "pointwise on embedded finite lattice configurations" (`SB:9-10`) connecting
them.

**GAP R4 — no covariance *operator* on the carrier, and no theorem that `mu_free` is Gaussian.**
The corpus proves that every finite weighted Fourier marginal of `mu_free` is the paired cosine/sine
Gaussian with resolvent covariance (`D10:8-11`, `D4:46-50`), and that the marginals determine `mu_free`
(`D7:18-20`, `D8:16-20`). It never states the consequence " `mu_free` is the centred Gaussian measure on
the carrier with covariance operator `(m^2-Delta_T)^{-1}` " as a theorem, and it never constructs that
operator on `H^{-3}`: `R` is constructed on the *unit-torus* `L2` space `E` only (`D1:162-175`), and the
only carrier-level object is the series pairing (`D1:99-103`). A paper that writes "the free Gaussian
measure on `H^{-3}`" must either prove the Gaussianity statement from the marginal theorems (it is true,
by cylinder determination) or phrase the theorem purely in terms of marginals as the sources do.

**GAP R5 — `D1` contradicts itself about whether the resolvent identification is done.**
`D1:251` and `D1:232` report `torusFourierGreenPairing_eq_physicalTorusResolventPairing` and the three
consumers as *in the verified root build*; `D1:61` and `D1:258-260` say the resolvent identification and
the series-pairing identification "remain obligations" (the latter describing the *interface field*
`target_green` of a conditional theorem, and `D1:256` labelling that paragraph "Previously verified ...").
Both statements are in the file; a referee reading `D1:260` will conclude the paper's central
identification is unproved. The paper must quote `D1:232`/`D1:251` (post-identification) and must not
quote `D1:260` without the `D1:256` label.

**GAP R6 — `D4` and `D5`/`D6`/`D8` disagree about what is still a named input.**
`D4:116-120` says full-space tightness, Borel generation and cylinder uniqueness "remain named inputs"
(`PeriodicFullSpaceWeakConvergenceInput`); `D5:38-40` says the compact-tail/weight comparison is "not left
as the old ... assumption", and `D6:24-29`, `D8:16-20` report those steps as theorems. Report both; the
resolution is that `D4` describes its own module's consumer interface while `D5`–`D8` describe the
assembled theorem's modules, and the assembled statement (`D10:3-11`) carries no packed input. A paper
must cite `D10`, not `D4:119`.

**GAP R7 — the tightness is first-moment only, so no rate, no exponential tail and no quantitative modulus
can be claimed.**
`LNPeriodicHMinusTwoUniformTightness.lean:235-237` states the mechanism ("The cutoff is `C / ε + 1`, so
the Markov tail is strictly smaller than `ε`") and `D5:32-40` lists the ingredients: Markov, no exponential
moment, no layer-cake. This is *sufficient* for Prokhorov and therefore not a defect in the theorem, but
any paper sentence of the form "quantitative tightness", "with rate", or "exponentially tight" would be
unsupported. Pointers: `D5:32-40`; `LNPeriodicHMinusTwoUniformTightness.lean:235-296`.

The remaining items are weaker and are listed for completeness, without `GAP:` marking:

| Rank | Issue | Pointer |
|---|---|---|
| R8 | `D1` proves the covariance limit for `C_b(T_L^d)`-periodic tests only, and says a common modewise summable envelope exists only after restricting to `C^{d+1}` (`r=d+1`) tests; the summable-envelope statement must not be presented as holding for all continuous tests | `D1:105`, `D1:109-123` |
| R9 | `D1:82-88`'s Bessel bound is **eventual in `N`** (`N>2K`) and would be false for all `N` by aliasing; a paper that writes "for all `N`" is wrong | `D1:86-87` |
| R10 | `D2`'s general `H^{-s}` rule is proved only by the `d=2` instance; the `d=4` sentence is a remark | `D2:64-77`, `D2:106-108` |
| R11 | `D3` (abstract Gaussian series) is in the corpus but off-graph: presenting it as part of the proof chain would overstate the dependence structure | `D3:55-65`, `D3:96-99` |
| R12 | `D2` opens with a `> status:` metadata line and `D8`/`D9` do not; the corpus is heterogeneous in format — irrelevant mathematically, but the paper's citation apparatus should cite files, not front-matter state | `D2:2` |
| R13 | The paper must state the dimension restriction honestly: the carrier, weights and theorem are `d=2`; `D1`'s `d`-general prose is supported by Lean only for the finite/Fourier layer, with `d=0` included and `d=4` excluded from the scope | `D1:7`, `D1:61`, `D2:6-8`, `SB:5` |
