# Lean declaration ledger — fixed-physical-volume periodic free-field weak limit

> status: ACTIVE · owner: PPHI2_FIXED_VOLUME_FREE_FIELD_MEASURE_LIMIT · asof: 2026-11-02

WORK-PRODUCT note for `paper/PPHI2_FIXED_VOLUME_COMPLETE`. It reports what the Lean sources
literally contain and nothing else: no status token is asserted or re-adjudicated here, and no
graph, log, runtime index, node, frontend or `.lean` file was touched. Every factual claim carries a
`path:line` pointer resolved against `E:\study\AImath`; where the files do not decide a question the
text says `UNVERIFIED`. Pointer convention: `path:line` is one line, `path:lines A-B` a range.

Scope objects: node keys `PPHI2_FIXED_VOLUME_COVARIANCE_LIMIT` and
`PPHI2_FIXED_VOLUME_FREE_FIELD_MEASURE_LIMIT`; registered contracts in
`formal/lean/challenges/_registry.yaml:22-56`; honest boundaries in
`proof_graph/scopes/PPHI2_FIXED_VOLUME_COVARIANCE_LIMIT.yaml:1-36` and
`proof_graph/scopes/PPHI2_FIXED_VOLUME_FREE_FIELD_MEASURE_LIMIT.yaml:1-40`. Sources:
`formal/lean/s6/pphi2_clean/AImathPPhi2Clean/*.lean` (89 modules, 13437 lines, `§6`) plus
`formal/lean/s6/pphi2_clean/audit/*.lean` (132 probe files, 1292 lines, `§6`).

---

## §1 Module inventory

The 25 modules below are the ones that carry the two statements. "Entry point" = the module a reader
should open first for that layer. Line counts and the membership claim for the untabulated remainder
are computed by the commands in `§6`.

| # | module | file | lines | role |
|---|---|---|---|---|
| **a** | | **periodic torus L²/H¹ and the discrete operator** | | entry point: `PeriodicTorusH1` |
| a1 | `PeriodicTorusH1` | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicTorusH1.lean` | 242 | Periodic H¹ as the closed value-gradient graph completion of unweighted trigonometric polynomials, plus the Riesz weak resolvent `periodicMassiveResolvent`. |
| a2 | `ConcreteLatticeOperator` | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/ConcreteLatticeOperator.lean` | 523 | The finite periodic lattice `Fin d → ZMod N`, its discrete Laplacian with spacing `a`, the mass operator `Q = -Δ_a + m²`, and `Q`'s Hermitian matrix with eigenbasis `massEigenvalues`/`massEigenvectorBasis`. |
| a3 | `PeriodicFourierLaplacian` | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicFourierLaplacian.lean` | 335 | Finite complex characters on `(ℤ/Nℤ)^d`, character orthogonality for composite `N`, finite Fourier inversion and Parseval, and the finite-difference eigenvalue symbol. |
| **b** | | **massive resolvent / energy solver and covariance** | | entry point: `PeriodicFourierCovarianceLimit` |
| b1 | `PeriodicTorusResolventLimit` | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicTorusResolventLimit.lean` | 114 | Physical-volume pairing against the independently constructed weak resolvent, its Parseval identification with the Fourier Green series, and the three covariance limits restated with the resolvent as target. |
| b2 | `PeriodicFourierCovarianceLimit` | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicFourierCovarianceLimit.lean` | 1509 | Sampled and continuum Fourier coefficients, mass symbols, the finite and continuum Green pairings, the uniform-in-`N` cutoff tail, and the three registered covariance-limit theorems. |
| **c** | | **physical lattice sampling and the Gaussian law** | | entry point: `PhysicalLatticeGaussianLaw` |
| c1 | `PhysicalLatticeSampling` | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PhysicalLatticeSampling.lean` | 81 | Physical site coordinates, the `a^d`-weighted Riemann evaluation of a test, and `physicalGJMeasure` as the pushforward of the finite Gaussian law. |
| c2 | `RealLatticeSpectralCovariance` | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/RealLatticeSpectralCovariance.lean` | 132 | The finite-dimensional spectral `Q^{-1/2}` covariance and its GJ rescaling `(√(a^d))⁻¹ • ·`. |
| c3 | `ConcreteLatticeCovariance` | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/ConcreteLatticeCovariance.lean` | 132 | The GJ-normalized lattice covariance and the exact identity `⟨T f, T g⟩ = a^{-d} Σ_x f(x) (Q^{-1} g)(x)`. |
| c4 | `NumberedLatticeGaussianMoment` | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/NumberedLatticeGaussianMoment.lean` | 65 | Transport of the lattice covariance along a numbering of sites, and the exact spectral second moment under the numbered finite Gaussian law. |
| c5 | `PhysicalLatticeGaussianLaw` | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PhysicalLatticeGaussianLaw.lean` | 490 | Zero mean, characteristic function, Gaussian law of every one-dimensional marginal, the mixed-moment identity, and the covariance-to-weak convergence transfer. |
| **d** | | **negative-Sobolev carriers, topology and Borel structure** | | entry points: `PeriodicHMinusThreeCompletion` (definitions), `PeriodicHMinusThreeTopologyBorel` (topology) |
| d1 | `PeriodicHMinusTwoWeight` | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicHMinusTwoWeight.lean` | 52 | The `H^{-2}` weights (two variants with different zero modes) and `periodicHMinusTwoCarrier`. |
| d2 | `PeriodicNegativeSobolevCarriers` | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicNegativeSobolevCarriers.lean` | 42 | The `H^{-3}` weight and `periodicHMinusThreeCarrier`. |
| d3 | `PeriodicHMinusThreeCompletion` | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicHMinusThreeCompletion.lean` | 70 | The Fourier index type, the concrete `lp` completion, the weight/deweight maps, the finite cylinder projection and its Borel instance. |
| d4 | `PeriodicNegativeSobolevTopologyInterfaces` | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicNegativeSobolevTopologyInterfaces.lean` | 452 | `H^{-2}`/`H^{-3}` norms, the compact-tail comparison, the embedding of `H^{-2}` coefficients into the completion, and compactness of the closed `H^{-2}` ball. |
| d5 | `PeriodicHMinusThreeTopologyBorel` | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicHMinusThreeTopologyBorel.lean` | 145 | Coordinate embedding, second countability, Polish/Separable space, cylinder `σ`-algebra equals Borel, and concrete separability of the carrier. |
| **e** | | **uniform `H^{-2}` moment and `H^{-3}` tightness** | | entry point: `PeriodicHMinusThreeFixedVolumeTightness` |
| e1 | `PeriodicHMinusTwoFiniteSourceTrace` | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicHMinusTwoFiniteSourceTrace.lean` | 379 | Integrability of the squared `H^{-2}` norm under the finite Gaussian source, its full trace, and the `n`-uniform moment bound for the carrier lift. |
| e2 | `PeriodicHMinusTwoUniformTightness` | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicHMinusTwoUniformTightness.lean` | 333 | The extended `H^{-2}` energy on the completion, compactness of its closed sublevel sets, the Markov tail, and the abstract uniform-moment-implies-tight lemma. |
| e3 | `PeriodicHMinusThreeFixedVolumeTightness` | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicHMinusThreeFixedVolumeTightness.lean` | 249 | The actual fixed-volume probability-measure sequence (pushforward of the finite Gaussian law), its energy bound, and tightness in `H^{-3}`. |
| **f** | | **finite real families: characteristic functions and covariance convergence** | | entry point: `FiniteRealFamilyWeakLimitInterface` |
| f1 | `FiniteRealFamilyWeakLimitInterface` | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/FiniteRealFamilyWeakLimitInterface.lean` | 884 | The periodic resolvent covariance matrix, its positive semidefiniteness and Gram factor, the canonical target Gaussian, and the unconditional finite-family weak-convergence theorem. |
| f2 | `FiniteFourierCoordinateConvergence` | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/FiniteFourierCoordinateConvergence.lean` | 123 | The wrapper that feeds concrete covariance limits into that theorem for an arbitrary indexed finite test family. |
| **g** | | **cylinder convergence** | | entry point: `PeriodicHMinusThreeCylinderConvergence` |
| g1 | `PeriodicHMinusThreeFourierMeasure` | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicHMinusThreeFourierMeasure.lean` | 488 | All lift maps: raw weighted lift, total carrier lift, per-site vectors, the finite-source lift, the named measurability input, and the finite-source probability measure. |
| g2 | `PeriodicHMinusThreeCylinderConvergence` | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicHMinusThreeCylinderConvergence.lean` | 478 | The paired cosine/sine cylinder test family, the complexifying reassembly map, and convergence of every finite Fourier cylinder marginal. |
| **h** | | **Prokhorov subsequence** | | entry point: `PeriodicHMinusThreeProkhorovSubsequence` |
| h1 | `PeriodicHMinusThreeProkhorovSubsequence` | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicHMinusThreeProkhorovSubsequence.lean` | 76 | The measure set of the sequence is tight, so any subsequence has a strictly monotone further subsequence converging to a Borel probability measure on the carrier. |
| **i** | | **cylinder-to-Borel uniqueness** | | entry point: `PeriodicHMinusThreeCylinderBorelUniqueness` |
| i1 | `PeriodicHMinusThreeCylinderBorelUniqueness` | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicHMinusThreeCylinderBorelUniqueness.lean` | 125 | Finite-coordinate cylinders as a `π`-system, the named Borel-generation input, and the two measure-extension theorems. |
| **j** | | **final assembly** | | entry point: `PeriodicHMinusThreeWeakLimitMarginal` |
| j1 | `PeriodicHMinusThreeWeakLimitMarginal` | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicHMinusThreeWeakLimitMarginal.lean` | 217 | Six of the seven registered measure-limit theorems: marginal identification, indexed-cylinder uniqueness, whole-sequence existence, marginal form of the limit, uniqueness, and the packaged existence-with-cylinders statement. |

Support modules inside the same import closure but not load-bearing for either statement's wording:
`PeriodicTorusL2`, `PeriodicMassiveWeakSolver`, `PeriodicMassiveEnergy`, `PeriodicTorusWeakResolvent`,
`FourierMassResolvent`, `ConcreteGaussianMoment`, `PhysicalCellRiemann`, `RealFourierTestFunctions`,
`RealFourierSecondMoment`, `PeriodicFrequencyBox`, `PeriodicFourierContinuumTail`,
`PeriodicComplexFourierProbe`, `PeriodicComplexFourierLift`, `PeriodicFullHMinusTwoTrace`,
`PeriodicFullHMinusTwoTraceConcrete`, `PeriodicHMinusTwoTraceMajorant`, `PeriodicHMinusTwoLatticeTrace`,
`PeriodicNegativeSobolevWeightComparison`, `FiniteRealFamilyMeasure`,
`FiniteRealFamilyCharacteristicFunction`, `FiniteRealFamilyCovarianceConvergence`,
`FiniteRealFamilyCovarianceQuadratic`, `FiniteRealFamilyVarianceIdentity`, `CoordinateTightness`
(membership established by the closure command in `§6`).

---

## §2 Declaration ledger

All names are fully qualified in namespace `Pphi2Clean.Continuum` unless the table says otherwise.
Asterisks (`**D12**` etc.) mark the theorems named in `formal/lean/challenges/_registry.yaml:22-47`.

### §2.1 Covariance limit (contract `PPHI2_FIXED_VOLUME_COVARIANCE_LIMIT`)

| id | declaration | kind | file:line | statement in plain mathematical English |
|---|---|---|---|---|
| D01 | `fixedVolumeCovarianceInner` | def | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicFourierCovarianceLimit.lean:1080` | For `d`, period `L > 0`, mass `mass > 0`, bounded continuous real `f, g` and `n : ℕ`, the real number `⟨T_N f, T_N g⟩` where `N = n+1`, `a = L/N`, `T_N = numberedLatticeCovarianceGJ d N a mass` and the test is sampled as `latticeTestField (physicalTestEval d N a) f`. This is the actual GJ covariance of the sampled field, not a Fourier surrogate. |
| D02 | `numberedLatticeCovarianceGJ_physical_eq_fourier` | theorem | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicFourierCovarianceLimit.lean:1176` | At every `N` and every bounded continuous `f, g`, that inner product equals the real part of the finite Fourier Green pairing `(L)^{-d} Σ_{p ∈ (ℤ/N)^d} conj(ĉ_f(p)) ĉ_g(p) / S(p)` with the sampled coefficients `ĉ` and the exact character symbol `S(p) = mass² - Σ_i λ_i(p)`. No diagonalization hypothesis is required of the caller. |
| D03 | `fixedVolumeCovarianceInner_eq_discreteFourierGreenPairing` | theorem | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicFourierCovarianceLimit.lean:1222` | Restatement of D02 at `a = L/N`: for every `n`, `fixedVolumeCovarianceInner … n = Re (discreteFourierGreenPairing d (n+1) L mass f g)`, unconditionally. |
| D04 | `sampledFourierCoefficient_parseval` | theorem | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicFourierCovarianceLimit.lean:543` | Exact Parseval in physical-volume normalization: `Σ_p ‖ĉ_f(p)‖² = L^d · ( (L/N)^d Σ_x f(a·x)² )`, i.e. the sampled coefficients are Riemann sums of the cell integral. |
| D05 | `discreteFourierGreenPairing_sub_cutoff_norm_le` | theorem | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicFourierCovarianceLimit.lean:1121` | For every `N` and every cutoff radius `K`, the complex difference between the full finite pairing and its symmetric cutoff at radius `K` is at most `L^d ‖f‖ ‖g‖ / (mass² + 16K²/L²)`; the bound is uniform in `N` and needs neither periodicity nor a regularity modulus. |
| D06 | `fixedVolumeCovarianceInner_sub_cutoff_abs_le` | theorem | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicFourierCovarianceLimit.lean:1276` | The same estimate for the actual covariance sequence: `|cov_n - Re(cutoff_{n,K})| ≤ L^d ‖f‖ ‖g‖ / (mass² + 16K²/L²)`. |
| D07 | `fixedVolumeCovarianceInner_uniform_tail` | theorem | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicFourierCovarianceLimit.lean:1288` | For every `ε > 0` there is `K₀` such that for all `K ≥ K₀` and all `n`, `|cov_n - Re(cutoff_{n,K})| < ε`: one cutoff controls every lattice size (Archimedean, `fixedVolume_tail_majorant_eventually_lt`, same file `:1231`). |
| D08 | `discreteFourierGreenCutoff_re_tendsto` | theorem | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicFourierCovarianceLimit.lean:1069` | At each fixed cutoff `K`, the real part of the lattice cutoff pairing tends, as `N → ∞`, to the real part of the continuum cutoff pairing over `[-K,K]^d`. |
| D09 | `torusFourierGreenCutoff_re_tendsto` | theorem | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicFourierCovarianceLimit.lean:1019` | The continuum cutoff pairings converge, as `K → ∞`, to the real part of the full Green series. |
| D10 | `torusFourierGreenTerm_summable` | theorem | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicFourierCovarianceLimit.lean:858` | The continuum Green series term family is summable, so the pairing in D09 is an absolutely convergent series (Young-type bound). |
| D11 | `torusFourierGreenPairing_symm` | theorem | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicFourierCovarianceLimit.lean:841` | The complete Green pairing is symmetric in its two arguments, by reindexing the frequency sum along `k ↦ -k`. |
| **D12** | `fixedVolumeCovarianceInner_tendsto_torusFourierGreenPairing` | theorem | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicFourierCovarianceLimit.lean:1457` | **Registered.** For `d`, `L > 0`, `mass > 0` and bounded continuous real `f, g` that are `L`-periodic in every coordinate, the actual lattice covariance sequence `n ↦ fixedVolumeCovarianceInner d L mass f g n` (i.e. `N = n+1`, `a = L/N`) converges in `ℝ` to the real part of the absolutely convergent torus Fourier Green series `L^{-d} Σ_{k ∈ ℤ^d} conj(ĉ_f(k)) ĉ_g(k) / (mass² + (2π/L)²‖k‖²)`. |
| **D13** | `physicalGJMeasure_fixedVolume_mixedMoment_tendsto_torusFourierGreenPairing` | theorem | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicFourierCovarianceLimit.lean:1469` | **Registered.** Under the same hypotheses, the actual mixed second moments `n ↦ ∫ ω f · ω g ∂ physicalGJMeasure 2 … (here general `d`)` of the pushed-forward physical lattice Gaussians converge to the same real number. |
| **D14** | `physicalGJMeasure_fixedVolume_covariance_tendsto_torusFourierGreenPairing` | theorem | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicFourierCovarianceLimit.lean:1488` | **Registered.** Same, for the centred covariance `∫ (ωf - ∫ηf)(ωg - ∫ηg)`; the two centred forms coincide with the mixed moment because both test means vanish identically at every mesh size (`physicalGJMeasure_eval_mean_zero`, D25). |

Signature of D12 (subtle: the periodicity hypothesis is on the *test*, and the limit is only the real
part of a complex series):

```lean
theorem fixedVolumeCovarianceInner_tendsto_torusFourierGreenPairing
    (d : ℕ) (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (f g : BoundedContinuousFunction (Fin d → ℝ) ℝ)
    (hf : IsFlatTorusPeriodic d L f) (hg : IsFlatTorusPeriodic d L g) :
    Filter.Tendsto (fixedVolumeCovarianceInner d L mass hL hmass f g)
      Filter.atTop (nhds (torusFourierGreenPairing d L mass f g).re) :=
```

`IsFlatTorusPeriodic d L f` is `∀ x i, f (x with coordinate i replaced by x i + L) = f x`
(`formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicFourierCovarianceLimit.lean:17-20`).
The discontinuity claim behind that is stated as an explicit residual: the file records that
"identifying an independently defined continuum resolvent with this series remains a separate
operator theorem" (`…PeriodicFourierCovarianceLimit.lean:1306-1308`). That separate theorem is D19.

### §2.2 The resolvent the covariance is compared with

| id | declaration | kind | file:line | statement in plain mathematical English |
|---|---|---|---|---|
| D15 | `periodicH1_graph_completion` | theorem | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicTorusH1.lean:158` | The range of the value-gradient graph map on the completed energy space is exactly the closure of the graph of arbitrary unweighted finite trigonometric polynomials with their classical coordinate derivatives. This is the assertion that periodic H¹ is the closed value-gradient graph completion, not an abstract Sobolev type. |
| D16 | `periodicMassiveResolvent_weak` | theorem | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicTorusH1.lean:170` | The Riesz solution `h` satisfies the massive weak equation `mass² ⟪u_h, u_v⟫ + Σ_i ⟪∂_i u_h, ∂_i u_v⟫ = ⟪g, u_v⟫` for **every** completed energy test `v`, with `u_· = periodicH1Value` and physical gradients `periodicH1Gradient`. |
| D17 | `periodicMassiveResolvent_existsUnique_weak` | theorem | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicTorusH1.lean:198` | For every `g` in periodic L² there is exactly one physical weak value `u` (in the completed polynomial graph, satisfying that equation against every energy test). |
| D18 | `physicalTorusTestL2_repr` | theorem | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicTorusL2.lean:107` | The Fourier coordinate of the L² class of a physical test on the probability-Haar torus equals `L^{-d}` times the physical cell integral `torusFourierCoefficient`: the exact probability/Lebesgue normalization. |
| D19 | `torusFourierGreenPairing_eq_physicalTorusResolventPairing` | theorem | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicTorusResolventLimit.lean:35` | For `L > 0`, `mass > 0` and arbitrary bounded continuous `f, g` (no periodicity hypothesis), the Fourier Green series equals `L^d · ⟪f, R g⟫` on the probability-Haar torus L², where `R` is the weak resolvent of D16/D17. |
| D20 | `fixedVolumeCovarianceInner_tendsto_periodicMassiveResolvent` | theorem | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicTorusResolventLimit.lean:69` | D12 with the limit rewritten as the real part of that resolvent pairing: no Fourier-interface or convergence hypothesis is required. |
| D21 | `physicalGJMeasure_fixedVolume_mixedMoment_tendsto_periodicMassiveResolvent` | theorem | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicTorusResolventLimit.lean:79` | D13 with the resolvent pairing as limit. |
| D22 | `physicalGJMeasure_fixedVolume_covariance_tendsto_periodicMassiveResolvent` | theorem | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicTorusResolventLimit.lean:97` | D14 with the resolvent pairing as limit. |

### §2.3 Lattice sampling and Gaussian-law support

| id | declaration | kind | file:line | statement in plain mathematical English |
|---|---|---|---|---|
| D23 | `latticeCovarianceGJ_inner_eq_massResolvent` | theorem | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/ConcreteLatticeCovariance.lean:120` | The GJ covariance bilinear form is `a^{-d} Σ_x f(x) (Q^{-1} g)(x)`, with `Q` the actual finite-difference mass operator and `Q^{-1}` obtained from positivity plus finite dimensionality. |
| D24 | `numberedLatticeCovarianceGJ_lift_second_moment` | theorem | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/NumberedLatticeGaussianMoment.lean:46` | The exact second moment `∫ (ω F)²` of the lifted field under the numbered finite Gaussian law equals `(a^d)⁻¹ Σ_k λ_k^{-1} (Σ_x e_k(x) F(eval_x))²` in the real mass eigenbasis. |
| D25 | `physicalGJMeasure_eval_mean_zero` | theorem | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PhysicalLatticeGaussianLaw.lean:199` | Every one-dimensional marginal `ω ↦ ω f` of the physical GJ measure has mean `0`, at every lattice size. |
| D26 | `physicalGJMeasure_eval_hasGaussianLaw` | theorem | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PhysicalLatticeGaussianLaw.lean:237` | Every `ω ↦ ω f` under the physical GJ measure has a Gaussian law (its characteristic function is `exp(-t²‖T (latticeTestField f)‖²/2)`, `physicalGJMeasure_charFun`, same file `:221`). |
| D27 | `physicalGJMeasure_mixedMoment` | theorem | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PhysicalLatticeGaussianLaw.lean:376` | The mixed moment `∫ ω f · ω g` of the physical GJ measure equals the GJ covariance inner product of the sampled test fields — an exact identity, not a limit. |
| D28 | `periodicHMinusTwoEnergyOnHMinusThree` | def | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicHMinusTwoUniformTightness.lean:12` | The extended `H^{-2}` energy of a completion point: `∑' k, ofReal (w^{-2}_k ‖c_k‖²)` computed from the **de-weighted** coefficients; it is `∞` outside the `H^{-2}` domain. |
| D29 | `measurable_periodicHMinusTwoEnergyOnHMinusThree` | theorem | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicHMinusTwoUniformTightness.lean:18` | That energy is Borel measurable on the completion (so its sublevels and Markov tails are measurable). |

### §2.4 Carriers, Polish space and Borel generation (separability)

| id | declaration | kind | file:line | statement in plain mathematical English |
|---|---|---|---|---|
| D30 | `periodicHMinusThreeCompletion_separable` | theorem | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicHMinusThreeTopologyBorel.lean:111` | **Registered.** The concrete carrier `lp ((Fin 2 → ℤ) → ℂ) 2` is a separable topological space. Proof shape: the countable set of coordinate unit vectors `lp.single 2 k 1` is separable, its `ℂ`-span is separable, that span is dense (finite truncations converge by `lp.hasSum_single`), hence the carrier is separable. |
| D31 | `periodicHMinusThree_polish_of_separable_input` | theorem | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicHMinusThreeTopologyBorel.lean:57` | Separability of the carrier implies `PolishSpace` (completeness comes from `lp`; second countability from separability of a metric space). |
| D32 | `periodicHMinusThree_cylinder_sigma_eq_borel_of_polish` | theorem | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicHMinusThreeTopologyBorel.lean:71` | Under Polish-ness, the `σ`-algebra generated by measurable finite-coordinate cylinders equals the Borel `σ`-algebra of the carrier. Proof: the coordinate embedding `x ↦ ((x k))_k` is a measurable embedding with injective continuous map, and `σ(cylinders) = comap(embedding)(product σ-algebra)`. |
| D33 | `periodicHMinusThreeCompletion_completeSpace` | theorem | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicHMinusThreeTopologyBorel.lean:8` | The carrier is complete (instance from `lp`). |
| D34 | `periodicHMinusThreeCompletion_declared_borel` | theorem | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicHMinusThreeTopologyBorel.lean:11` | The declared measurable space on the carrier is definitionally the Borel one (the instance is `borel …`, `PeriodicHMinusThreeCompletion.lean:52-55`). |

### §2.5 Uniform `H^{-2}` moment, compact tail and `H^{-3}` tightness

| id | declaration | kind | file:line | statement in plain mathematical English |
|---|---|---|---|---|
| D35 | `periodicHMinusTwoEnergy_sublevel_mem_ball` | theorem | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicHMinusTwoUniformTightness.lean:39` | If the extended energy at `x` is at most `R ≥ 0` then `x` lies in the concrete `H^{-2}` ball of radius `√R` inside the `H^{-3}` completion. |
| D36 | `periodicHMinusTwoEnergy_sublevel_closure_compact` | theorem | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicHMinusTwoUniformTightness.lean:102` | **Compact tail.** For `R ≥ 0` the closure of `{x : E(x) ≤ R}` is compact, inherited from compactness of the closed `H^{-2}` ball (`isCompact_closure_periodicHMinusTwoBallInHMinusThree`, `…PeriodicNegativeSobolevTopologyInterfaces.lean:446`). This is the only compactness engine of the tightness argument. |
| D37 | `periodicHMinusThree_measure_family_tight_of_uniform_HMinusTwo_energy` | theorem | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicHMinusTwoUniformTightness.lean:239` | If `C ≥ 0` and `∫⁻ E dμ_n ≤ ofReal C` for all `n`, then for every `ε > 0` the compact set `K = closure {x : E(x) ≤ ofReal (C/ε + 1)}` satisfies `μ_n (Kᶜ) ≤ ofReal ε` for all `n`. The cutoff `C/ε + 1` makes the Markov tail strictly below `ε`. |
| D38 | `periodicHMinusThree_probabilityMeasure_family_tight_of_uniform_HMinusTwo_energy` | theorem | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicHMinusTwoUniformTightness.lean:297` | Same statement for `ProbabilityMeasure`-valued families (coercion to `Measure`). |
| D39 | `periodicHMinusTwoFixedVolumeTraceConstant` | def | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicHMinusTwoUniformTightness.lean:309` | The `n`-independent energy constant `mass⁻¹²·L²·(1 + 2 Σ'_k w^{-2}_k)` (written `mass⁻¹ ^ 2 * L ^ 2 + (2 * (mass⁻¹ ^ 2 * L ^ 2)) * Σ' k, periodicHMinusTwoWeight k`). |
| D40 | `periodicHMinusTwo_fixedVolume_trace_uniform_in_n` | theorem | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicHMinusTwoUniformTightness.lean:321` | At `N = n+1`, `a = L/(n+1)`, the full lifted trace is bounded by that constant for every `n`. |
| D41 | `periodicHMinusThreeFixedVolumeFreeFieldProbabilityMeasure_energy_bound` | theorem | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicHMinusThreeFixedVolumeTightness.lean:156` | The `H^{-2}` energy lintegral of the fixed-volume law is at most `ofReal (periodicHMinusTwoFixedVolumeTraceConstant L mass)`, uniformly in `n`. |
| D42 | `periodicHMinusThree_fixedVolume_freeField_tight` | theorem | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicHMinusThreeFixedVolumeTightness.lean:230` | **Tightness.** For `L > 0`, `mass > 0` and every `ε > 0` there is a compact `K` in the carrier with `μ_n (Kᶜ) ≤ ofReal ε` for all `n`, where `μ_n` is the fixed-volume law of D44/T16. |
| D43 | `periodicHMinusThree_fixedVolume_probabilityMeasureSet_tight` | theorem | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicHMinusThreeProkhorovSubsequence.lean:20` | The set of measures `{ρ : ∃ n, ρ = μ_n}` is an `IsTightMeasureSet` (the form Prokhorov consumes), converted from D42 via `isTightMeasureSet_iff_exists_isCompact_measure_compl_le`. |

### §2.6 Finite real families: characteristic functions and covariance convergence

| id | declaration | kind | file:line | statement in plain mathematical English |
|---|---|---|---|---|
| D44 | `finiteGaussian_weak_tendsto_of_covariance_entries` | theorem | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/FiniteRealFamilyCovarianceQuadratic.lean:5` | If every `μ_n` and `μ₀` are Gaussian on `ℝ^m`, the means converge, the matrix entries `Cn n i j → C i j`, and all projected variances are the respective matrix quadratic forms, then `μ_n ⇒ μ₀` weakly. |
| D45 | `finiteGaussian_weak_tendsto_of_mean_variance` | theorem | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/FiniteRealFamilyCharacteristicFunction.lean:48` | The characteristic-function engine used by D44: Gaussian laws on `ℝ^m` converge weakly once means and all projected variances converge. |
| D46 | `physicalFamilyEvalMeasure_fixedVolume_covariance_entry_tendsto` | theorem | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/FiniteRealFamilyCovarianceConvergence.lean:5` | Given convergence of the lattice covariance inner products of a finite test family, every second-moment entry `∫ z_i z_j` of the evaluated finite-dimensional law converges to the same limit. |
| D47 | `periodicResolventCovarianceMatrix_matrix_posSemidef_of_factorization` | theorem | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/FiniteRealFamilyWeakLimitInterface.lean:447` | The periodic resolvent covariance matrix `(i,j) ↦ Re ⟪f_i, R f_j⟫` is positive semidefinite as a real matrix, obtained from a Gram factorization (the Fourier square formula supplies it). |
| D48 | `physicalFamilyEvalProbabilityMeasure_fixedVolume_weak_tendsto_of_periodic_fourier` | theorem | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/FiniteRealFamilyWeakLimitInterface.lean:855` | **Unconditional finite-family convergence**: for `L > 0`, `mass > 0` and any finite family `fs` of bounded continuous real tests, the finite-dimensional laws converge weakly to the canonical target Gaussian whose covariance is the periodic resolvent matrix. This is where the PSD and the target construction meet the covariance limit D12. |
| D49 | `physicalFamilyEvalProbabilityMeasure_fixedVolume_weak_tendsto_of_any_finite_test_family_indexed` | theorem | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/FiniteFourierCoordinateConvergence.lean:86` | The same conclusion, taking only the covariance-entry limits `hinner` and the identification `hC` of the limit matrix with the resolvent matrix as inputs; this is the wrapper the cylinder step calls. |

### §2.7 Cylinder convergence

| id | declaration | kind | file:line | statement in plain mathematical English |
|---|---|---|---|---|
| D50 | `periodicHMinusThreeFiniteSourceCylinderProbabilityMeasure_tendsto_fixedVolume` | theorem | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicHMinusThreeCylinderConvergence.lean:415` | **Cylinder marginals.** For every `m` and every `m`-tuple of Fourier modes, the pushforward of the finite-source law at `N = n+1`, `a = L/N` under the `m`-coordinate cylinder map converges weakly to the pushforward of the target Gaussian on `ℝ^{2m}` under the complexifying reassembly map. No whole-carrier convergence is asserted. |
| D51 | `periodicHMinusThreeFixedVolumeMeasureSequence_cylinder_tendsto` | theorem | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicHMinusThreeCylinderConvergence.lean:451` | The same statement for the actual sequence `μ_n = periodicHMinusThreeFixedVolumeFreeFieldProbabilityMeasure`, obtained from D50 by rewriting the measure definition (`:469-475`). |
| D52 | `periodicHMinusThreeCylinderMap` | def | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicHMinusThreeCompletion.lean:35` | The finite cylinder projection `x ↦ (x (modes 0), …, x (modes m-1))`, i.e. the coordinates are the **weighted** coefficients stored by the completion. |
| D53 | `periodicHMinusThreeComplexifyCylinder` | def | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicHMinusThreeCylinderConvergence.lean:24` | Reassembly of the `2m` real cosine/sine coordinates into `m` complex coordinates: `i ↦ √(w_k) · (x_{i,cos} + i·x_{i,sin})`. The `√w` factor is applied **here**, not in the real family. |

### §2.8 Prokhorov extraction

| id | declaration | kind | file:line | statement in plain mathematical English |
|---|---|---|---|---|
| D54 | `periodicHMinusThree_fixedVolume_prokhorov_subsequence` | theorem | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicHMinusThreeProkhorovSubsequence.lean:47` | Assuming the carrier is separable, for `L > 0`, `mass > 0` and **any** `ns → ∞` there are a strictly increasing `ms` and a Borel probability measure `ν` on the carrier with `μ_{ns(ms k)} ⇒ ν`. Proof: tightness (D43) makes `closure (range μ)` compact, then `IsCompact.tendsto_subseq`. The limit is a genuine measure on the carrier, not a family of finite marginals. |

Signature of D54 (subtle: separability is an explicit hypothesis, and the statement is about an
arbitrary subsequence, which is what the whole-sequence argument needs):

```lean
theorem periodicHMinusThree_fixedVolume_prokhorov_subsequence
    (hsep : TopologicalSpace.SeparableSpace PeriodicHMinusThreeCompletion)
    (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass)
    (ns : ℕ → ℕ) (_hns : Tendsto ns atTop atTop) :
    ∃ (ms : ℕ → ℕ) (ν : ProbabilityMeasure PeriodicHMinusThreeCompletion),
      StrictMono ms ∧
      Tendsto (fun k =>
        (periodicHMinusThreeFixedVolumeFreeFieldProbabilityMeasure
          L mass hL hmass (ns (ms k)))) atTop (𝓝 ν) :=
```

### §2.9 Cylinder-to-Borel uniqueness

| id | declaration | kind | file:line | statement in plain mathematical English |
|---|---|---|---|---|
| D55 | `periodicHMinusThree_measure_ext_of_cylinder` | theorem | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicHMinusThreeCylinderBorelUniqueness.lean:77` | Two finite Borel measures that agree on every measurable finite-coordinate cylinder and have equal total mass are equal, **given** the named Borel-generation input (`PeriodicHMinusThreeCylinderBorelGenerationInput`, same file `:54`). Uses `ext_of_generate_finite` on a `π`-system. |
| D56 | `periodicHMinusThree_probabilityMeasure_ext_of_finite_marginals` | theorem | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicHMinusThreeCylinderBorelUniqueness.lean:97` | Two Borel probability measures on the carrier are equal as soon as all their finitely-supported coordinate pushforward laws coincide (still conditional on the named generation input). |
| D57 | `periodicHMinusThree_probabilityMeasure_ext_of_indexed_cylinder_marginals` | theorem | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicHMinusThreeWeakLimitMarginal.lean:80` | **Registered. Unconditional.** If two Borel probability measures have equal pushforwards under `periodicHMinusThreeCylinderMap m modes` for every `m` and every `m`-tuple of modes, they are equal. The Borel-generation input of D55/D56 is *discharged* here from concrete separability via D31/D32 (`:86-89`), and an arbitrary finset is reduced to an `m`-tuple (`:91-119`). |

### §2.10 Final assembly (whole-sequence limit)

| id | declaration | kind | file:line | statement in plain mathematical English |
|---|---|---|---|---|
| D58 | `periodicHMinusThree_weak_limit_has_expected_cylinder_marginal` | theorem | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicHMinusThreeWeakLimitMarginal.lean:16` | If `μ_{ns(ms k)} ⇒ ν` along a strictly increasing `ms` and the cylinder pushforwards of `μ_n` converge to the target family, then `ν`'s cylinder marginal equals the target's. Proof: continuous mapping of probability measures plus uniqueness of limits in the finite-dimensional probability-measure space. |
| D59 | `periodicHMinusThree_fixedVolume_subsequential_limit_has_expected_cylinder` | theorem | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicHMinusThreeWeakLimitMarginal.lean:50` | **Registered.** Any subsequential limit of the actual fixed-volume sequence has the expected finite Fourier cylinder marginals (D51 feeds D58). |
| D60 | `periodicHMinusThree_fixedVolume_weak_limit_exists` | theorem | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicHMinusThreeWeakLimitMarginal.lean:124` | **Registered.** For `L > 0`, `mass > 0` there **exists** a Borel probability measure `μfree` on the carrier such that the **whole** sequence `μ_n` converges weakly to it. Proof: extract one subsequential limit `μfree` (D54 at `id`), then show every subsequence has a further subsequence converging to `μfree` (D54 + D59 twice + D57), then `Filter.tendsto_of_subseq_tendsto`. |
| D61 | `periodicHMinusThree_fixedVolume_weak_limit_has_expected_cylinder` | theorem | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicHMinusThreeWeakLimitMarginal.lean:161` | **Registered.** Any `μfree` that is a weak limit of the whole sequence has the expected finite Fourier cylinder marginals — exposed as a public theorem rather than left inside the existence proof (docstring `:157-160`). |
| D62 | `periodicHMinusThree_fixedVolume_weak_limit_unique` | theorem | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicHMinusThreeWeakLimitMarginal.lean:190` | **Registered.** Any two weak limits of the sequence coincide. Note the proof is `tendsto_nhds_unique` (`:198`): this is Hausdorff uniqueness of a filter limit, not an additional identification statement — the identification lives in D61/D57. |
| D63 | `periodicHMinusThree_fixedVolume_weak_limit_exists_with_expected_cylinders` | theorem | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicHMinusThreeWeakLimitMarginal.lean:202` | **Registered.** Conjunction of D60 and D61: there is `μfree` with `μ_n ⇒ μfree` and with every finite Fourier marginal equal to the target's. |

Signature of D60 (the paper's headline existence statement; the conclusion is `∃` plus weak
convergence of the whole sequence, with no hypothesis beyond `L > 0` and `mass > 0`):

```lean
theorem periodicHMinusThree_fixedVolume_weak_limit_exists
    (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    ∃ μfree : ProbabilityMeasure PeriodicHMinusThreeCompletion,
      periodicHMinusThreeFixedVolumeFreeFieldWeakLimit L mass hL hmass μfree :=
```

where `periodicHMinusThreeFixedVolumeFreeFieldWeakLimit … μfree` *is by definition*
`Filter.Tendsto (periodicHMinusThreeFixedVolumeFreeFieldMeasureSequence L mass hL hmass) atTop
(nhds μfree)` (`formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicHMinusThreeFixedVolumeTightness.lean:119-124`).

---

## §3 Definition ledger

Conventions a reader can get wrong are called out explicitly. Notation: `w^{-2}`, `w^{-3}` are the
weight functions of T2; `‖·‖` is the Euclidean norm on `Fin 2 → ℤ`.

| id | object | file:line | exact definition / formula | conventions to fix |
|---|---|---|---|---|
| T1 | Fourier index set `PeriodicFourierIndex` | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicHMinusThreeCompletion.lean:10` | `abbrev PeriodicFourierIndex := Fin 2 → ℤ` | **The carrier is two-dimensional.** The covariance theorem D12 is stated for general `d : ℕ`, but every measure-limit object (`PeriodicHMinusThreeCompletion`, the cylinder maps, the law sequence) is hard-wired to `Fin 2 → ℤ`. A paper that says "in dimension `d`" for the measure limit overstates the formalization. |
| T2 | weight and its zero mode | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicNegativeSobolevCarriers.lean:5-6`; `…/PeriodicHMinusTwoWeight.lean:5-6`, `:22-23` | `periodicHMinusThreeWeight k = if k = 0 then 1 else ‖k‖^(-6)`; `periodicHMinusTwoWeight k = if k = 0 then 0 else ‖k‖^(-4)`; `periodicHMinusTwoFullWeight k = if k = 0 then 1 else periodicHMinusTwoWeight k` | **Two negative-Sobolev weights with different zero-mode conventions.** The `H^{-3}` weight has zero mode `1` (not `0`, and not `‖0‖^{-6}`); the `H^{-2}` "tail" weight has zero mode `0`, while the `H^{-2}` *full* weight used by the carrier has zero mode `1`. Mixing the two `H^{-2}` variants changes the trace constants. Both are sums over the same index type `Fin 2 → ℤ`. |
| T3 | `periodicHMinusTwoCarrier` | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicHMinusTwoWeight.lean:46-47` | `{c : (Fin 2 → ℤ) → ℂ \| Summable (fun k => periodicHMinusTwoFullWeight k * ‖c k‖ ^ 2)}` | Uses the **full** weight (zero mode `1`), so the carrier is a normed sequence space with the constant sequence square-summable. It is a `Set`, not a type. |
| T4 | `periodicHMinusThreeCarrier` | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicNegativeSobolevCarriers.lean:33-34` | `{c : (Fin 2 → ℤ) → ℂ \| Summable (fun k => periodicHMinusThreeWeight k * ‖c k‖ ^ 2)}` | Zero mode weight `1`, so no mode is annihilated: the pairing with the zero mode is part of the `H^{-3}` norm. |
| T5 | `PeriodicHMinusTwoSpace` (the carrier subtype) | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicComplexFourierLift.lean:19-20` | `{c : (Fin 2 → ℤ) → ℂ // c ∈ periodicHMinusTwoCarrier}` | A **bare subtype**: it carries no norm, no topology and no measurable structure. Do not confuse it with `PeriodicHMinusThreeCompletion` (T6), which is an `lp` space. Only the `H^{-3}` object is used for weak convergence. |
| T6 | `PeriodicHMinusThreeCompletion` and `lp … 2` | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicHMinusThreeCompletion.lean:14-15` | `abbrev PeriodicHMinusThreeCompletion := lp (fun _ : PeriodicFourierIndex => ℂ) 2` | `lp … 2` is Mathlib's ℓ²-type space of coefficient families satisfying `Memℓp · 2` with the ℓ² norm. **The coordinates are the weighted coefficients** `√w_k · c_k`, not the raw distribution coefficients — see T7. Consequently the cylinder coordinates of D52 are already weighted. |
| T7 | weight / deweight maps | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicHMinusThreeCompletion.lean:18-26` | `periodicHMinusThreeWeightedCoefficients c k = √(w_k) * c k`; `periodicHMinusThreeDistributionCoefficients x k = x k / √(w_k)` | The decode is total. It is safe only because `w_k > 0` for **every** `k`, including `k = 0` (zero mode `1`, T2) — that is exactly why the `H^{-3}` zero mode is `1` and not `0`. |
| T8 | `periodicHMinusTwoBallInHMinusThree` | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicNegativeSobolevTopologyInterfaces.lean:367-370` | `{x \| ∃ c ∈ periodicHMinusTwoCarrier, periodicHMinusTwoNorm c ≤ B ∧ x = periodicHMinusThreeEmbeddingOfHMinusTwo c hc}` | The ball is defined through the **embedding of `H^{-2}` coefficients** into the completion (`periodicHMinusThreeEmbeddingOfHMinusTwo`, same file `:227-231`), not as a metric ball of the completion's own norm. Its closed closure is the compact set used in D36. |
| T9 | coordinate embeddings | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicHMinusThreeTopologyBorel.lean:15-17`; `…/PeriodicHMinusThreeCompletion.lean:35-38` | `periodicHMinusThreeCoordinateEmbedding x = fun k => x k`; `periodicHMinusThreeCylinderMap m modes x = fun i => x (modes i)` | The embedding is continuous, injective, and a `MeasurableEmbedding` once Polish-ness is available (`periodicHMinusThree_coordinateEmbedding_measurableEmbedding_of_polish`, same file `:64-69`) — that is the step that makes "cylinders generate the Borel σ-algebra" true rather than assumed. |
| T10 | lattice configuration space | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/ConcreteLatticeOperator.lean:21`, `:27`; `…/LatticeGaussianContinuumConsumer.lean:61`, `:63` | `FinLatticeSites d N := Fin d → ZMod N`; `FinLatticeField d N := FinLatticeSites d N → ℝ`; but the **source space of the Gaussian law** is `FiniteLatticeField n := Fin n → ℝ` and `FiniteLatticeConfiguration n := WeakDual ℝ (FiniteLatticeField n)` | Two different lattices coexist: the periodic site type `Fin d → ZMod N` (used by the Laplacian, characters and eigenbasis) and the numbered real vector space `Fin n → ℝ` with `n = card (Fin d → ZMod N)` (used by the Gaussian measure). They are glued by `Fintype.equivFin` (`reindexCovariance`, `…/NumberedLatticeGaussianMoment.lean:9-26`). The measure lives on the **weak dual**, not on the field space. |
| T11 | `latticePhysicalPoint` | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PhysicalLatticeSampling.lean:9-11` | `latticePhysicalPoint d N a x := fun i => a * (x i).val` with `a = L/N` | Sites are the residue representatives in `[0, aN) = [0, L)`; there is no `-L/2` shift, so physical positions are the lower-left anchored mesh. |
| T12 | `physicalTestEval` (sampling weight) | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PhysicalLatticeSampling.lean:14-18` | `(a^d) • evalCLM (latticePhysicalPoint d N a j)` | The Riemann weight `a^d` (**not** `a^{-d}`, **not** `a^{d/2}`) sits on the *test evaluation*, so every sampled test carries the cell volume. Grep of the tree finds no occurrence of an `a·d/2`-shaped factor; the only `a`-powers that occur in the chain are `a^d` here and `(a^d)^{1/2}` in T13. |
| T13 | lattice covariance normalization | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/ConcreteLatticeCovariance.lean:17-22`, `:39-51`; `…/RealLatticeSpectralCovariance.lean:41-59`, `:99-103` | `latticeCovarianceGJ = spectralCovarianceGJ a d ha (spectralData …)`; `spectralCovarianceGJ = (√(a^d))⁻¹ • spectralCovariance`; `spectralCovariance D f = Σ_k (√λ_k)⁻¹ (Σ_x e_k(x) f(x)) • e_k`; hence `⟨T f, T g⟩ = (a^d)⁻¹ ⟨T_bare f, T_bare g⟩` | The GJ normalization is `a^{-d}` on the **bilinear form**, i.e. `a^{-d/2}` per covariance factor (`√(a^d)⁻¹`). It multiplies the *bare* `Q^{-1/2}` factor; it is not a mass rescaling and not a `1/2` in the exponent of the spacing. A second, unrelated definition with the same name exists as a field-driven interface, `LatticeCovarianceGJRescalingData.latticeCovarianceGJ` (`…/LatticeGaussianContinuumConsumer.lean:222-228`), which is **not** the spectral object used by the chain — a real name collision to avoid in the paper. |
| T14 | `numberedLatticeCovarianceGJ` | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/NumberedLatticeGaussianMoment.lean:37-42` | `reindexCovariance (Fintype.equivFin (FinLatticeSites d N)) (latticeCovarianceGJ d N a mass ha hmass)` | This is the object the covariance theorems actually quote; it is `latticeCovarianceGJ` transported along **one particular numbering** of sites. The numbering is fixed by `Fintype.equivFin`, so statements are numbering-dependent only up to the transport lemma `reindexCovariance_inner` (`:28-34`). |
| T15 | `finiteCovarianceGaussianMeasure` | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/ConcreteGaussianMoment.lean:148-151` | `(productGaussian (Fintype.card ι) 1).map (covarianceConfiguration T)` | The reference Gaussian is a **product of `card ι` standard normals** pushed through the covariance configuration; hence `∫ ω f · ω g = ⟨T f, T g⟩` (`finiteCovarianceGaussianMeasure_covariance`, `:159-170`). Not a spectral measure and not normalized by `(2π)^{-n/2}`. |
| T16 | `physicalGJMeasure` | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PhysicalLatticeSampling.lean:43-47` | `(finiteCovarianceGaussianMeasure (numberedLatticeCovarianceGJ d N a mass ha hmass)).map (latticeEmbedLift (physicalTestEval d N a))` | Lives on `WeakDual ℝ (BoundedContinuousFunction (Fin d → ℝ) ℝ)` — i.e. on the test-function dual, not on a function space. It is a probability measure (`:49-53`). Its test means vanish (D25) but its **covariance is `a^{-d}`-normalized while its tests carry `a^d`**, so the two factors almost cancel in the mesh limit; the surviving content is the mass-symbol sum. |
| T17 | lift maps (raw, total, per-site, finite-source) | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicHMinusThreeFourierMeasure.lean:14-17`, `:43-47`, `:186-191`, `:251-257`; `…/PeriodicHMinusThreeSiteWeightedSequence` | `periodicHMinusThreeRawWeightedLift = √w_k · periodicComplexFourierLift`; `periodicHMinusThreeTotalCarrierLift ω = if h : Memℓp c 2 then ⟨c, h⟩ else 0`; per-site vector `k ↦ √(w_k) · ( a²cos θ + i·a² sin θ )` with `θ = (2π/L) Σ_i k_i (physical point)_i`; `periodicHMinusThreeFiniteSourceFourierLift ω = Σ_j ω_j • (site vector j)` | Three traps: (i) the **total** lift silently sends the exceptional set to `0` and the docstring says it does *not* assert that set is null (`:40-42`); (ii) the per-site vector carries `a²`, i.e. `a^d` at `d = 2`, **inside** the lift — so the `a`-powers appear once in the test sampling (T12) and once here; (iii) the phase `θ` uses the physical point `a·x`, so the lift is the actual Fourier transform of the sampled field, not of the residue index. |
| T18 | `liftedMeasure` | field: `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicFreeFieldFinalTheorem.lean:18-21`. Real measures: `…/PeriodicHMinusThreeFourierMeasure.lean:401-406`, `:411-419`; `…/PeriodicHMinusThreeFixedVolumeTightness.lean:93-106`, `:110-114` | There is **no declaration named `liftedMeasure` that defines a measure**. `liftedMeasure : ℕ → Measure Carrier` is a *field of a generic structure* `PeriodicFreeFieldFinalData`, constrained only by a field equation `liftedMeasure n = Measure.map (latticeToContinuumLift n) (sourceMeasure n)`. The concrete objects are: `periodicHMinusThreeLatticeMeasure = Measure.map (totalCarrierLift) (physicalGJMeasure …)`, `periodicHMinusThreeFiniteSourceMeasure = Measure.map (totalCarrierLift ∘ latticeEmbedLift ∘ physicalTestEval) (finiteCovarianceGaussianMeasure …)`, and `periodicHMinusThreeFixedVolumeFreeFieldProbabilityMeasure n` = the finite-source pushforward at `N = n+1`, `a = L/N`. | **A paper must not cite `liftedMeasure` as the construction.** It is an abstract placeholder in a module that is not reachable from the package root and is not in either contract's closure (`§5.iii`). The object the theorems are about is `periodicHMinusThreeFixedVolumeFreeFieldProbabilityMeasure` (T18, third bullet) — a pushforward of the **finite Gaussian source**, not of `physicalGJMeasure`. |
| T19 | `sampledFourierCoefficient`, `torusFourierCoefficient`, `torusMassSymbol`, `torusFourierGreenPairing` | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicFourierCovarianceLimit.lean:24-30`, `:378-381`, `:424-425`, `:493-497` | `ĉ_f(p) = (L/N)^d Σ_x f(a·x) χ_N(-p)(x)`; `c_f(k) = ∫_{[0,L]^d} f(x) e^{-i(2π/L)k·x} dx`; `S(k) = mass² + (2π/L)² Σ_i k_i²`; `G(f,g) = (L)^{-d} Σ'_k conj(c_f(k)) c_g(k) / S(k)` | The **negative phase** convention is used for both transforms (`χ(-p)`, `e^{-ikx}`). The prefactor `L^{-d}` on the Green series is what turns the Lebesgue cell integral into the probability-Haar pairing of D18/D19. The continuum series is absolutely convergent (D10), so `∑'` needs no summability hypothesis from the caller. |
| T20 | `fixedVolumeCovarianceInner` | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicFourierCovarianceLimit.lean:1080-1094` | see D01 | Its `N` and `a` are **derived** (`N = n+1`, `a = L/N`), so the mesh is not a free parameter anywhere in the chain; the only free parameters are `L` and `mass`. |
| T21 | `periodicHMinusTwoFixedVolumeTraceConstant` | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicHMinusTwoUniformTightness.lean:309-311` | `mass⁻¹ ^ 2 * L ^ 2 + (2 * (mass⁻¹ ^ 2 * L ^ 2)) * ∑' k, periodicHMinusTwoWeight k` | The constant is `n`-independent because `a·N = L` is imposed (`hL : a * (N:ℝ) = L`); it contains `Σ' w^{-2}_k` with zero mode `0`, so the summand at `k = 0` contributes nothing. |
| T22 | `periodicResolventCovarianceMatrix`, `periodicResolventTargetProbabilityMeasure` | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/FiniteRealFamilyWeakLimitInterface.lean:236-239`, `:775-786` | `M i j = Re (physicalTorusResolventPairing d L mass hmass (fs i) (fs j))`; target measure = `targetCoordinateMeasure (periodicResolventCovarianceCanonicalFactor …)`, i.e. the law of `T·(standard normal)` with `T` a Gram factor of `M` | The cylinder target is defined **through the resolvent** via `physicalTorusResolventPairing` (which contains the factor `L^d`). Since D19 identifies that pairing with the Green series, the target of the measure theorem and the target of the covariance theorem are the same object — but only through D19, so the paper must cite D19 when it says the two nodes concern one limit. |
| T23 | `IsFlatTorusPeriodic` | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicFourierCovarianceLimit.lean:17-20` | `∀ (x : Fin d → ℝ) (i : Fin d), f (fun j => if j = i then x j + L else x j) = f x` | Periodicity is stated for the **lift**, i.e. as a condition on the bounded continuous function on `ℝ^d`, not as a descent datum to `UnitAddTorus`. Every cylinder test used in the measure chain discharges it (`periodicHMinusThreeCylinderTestFamily_isFlatTorusPeriodic`, `…/PeriodicHMinusThreeCylinderConvergence.lean:400-410`). |

---

## §4 Axiom footprint

### §4.1 What the project claims, and where

| claim | pointer |
|---|---|
| The permitted axiom set is the Lean kernel trio. | `formal/lean/challenges/_registry.yaml:19` — `permitted_axioms: [propext, Classical.choice, Quot.sound]` |
| The three covariance theorems' footprints are exactly that trio, checked on Lean `v4.34.0-rc2`. | `proof_graph/scopes/PPHI2_FIXED_VOLUME_COVARIANCE_LIMIT.yaml:29-35` — "New declaration footprints were checked against the standard propext, Classical.choice and Quot.sound allowlist." |
| The seven measure-limit theorems' footprints are exactly the trio. | `proof_graph/scopes/PPHI2_FIXED_VOLUME_FREE_FIELD_MEASURE_LIMIT.yaml:36-40` — "all seven theorem footprints are exactly the kernel trio [propext, Classical.choice, Quot.sound]." |
| Both contracts are `remote_only` and score `SKIP` locally, so a local `lean_challenge --run` is not a pass. | `formal/lean/challenges/_registry.yaml:28-34`, `:48-56`; `proof_graph/scopes/PPHI2_FIXED_VOLUME_FREE_FIELD_MEASURE_LIMIT.yaml:37-39` |
| No `sorry` and no project `axiom` survive in the 89 package modules (comment-stripped count; the one naive hit is doc-comment prose). | computed, `§6`; the naive hit is `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/NelsonLayerCake.lean:85` ("axiom asserts.") |

### §4.2 Checked-in transcript that this note found on disk

A transcript **exists** for exactly the ten chain theorems (3 covariance + 7 measure):
`paper/PPHI2_FIXED_VOLUME_COMPLETE/ext/axiom_transcript.txt:1-44`. Verbatim (lines 27-36, the TAB
separated body; header lines 3-6 give the recorded date, project, toolchain and source directory, and
lines 8-18 the recorded commands):

```text
Pphi2Clean.Continuum.fixedVolumeCovarianceInner_tendsto_torusFourierGreenPairing	propext, Classical.choice, Quot.sound
Pphi2Clean.Continuum.physicalGJMeasure_fixedVolume_mixedMoment_tendsto_torusFourierGreenPairing	propext, Classical.choice, Quot.sound
Pphi2Clean.Continuum.physicalGJMeasure_fixedVolume_covariance_tendsto_torusFourierGreenPairing	propext, Classical.choice, Quot.sound
Pphi2Clean.Continuum.periodicHMinusThreeCompletion_separable	propext, Classical.choice, Quot.sound
Pphi2Clean.Continuum.periodicHMinusThree_probabilityMeasure_ext_of_indexed_cylinder_marginals	propext, Classical.choice, Quot.sound
Pphi2Clean.Continuum.periodicHMinusThree_fixedVolume_subsequential_limit_has_expected_cylinder	propext, Classical.choice, Quot.sound
Pphi2Clean.Continuum.periodicHMinusThree_fixedVolume_weak_limit_exists	propext, Classical.choice, Quot.sound
Pphi2Clean.Continuum.periodicHMinusThree_fixedVolume_weak_limit_has_expected_cylinder	propext, Classical.choice, Quot.sound
Pphi2Clean.Continuum.periodicHMinusThree_fixedVolume_weak_limit_unique	propext, Classical.choice, Quot.sound
Pphi2Clean.Continuum.periodicHMinusThree_fixedVolume_weak_limit_exists_with_expected_cylinders	propext, Classical.choice, Quot.sound
```

Its own header states the toolchain and the project (`…/ext/axiom_transcript.txt:4-5`:
`/home/zhengyj/AImath-lean/AImathPPhi2Clean`, `leanprover/lean4:v4.34.0-rc2`), records the build and
`#print axioms` commands (`:8-18`), and records a negative control (`:38-44`) whose witness file is
`formal/lean/s6/pphi2_clean/audit/negative_axiom.lean:1`
(`axiom injectedAxiom : False`, comment-stripped search finds **no** similarly shaped line anywhere in
the 89 package modules).

A second, independent transcript covers the covariance trio inside a broader declaration audit:
`formal/lean/s6/pphi2_clean/audit/finite_lattice_all_declarations_interface.log:106-108` (and
`:109-111`, `:112-114`) reads, wrapping preserved:

```text
'Pphi2Clean.Continuum.fixedVolumeCovarianceInner_tendsto_torusFourierGreenPairing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

That log files 266 footprints in total, and every one of them is the trio: 179 single-line
occurrences plus 87 occurrences of the three-line form
`depends on axioms: [propext,` / ` Classical.choice,` / ` Quot.sound]`, with no other shape present.
A third, narrow transcript is `formal/lean/s6/pphi2_clean/audit/clean_axioms.log:1-3` (three
`Schwinger`/Wick declarations, trio each).

### §4.3 What this note did **not** verify

**This note did not run Lean.** No `lake` command was invoked and no `#print axioms` was executed in
this session. Therefore:

- For the ten chain theorems listed in `§4.2`: the footprints above are **quoted from a checked-in
  transcript**, and that transcript's provenance is a server run recorded only in its own prose
  header (`…/ext/axiom_transcript.txt:3-18`). That provenance is `UNVERIFIED-BY-THIS-NOTE`.
- For the *current bytes* of the sources, all footprints are `UNVERIFIED-BY-THIS-NOTE`, for a concrete
  reason: the audit transcript postdates the source manifest it would have to be pinned to.
  `formal/lean/s6/pphi2_clean/audit/finite_lattice_source.sha256` holds 67 entries and **none of the
  periodic `H^{-3}`/covariance-limit modules** (no `PeriodicFourierCovarianceLimit`,
  no `PeriodicHMinusThree*`), and its mtime is older than the module mtimes
  (`…/PeriodicFourierCovarianceLimit.lean` is dated 2026-10-25; the audit `.log` 2026-10-24;
  the manifest 2026-10-20). So even the covariance-trio transcript is a snapshot of an older tree.
- The audit driver `formal/lean/s6/pphi2_clean/audit/finite_lattice_all_declarations_interface.lean`
  imports the package root `AImathPPhi2Clean` (`:1`) and issues 268 `#print axioms` directives, none
  of them about the `H^{-3}` modules. The two directives with no output line in the log are
  `Pphi2Clean.UpstreamLattice.FinLatticeSites` and `…InfLatticeSites`, which are `abbrev`s and so print
  no axiom line — not a footprint gap.

Nothing in this section is a governance judgement: no status token is asserted for either node.

---

## §5 Known gaps and honest boundaries

### (i) Theorems carrying an explicit hypothesis that is not proved in this development

**The only such hypothesis that touches the registered statements is a measurability input, and it is
not a premise of the final six measure-limit theorems.**

| object | file:line | exact content | where it is used |
|---|---|---|---|
| `PeriodicHMinusThreeLiftMeasureInput` | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicHMinusThreeFourierMeasure.lean:390-397` | `AEMeasurable (periodicHMinusThreeTotalCarrierLift L hperiod) (physicalGJMeasure 2 N a mass ha hmass) ∧ ∀ᵐ ω ∂physicalGJMeasure …, ∀ k, totalCarrierLift ω k = rawWeightedLift ω k` — i.e. the total lift is a.e. measurable **and** agrees a.e. with the raw weighted lift on *every* Fourier coordinate. | `…/PeriodicHMinusThreeCylinderConvergence.lean:76`, `:87`, `:226`, `:130-135` (per-`n` wrapper `periodicHMinusThreeLiftMeasureInputAt`), `…/PeriodicHMinusThreeFourierMeasure.lean:452` |

The unwinding chain that makes this hypothesis *irrelevant* to the registered theorem is recorded in
the source and can be checked line by line:

1. `periodicHMinusThreeFiniteSourceProbabilityMeasure` (`…/PeriodicHMinusThreeFourierMeasure.lean:478-487`)
   is the pushforward of `finiteCovarianceGaussianMeasure` through
   `periodicHMinusThreeFiniteSourceFourierLift` — a **measurable** map
   (`measurable_periodicHMinusThreeFiniteSourceFourierLift`, `:259-272`), so no `AEMeasurable`
   hypothesis is needed.
2. `periodicHMinusThreeFixedVolumeFreeFieldProbabilityMeasure` (`…/PeriodicHMinusThreeFixedVolumeTightness.lean:93-106`)
   is literally that object at `N = n+1`, `a = L/(n+1)`, and
   `…FixedVolumeFreeFieldProbabilityMeasure_toMeasure` (`:136-152`) identifies it with
   `periodicHMinusThreeFiniteSourceMeasure` **unconditionally**.
3. `periodicHMinusThreeFiniteSourceCylinderLaw_eq_familyEvalLaw`
   (`…/PeriodicHMinusThreeCylinderConvergence.lean:240-249`) identifies the finite-source *cylinder*
   laws with the laws of the finite family evaluated against `physicalGJMeasure`, again
   **unconditionally**; the version that needs `hinput` is the *full-carrier* identity
   `…FiniteSourceCylinderLaw_eq_latticeCylinderLaw` (`:222-239`) and
   `…FiniteSourceFourierLift_map_eq_latticeMeasure` (`…/PeriodicHMinusThreeFourierMeasure.lean:449-474`).
4. Hence the D58/D59/D63 chain never mentions the input, and
   `proof_graph/scopes/PPHI2_FIXED_VOLUME_FREE_FIELD_MEASURE_LIMIT.yaml:13-14` states exactly this:
   "The stronger abstract `PeriodicHMinusThreeLiftMeasureInput` interface for arbitrary physicalGJ
   pushforwards is not a premise of this theorem." The Lean evidence for that scope sentence is
   points 1-3 above.

Declared-but-never-used hypothesis predicates (each occurs exactly once, at its own definition, so no
theorem consumes them — a referee should be told they are dead declarations, not silent assumptions):

| predicate | sole occurrence |
|---|---|
| `PeriodicHMinusTwoLiftInput` | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicComplexFourierLift.lean:28-33` |
| `PeriodicHMinusTwoDiscreteLiftInput` | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicComplexFourierLift.lean:63-70` |
| `PeriodicHMinusTwoToHMinusThreeCarrierInclusionInput` | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicNegativeSobolevCarriers.lean:39-41` |
| `PeriodicFullSpaceWeakLimitBridge` / `PeriodicFullSpaceWeakConvergenceInput` | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicFullSpaceWeakConvergence.lean:11`, `:39` (module outside both closures, `§5.iii`) |

Two hypothesis predicates that *are* consumed but also *discharged* on the live path, so they are not
gaps: `PeriodicHMinusTwoToHMinusThreeWeightRatioInput`
(`…/PeriodicNegativeSobolevTopologyInterfaces.lean:25-28`) is proved outright as
`periodicHMinusThree_weight_ratio_tendsto_zero` (`:30`), and
`PeriodicHMinusThreeCylinderBorelGenerationInput` (`…/PeriodicHMinusThreeCylinderBorelUniqueness.lean:54-56`)
is proved outright as `periodicHMinusThree_cylinder_sigma_eq_borel_of_polish` (D32) and instantiated
at `…/PeriodicHMinusThreeWeakLimitMarginal.lean:86-89`.

Superseded interface architecture (a reader must not quote these as the result). Four modules state the
Prokhorov extraction and the cylinder identification as **inputs** and derive the whole-sequence limit
from them; the current chain obtains the same extraction as a theorem (D54) and the cylinder
identification as a theorem (D59). All four are outside both contracts' closures:

| module | input structure(s) | derived theorem |
|---|---|---|
| `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicHMinusThreeProkhorovWeakConvergence.lean` | `PeriodicHMinusThreeProkhorovSubsequenceIdentificationInput` (`:15-23`), `PeriodicHMinusThreeFullWeakConvergenceInput` (`:39-48`), `PeriodicHMinusThreeProkhorovIdentificationData` (`:64-85`) | `periodicHMinusThree_probabilityMeasure_tendsto_of_prokhorov_subsequence_identification` (`:28`), `…_full_probabilityMeasure_tendsto` (`:54`), `…_of_prokhorov_extraction_and_cylinder_identification` (`:103`) |
| `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicHMinusThreeFreeFieldCandidate.lean` | `PeriodicHMinusThreeFreeFieldExistenceInput` (`:12-30`) | `periodicHMinusThreeFreeFieldCandidate` (`:34-37`), `…_has_expected_finite_fourier_marginals` (`:41`) |
| `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicHMinusThreeMarginalUniqueness.lean` | takes `hpolish` and the existence input | `periodicHMinusThree_subsequence_limit_eq_free_of_cylinder_marginals` (`:13-28`) |
| `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicFreeFieldFinalTheorem.lean` | `PeriodicFreeFieldFinalData` (`:8-29`), whose fields include `tightness_input`, `finite_marginal_input`, `cylinder_borel_input`, `subsequential_identification_input` (`:25-29`) | `latticeFreeFieldMeasure_tendsto_periodicFreeGaussian` (`:35-48`) — its conclusion is byte-for-byte its own hypothesis `hfinal` and its proof is `exact hfinal` (`:48`) |

### (ii) `not_included` of both scope files, quoted

`proof_graph/scopes/PPHI2_FIXED_VOLUME_COVARIANCE_LIMIT.yaml:19-22`:

> "No equivalence with a pre-existing distribution-defined Sobolev type or strong unbounded Laplacian domain theorem is asserted."
>
> "No limiting probability measure, interacting ultraviolet limit, or OS reconstruction is constructed by this tested-covariance theorem."

`proof_graph/scopes/PPHI2_FIXED_VOLUME_FREE_FIELD_MEASURE_LIMIT.yaml:16-21`:

> "No equivalence with a pre-existing distribution-defined Sobolev space or strong unbounded Laplacian domain theorem is asserted."
>
> "The separate identity theorem for the abstract physicalGJ pushforward `periodicHMinusThreeLatticeMeasure` remains conditional on `PeriodicHMinusThreeLiftMeasureInput`; this condition is not a premise of the fixed-volume Fourier-pushforward convergence theorem."
>
> "No interacting ultraviolet limit or Osterwalder-Schrader reconstruction is proved by this free-field measure limit."

The second of these three is borne out exactly by §5(i) points 1-3. The third also has a witness in
the tree: the OS-related modules (`OSGaussian`, `OSPositivity`, `OSReflectionLimit`,
`formal/lean/s6/pphi2_clean/AImathPPhi2Clean/OSReflectionLimit.lean`) are not in the import closure of
either contract (command in `§6`).

### (iii) Modules not reachable from the package root aggregator

`formal/lean/s6/pphi2_clean/AImathPPhi2Clean.lean` has **57** lines and **57** imports, one per line
(`:1-57`), out of 89 package modules. The import graph is acyclic and self-consistent (no import names
a module absent from disk, and there are no duplicate imports). Measured (`§6`):

| quantity | value |
|---|---|
| package modules under `AImathPPhi2Clean/` | 89 |
| direct imports in `formal/lean/s6/pphi2_clean/AImathPPhi2Clean.lean` | 57 |
| modules transitively reachable from the root file | 81 |
| modules **not** reachable from the root file at all | 8 |
| modules in the import closure of the two contracts | 62 |
| modules in the closure of the contracts but missing from the root file's direct import list | 26 |

The eight modules that the root file does not reach, transitively:

| module | inside a contract closure? | why it matters |
|---|---|---|
| `PeriodicHMinusThreeWeakLimitMarginal` | **yes** (it is listed in `formal/lean/challenges/_registry.yaml:39`, and holds D57, D60, D61, D62, D63) | **Six of the seven registered measure-limit theorems are declared only here.** Since the root file does not import it, and the on-disk axiom audit imports only the root (`…/audit/finite_lattice_all_declarations_interface.lean:1`), those six declarations cannot appear in any local transcript — which is exactly what is observed (`§4.2`): the footprint evidence for them is the server-side paper transcript only. |
| `PeriodicHMinusThreeProkhorovSubsequence` | **yes** (holds D43 and D54) | the Prokhorov extraction theorem is likewise not in the local build. |
| `PeriodicHMinusThreeFreeFieldCandidate` | no | superseded interface (§5.i). |
| `PeriodicHMinusThreeMarginalUniqueness` | no | superseded interface. |
| `PeriodicHMinusThreeProkhorovWeakConvergence` | no | superseded interface. |
| `PeriodicFreeFieldFinalTheorem` | no | vacuous wrapper `exact hfinal` (§5.i). |
| `PeriodicFullSpaceWeakConvergence` | no | abstract bridge only. |
| `PeriodicInfiniteGaussianMeasure` | no | not used by either statement. |

Note the precise wording: the *declarations* exist and are well-formed source; what is missing is a
local build path to them. Both contracts declare `remote_only: true` with a separate Lake project
(`formal/lean/challenges/_registry.yaml:28-34`, `:48-56`), so the local root build was evidently never
intended to be the authority — but a paper that says "the package root builds all 89 modules and the
audit covers every declaration" would be wrong, and the numbers above are the ones to quote instead.
The other 24 of those 26 *are* reachable transitively through other modules (the two that are not are
`PeriodicHMinusThreeWeakLimitMarginal` and `PeriodicHMinusThreeProkhorovSubsequence`, the first two rows
of the table above), so the 81/89 figure is the honest reachability statement.

### (iv) Other steps a referee would call unsupported or over-claimed

| # | item | pointer |
|---|---|---|
| 1 | **Vacuous final theorem.** `latticeFreeFieldMeasure_tendsto_periodicFreeGaussian` concludes its own hypothesis `hfinal`; the proof is `exact hfinal`. If a paper cites this as "the final theorem", the citation is empty. It is outside both closures and outside the root build. | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicFreeFieldFinalTheorem.lean:44-48` |
| 2 | **`liftedMeasure` is a structure field, not a construction.** See T18 in `§3`. | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicFreeFieldFinalTheorem.lean:18-21` |
| 3 | **The total lift's zero convention is not proved null.** `periodicHMinusThreeTotalCarrierLift` sends the (possibly non-null) exceptional set to `0`; the docstring says the nullity is not asserted. The measure chain never relies on it (it uses the finite-source lift, §5(i)), but any statement about the *physicalGJ* pushforward on the whole carrier does rely on it. | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicHMinusThreeFourierMeasure.lean:40-47` |
| 4 | **The carrier is 2-dimensional only**, while the registered covariance theorems are stated for arbitrary `d`. Do not present the measure limit in dimension `d > 2`. | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicHMinusThreeCompletion.lean:10`; `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicFourierCovarianceLimit.lean:1457-1465` |
| 5 | **`…_weak_limit_unique` is Hausdorff uniqueness, not identification.** It says two limits of the same filter agree; the characterisation by cylinder marginals is D61 + D57. Quoting D62 as "the limit is unique, hence characterised" reverses the logic. | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicHMinusThreeWeakLimitMarginal.lean:190-198` |
| 6 | **Stale docstring on the existence target.** `periodicHMinusThreeFixedVolumeFreeFieldWeakLimitExists` is documented as a "target … not asserted here as a theorem", but that exact proposition is proved as D60. The docstring is a leftover, not a gap; the paper should quote D60, not the docstring. | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicHMinusThreeFixedVolumeTightness.lean:126-132` versus `…/PeriodicHMinusThreeWeakLimitMarginal.lean:124-127` |
| 7 | **Name collision on `latticeCovarianceGJ`.** The spectral object used by all theorems (`…/ConcreteLatticeCovariance.lean:17`) and an unrelated field-driven interface (`…/LatticeGaussianContinuumConsumer.lean:222`) share the name; the latter even documents that the upstream spectral `T = Q^{-1/2}` "is not present here" as a construction input. Cite by module, never bare. | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/LatticeGaussianContinuumConsumer.lean:220-228` |
| 8 | **The Fourier-series target and the resolvent target are identified only through D19.** If a paper equates "the limit of the covariance node" with "the weak resolvent pairing", it must cite `torusFourierGreenPairing_eq_physicalTorusResolventPairing`; the covariance-limit module itself flags the identification as "a separate operator theorem". | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicFourierCovarianceLimit.lean:1302-1308`; `…/PeriodicTorusResolventLimit.lean:35-65` |
| 9 | **`IsFlatTorusPeriodic` is a hypothesis of D12/D20 but not of D19.** D19 holds for arbitrary bounded continuous tests; D12/D13/D14 do not. Restating the covariance limit "for every bounded continuous test" overstates the formalized statement. | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicFourierCovarianceLimit.lean:1457-1460` versus `…/PeriodicTorusResolventLimit.lean:35-39` |
| 10 | **`PeriodicFullHMinusTwoTrace` still exposes a zero-mode hypothesis** (`PeriodicHMinusTwoZeroModeTraceInput`, `:10-13`) that the uniform-in-`n` trace bound of D40 does not consume; the live trace route goes through `…/PeriodicFullHMinusTwoTraceConcrete.lean:13` (`periodicHMinusTwoFullLiftTrace_concrete_le`). Do not quote the conditional trace summation theorem as the fixed-volume bound. | `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicFullHMinusTwoTrace.lean:14-20` |
| 11 | **The registered node-level residue is not a mathematical gap here**: both nodes are listed as `unwired` — no `requires` edge consumes them — so the two contracts currently affect no milestone closure. That is a governance fact, not a Lean fact, and it is recorded by the project itself. | `formal/lean/challenges/_registry.yaml:385-390` |
| 12 | **Nothing in this ledger certifies a compiled build.** No build of `formal/lean/s6/pphi2_clean` was run by this note; the on-disk `audit/*.log` build logs are older than several of the modules they would have to cover (e.g. `…/audit/full-build-r27-final.log`, mtime 2026-10, versus `…/PeriodicHMinusThreeWeakLimitMarginal.lean`, 2026-11-01). Build status is `UNVERIFIED-BY-THIS-NOTE`. | `formal/lean/s6/pphi2_clean/audit/full-build-r27-final.log`; `formal/lean/s6/pphi2_clean/AImathPPhi2Clean/PeriodicHMinusThreeWeakLimitMarginal.lean` |

---

## §6 Numbers

All numbers below were computed by this note on **2026-11-02** from `E:\study\AImath`, with the exact
commands shown. Line counts use `str.splitlines()` semantics (a file with `n` LF bytes and a trailing
newline has `n` lines); all package files are LF-only with no CR bytes (checked, see command 1).

**Command 1 — module and line counts, `audit/` counts, root-import count, `sorry`/`axiom` counts.**

```text
cd E:\study\AImath
python - (stdin)
  import pathlib, re
  base = pathlib.Path('formal/lean/s6/pphi2_clean')
  lib  = sorted((base/'AImathPPhi2Clean').glob('*.lean'))
  aud  = sorted((base/'audit').glob('*.lean'))
  lines = lambda ps: sum(len(p.read_bytes().decode('utf-8').splitlines()) for p in ps)
  BLOCK = re.compile(r'/-.*?-/', re.S); LINE = re.compile(r'--[^\n]*')
  strip = lambda t: LINE.sub('', BLOCK.sub('', t))
  s=a=0
  for p in lib:
      b = strip(p.read_text(encoding='utf-8'))
      s += len(re.findall(r'\bsorry\b', b)); a += len(re.findall(r'^\s*axiom\s+\w', b, re.M))
  root = (base/'AImathPPhi2Clean.lean').read_text(encoding='utf-8').splitlines()
  print(len(lib), lines(lib), len(aud), lines(aud), s, a,
        len(root), sum(1 for l in root if l.startswith('import AImathPPhi2Clean.')))
```

Result: `89 13437 132 1292 0 0 57 57` — i.e. 89 modules / 13437 lines in the package, 132 probe files /
1292 lines in `audit/`, 0 comment-stripped `sorry`, 0 comment-stripped project `axiom`, root aggregator
57 lines with 57 imports. The single naive `axiom`-shaped hit is prose at
`formal/lean/s6/pphi2_clean/AImathPPhi2Clean/NelsonLayerCake.lean:85`. Independent cross-check: the
paper's own generator emits the same two headline numbers
(`paper/PPHI2_FIXED_VOLUME_COMPLETE/generated/metrics.tex:8-10`:
`\NumCleanModules{89}`, `\NumCleanLines{13437}`, `\NumAuditProbes{132}`).

**Command 2 — import graph, contract closures, root reachability.**

```text
cd E:\study\AImath
python - (stdin)
  import pathlib
  root = pathlib.Path('formal/lean/s6/pphi2_clean/AImathPPhi2Clean')
  mods = {p.stem: p for p in root.glob('*.lean')}
  imp  = {m: [l.split('AImathPPhi2Clean.',1)[1].strip()
              for l in p.read_text(encoding='utf-8').splitlines()
              if l.startswith('import AImathPPhi2Clean.')] for m,p in mods.items()}
  top  = pathlib.Path('formal/lean/s6/pphi2_clean/AImathPPhi2Clean.lean')
  direct = [l.split('AImathPPhi2Clean.',1)[1].strip()
            for l in top.read_text(encoding='utf-8').splitlines()
            if l.startswith('import AImathPPhi2Clean.')]
  def closure(seed):
      seen, stack = set(), list(seed)
      while stack:
          c = stack.pop()
          if c in seen or c not in mods: continue
          seen.add(c); stack.extend(imp.get(c, []))
      return seen
  cov = closure(['PeriodicFourierCovarianceLimit'])
  mea = closure(['PeriodicHMinusThreeTopologyBorel','PeriodicHMinusThreeWeakLimitMarginal'])
  print(len(cov), len(mea), len(cov|mea), len(closure(direct)), sorted(set(mods)-closure(direct)))
```

Result: covariance contract closure 22 modules; measure contract closure 62; union 62; **81** modules
transitively reachable from the root file; the 8 unreachable modules are exactly
`PeriodicFreeFieldFinalTheorem`, `PeriodicFullSpaceWeakConvergence`,
`PeriodicHMinusThreeFreeFieldCandidate`, `PeriodicHMinusThreeMarginalUniqueness`,
`PeriodicHMinusThreeProkhorovSubsequence`, `PeriodicHMinusThreeProkhorovWeakConvergence`,
`PeriodicHMinusThreeWeakLimitMarginal`, `PeriodicInfiniteGaussianMeasure`. No import names a module
absent from disk and no import is duplicated.

**Command 3 — the one doc-comment `axiom` hit and the `a`-power search quoted in T12.**

```text
cd E:\study\AImath
Select-String -Path 'formal\lean\s6\pphi2_clean\AImathPPhi2Clean\*.lean' -Pattern '^\s*axiom\s+\w'
python - (stdin)  # regex: a\s*\*\s*d\s*/\s*2 | a\s*\^\s*\(d\s*/\s*2\) | \bd\s*/\s*2\s*\*
```

Result: one hit, `NelsonLayerCake.lean:85` ("axiom asserts." — prose inside a comment); zero
occurrences of an `a·d/2`-shaped factor anywhere in the package.

**Command 4 — declaration line numbers quoted in `§2`/`§3`.**

```text
cd E:\study\AImath
python - (stdin)  # regex over each module:
#   (?:noncomputable )?(?:theorem|def|structure|abbrev|lemma|instance)\s+([A-Za-z0-9_.]+)
#   -> file:line for a fixed list of 55 names
```

Result: every line number in `§2` and `§3` was produced by that index, not by eye. Counts of this
note's own content: **63 declarations** logged in `§2` (D01-D63, contiguous, no gaps), **23 definitions**
logged in `§3` (T1-T23), 25 modules inventoried in `§1`.

**Environment facts recorded, not claimed.** Lean toolchain `v4.34.0-rc2` is what the registry and the
transcript header say (`formal/lean/challenges/_registry.yaml:19,32-34`;
`paper/PPHI2_FIXED_VOLUME_COMPLETE/ext/axiom_transcript.txt:5`); this note did not run Lean and makes
no build claim (`§4.3`, `§5.iv` #12).
