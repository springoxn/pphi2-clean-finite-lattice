# Four-dimensional periodic lattice Gaussian measure limit

> Release proof guide for the four-dimensional periodic raw-lift theorem. Paper estimates, finite CAS checks, and Lean results below have separate evidential roles. Current release evidence is in `release_evidence.json`; reproduce it with `python audit/check_fs4_release.py --lean`.

## Statement and model normalization

Fix `L > 0` and `mass > 0`. On `T_L^4 = (R/LZ)^4`, let `N` range through positive integers and set `a = L/N`. The lattice sites are `(Z/NZ)^4`. The nearest-neighbour operator is

`(-Delta_a f)(x) = a^-2 sum_j (2 f(x) - f(x+e_j) - f(x-e_j))`.

Its massive eigenvalue is

`lambda_N(p) = mass^2 + 4 a^-2 sum_j sin^2(pi p_j/N)`.

Let `G_N` denote the matrix inverse of `mass^2 - Delta_a`. The centered site Gaussian has covariance `a^-4 G_N(x,y)`. The factor `a^-4` is essential: omitting it makes the same atomic lift degenerate in the continuum limit. Define the raw atomic lift

`X_N = a^4 sum_x phi_x delta_[ax]`.

The continuum symbol is

`lambda(k) = mass^2 + (2*pi/L)^2 sum_j k_j^2`.

For real periodic tests, the desired covariance is

`Q(f,g) = L^-4 sum_k conj(F(f)(k)) F(g)(k) / lambda(k)`,

where `F(f)(k) = integral_[0,L]^4 f(x) exp(-2*pi*i*k.x/L) dx`.

The theorem `fs4PeriodicFixedVolume_weak_tendsto_free` in the server authority module `AImathPPhi2Clean/PeriodicFS4DProbeMoment.lean` proves

`fs4PeriodicFixedVolumeProbabilityMeasure L mass hL hmass -> fs4GaussianCarrierProbabilityMeasure L mass`

in the weak topology of probability measures on the weighted Fourier realization of `H^-4`. Its only explicit hypotheses are positivity of `L` and `mass`. The source sequence uses `N = n+1` and `a=L/N` and is the actual finite-source raw-lift pushforward. The target is an explicit measurable Gaussian-series pushforward, rather than a caller-supplied marginal or limit interface.

## Carrier and Fourier convention

For `r(k)=max_j |k_j|`, the Lean weight is `w_s(k)=(1+r(k))^(-2s)`. In source this is expressed as `max ‖(fs4SplitIndex k).1‖ ‖(fs4SplitIndex k).2‖`: each block has type `Fin 2 → ℤ`, whose Mathlib Pi norm is the supremum norm, so the expression is exactly the coordinate maximum. It is not the Euclidean block norm. A direct Lean instance check gives `‖(fun _ : Fin 2 => (1 : ℤ))‖ = 1`, and `Pi.norm_def` identifies the finite supremum. A stored carrier vector has coordinate `sqrt(w_4(k)) Xhat(k)` and belongs to `lp (fun _ : Fin 4 -> Z => C) 2`. The physical coefficient is recovered by division by the strictly positive weight square root. The real carrier is the closed subspace specified by `x(-k)=conj(x(k))`.

This is an equivalent Fourier Sobolev realization. With `q(k)=sum_j k_j^2`, one has `r^2 <= q <= 4r^2`, hence

`1+q <= 4(1+r)^2`, and `(1+r)^2 <= 2(1+q)`.

For `s >= 0` these imply

`4^(-s) w_s(k) <= (1+q(k))^(-s) <= 2^s w_s(k)`.

Thus the weighted norm induces the usual Fourier `H^-s` topology. For fixed positive `L`, the Bessel weight using `(2*pi/L)^2 q` is also equivalent. These elementary norm comparisons are paper arguments here; the theorem does not claim a separately packaged Lean isomorphism to a distribution-library Bessel-potential space. The frequency symbol itself uses the Euclidean sum of squares, even though the equivalent carrier weight uses a max norm.

The Lean complex probe is `cosine + I*sine`. The paper formulas and finite CAS probe use

`Xhat_N(k)=a^4 sum_x phi_x exp(-2*pi*i*k.x/N)=C_N(k)-i*S_N(k)`.

They are related by frequency reversal, or conjugation on the real carrier. Both `lambda_N` and `lambda` are even, so this convention change preserves the covariance symbol. The formal proof identifies cosine and sine evaluations directly; it does not infer a joint law from symmetry of individual sine laws.

## Mode identities and bounded verification

Finite character orthogonality gives the paper identities, with residues `p_N(k)=k mod N`,

`E[Xhat_N(k) conj(Xhat_N(l))] = L^4 1_{p_N(k)=p_N(l)} / lambda_N(p_N(k))`,

`E[Xhat_N(k) Xhat_N(l)] = L^4 1_{p_N(k)=-p_N(l)} / lambda_N(p_N(k))`.

The prefactor follows from `a^8 a^-4 N^-4 N^4 N^4=(aN)^4=L^4`. These formulas retain aliases and zero/Nyquist self-opposition. Distinct continuum labels need not be independent at finite N. For a fixed finite set, nontrivial collisions disappear once N exceeds every relevant nonzero coordinate of pairwise sums and differences.

The inequality `0 <= t^2-sin(t)^2 <= t^4/3` gives the paper dispersion estimate

`0 <= lambda(k)-lambda_N(p_N(k)) <= (4*pi^4*a^2/(3*L^4)) sum_j k_j^4`,

and the mass gap gives

`0 <= L^4/lambda_N(p_N(k))-L^4/lambda(k) <= (4*pi^4*a^2/(3*mass^4)) sum_j k_j^4`.

Correction recorded with the dimensional-bridge article: the earlier guide omitted `L^-4` in the dispersion error and retained a spurious `L^4` in the variance-error bound. The corrected formulas follow by substituting `pi*k_j/N = pi*a*k_j/L`. The article audit includes a small-volume negative control; the Lean sources and formal convergence theorem are unchanged.

This is an analytic fixed-mode estimate. Finite-grid checks validate bounded instances and scale bookkeeping, not the all-N statement. The exact raw complex moment formula remains a paper identity unless separately instantiated as a Lean theorem; the completed weak-limit proof does not require that stronger raw identity as an assumption.

Project Lean proves the sampled cosine/sine coefficient formulas, exact discrete real-mode Green pairings including merged zero/Nyquist supports, the physical covariance-to-Green-pairing bridge, and the fixed-mode covariance limit. The actual all-N complex probe bound used in the limit proof is

`E|Xhat_N(k)|^2 <= 2*mass^-2*L^4`,

obtained from the two real bounded test moments. It is valid uniformly in frequency and lattice scale at fixed physical volume.

## Four-dimensional carrier and tightness

`PeriodicFS4DSobolevWeights.lean` proves summability of `w_3` and `w_4` in four dimensions by splitting the integer lattice into two rank-two blocks and comparing with a product of summable block weights. No two-dimensional carrier is substituted for the four-dimensional one.

The finite-source H^-3 and H^-4 maps are finite sums of weighted point-mass Fourier sequences. They are measurable, have the weighted raw coefficient formulas, and lie in the conjugate-symmetric real carrier for every finite configuration. The actual carrier-valued map has no zero fallback. Its H^-3 norm squared equals the weighted raw coefficient sum. The proved integral/t-sum exchange and all-N probe bound yield

`sup_N E ||X_N||_(H^-3)^2 <= 2*mass^-2*L^4 sum_k w_3(k)`.

The inclusion from the H^-3 coefficient ball into H^-4 has uniformly small high-frequency tails and finite-dimensional low-frequency projections. Lean proves compactness of its closure, including the real slice. Markov's inequality transfers the uniform H^-3 bound to compact H^-4 tails of the actual pushforward laws. Carrier separability is proved using dense finite-support vectors. These ingredients establish the instantiated tightness and Prokhorov subsequence theorems.

A sharper paper estimate uses the exact mode identity and the Euclidean weight: `sum_k (1+|k|^2)^-3 <= 121`, by the shell count `(2r+1)^4-(2r-1)^4=64r^3+16r`. The resulting bound `121 L^4/mass^2` is not the Lean constant consumed by the tightness proof.

## Explicit target and its finite laws

Choose the canonical representative of each nonzero pair `{k,-k}` by the first nonzero coordinate being positive. For independent standard real Gaussians, set

`Xhat(0)=(L^2/mass) xi_0`,

`Xhat(k)=L^2 (xi_k+i eta_k)/(sqrt(2)*sqrt(lambda(k)))`,

and `Xhat(-k)=conj(Xhat(k))`.

The formal construction uses an explicit countable indexing of zero, cosine and sine directions. Absolute summability of their H^-4 norms gives an almost surely convergent Gaussian Hilbert series. Its measurable random-element law is `fs4GaussianCarrierMeasure`; the probability wrapper is `fs4GaussianCarrierProbabilityMeasure`. Real support is proved almost everywhere.

The unnormalized physical variances are

`E|Xhat(k)|^2=L^4/lambda(k)`,

`Var(C_k)=Var(S_k)=L^4/(2*lambda(k))` for nonzero canonical k,

and `Var(Xhat(0))=L^4/mass^2`.

Zero sine vanishes; the nonzero canonical real coordinates are independent. Lean proves the actual finite product Gaussian laws, then their Gaussianity, zero projected means and precise projected variances after conversion to Euclidean vectors. `fs4PhysicalCoordinateTest_covariance` evaluates the actual torus Green pairing for every pair of unified real-coordinate tags: the variance on the diagonal and zero off the diagonal. `fs4PhysicalFiniteMarginal_eq_resolventTarget` uses characteristic-function uniqueness to identify each finite injective physical marginal with the existing periodic-resolvent target measure.

## Full weak-limit assembly

The following are instantiated project Lean results in `PeriodicFS4DProbeMoment.lean`:

1. `fs4PhysicalRealCoordinate_finiteSource` includes the zero mode and identifies physical real coordinates of every lattice carrier lift with raw cosine/sine evaluations.
2. `fs4PhysicalFiniteProjection_latticeMeasure_eq_family` identifies the actual lattice carrier pushforward marginal with the physical test-family measure for every positive N.
3. `fs4PeriodicFixedVolume_finitePhysicalMarginal_tendsto` combines that equality, existing finite test-family convergence, and the identified candidate target.
4. `fs4Periodic_subsequence_limit_finitePhysicalMarginal` identifies finite real marginals of every weak sublimit by the continuous mapping theorem.
5. `fs4Periodic_subsequence_limit_realCarrier_ae` transfers real support to weak limits by Portmanteau on the open complement of the closed real carrier.
6. `fs4PhysicalCoordinateEncoding_injOn` reconstructs all Fourier coordinates on the real carrier from zero/canonical real coordinates. Its proof uses zero-mode reality and negative-frequency conjugation.
7. `fs4HminusFour_probabilityMeasure_ext_of_real_finite_marginals` promotes finite injective real marginals to equality of the full encoding pushforwards using measurable cylinders, then to equality of the original real-supported measures using measurable images on the Polish carrier.
8. `fs4Periodic_subsequence_limit_eq_free` identifies every Prokhorov sublimit with the constructed candidate.
9. `fs4PeriodicFixedVolume_weak_tendsto_free` applies Prokhorov to every subsequence and the filter subsequence criterion to conclude convergence of the full sequence.

The final theorem has only `L`, `mass`, and their positivity hypotheses. No caller-supplied tightness, separability, Borel-generation, target-law, or sublimit-identification premise remains. Negative and repeated complex labels require no additional independence assumption for uniqueness: injective canonical real-coordinate cylinders already determine the real-supported law.

## Verification boundary

The canonical server module was built and the final theorem's `#print axioms` checked under the project toolchain `v4.34.0-rc2`. The reported axioms are `propext`, `Classical.choice`, and `Quot.sound`. This is evidence about the actual theorem and its dependency cone, rather than a source-level `0 sorry` count.

The finite exact probe [fs4d_periodic_gaussian_limit_probe.py](../../audit/fs4d_periodic_gaussian_limit_probe.py) checks bounded character sums, alias and Nyquist cases, raw-lift Fourier convention, lattice/target normalization, covariance conversion, finite dispersion inequalities and negative controls. It is separate from the infinite-family Lean proof. The standard verification kernel is an additional project acceptance check; its live result is collected from the running tools rather than frozen into this document.

The published Lean files are a byte-exact export of the authoritative proof source. The release verifier binds them, their dependency lock, and the typed contract to a fresh build and axiom transcript. Historical archive evidence is kept separately and is not evidence that every later file was built at the original archive pin.

## Literature boundary

Cipriani and van Ginkel, [The discrete Gaussian free field on a compact manifold](https://arxiv.org/html/1809.03382v4), Theorems 1.1 and 1.4 and Remark 3.1, provide a distribution-valued precedent. Their massless mean-zero DGFF and Voronoi lift differ from the massive raw atomic lift here. Their strong Sobolev range includes d=4 and s=4, but their result is comparison material, not a premise of this theorem.

Sheffield, [Gaussian free fields for mathematicians](https://doi.org/10.1007/s00440-006-0050-1), supplies Fourier and nearest-neighbour background, without proving this exact massive raw-lift limit. Dello Schiavo, Herry, Kopfer and Sturm, [Polyharmonic Fields and Liouville Quantum Gravity Measures on Tori of Arbitrary Dimension: From Discrete to Continuous](https://arxiv.org/html/2302.02963), treat massless grounded polyharmonic fields and other extension maps; those covariance orders and convergence statements differ from the theorem here.

The published `PeriodicFourierCovarianceLimit.lean` chain supplies the model-matched covariance input. The actual four-dimensional carrier, explicit Gaussian target, tightness, cylinder uniqueness and full weak-limit assembly are established by the project Lean chain described above, independently of these literature comparisons.
