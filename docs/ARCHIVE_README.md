# Finite periodic-lattice Gaussian covariance in clean types

This package isolates the finite periodic lattice construction from GaussianField at commit `d63a28568a75d99f6cb27af1f888a49a69855a66` and connects it to the AImath clean Gaussian and weak-dual interfaces. It uses Lean `v4.34.0-rc2` and the Mathlib revision pinned by the Lake manifest.

The site type is `Fin d → ZMod N`. The mass operator is `Q = -Δ_a + mass²`, with `a > 0`, `mass > 0` and `N ≠ 0`. The migrated spectral data come from the Hermitian matrix of this concrete operator; positive eigenvalues are proved from its positive definiteness.

The clean factor `latticeCovarianceGJ` takes values in the finite Euclidean space on the sites. Upstream records eigenbasis coefficients in ℓ² on natural numbers. These are different representations. `latticeCovarianceGJ_upstream_coefficients` proves the exact finite `lp.single` coefficient formula after changing from physical coordinates to the mass eigenbasis, and `spectralCoefficientEmbedding_inner` proves that this representation change preserves inner products. The source check verifies the computational definitions against the fixed, unmodified upstream commit.

The covariance measure is the pushforward of finitely many independent standard real Gaussians by a measurable map into the cylindrical weak dual. The following identities are proved with their L² and measurability requirements:

\[
\int \omega(f)\omega(g)\,d\mu_T=\langle Tf,Tg\rangle,
\]

\[
\int \omega(f)\omega(g)\,d\mu_{GJ}
=a^{-d}\sum_k\lambda_k^{-1}
  \Big(\sum_x e_k(x)f(x)\Big)\Big(\sum_x e_k(x)g(x)\Big).
\]

`latticeCovarianceGJ_pushforward_second_moment` proves the finite-site lift identity. `numberedLatticeCovarianceGJ_lift_second_moment` transports both test fields and Hilbert outputs along the explicit site numbering and proves the exact second moment through the original clean `latticeEmbedLift` on `Fin (Fintype.card (FinLatticeSites d N))`.

The lift accepts arbitrary continuous linear evaluation maps. A physical sampling or Riemann-sum convention must be supplied in these maps; the theorem does not silently add a lattice-volume weight.

The package does not assert equality of the full upstream infinite-noise Gaussian implementation with this finite-noise pushforward law. The proved correspondence is the concrete covariance factor under an inner-product-preserving change of representation, followed by the stated exact Gaussian moments. It contains no assertion about a continuum limit, infinite volume, exponential clustering, or an interacting measure.

Run the checks in the remote project root:

```bash
bash audit/run_finite_lattice_checks.sh /home/zhengyj/AImath-lean/S6Isserlis/.lake/packages/GaussianField
```

This builds the root, verifies the pinned source correspondence, checks the axiom allowlist for every public declaration in the finite-lattice migration, and runs the complete interface/firewall suite with parser negative controls. The allowlist is `propext`, `Classical.choice`, and `Quot.sound`.

The source correspondence checker is a separate provenance test. The representation, covariance, and moment identities themselves are Lean theorems; a textual source check is not used as a Lean proof.
