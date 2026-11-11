# H^-3 endpoint for the actual 3D periodic Gaussian source

> status: ACTIVE · owner: PERIODIC3D_GAUSSIAN_RAW_LIFT_LIMIT · asof: 2026-11-11

The isolated pinned-release Lean endpoint is archived in `deliverables/20261111_periodic3d_hminus3_endpoint.zip`. It extends the actual finite 3D raw atomic lattice lifts from the historical H^-4 carrier to the weighted H^-3 carrier.

The compactness route is the preferred H^-2 route: every raw lattice lift has a finite H^-2 weighted coefficient energy, and the fixed-volume Gaussian expectation is bounded uniformly by

`2 * (mass⁻¹ ^ 2 * L ^ 3) * ∑' k, periodic3DHminusTwoWeight k`.

The closure of each bounded H^-2 ball, viewed in H^-3 weighted coordinates, is compact in the H^-3 carrier topology because the H^-3/H^-2 weight ratio tends to zero at high frequency. Markov's inequality therefore gives a uniform compact-tail estimate for the H^-3 pushforward laws and a fixed-volume Prokhorov subsequence.

The H^-3 limit is identified through the continuous injective weighted inclusion H^-3 → H^-4. The inclusion maps every actual finite H^-3 source lift to the historical H^-4 source lift. Existing H^-4 weak convergence then identifies the image of every H^-3 subsequential limit with the scaled 4D frequency-slice Gaussian target. Measurable embedding and injectivity give uniqueness of the H^-3 lift.

The finite H^-3 Fourier-family marginals are obtained by composing the existing physical real/sine projections with the H^-3→H^-4 inclusion. Their target law is the existing 3D resolvent target law. The separating-family theorem proves that equality of these finite marginals determines an H^-3 probability measure.

## Reproduction and audit

From the archive overlay, run:

```text
lake build AImathPPhi2Clean.Periodic3DHminusThreeMarginals
lake env lean AImathPPhi2Clean/Periodic3DHminusThreeMarginals.lean
```

The source endpoint was checked at `leanprover/lean4:v4.34.0-rc2`. The focused endpoint modules contain no `sorry`, `axiom`, or `admit`; their audited theorem axiom footprint is `[propext, Classical.choice, Quot.sound]`. The formal endpoint does not introduce a separate Mathlib `IsGaussian` predicate for the infinite-dimensional H^-3 measure. Gaussianity is characterized by the proved finite Fourier-family Gaussian marginals and the separating-family uniqueness theorem.

The historical 2D/4D article and the delivered 3D companion snapshots were preserved. The archive contains only the isolated Lean source overlay and reproduction metadata.
