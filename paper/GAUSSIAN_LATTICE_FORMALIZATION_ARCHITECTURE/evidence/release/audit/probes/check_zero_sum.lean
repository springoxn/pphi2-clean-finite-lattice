import AImathPPhi2Clean.PeriodicHMinusTwoWeight
example : Summable (fun k : Fin 2 → ℤ => if k = 0 then (1 : ℝ) else 0) := by
  apply summable_of_hasFiniteSupport
  apply (Set.finite_singleton (0 : Fin 2 → ℤ)).subset
  intro k hk
  simp_all
