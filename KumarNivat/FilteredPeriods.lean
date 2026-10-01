import KumarNivat.LaurentAlgebra

namespace KumarNivat

-- every finite operator samples a finite set of finite-image tuples.
theorem finite_range_act {K : Type*} [CommRing K] (c : Site → K)
    (hc : (Set.range c).Finite) (f : Stencil K) : (Set.range (act f c)).Finite := by
  classical
  let value : (f.support → K) → K := fun p => ∑ u : f.support, f u.val * p u
  apply ((patterns_finite_of_range c hc f.support).image value).subset
  rintro x ⟨g, rfl⟩
  refine ⟨fun u => c (g + u.val), ⟨g, rfl⟩, ?_⟩
  change (∑ u : f.support, f u.val * c (g + u.val)) = f.sum (fun u a => a * c (g + u))
  exact Finset.sum_coe_sort f.support (fun u : Site => f u * c (g + u))

-- filters preserve all periods of an array.
theorem IsPeriod.filtered {K : Type*} [CommRing K] {c : Site → K} {v : Site}
    (hp : IsPeriod c v) (f : Stencil K) : IsPeriod (act f c) v := by
  have hs : shift v c = c := funext hp
  intro x
  change shift v (act f c) x = act f c x
  rw [← act_shift, hs]

-- lemma 2.5's period follows from the periodic remainder and the factor divisibility.
theorem filtered_period_of_periodic_remainder {K : Type*} [Field K] [CharZero K]
    (c : Site → K) (hc : (Set.range c).Finite)
    (φ ψ f a : Laurent K) (v : Site)
    (hφ : φ = ψ * f) (hv : binomial v = ψ * a)
    (hremainder : IsPeriod (laurentAct φ c) v) : IsPeriod (laurentAct f c) v := by
  have hidentity : difference v (laurentAct f c) = laurentAct a (laurentAct φ c) := by
    rw [← laurentAct_binomial, ← laurentAct_mul]
    have he : binomial v * f = a * φ := by rw [hv, hφ]; ring
    rw [he, laurentAct_mul]
  apply finite_range_constant_increment (laurentAct f c) (finite_range_act c hc f.coeff) v
  rw [hidentity]
  exact hremainder.filtered a.coeff

end KumarNivat
