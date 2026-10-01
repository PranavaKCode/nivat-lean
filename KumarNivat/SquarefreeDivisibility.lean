import Mathlib.Algebra.Squarefree.Basic

namespace KumarNivat

-- a squarefree element divides another element once each of its prime factors does.
theorem squarefree_dvd_of_prime_factors {R : Type*} [CommMonoidWithZero R]
    [UniqueFactorizationMonoid R] [NormalizationMonoid R]
    (a b : R) (ha : a ≠ 0) (hsquare : Squarefree a)
    (hprime : ∀ p : R, Prime p → p ∣ a → p ∣ b) : a ∣ b := by
  classical
  by_cases hb : b = 0
  · rw [hb]
    exact dvd_zero _
  · apply (UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors ha hb).mpr
    have hnodup := (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors ha).mp hsquare
    apply (Multiset.le_iff_subset hnodup).mpr
    intro p hp
    have hpp := UniqueFactorizationMonoid.prime_of_normalized_factor p hp
    apply (UniqueFactorizationMonoid.mem_normalizedFactors_iff' hb).mpr
    exact ⟨hpp.irreducible, UniqueFactorizationMonoid.normalize_normalized_factor p hp,
      hprime p hpp (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hp)⟩

end KumarNivat
