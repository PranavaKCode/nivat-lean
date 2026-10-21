module

public import KumarNivat.PeriodLattice

@[expose] public section

namespace KumarNivat

-- a finite convolution operator commutes with every directional difference.
theorem laurentAct_difference {K : Type*} [CommRing K]
    (f : Laurent K) (v : Site) (c : Site → K) :
    laurentAct f (difference v c) = difference v (laurentAct f c) := by
  rw [← laurentAct_binomial, ← laurentAct_mul, mul_comm,
    laurentAct_mul, laurentAct_binomial]

-- a period of the common filtered remainder annihilates the transverse defect.
theorem factor_annihilates_defect {K : Type*} [CommRing K]
    (c : Site → K) (φ ψ f : Laurent K) (v : Site)
    (hφ : φ = ψ * f) (hperiod : IsPeriod (laurentAct φ c) v) :
    laurentAct ψ (difference v (laurentAct f c)) = 0 := by
  rw [laurentAct_difference, ← laurentAct_mul, ← hφ]
  funext g
  exact sub_eq_zero.mpr (hperiod g)

-- a non-fully-periodic directional filter has a nonzero defect in every independent direction.
theorem exists_nonzero_transverse_defect {K : Type*} [AddGroup K]
    (A : Site → K) (v w : Site) (hdet : determinant v w ≠ 0)
    (hp : IsPeriod A v) (hnot : ¬ FullyPeriodic A) :
    ∃ g, difference w A g ≠ 0 := by
  by_contra hn
  have hw : IsPeriod A w := by
    intro g
    apply sub_eq_zero.mp
    by_contra hne
    exact hn ⟨g, hne⟩
  exact hnot ⟨v, w, hdet, hp, hw⟩

end KumarNivat
