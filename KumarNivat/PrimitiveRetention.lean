import KumarNivat.PrimitiveDirections
import KumarNivat.PeriodBinomials

namespace KumarNivat

-- two independent regional periods are the half-plane periodicity excluded by the reference.
def FullyRegionallyPeriodic {A : Type*} (w : Site → A) (H : Set Site) : Prop :=
  ∃ u v : Site, determinant u v ≠ 0 ∧ RegionalPeriod w H u ∧ RegionalPeriod w H v

-- lemma 8.3 now derives the parallel-period restriction from primitivity and the reference hypothesis.
theorem nonperiodic_of_primitive_retained_disagreement {A : Type*} (θ w : Site → A)
    (R H : Set Site) (a : Site) (hprimitive : Int.gcd a.1 a.2 = 1)
    (l : ℕ) (hl : 0 < l) (hw : IsPeriod w ((l : ℤ) • a))
    (hagree : ∀ g ∈ R, θ g = w g) (htravel : BackwardCofinal R H a)
    (hnotFull : ¬ FullyRegionallyPeriodic w H) (hfail : ∃ g ∈ H, θ g ≠ w g) :
    ¬ ∃ p : Site, p ≠ 0 ∧ IsPeriod θ p := by
  obtain ⟨τ, _ht, hker⟩ := primitive_direction_coordinate a hprimitive
  apply nonperiodic_of_retained_disagreement θ w R H a l hl hw hagree htravel _ hfail
  intro p hp
  have hdet : determinant a p = 0 := by
    by_contra hn
    apply hnotFull
    refine ⟨(l : ℤ) • a, p, ?_, fun g _hg _hgl => hw g, hp⟩
    have he : determinant ((l : ℤ) • a) p = (l : ℤ) * determinant a p := by
      simpa only [one_smul, mul_one] using determinant_zsmul a p (l : ℤ) 1
    rw [he]
    exact mul_ne_zero (by exact_mod_cast Nat.ne_of_gt hl) hn
  exact ⟨τ p, hker p hdet⟩

end KumarNivat
