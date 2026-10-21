module

public import KumarNivat.PeriodLattice
public import Mathlib.Algebra.Ring.GeomSum

@[expose] public section

namespace KumarNivat

-- enlarging a directional period preserves its binomial divisor.
theorem binomial_dvd_positive_multiple {K : Type*} [CommRing K] (v : Site) (n : ℕ) :
    (binomial v : Laurent K) ∣ binomial ((n : ℤ) • v) := by
  have hpow : (AddMonoidAlgebra.single v 1 : Laurent K) ^ n =
      AddMonoidAlgebra.single ((n : ℤ) • v) 1 := by
    simp
  have hdiv := sub_one_dvd_pow_sub_one (AddMonoidAlgebra.single v 1 : Laurent K) n
  rw [hpow] at hdiv
  exact hdiv

-- nonzero scalar multiples preserve independence of the two periods.
theorem determinant_zsmul (v w : Site) (a b : ℤ) :
    determinant (a • v) (b • w) = a * b * determinant v w := by
  simp [determinant]
  ring

-- choose one enlarged period that fixes both the reference and the remainder.
theorem common_period_multiple_pair {A : Type*} (B ρ : Site → A)
    (hB : FullyPeriodic B) (hρ : FullyPeriodic ρ) (v : Site) :
    ∃ n : ℕ, 0 < n ∧ IsPeriod B ((n : ℤ) • v) ∧ IsPeriod ρ ((n : ℤ) • v) := by
  obtain ⟨b, hb, hpB⟩ := hB.exists_period_multiple v
  obtain ⟨r, hr, hpρ⟩ := hρ.exists_period_multiple v
  refine ⟨b * r, Nat.mul_pos hb hr, ?_, ?_⟩
  · convert hpB.zsmul (r : ℤ) using 1
    ext <;> simp <;> ring
  · convert hpρ.zsmul (b : ℤ) using 1
    ext <;> simp <;> ring

end KumarNivat
