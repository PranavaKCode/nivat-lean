import KumarNivat.PeriodicRemainder

namespace KumarNivat

-- the unit inverse recovers the original array from its fully periodic filtered remainder.
theorem fullyPeriodic_of_unit_filter {K : Type*} [Field K]
    (c : Site → K) (φ : Laurent K) (hunit : IsUnit φ)
    (hperiodic : FullyPeriodic (laurentAct φ c)) : FullyPeriodic c := by
  obtain ⟨ψ, hψ⟩ := isUnit_iff_exists_inv.mp hunit
  have he : laurentAct ψ (laurentAct φ c) = c := by
    rw [← laurentAct_mul, mul_comm, hψ, laurentAct_one]
  exact he ▸ hperiodic.filtered ψ

-- a fully periodic array always has one nonzero global period.
theorem FullyPeriodic.exists_nonzero_period {A : Type*} (c : Site → A)
    (hperiodic : FullyPeriodic c) : ∃ v : Site, v ≠ 0 ∧ IsPeriod c v := by
  obtain ⟨u, v, hdet, hu, _hv⟩ := hperiodic
  refine ⟨u, ?_, hu⟩
  intro hz
  apply hdet
  simp [hz, determinant]

-- one surviving binomial direction would already give a global period of the original array.
theorem period_of_divisor_periodic_remainder {K : Type*} [Field K] [CharZero K]
    (c : Site → K) (hc : (Set.range c).Finite) (φ : Laurent K)
    (hperiodic : FullyPeriodic (laurentAct φ c)) (v : Site) (hv : v ≠ 0)
    (hdiv : φ ∣ binomial v) : ∃ w : Site, w ≠ 0 ∧ IsPeriod c w := by
  obtain ⟨q, hq, hp⟩ := hperiodic.exists_period_multiple v
  let w := (q : ℤ) • v
  have hw : w ≠ 0 := smul_ne_zero (by exact_mod_cast Nat.ne_of_gt hq) hv
  obtain ⟨a, ha⟩ := hdiv.trans (binomial_dvd_positive_multiple v q)
  have hφ : φ = φ * 1 := by rw [mul_one]
  have hglobal := filtered_period_of_periodic_remainder c hc φ φ 1 a w hφ ha hp
  exact ⟨w, hw, by simpa only [laurentAct_one] using hglobal⟩

-- nonperiodicity excludes both the zero-factor and single-direction alternatives in lemma 2.4.
theorem nonperiodic_divisor_obstructions {K : Type*} [Field K] [CharZero K]
    (c : Site → K) (hc : (Set.range c).Finite) (φ : Laurent K)
    (hperiodic : FullyPeriodic (laurentAct φ c))
    (hnot : ¬ ∃ v : Site, v ≠ 0 ∧ IsPeriod c v) :
    ¬ IsUnit φ ∧ ∀ v : Site, v ≠ 0 → ¬ φ ∣ binomial v := by
  constructor
  · intro hunit
    exact hnot (FullyPeriodic.exists_nonzero_period c (fullyPeriodic_of_unit_filter c φ hunit hperiodic))
  · intro v hv hdiv
    exact hnot (period_of_divisor_periodic_remainder c hc φ hperiodic v hv hdiv)

-- a proper nonunit factor prevents its complementary filtered array from becoming fully periodic.
theorem complementary_filter_not_fullyPeriodic {K : Type*} [Field K]
    (c : Site → K) (φ ψ f : Laurent K) (hφ : φ ≠ 0) (hprod : φ = ψ * f)
    (hψ : ¬ IsUnit ψ) (hcommon : ∀ a : Laurent K, laurentAct a c = 0 → φ ∣ a) :
    ¬ FullyPeriodic (laurentAct f c) := by
  have hf : f ≠ 0 := by
    intro hz
    apply hφ
    rw [hprod, hz, mul_zero]
  rintro ⟨u, v, hdet, hu, hv⟩
  have hdiv (w : Site) (hp : IsPeriod (laurentAct f c) w) : ψ ∣ binomial w := by
    have hann : laurentAct (binomial w * f) c = 0 := by
      rw [laurentAct_mul]
      exact (binomial_annihilates_iff_period (laurentAct f c) w).mpr hp
    have hd := hcommon (binomial w * f) hann
    rw [hprod] at hd
    exact (mul_dvd_mul_iff_right hf).mp hd
  exact hψ (independent_binomials_isRelPrime u v hdet (hdiv u hu) (hdiv v hv))

end KumarNivat
