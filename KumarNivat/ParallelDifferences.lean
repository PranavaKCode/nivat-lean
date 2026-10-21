module

public import KumarNivat.PeriodBinomials
public import KumarNivat.FilteredPeriods
public import KumarNivat.LineFactorCoefficients

@[expose] public section

namespace KumarNivat

-- reversing a difference direction changes the binomial only by a laurent unit.
theorem binomial_negative {K : Type*} [CommRing K] (v : Site) :
    (binomial (-v) : Laurent K) = -AddMonoidAlgebra.single (-v) 1 * binomial v := by
  simp [binomial, neg_mul, mul_sub, AddMonoidAlgebra.single_mul_single,
    AddMonoidAlgebra.one_def]
  ring

-- any integer multiple of a direction preserves the original binomial divisor.
theorem binomial_dvd_integer_multiple {K : Type*} [CommRing K] (v : Site) (n : ℤ) :
    (binomial v : Laurent K) ∣ binomial (n • v) := by
  have hneg (w : Site) : (binomial w : Laurent K) ∣ binomial (-w) := by
    refine ⟨-AddMonoidAlgebra.single (-w) 1, ?_⟩
    rw [binomial_negative]
    ring
  cases n with
  | ofNat m => exact binomial_dvd_positive_multiple v m
  | negSucc m =>
    change (binomial v : Laurent K) ∣ binomial (-((m + 1 : ℕ) : ℤ) • v)
    rw [neg_zsmul]
    exact (binomial_dvd_positive_multiple v (m + 1)).trans (hneg _)

-- a directional difference retains finite image under the same finite-operator action.
theorem finite_range_difference {K : Type*} [CommRing K]
    (c : Site → K) (hc : (Set.range c).Finite) (v : Site) :
    (Set.range (difference v c)).Finite := by
  have hf := finite_range_act c hc (binomial v).coeff
  change (Set.range (laurentAct (binomial v) c)).Finite at hf
  rw [laurentAct_binomial] at hf
  exact hf

-- finite image removes every repeated power of the same directional difference.
theorem period_of_binomial_power {K : Type*} [Field K] [CharZero K]
    (v : Site) (n : ℕ) (c : Site → K) (hc : (Set.range c).Finite) (hn : 0 < n)
    (hann : laurentAct ((binomial v : Laurent K) ^ n) c = 0) : IsPeriod c v := by
  induction n generalizing c with
  | zero => omega
  | succ n ih =>
    by_cases hz : n = 0
    · subst n
      rw [pow_one, laurentAct_binomial] at hann
      intro g
      exact sub_eq_zero.mp (congrFun hann g)
    · let d := difference v c
      have hd : (Set.range d).Finite := finite_range_difference c hc v
      have hnext : laurentAct ((binomial v : Laurent K) ^ n) d = 0 := by
        dsimp only [d]
        rw [← laurentAct_binomial, ← laurentAct_mul, ← pow_succ]
        exact hann
      have hp := ih d hd (by omega) hnext
      exact finite_range_constant_increment c hc v hp

-- two parallel nonzero lattice vectors have a common nonzero integer multiple.
theorem parallel_common_integer_multiple (p q : Site) (hp : p ≠ 0) (hq : q ≠ 0)
    (hparallel : determinant p q = 0) :
    ∃ a b : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ a • p = b • q := by
  by_cases hq₁ : q.1 = 0
  · have hq₂ : q.2 ≠ 0 := by
      intro hz
      exact hq (Prod.ext hq₁ hz)
    have hp₁ : p.1 = 0 := by
      have he : p.1 * q.2 = 0 := by simpa [determinant, hq₁] using hparallel
      exact (mul_eq_zero.mp he).resolve_right hq₂
    have hp₂ : p.2 ≠ 0 := by
      intro hz
      exact hp (Prod.ext hp₁ hz)
    refine ⟨q.2, p.2, hq₂, hp₂, ?_⟩
    apply Prod.ext
    · simp [hq₁, hp₁]
    · change q.2 * p.2 = p.2 * q.2
      ring
  · have hp₁ : p.1 ≠ 0 := by
      intro hz
      have he : p.2 * q.1 = 0 := by
        have he := hparallel
        simp only [determinant, hz, zero_mul, zero_sub, neg_eq_zero] at he
        exact he
      have hp₂ := (mul_eq_zero.mp he).resolve_right hq₁
      exact hp (Prod.ext hz hp₂)
    refine ⟨q.1, p.1, hq₁, hp₁, ?_⟩
    apply Prod.ext
    · change q.1 * p.1 = p.1 * q.1
      ring
    · change q.1 * p.2 = p.1 * q.2
      dsimp [determinant] at hparallel
      nlinarith

-- a product of two parallel differences reduces to one difference along their common multiple.
theorem collapse_parallel_differences {K : Type*} [Field K] [CharZero K]
    (c : Site → K) (hc : (Set.range c).Finite) (p q : Site)
    (hp : p ≠ 0) (hq : q ≠ 0) (hparallel : determinant p q = 0)
    (hann : laurentAct ((binomial p : Laurent K) * binomial q) c = 0) :
    ∃ h : Site, ∃ b : ℤ, b ≠ 0 ∧ h = b • q ∧ h ≠ 0 ∧ IsPeriod c h := by
  obtain ⟨a, b, ha, hb, he⟩ := parallel_common_integer_multiple p q hp hq hparallel
  let h := a • p
  have hqrep : h = b • q := he
  have hne : h ≠ 0 := smul_ne_zero ha hp
  have hdiv : (binomial p : Laurent K) * binomial q ∣ binomial h ^ 2 := by
    rw [pow_two]
    exact mul_dvd_mul (by simpa only [h] using binomial_dvd_integer_multiple p a)
      (by simpa only [hqrep] using binomial_dvd_integer_multiple q b)
  obtain ⟨f, hf⟩ := hdiv
  have hpower : laurentAct ((binomial h : Laurent K) ^ 2) c = 0 := by
    rw [hf, mul_comm, laurentAct_mul, hann, laurentAct_config_zero]
  exact ⟨h, b, hb, hqrep, hne, period_of_binomial_power h 2 c hc (by omega) hpower⟩

end KumarNivat
