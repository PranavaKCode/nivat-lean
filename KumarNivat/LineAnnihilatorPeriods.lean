module

public import KumarNivat.FiniteRecurrence
public import KumarNivat.LineOperators
public import KumarNivat.PeriodBinomials

@[expose] public section

namespace KumarNivat

-- a directional annihilator with nonzero endpoints gives one common period on every line.
theorem line_annihilator_period {K : Type*} [Field K]
    (c : Site → K) (hc : (Set.range c).Finite) (E p : Site)
    (t : ℕ) (α : Fin (t + 1) → K) (hfirst : α 0 ≠ 0) (hlast : α (Fin.last t) ≠ 0)
    (hann : laurentAct (lineOperator E p t α) c = 0) :
    IsPeriod c ((((Set.range c).ncard ^ t).factorial : ℤ) • p) := by
  exact finite_range_recurrence_period c hc p t α hfirst hlast
    (lineRecurrence_of_lineOperator E p t α c hann)

-- two independent directional eliminants complete the finite-image part of lemma 2.3.
theorem fullyPeriodic_of_independent_line_annihilators {K : Type*} [Field K]
    (c : Site → K) (hc : (Set.range c).Finite) (E₁ E₂ p q : Site)
    (hdet : determinant p q ≠ 0) (t₁ t₂ : ℕ)
    (α₁ : Fin (t₁ + 1) → K) (α₂ : Fin (t₂ + 1) → K)
    (hfirst₁ : α₁ 0 ≠ 0) (hlast₁ : α₁ (Fin.last t₁) ≠ 0)
    (hfirst₂ : α₂ 0 ≠ 0) (hlast₂ : α₂ (Fin.last t₂) ≠ 0)
    (hann₁ : laurentAct (lineOperator E₁ p t₁ α₁) c = 0)
    (hann₂ : laurentAct (lineOperator E₂ q t₂ α₂) c = 0) : FullyPeriodic c := by
  let M := ((Set.range c).ncard ^ t₁).factorial
  let N := ((Set.range c).ncard ^ t₂).factorial
  have hM : (M : ℤ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero _)
  have hN : (N : ℤ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero _)
  refine ⟨(M : ℤ) • p, (N : ℤ) • q, ?_, ?_, ?_⟩
  · rw [determinant_zsmul]
    exact mul_ne_zero (mul_ne_zero hM hN) hdet
  · exact line_annihilator_period c hc E₁ p t₁ α₁ hfirst₁ hlast₁ hann₁
  · exact line_annihilator_period c hc E₂ q t₂ α₂ hfirst₂ hlast₂ hann₂

end KumarNivat
