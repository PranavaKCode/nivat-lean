module

public import KumarNivat.LineOperators
public import KumarNivat.RectangleQuotient

@[expose] public section

namespace KumarNivat

-- a nonzero integer direction has distinct integer multiples.
theorem integer_direction_multiple_injective (p : Site) (hp : p ≠ 0) :
    Function.Injective (fun n : ℤ => n • p) := by
  intro a b he
  by_cases hp₁ : p.1 = 0
  · have hp₂ : p.2 ≠ 0 := by
      intro hp₂
      exact hp (Prod.ext hp₁ hp₂)
    have he₂ := congrArg Prod.snd he
    change a * p.2 = b * p.2 at he₂
    exact mul_right_cancel₀ hp₂ he₂
  · have he₁ := congrArg Prod.fst he
    change a * p.1 = b * p.1 at he₁
    exact mul_right_cancel₀ hp₁ he₁

-- the coefficient at each exponent is the corresponding recurrence coefficient.
theorem lineOperator_coeff {K : Type*} [CommRing K] (E p : Site) (hp : p ≠ 0)
    (t : ℕ) (α : Fin (t + 1) → K) (i : Fin (t + 1)) :
    (lineOperator E p t α).coeff (E + (i.val : ℤ) • p) = α i := by
  classical
  have hinj : Function.Injective (fun j : Fin (t + 1) => E + (j.val : ℤ) • p) := by
    intro j l he
    apply Fin.ext
    have hz := integer_direction_multiple_injective p hp (add_left_cancel he)
    exact_mod_cast hz
  simp only [lineOperator, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    AddMonoidAlgebra.coeff_single, Finsupp.single_apply, hinj.eq_iff]
  simp

-- nonzero endpoint coefficients ensure the two segment endpoints occur in the factor support.
theorem lineOperator_endpoints_mem {K : Type*} [CommRing K] (E p : Site) (hp : p ≠ 0)
    (t : ℕ) (α : Fin (t + 1) → K) (hfirst : α 0 ≠ 0) (hlast : α (Fin.last t) ≠ 0) :
    E ∈ (lineOperator E p t α).coeff.support ∧
      E + (t : ℤ) • p ∈ (lineOperator E p t α).coeff.support := by
  constructor
  · apply Finsupp.mem_support_iff.mpr
    have he := lineOperator_coeff E p hp t α 0
    simpa using he.trans_ne hfirst
  · apply Finsupp.mem_support_iff.mpr
    exact (lineOperator_coeff E p hp t α (Fin.last t)).trans_ne hlast

-- normalized segment extrema are attained by genuine nonzero factor coefficients.
theorem lineOperator_box_extrema {K : Type*} [CommRing K]
    (E p : Site) (hp : p ≠ 0) (t r s : ℕ) (α : Fin (t + 1) → K)
    (hfirst : α 0 ≠ 0) (hlast : α (Fin.last t) ≠ 0)
    (hxlo : E.1 = 0 ∨ (E + (t : ℤ) • p).1 = 0)
    (hxhi : E.1 = (r : ℤ) ∨ (E + (t : ℤ) • p).1 = (r : ℤ))
    (hylo : E.2 = 0 ∨ (E + (t : ℤ) • p).2 = 0)
    (hyhi : E.2 = (s : ℤ) ∨ (E + (t : ℤ) • p).2 = (s : ℤ)) :
    BoxExtrema (lineOperator E p t α) r s := by
  have he := lineOperator_endpoints_mem E p hp t α hfirst hlast
  refine ⟨?_, ?_, ?_, ?_⟩
  · rcases hxlo with h | h
    · exact ⟨E, he.1, h⟩
    · exact ⟨E + (t : ℤ) • p, he.2, h⟩
  · rcases hxhi with h | h
    · exact ⟨E, he.1, h⟩
    · exact ⟨E + (t : ℤ) • p, he.2, h⟩
  · rcases hylo with h | h
    · exact ⟨E, he.1, h⟩
    · exact ⟨E + (t : ℤ) • p, he.2, h⟩
  · rcases hyhi with h | h
    · exact ⟨E, he.1, h⟩
    · exact ⟨E + (t : ℤ) • p, he.2, h⟩

end KumarNivat
