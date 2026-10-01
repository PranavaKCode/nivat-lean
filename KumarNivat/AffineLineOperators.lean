import KumarNivat.AxisOperators
import KumarNivat.LineFactorCoefficients

namespace KumarNivat

-- multiplying by a monomial translates the whole line block without changing its coefficients.
theorem single_mul_lineOperator {K : Type*} [CommRing K]
    (u E p : Site) (t : ℕ) (α : Fin (t + 1) → K) :
    AddMonoidAlgebra.single u (1 : K) * lineOperator E p t α =
      lineOperator (u + E) p t α := by
  classical
  simp only [lineOperator, Finset.mul_sum, AddMonoidAlgebra.single_mul_single,
    one_mul, add_assoc]

-- pull back any nonzero affine-line stencil and trim to its actual first and last coefficients.
theorem exists_affine_support_line_block {K : Type*} [CommRing K]
    (f : Laurent K) (hf : f ≠ 0) (E p : Site) (hp : p ≠ 0)
    (hline : (f.coeff.support : Set Site) ⊆ Set.range (fun n : ℤ => E + n • p)) :
    ∃ m : ℤ, ∃ t : ℕ, ∃ α : Fin (t + 1) → K,
      α 0 ≠ 0 ∧ α (Fin.last t) ≠ 0 ∧ f = lineOperator (E + m • p) p t α := by
  classical
  let f₀ := AddMonoidAlgebra.single (-E) (1 : K) * f
  have hinverse : AddMonoidAlgebra.single E (1 : K) * f₀ = f := by
    simp only [f₀, ← mul_assoc, AddMonoidAlgebra.single_mul_single,
      add_neg_cancel, one_mul, ← AddMonoidAlgebra.one_def]
  have hf₀ : f₀ ≠ 0 := by
    intro hz
    have he := hinverse
    rw [hz, mul_zero] at he
    exact hf he.symm
  have hsupp : (f₀.coeff.support : Set Site) ⊆ Set.range (directionLine p) := by
    intro u hu
    have hv : f.coeff (E + u) ≠ 0 := by
      simpa only [f₀, AddMonoidAlgebra.coeff_single_mul_apply, neg_neg, one_mul]
        using Finsupp.mem_support_iff.mp hu
    obtain ⟨n, hn⟩ := hline (Finsupp.mem_support_iff.mpr hv)
    exact ⟨n, add_left_cancel hn⟩
  let d := AddMonoidAlgebra.comapDomain (directionLine p)
    (integer_direction_multiple_injective p hp) f₀
  have hdaxis : axisOperator p d = f₀ :=
    AddMonoidAlgebra.mapDomain_comapDomain hsupp (integer_direction_multiple_injective p hp)
  have hd : d ≠ 0 := by
    intro hz
    apply hf₀
    rw [← hdaxis, hz, map_zero]
  obtain ⟨m, t, α, hfirst, hlast, hdblock⟩ := exists_reversible_laurent_block d hd
  have hblock : f₀ = lineOperator (m • p) p t α := by
    rw [← hdaxis, hdblock, axisOperator_block]
  exact ⟨m, t, α, hfirst, hlast, by rw [← hinverse, hblock, single_mul_lineOperator]⟩

end KumarNivat
