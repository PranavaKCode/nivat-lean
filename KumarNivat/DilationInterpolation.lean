import KumarNivat.PrimeDilation
import Mathlib.Algebra.Polynomial.Eval.Defs

namespace KumarNivat

-- expand a dilated operator using its original finite coefficient support.
theorem dilate_coefficient_sum {K : Type*} [CommRing K] (r : ℕ) (f : Laurent K) :
    dilate r f = ∑ u ∈ f.coeff.support, AddMonoidAlgebra.single (r • u) (f.coeff u) := by
  classical
  calc
    dilate r f = dilate r (f.coeff.sum AddMonoidAlgebra.single) :=
      congrArg (dilate r) (AddMonoidAlgebra.sum_coeff_single f).symm
    _ = _ := by rw [map_finsuppSum]; simp only [dilate_single, Finsupp.sum]

-- a progression exponent separates into one base monomial and a power of its dilated monomial.
theorem single_progression_exponent {K : Type*} [CommRing K]
    (r j : ℕ) (u : Site) (a : K) :
    AddMonoidAlgebra.single ((1 + j * r) • u) a =
      AddMonoidAlgebra.single u a * (AddMonoidAlgebra.single (r • u) 1 : Laurent K) ^ j := by
  simp [AddMonoidAlgebra.single_pow, AddMonoidAlgebra.single_mul_single, add_smul, mul_smul]

-- interpolation turns a combination of progression dilations into coefficientwise evaluations.
theorem operator_dilation_interpolation {K : Type*} [CommRing K]
    (r : ℕ) (f : Laurent K) (H : Polynomial (Laurent K)) :
    H.sum (fun j a => a * dilate (1 + j * r) f) =
      ∑ u ∈ f.coeff.support, AddMonoidAlgebra.single u (f.coeff u) *
        H.eval (AddMonoidAlgebra.single (r • u) 1) := by
  classical
  simp only [Polynomial.sum_def, dilate_coefficient_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [single_progression_exponent]
  ac_rfl

-- interpolation kills every nonconstant support monomial and leaves the selected coefficient.
theorem centered_integer_product_annihilator (f : Laurent ℤ) (c : Site → ℤ)
    (hf₀ : f.coeff 0 ≠ 0) (hc : (Set.range c).Finite) (hann : laurentAct f c = 0) :
    ∃ r : ℕ, 0 < r ∧
      laurentAct (∏ u ∈ f.coeff.support.erase 0, binomial (r • u)) c = 0 := by
  classical
  obtain ⟨B, hbound⟩ := exists_dilated_output_bound f c hc
  let r := B.factorial
  let S := f.coeff.support.erase 0
  let H : Polynomial (Laurent ℤ) :=
    ∏ u ∈ S, (Polynomial.C (AddMonoidAlgebra.single (r • u) 1) - Polynomial.X)
  let P : Laurent ℤ := ∏ u ∈ S, binomial (r • u)
  have hcomb : laurentAct (H.sum (fun j a => a * dilate (1 + j * r) f)) c = 0 := by
    rw [Polynomial.sum_def, laurentAct_sum]
    apply Finset.sum_eq_zero
    intro j hj
    rw [laurentAct_mul, annihilator_dilate_progression f c B hbound hann j,
      laurentAct_config_zero]
  have hroot (u : Site) (hu : u ∈ S) : H.eval (AddMonoidAlgebra.single (r • u) 1) = 0 := by
    dsimp only [H]
    rw [Polynomial.eval_prod]
    exact Finset.prod_eq_zero hu (by simp)
  have hunit : H.eval (AddMonoidAlgebra.single (r • (0 : Site)) 1) = P := by
    simp [H, P, binomial, Polynomial.eval_prod, AddMonoidAlgebra.one_def]
  have hid := operator_dilation_interpolation r f H
  rw [Finset.sum_eq_single 0] at hid
  · rw [hunit] at hid
    rw [hid, laurentAct_mul, laurentAct_single] at hcomb
    refine ⟨r, Nat.factorial_pos B, ?_⟩
    change laurentAct P c = 0
    funext g
    have he := congrFun hcomb g
    change f.coeff 0 * laurentAct P c (g + 0) = 0 at he
    rw [add_zero] at he
    exact (mul_eq_zero.mp he).resolve_left hf₀
  · intro u hu hne
    rw [hroot u (Finset.mem_erase.mpr ⟨hne, hu⟩), mul_zero]
  · intro hnot
    exact (hnot (Finsupp.mem_support_iff.mpr hf₀)).elim

end KumarNivat
