import KumarNivat.LaurentMaps
import Mathlib.Algebra.Squarefree.Basic

namespace KumarNivat

-- weight each exponent by an integer normal, giving the corresponding euler derivative.
noncomputable def eulerWeight {K : Type*} [CommRing K] (ν : Site →+ ℤ)
    (f : Laurent K) : Laurent K :=
  f.coeff.sum (fun u a => AddMonoidAlgebra.single u ((ν u : K) * a))

-- the zero operator has zero weighted derivative.
@[simp] theorem eulerWeight_zero {K : Type*} [CommRing K] (ν : Site →+ ℤ) :
    eulerWeight ν (0 : Laurent K) = 0 := by simp [eulerWeight]

-- the weighting respects addition of coefficient functions.
theorem eulerWeight_add {K : Type*} [CommRing K] (ν : Site →+ ℤ) (f g : Laurent K) :
    eulerWeight ν (f + g) = eulerWeight ν f + eulerWeight ν g := by
  unfold eulerWeight
  change (f.coeff + g.coeff).sum _ = _
  apply Finsupp.sum_add_index'
  · intro u
    simp
  · intro u a b
    rw [mul_add, AddMonoidAlgebra.single_add]

-- on one monomial the derivative multiplies its coefficient by the normal value.
@[simp] theorem eulerWeight_single {K : Type*} [CommRing K]
    (ν : Site →+ ℤ) (u : Site) (a : K) :
    eulerWeight ν (AddMonoidAlgebra.single u a) =
      AddMonoidAlgebra.single u ((ν u : K) * a) := by
  simp [eulerWeight]

-- bundle additivity so subtraction uses the existing homomorphism law.
noncomputable def eulerOperator {K : Type*} [CommRing K] (ν : Site →+ ℤ) :
    Laurent K →+ Laurent K where
  toFun := eulerWeight ν
  map_zero' := eulerWeight_zero ν
  map_add' := eulerWeight_add ν

-- the product rule follows from additivity of the exponent normal.
theorem eulerWeight_mul {K : Type*} [CommRing K] (ν : Site →+ ℤ) (f g : Laurent K) :
    eulerWeight ν (f * g) = eulerWeight ν f * g + f * eulerWeight ν g := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f h hf hh =>
    rw [add_mul, eulerWeight_add, hf, hh, eulerWeight_add, add_mul, add_mul]
    ring
  | single u a =>
    induction g using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add g h hg hh =>
      rw [mul_add, eulerWeight_add, hg, hh, eulerWeight_add, mul_add, mul_add]
      ring
    | single v b =>
      rw [AddMonoidAlgebra.single_mul_single, eulerWeight_single, eulerWeight_single,
        eulerWeight_single, AddMonoidAlgebra.single_mul_single,
        AddMonoidAlgebra.single_mul_single, ← AddMonoidAlgebra.single_add]
      congr 1
      rw [map_add]
      push_cast
      ring

-- the derivative of a difference binomial is a single weighted monomial.
theorem eulerWeight_binomial {K : Type*} [CommRing K] (ν : Site →+ ℤ) (h : Site) :
    eulerWeight ν (binomial h : Laurent K) = AddMonoidAlgebra.single h (ν h : K) := by
  change eulerOperator ν (AddMonoidAlgebra.single h 1 - 1) = _
  rw [map_sub]
  simp [eulerOperator, AddMonoidAlgebra.one_def]

-- a unit derivative prevents every nonunit square from dividing the original element.
theorem squarefree_of_unit_derivative {R : Type*} [CommRing R]
    (D : R → R) (hproduct : ∀ x y, D (x * y) = D x * y + x * D y)
    (f : R) (hunit : IsUnit (D f)) : Squarefree f := by
  intro d hdiv
  obtain ⟨q, hq⟩ := hdiv
  have hderivative : d ∣ D f := by
    refine ⟨(D d + D d) * q + d * D q, ?_⟩
    rw [hq, hproduct, hproduct]
    ring
  exact isUnit_of_dvd_unit hderivative hunit

-- a nonzero coefficient times an invertible lattice monomial is a unit.
theorem single_isUnit {K : Type*} [Field K] (h : Site) (a : K) (ha : a ≠ 0) :
    IsUnit (AddMonoidAlgebra.single h a : Laurent K) := by
  apply isUnit_iff_exists_inv.mpr
  refine ⟨AddMonoidAlgebra.single (-h) a⁻¹, ?_⟩
  simp [AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.one_def, ha]

-- a nonzero normal value makes the difference binomial squarefree in characteristic zero.
theorem binomial_squarefree_of_normal {K : Type*} [Field K] [CharZero K]
    (ν : Site →+ ℤ) (h : Site) (hν : ν h ≠ 0) : Squarefree (binomial h : Laurent K) := by
  apply squarefree_of_unit_derivative (eulerWeight ν) (eulerWeight_mul ν)
  rw [eulerWeight_binomial]
  apply single_isUnit
  exact_mod_cast hν

end KumarNivat
