module

public import KumarNivat.LaurentEliminant
public import KumarNivat.AxisOperators

@[expose] public section

namespace KumarNivat

-- an isomorphism preserves relative primeness because it reflects divisors and units.
theorem ringEquiv_preserves_relPrime {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (f g : R) (hcop : IsRelPrime f g) : IsRelPrime (e f) (e g) := by
  intro d hdf hdg
  have hf : e.symm d ∣ f := by
    simpa only [RingEquiv.symm_apply_apply] using map_dvd e.symm hdf
  have hg : e.symm d ∣ g := by
    simpa only [RingEquiv.symm_apply_apply] using map_dvd e.symm hdg
  simpa only [RingEquiv.apply_symm_apply] using (hcop hf hg).map e

-- the coefficient-ring eliminant becomes a vertical stencil in the original lattice basis.
theorem exists_vertical_eliminant {K : Type*} [Field K]
    (f g : Laurent K) (hf : f ≠ 0) (hcop : IsRelPrime f g) :
    ∃ d : LaurentPolynomial K, d ≠ 0 ∧ ∃ a b : Laurent K,
      a * f + b * g = axisOperator (0, 1) d := by
  let e := nestedLaurentEquiv (K := K)
  have hf' : e f ≠ 0 := by
    intro hz
    apply hf
    apply e.injective
    simpa only [map_zero] using hz
  obtain ⟨d, hd, a, b, he⟩ := laurent_relPrime_eliminant (e f) (e g) hf'
    (ringEquiv_preserves_relPrime e f g hcop)
  refine ⟨d, hd, e.symm a, e.symm b, ?_⟩
  have hid := congrArg e.symm he
  simpa only [map_add, map_mul, RingEquiv.symm_apply_apply, e, nestedLaurent_C] using hid

-- interchange the two coordinates only while constructing the second eliminant.
noncomputable def swapLaurent {K : Type*} [CommRing K] : Laurent K ≃+* Laurent K :=
  AddMonoidAlgebra.mapDomainRingEquiv K AddEquiv.prodComm

-- a coordinate swap sends one monomial to its swapped lattice exponent.
theorem swapLaurent_single {K : Type*} [CommRing K] (u : Site) (a : K) :
    swapLaurent (AddMonoidAlgebra.single u a) = AddMonoidAlgebra.single (u.2, u.1) a := by
  rw [swapLaurent, AddMonoidAlgebra.mapDomainRingEquiv_single]
  rfl

-- two swaps restore the exact original exponent and coefficient.
theorem swapLaurent_twice {K : Type*} [CommRing K] (f : Laurent K) :
    swapLaurent (swapLaurent f) = f := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single u a => simp only [swapLaurent_single]

-- the inverse swap is the same coordinate interchange.
theorem swapLaurent_symm_apply {K : Type*} [CommRing K] (f : Laurent K) :
    swapLaurent.symm f = swapLaurent f := by
  apply swapLaurent.injective
  rw [RingEquiv.apply_symm_apply, swapLaurent_twice]

-- returning from swapped coordinates turns the vertical eliminant into a horizontal one.
theorem swapLaurent_vertical_axis {K : Type*} [CommRing K] (d : LaurentPolynomial K) :
    swapLaurent.symm (axisOperator (0, 1) d) = axisOperator (1, 0) d := by
  rw [swapLaurent_symm_apply]
  induction d using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add d e hd he => simp only [map_add, hd, he]
  | single n a =>
    rw [axisOperator_single, swapLaurent_single, axisOperator_single]
    congr 1

-- both directional eliminants are linear combinations of the original two coprime operators.
theorem exists_coordinate_eliminants {K : Type*} [Field K]
    (f g : Laurent K) (hf : f ≠ 0) (hcop : IsRelPrime f g) :
    ∃ d₁ d₂ : LaurentPolynomial K, d₁ ≠ 0 ∧ d₂ ≠ 0 ∧ ∃ a₁ b₁ a₂ b₂ : Laurent K,
      a₁ * f + b₁ * g = axisOperator (1, 0) d₁ ∧
      a₂ * f + b₂ * g = axisOperator (0, 1) d₂ := by
  obtain ⟨d₂, hd₂, a₂, b₂, he₂⟩ := exists_vertical_eliminant f g hf hcop
  have hf' : swapLaurent f ≠ 0 := by
    intro hz
    apply hf
    apply swapLaurent.injective
    simpa only [map_zero] using hz
  obtain ⟨d₁, hd₁, a₁, b₁, he₁⟩ := exists_vertical_eliminant (swapLaurent f) (swapLaurent g) hf'
    (ringEquiv_preserves_relPrime swapLaurent f g hcop)
  refine ⟨d₁, d₂, hd₁, hd₂, swapLaurent.symm a₁, swapLaurent.symm b₁, a₂, b₂, ?_, he₂⟩
  have hid := congrArg swapLaurent.symm he₁
  simpa only [map_add, map_mul, RingEquiv.symm_apply_apply, swapLaurent_vertical_axis] using hid

end KumarNivat
