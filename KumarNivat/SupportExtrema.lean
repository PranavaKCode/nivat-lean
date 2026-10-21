module

public import KumarNivat.LaurentAlgebra
public import Mathlib.Algebra.Order.Monoid.Prod
public import Mathlib.Algebra.MonoidAlgebra.Support

@[expose] public section

namespace KumarNivat

-- in an ordered grading, the two maximal terms give a unique product coefficient.
theorem product_support_extreme {K G : Type*} [Field K] [AddCommGroup G]
    [LinearOrder G] [IsOrderedAddMonoid G]
    (f h : Laurent K) (hf : f ≠ 0) (hh : h ≠ 0)
    (E : Site →+ G) (hE : Function.Injective E) :
    ∃ u ∈ f.coeff.support, ∃ v ∈ h.coeff.support,
      u + v ∈ (f * h).coeff.support ∧
        (∀ x ∈ f.coeff.support, E x ≤ E u) ∧
        (∀ x ∈ h.coeff.support, E x ≤ E v) := by
  classical
  have hfs : f.coeff.support.Nonempty := Finsupp.support_nonempty_iff.mpr
    (fun hz => hf (AddMonoidAlgebra.coeff_injective hz))
  have hhs : h.coeff.support.Nonempty := Finsupp.support_nonempty_iff.mpr
    (fun hz => hh (AddMonoidAlgebra.coeff_injective hz))
  obtain ⟨u, hu, humax⟩ := f.coeff.support.exists_max_image E hfs
  obtain ⟨v, hv, hvmax⟩ := h.coeff.support.exists_max_image E hhs
  have hunique : UniqueAdd f.coeff.support h.coeff.support u v := by
    intro x y hx hy hxy
    have hsum : E x + E y = E u + E v := by simp only [← map_add, hxy]
    have hxle := humax x hx
    have hyle := hvmax y hy
    have hxge : E u ≤ E x := by
      have he := add_le_add_right hyle (E x)
      rw [hsum] at he
      exact le_of_add_le_add_right he
    have hex : E x = E u := le_antisymm hxle hxge
    have hey : E y = E v := by rw [hex] at hsum; exact add_left_cancel hsum
    exact ⟨hE hex, hE hey⟩
  refine ⟨u, hu, v, hv, ?_, humax, hvmax⟩
  apply Finsupp.mem_support_iff.mpr
  rw [AddMonoidAlgebra.coeff_mul_add_of_uniqueAdd hunique]
  exact mul_ne_zero (Finsupp.mem_support_iff.mp hu) (Finsupp.mem_support_iff.mp hv)

-- lexicographic refinement preserves the chosen coordinate while breaking support ties.
def lexRefinement (F : Site →+ Site) : Site →+ Lex Site where
  toFun g := toLex (F g)
  map_zero' := by simp only [map_zero]; rfl
  map_add' x y := by simp only [map_add]; rfl

-- every pair of factor exponents obeys a coordinate bound on the product support.
theorem coordinate_sum_bound {K : Type*} [Field K] (f h : Laurent K)
    (hf : f ≠ 0) (hh : h ≠ 0) (F : Site →+ Site) (hF : Function.Injective F)
    (B : ℤ) (hbound : ∀ z ∈ (f * h).coeff.support, (F z).1 ≤ B) :
    ∀ u ∈ f.coeff.support, ∀ v ∈ h.coeff.support, (F (u + v)).1 ≤ B := by
  have hinj : Function.Injective (lexRefinement F) := by
    intro x y hxy
    apply hF
    change toLex (F x) = toLex (F y) at hxy
    exact congrArg (fun z : Lex Site => ofLex z) hxy
  obtain ⟨a, ha, b, hb, hab, hma, hmb⟩ := product_support_extreme f h hf hh
    (lexRefinement F) hinj
  intro u hu v hv
  have hua : (F u).1 ≤ (F a).1 := by
    have he := hma u hu
    change toLex (F u) ≤ toLex (F a) at he
    exact Prod.Lex.monotone_fst _ _ he
  have hvb : (F v).1 ≤ (F b).1 := by
    have he := hmb v hv
    change toLex (F v) ≤ toLex (F b) at he
    exact Prod.Lex.monotone_fst _ _ he
  have hsum := hbound (a + b) hab
  simp only [map_add, Prod.fst_add] at hsum ⊢
  omega

end KumarNivat
