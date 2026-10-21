module

public import KumarNivat.SupportExtrema
public import KumarNivat.MinkowskiStencilFit
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.LocallyConvex.Separation

@[expose] public section

namespace KumarNivat

open scoped Pointwise

-- the lattice coordinates resolve all ties without changing the leading real normal.
def realNormalLexRefinement (ell : Site →+ ℝ) : Site →+ Lex (ℝ × Lex Site) where
  toFun g := toLex (ell g, toLex g)
  map_zero' := by simp only [map_zero]; rfl
  map_add' g h := by simp only [map_add]; rfl

-- maximal input terms survive multiplication even when the normal has tied faces.
theorem product_support_real_extreme {K : Type*} [CommRing K] [NoZeroDivisors K]
    (f h : Laurent K) (hf : f ≠ 0) (hh : h ≠ 0) (ell : Site →+ ℝ) :
    ∃ u ∈ f.coeff.support, ∃ v ∈ h.coeff.support,
      u + v ∈ (f * h).coeff.support ∧
        (∀ x ∈ f.coeff.support, ell x ≤ ell u) ∧
        (∀ x ∈ h.coeff.support, ell x ≤ ell v) := by
  classical
  let E := realNormalLexRefinement ell
  have hE : Function.Injective E := by
    intro x y he
    exact congrArg (fun z : Lex (ℝ × Lex Site) => ofLex (ofLex z).2) he
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
  refine ⟨u, hu, v, hv, ?_, ?_, ?_⟩
  · apply Finsupp.mem_support_iff.mpr
    rw [AddMonoidAlgebra.coeff_mul_add_of_uniqueAdd hunique]
    exact mul_ne_zero (Finsupp.mem_support_iff.mp hu) (Finsupp.mem_support_iff.mp hv)
  · intro x hx
    have he := humax x hx
    change toLex (ell x, toLex x) ≤ toLex (ell u, toLex u) at he
    exact Prod.Lex.monotone_fst _ _ he
  · intro x hx
    have he := hvmax x hx
    change toLex (ell x, toLex x) ≤ toLex (ell v, toLex v) at he
    exact Prod.Lex.monotone_fst _ _ he

-- convolution cancellation leaves the complete minkowski sum of the actual newton hulls.
theorem latticeHull_product_eq_minkowski {K : Type*} [CommRing K] [NoZeroDivisors K]
    (f h : Laurent K) (hf : f ≠ 0) (hh : h ≠ 0) :
    latticeHull (f * h).coeff.support = latticeHull f.coeff.support + latticeHull h.coeff.support := by
  classical
  let A := latticeEmbedding '' (f.coeff.support : Set Site)
  let B := latticeEmbedding '' (h.coeff.support : Set Site)
  have hleft : latticeHull (f * h).coeff.support ⊆ latticeHull f.coeff.support +
      latticeHull h.coeff.support := by
    apply convexHull_min ?_ ((convex_convexHull ℝ _).add (convex_convexHull ℝ _))
    rintro _ ⟨u, hu, rfl⟩
    obtain ⟨a, ha, b, hb, he⟩ := Finset.mem_add.mp
      (AddMonoidAlgebra.support_coeff_mul_subset f h hu)
    rw [← he, latticeEmbedding_add]
    exact Set.add_mem_add (subset_convexHull ℝ _ ⟨a, ha, rfl⟩)
      (subset_convexHull ℝ _ ⟨b, hb, rfl⟩)
  have hgen : A + B ⊆ latticeHull (f * h).coeff.support := by
    rintro _ ⟨_a, ⟨a, ha, rfl⟩, _b, ⟨b, hb, rfl⟩, rfl⟩
    by_contra hn
    have hclosed : IsClosed (latticeHull (f * h).coeff.support) :=
      ((f * h).coeff.support.finite_toSet.image latticeEmbedding).isClosed_convexHull ℝ
    obtain ⟨ell, t, hbelow, habove⟩ := geometric_hahn_banach_closed_point
      (convex_convexHull ℝ _) hclosed hn
    let ν : Site →+ ℝ :=
      { toFun := fun u => ell (latticeEmbedding u)
        map_zero' := by
          have he : latticeEmbedding (0 : Site) = (0 : RealPlane) := by
            ext <;> simp [latticeEmbedding]
          rw [he, map_zero]
        map_add' := by intro u v; rw [latticeEmbedding_add, map_add] }
    obtain ⟨u, hu, v, hv, huv, humax, hvmax⟩ := product_support_real_extreme f h hf hh ν
    have hmax : ell (latticeEmbedding a + latticeEmbedding b) ≤
        ell (latticeEmbedding (u + v)) := by
      rw [latticeEmbedding_add, map_add, map_add]
      exact add_le_add (humax a ha) (hvmax b hb)
    have hlow := hbelow (latticeEmbedding (u + v))
      (subset_convexHull ℝ _ ⟨u + v, huv, rfl⟩)
    linarith
  have hright : latticeHull f.coeff.support + latticeHull h.coeff.support ⊆
      latticeHull (f * h).coeff.support := by
    change convexHull ℝ A + convexHull ℝ B ⊆ _
    rw [← convexHull_add]
    exact convexHull_min hgen (convex_convexHull ℝ _)
  exact Set.Subset.antisymm hleft hright

end KumarNivat
