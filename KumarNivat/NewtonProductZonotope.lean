import KumarNivat.NewtonProductGeometry
import KumarNivat.NormalMinima
import KumarNivat.SquarefreeProducts
import KumarNivat.LineFaceGeometry

namespace KumarNivat

open scoped Pointwise

-- this is the manuscript's segment sum in the original lattice coordinates.
def differenceZonotope : List Site → Set RealPlane
  | [] => {0}
  | h :: hs => lineInterval 0 (latticeEmbedding h) 0 1 + differenceZonotope hs

-- the segment sum retains the convexity used in the manuscript's envelope geometry.
theorem differenceZonotope_convex (hs : List Site) : Convex ℝ (differenceZonotope hs) := by
  induction hs with
  | nil => exact convex_singleton 0
  | cons h hs ih => exact (lineInterval_convex 0 (latticeEmbedding h) 0 1 (by norm_num)).add ih

-- finite segment sums are compact, so their actual supporting extrema are attained.
theorem differenceZonotope_isCompact (hs : List Site) : IsCompact (differenceZonotope hs) := by
  induction hs with
  | nil => exact isCompact_singleton
  | cons h hs ih =>
    have hc : IsCompact (lineInterval 0 (latticeEmbedding h) 0 1) :=
      isCompact_Icc.image (by fun_prop)
    exact hc.add ih

-- a nonzero difference binomial has both of its actual endpoint coefficients.
theorem binomial_support_eq_pair {K : Type*} [CommRing K] [Nontrivial K]
    (h : Site) (hh : h ≠ 0) : (binomial h : Laurent K).coeff.support = {0, h} := by
  classical
  apply Finset.Subset.antisymm
  · intro u hu
    rcases Finset.mem_union.mp (binomial_support_subset h hu) with huh | hu0
    · exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr (Finset.mem_singleton.mp huh))
    · exact Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp hu0))
  · intro u hu
    rcases Finset.mem_insert.mp hu with rfl | hu
    · apply Finsupp.mem_support_iff.mpr
      simp [binomial, AddMonoidAlgebra.one_def, hh]
    · rw [Finset.mem_singleton.mp hu]
      apply Finsupp.mem_support_iff.mpr
      simp [binomial, AddMonoidAlgebra.one_def, hh]

-- the binomial newton hull is the complete real segment between those endpoints.
theorem latticeHull_binomial_eq_segment {K : Type*} [CommRing K] [Nontrivial K]
    (h : Site) (hh : h ≠ 0) :
    latticeHull (binomial h : Laurent K).coeff.support = lineInterval 0 (latticeEmbedding h) 0 1 := by
  classical
  rw [binomial_support_eq_pair h hh]
  unfold latticeHull
  have he0 : latticeEmbedding (0 : Site) = (0 : RealPlane) := by
    ext <;> simp [latticeEmbedding]
  have he : latticeEmbedding '' ({0, h} : Set Site) = {0, latticeEmbedding h} := by
    rw [Set.image_insert_eq, Set.image_singleton, he0]
  simp only [Finset.coe_insert, Finset.coe_singleton]
  rw [he, convexHull_pair, lineInterval_eq_segment 0 (latticeEmbedding h) 0 1 (by norm_num)]
  simp

-- the actual product hull equals the full zonotope, including canceled interior monomials.
theorem latticeHull_differenceProduct_eq_zonotope {K : Type*} [CommRing K] [Nontrivial K]
    [NoZeroDivisors K] (hs : List Site) (hdirs : ∀ h ∈ hs, h ≠ 0) :
    latticeHull (differenceProduct hs : Laurent K).coeff.support = differenceZonotope hs := by
  classical
  induction hs with
  | nil =>
    simp [differenceZonotope, latticeHull, AddMonoidAlgebra.one_def,
      AddMonoidAlgebra.coeff_single, latticeEmbedding, convexHull_singleton]
  | cons h hs ih =>
    have hh := hdirs h List.mem_cons_self
    have htail : ∀ p ∈ hs, p ≠ 0 := fun p hp => hdirs p (List.mem_cons_of_mem h hp)
    rw [differenceProduct_cons, latticeHull_product_eq_minkowski (binomial h) (differenceProduct hs)
      (binomial_ne_zero h hh) (differenceProduct_ne_zero hs htail),
      latticeHull_binomial_eq_segment h hh, ih htail]
    rfl

end KumarNivat
