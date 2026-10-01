import KumarNivat.NewtonCyclicFacets
import KumarNivat.SupportingFaceVertices

namespace KumarNivat

-- the sum of adjacent inward normals exposes the actual shared corner uniquely.
theorem ordered_cyclic_walk_vertex_extreme {n : ℕ} [NeZero n]
    (e : ZMod n → Site) (horder : CyclicEdgeOrder e) (v : ZMod n → Site)
    (r : ZMod n → ℤ) (hr : ∀ i, 0 < r i)
    (hedge : ∀ i, v (i + 1) = v i + r i • e i) (i : ZMod n) :
    latticeEmbedding (v i) ∈
      (convexHull ℝ (Set.range (fun j => latticeEmbedding (v j)))).extremePoints ℝ := by
  let P := convexHull ℝ (Set.range (fun j => latticeEmbedding (v j)))
  let p := e (i - 1)
  let q := e i
  let a := latticeEmbedding (v i)
  let L := latticeNormal (directionNormal p) + latticeNormal (directionNormal q)
  have hfacets := ordered_cyclic_walk_facet_presentation e horder v r hr hedge
  have hbounds (x : RealPlane) (hx : x ∈ P) (j : ZMod n) :
      (directionNormal (e j) (v j) : ℝ) ≤ latticeNormal (directionNormal (e j)) x := by
    change x ∈ convexHull ℝ (Set.range (fun j => latticeEmbedding (v j))) at hx
    rw [hfacets] at hx
    exact hx j
  have hprevious := congrArg (directionNormal p) (hedge (i - 1))
  have hpSelf : directionNormal p (e (i - 1)) = 0 := directionNormal_self (e (i - 1))
  simp only [sub_add_cancel, map_add, map_zsmul, hpSelf, smul_zero, add_zero] at hprevious
  have hprev (x : RealPlane) (hx : x ∈ P) :
      latticeNormal (directionNormal p) a ≤ latticeNormal (directionNormal p) x := by
    rw [latticeNormal_embedding, hprevious]
    exact hbounds x hx (i - 1)
  have hnext (x : RealPlane) (hx : x ∈ P) :
      latticeNormal (directionNormal q) a ≤ latticeNormal (directionNormal q) x := by
    rw [latticeNormal_embedding]
    exact hbounds x hx i
  have hmin : ∀ x ∈ P, L a ≤ L x := by
    intro x hx
    exact add_le_add (hprev x hx) (hnext x hx)
  have hunique : ∀ x ∈ P, L x = L a → x = a := by
    intro x hx he
    have hp := hprev x hx
    have hq := hnext x hx
    change latticeNormal (directionNormal p) x + latticeNormal (directionNormal q) x =
      latticeNormal (directionNormal p) a + latticeNormal (directionNormal q) a at he
    have hpzero : latticeNormal (directionNormal p) (x - a) = 0 := by rw [map_sub]; linarith
    have hqzero : latticeNormal (directionNormal q) (x - a) = 0 := by rw [map_sub]; linarith
    have hcramer := real_plane_edge_cramer_identity p q (x - a)
    rw [hpzero, hqzero, neg_zero, zero_smul, zero_smul, add_zero] at hcramer
    have hdet : (determinant p q : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt (horder.adjacent_pos i)
    have hzero : x - a = 0 := (smul_eq_zero.mp hcramer).resolve_left hdet
    exact sub_eq_zero.mp hzero
  exact unique_normal_minimum_is_extremePoint P L a
    (subset_convexHull ℝ _ ⟨i, rfl⟩) hmin hunique

-- an exposed actual hull corner belongs to its original finite coefficient support, even with interior cancellation.
theorem ordered_cyclic_walk_vertex_mem_actual_support {n : ℕ} [NeZero n]
    (e : ZMod n → Site) (horder : CyclicEdgeOrder e) (v : ZMod n → Site)
    (r : ZMod n → ℤ) (hr : ∀ i, 0 < r i)
    (hedge : ∀ i, v (i + 1) = v i + r i • e i) (T : Finset Site)
    (hhull : latticeHull T = convexHull ℝ (Set.range (fun j => latticeEmbedding (v j)))) :
    ∀ i, v i ∈ T := by
  intro i
  apply latticeVertex_mem T (v i)
  change latticeEmbedding (v i) ∈ (latticeHull T).extremePoints ℝ
  rw [hhull]
  exact ordered_cyclic_walk_vertex_extreme e horder v r hr hedge i

end KumarNivat
