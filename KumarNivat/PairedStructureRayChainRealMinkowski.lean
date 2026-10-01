import KumarNivat.PairedStructureRayChainRealOrder

namespace KumarNivat

open scoped Pointwise

-- real residual lengths give the same exact vertexwise minkowski construction.
theorem ordered_real_cyclic_walk_minkowski {n : ℕ} [NeZero n]
    (e : ZMod n → Site) (horder : CyclicEdgeOrder e)
    (v w : ZMod n → RealPlane) (r d : ZMod n → ℝ)
    (hr : ∀ i, 0 < r i) (hd : ∀ i, 0 ≤ d i)
    (hv : ∀ i, v (i + 1) = v i + r i • latticeEmbedding (e i))
    (hw : ∀ i, w (i + 1) = w i + d i • latticeEmbedding (e i)) :
    convexHull ℝ (Set.range (fun i => v i + w i)) =
      convexHull ℝ (Set.range v) + convexHull ℝ (Set.range w) := by
  classical
  let A := Set.range v
  let B := Set.range w
  let C := Set.range (fun i => v i + w i)
  have hleft : convexHull ℝ C ⊆ convexHull ℝ A + convexHull ℝ B := by
    apply convexHull_min ?_ ((convex_convexHull ℝ _).add (convex_convexHull ℝ _))
    rintro _ ⟨i, rfl⟩
    exact Set.add_mem_add (subset_convexHull ℝ _ ⟨i, rfl⟩) (subset_convexHull ℝ _ ⟨i, rfl⟩)
  have hgen : A + B ⊆ convexHull ℝ C := by
    rintro _ ⟨_x, ⟨i, rfl⟩, _y, ⟨j, rfl⟩, rfl⟩
    by_contra hn
    have hclosed : IsClosed (convexHull ℝ C) := (Set.finite_range (fun i => v i + w i)).isClosed_convexHull ℝ
    obtain ⟨L, t, hbelow, habove⟩ := geometric_hahn_banach_closed_point (convex_convexHull ℝ _) hclosed hn
    obtain ⟨k, hkV, hkW⟩ := ordered_real_cyclic_common_linear_maximum e horder v w r d hr hd hv hw L.toLinearMap
    have hmax : L (v i + w j) ≤ L (v k + w k) := by
      rw [map_add, map_add]
      exact add_le_add (hkV i) (hkW j)
    have hlow := hbelow (v k + w k) (subset_convexHull ℝ _ ⟨k, rfl⟩)
    linarith
  have hright : convexHull ℝ A + convexHull ℝ B ⊆ convexHull ℝ C := by
    rw [← convexHull_add]
    exact convexHull_min hgen (convex_convexHull ℝ _)
  exact Set.Subset.antisymm hleft hright

-- real positive edge lengths provide the complete facet presentation, including nonintegral residual expansions.
theorem ordered_real_cyclic_walk_facet_presentation {n : ℕ} [NeZero n]
    (e : ZMod n → Site) (horder : CyclicEdgeOrder e) (v : ZMod n → RealPlane)
    (r : ZMod n → ℝ) (hr : ∀ i, 0 < r i)
    (hedge : ∀ i, v (i + 1) = v i + r i • latticeEmbedding (e i)) :
    convexHull ℝ (Set.range v) = {x : RealPlane | ∀ i,
      latticeNormal (directionNormal (e i)) (v i) ≤ latticeNormal (directionNormal (e i)) x} := by
  classical
  have hmin := ordered_real_cyclic_walk_normal_minimum e horder v r (fun i => (hr i).le) hedge
  ext x
  constructor
  · intro hx i
    have hgen : Set.range v ⊆ {y | latticeNormal (directionNormal (e i)) (v i) ≤ latticeNormal (directionNormal (e i)) y} := by
      rintro _ ⟨j, rfl⟩
      exact hmin i j
    exact convexHull_min hgen
      ((convex_Ici (latticeNormal (directionNormal (e i)) (v i))).linear_preimage (latticeNormal (directionNormal (e i)))) hx
  · intro hx
    by_contra hn
    have hclosed : IsClosed (convexHull ℝ (Set.range v)) := (Set.finite_range v).isClosed_convexHull ℝ
    obtain ⟨L, t, hbelow, habove⟩ := geometric_hahn_banach_closed_point (convex_convexHull ℝ _) hclosed hn
    obtain ⟨i, _hi, hmax⟩ := Finset.univ.exists_max_image (fun j => L (v j))
      (Finset.univ_nonempty : (Finset.univ : Finset (ZMod n)).Nonempty)
    have hmax' : ∀ j, L (v j) ≤ L (v i) := fun j => hmax j (Finset.mem_univ j)
    obtain ⟨hprevsign, hnextsign⟩ := real_cyclic_maximum_adjacent_signs e v r hr hedge L.toLinearMap i hmax'
    have hprevious := congrArg (latticeNormal (directionNormal (e (i - 1)))) (hedge (i - 1))
    simp only [sub_add_cancel, map_add, map_smul, latticeNormal_embedding, directionNormal_self,
      Int.cast_zero, smul_zero, add_zero] at hprevious
    have hpx : 0 ≤ latticeNormal (directionNormal (e (i - 1))) (x - v i) := by
      rw [map_sub, hprevious]
      exact sub_nonneg.mpr (hx (i - 1))
    have hqx : 0 ≤ latticeNormal (directionNormal (e i)) (x - v i) := by
      rw [map_sub]
      exact sub_nonneg.mpr (hx i)
    have hcontrol := adjacent_edge_normals_linear_control (e (i - 1)) (e i)
      (horder.adjacent_pos i) L.toLinearMap hprevsign hnextsign _ hpx hqx
    rw [map_sub] at hcontrol
    change L x - L (v i) ≤ 0 at hcontrol
    have hlow := hbelow (v i) (subset_convexHull ℝ _ ⟨i, rfl⟩)
    linarith

end KumarNivat
