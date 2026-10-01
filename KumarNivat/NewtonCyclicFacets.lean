import KumarNivat.NewtonCyclicNormals
import KumarNivat.AnchoredMaximalPolygons

namespace KumarNivat

-- the ordered actual edge walk gives every facet inequality and their complete hull presentation.
theorem ordered_cyclic_walk_facet_presentation {n : ℕ} [NeZero n]
    (e : ZMod n → Site) (horder : CyclicEdgeOrder e) (v : ZMod n → Site)
    (r : ZMod n → ℤ) (hr : ∀ i, 0 < r i)
    (hedge : ∀ i, v (i + 1) = v i + r i • e i) :
    convexHull ℝ (Set.range (fun i => latticeEmbedding (v i))) =
      {x : RealPlane | ∀ i, (directionNormal (e i) (v i) : ℝ) ≤ latticeNormal (directionNormal (e i)) x} := by
  classical
  have hmin := ordered_cyclic_walk_normal_minimum e horder v r (fun i => le_of_lt (hr i)) hedge
  ext x
  constructor
  · intro hx i
    have hgen : Set.range (fun j => latticeEmbedding (v j)) ⊆
        {y : RealPlane | (directionNormal (e i) (v i) : ℝ) ≤ latticeNormal (directionNormal (e i)) y} := by
      rintro _ ⟨j, rfl⟩
      change (directionNormal (e i) (v i) : ℝ) ≤ latticeNormal (directionNormal (e i)) (latticeEmbedding (v j))
      rw [latticeNormal_embedding]
      exact_mod_cast hmin i j
    exact convexHull_min hgen
      ((convex_Ici (directionNormal (e i) (v i) : ℝ)).linear_preimage (latticeNormal (directionNormal (e i)))) hx
  · intro hx
    by_contra hn
    have hclosed : IsClosed (convexHull ℝ (Set.range (fun i => latticeEmbedding (v i)))) :=
      (Set.finite_range (fun i => latticeEmbedding (v i))).isClosed_convexHull ℝ
    obtain ⟨L, t, hbelow, habove⟩ := geometric_hahn_banach_closed_point
      (convex_convexHull ℝ _) hclosed hn
    obtain ⟨i, _hi, hmax⟩ := Finset.univ.exists_max_image (fun j => L (latticeEmbedding (v j)))
      (Finset.univ_nonempty : (Finset.univ : Finset (ZMod n)).Nonempty)
    have hmax' : ∀ j, L (latticeEmbedding (v j)) ≤ L (latticeEmbedding (v i)) :=
      fun j => hmax j (Finset.mem_univ j)
    obtain ⟨hprevsign, hnextsign⟩ := cyclic_maximum_adjacent_signs e v r hr hedge L.toLinearMap i hmax'
    have hprevious := congrArg (directionNormal (e (i - 1))) (hedge (i - 1))
    simp only [sub_add_cancel, map_add, map_zsmul, directionNormal_self, smul_zero, add_zero] at hprevious
    have hpx : 0 ≤ latticeNormal (directionNormal (e (i - 1))) (x - latticeEmbedding (v i)) := by
      rw [map_sub, latticeNormal_embedding, hprevious]
      exact sub_nonneg.mpr (hx (i - 1))
    have hqx : 0 ≤ latticeNormal (directionNormal (e i)) (x - latticeEmbedding (v i)) := by
      rw [map_sub, latticeNormal_embedding]
      exact sub_nonneg.mpr (hx i)
    have hcontrol := adjacent_edge_normals_linear_control (e (i - 1)) (e i) (horder.adjacent_pos i)
      L.toLinearMap hprevsign hnextsign _ hpx hqx
    rw [map_sub] at hcontrol
    change L x - L (latticeEmbedding (v i)) ≤ 0 at hcontrol
    have hlow := hbelow (latticeEmbedding (v i)) (subset_convexHull ℝ _ ⟨i, rfl⟩)
    linarith

-- the finite fixed-normal presentation applies directly to actual cyclic lattice polygons.
theorem ordered_cyclic_polygon_integer_facets {n : ℕ} [NeZero n]
    (e : ZMod n → Site) (horder : CyclicEdgeOrder e) (F : Finset Site)
    (P : OrderedCyclicLatticePolygon e F) :
    HasIntegerFacetPresentation Finset.univ (fun i => directionNormal (e i)) F := by
  classical
  refine ⟨fun i => directionNormal (e i) (P.vertex i), ?_⟩
  rw [P.hull_eq, ordered_cyclic_walk_facet_presentation e horder P.vertex P.edgeLength P.length_pos P.edge_eq]
  ext x
  simp

end KumarNivat
