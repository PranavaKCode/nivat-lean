module

public import KumarNivat.PairedStructureRayChainFacets
public import KumarNivat.RayChainRelaxationNormals

@[expose] public section

namespace KumarNivat

open scoped Pointwise

-- the final chain half-plane has the original polygon's attained first support level.
theorem forward_factor_final_region_original_support {q : ℕ} [NeZero q]
    (hq : 2 ≤ q) (e : ZMod (2 * q) → Site) (hfan : AnchoredChainFanOrder e)
    (T : Finset Site) (P : OrderedCyclicLatticePolygon e T) (G : Site) :
    forwardFactorNewtonRegion T G e q =
      {x | (directionNormal (e 0) (P.vertex 0 + G) : ℝ) ≤ latticeNormal (directionNormal (e 0)) x} := by
  have hT : T.Nonempty := ⟨P.vertex 0, P.vertex_mem 0⟩
  obtain ⟨u, hu, hmin, hhalf⟩ := newton_hull_plus_homogeneous_halfplane T hT G (directionNormal (e 0))
  have hvertex : latticeEmbedding u ∈ latticeHull T := subset_convexHull ℝ _ ⟨u, hu, rfl⟩
  rw [P.hull_eq, ordered_cyclic_walk_facet_presentation e hfan.order P.vertex P.edgeLength P.length_pos P.edge_eq] at hvertex
  have hlo : directionNormal (e 0) (P.vertex 0) ≤ directionNormal (e 0) u := by
    have h := hvertex 0
    rw [latticeNormal_embedding] at h
    exact_mod_cast h
  have heq := le_antisymm (hmin _ (P.vertex_mem 0)) hlo
  have hcut : directionNormal (e 0) (G + u) = directionNormal (e 0) (P.vertex 0 + G) := by
    rw [map_add, map_add, heq]
    exact add_comm _ _
  have hcone := (forward_factor_ray_cones_chain e hfan hq).2
  simpa only [forwardFactorNewtonRegion, hcone, hcut] using hhalf

-- passing to the actual successor ray removes exactly the named moving facet, including the final antipodal stage.
theorem forward_factor_region_after_current_facet_removal {q : ℕ} [NeZero q]
    (hq : 2 ≤ q) (e : ZMod (2 * q) → Site) (hfan : AnchoredChainFanOrder e)
    (T : Finset Site) (P : OrderedCyclicLatticePolygon e T) (G : Site)
    (k : ℕ) (hk₀ : 0 < k) (hkq : k < q) :
    forwardFactorNewtonRegion T G e (k + 1) =
      inwardLayerRegion (directionNormal (e 0)) (directionNormal (e 0) (P.vertex 0 + G))
        (Finset.Icc (k + 1) (q - 1)) (fun i => -directionNormal (e (i : ZMod (2 * q))))
        (fun i => (-directionNormal (e (i : ZMod (2 * q)))) (P.vertex ((q + i : ℕ) : ZMod (2 * q)) + G)) := by
  by_cases hnext : k + 1 < q
  · exact forward_factor_newton_region_integer_facets hq e hfan T P G (k + 1) (by omega) hnext
  · have he : k + 1 = q := by omega
    rw [he, forward_factor_final_region_original_support hq e hfan T P G]
    have hJ : Finset.Icc q (q - 1) = ∅ := Finset.Icc_eq_empty_of_lt (by omega)
    simp [hJ, inwardLayerRegion]

end KumarNivat
