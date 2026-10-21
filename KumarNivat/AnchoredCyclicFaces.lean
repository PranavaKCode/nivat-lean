module

public import KumarNivat.AnchoredCyclicFacesNonnegative

@[expose] public section

namespace KumarNivat

-- the actual supporting inequalities hold at every real point of the named polygon hull.
theorem ordered_cyclic_real_point_normal_minimum {n : ℕ} [NeZero n]
    (e : ZMod n → Site) (horder : CyclicEdgeOrder e) (F : Finset Site)
    (P : OrderedCyclicLatticePolygon e F) (x : RealPlane) (hx : x ∈ latticeHull F) :
    ∀ i, (directionNormal (e i) (P.vertex i) : ℝ) ≤ latticeNormal (directionNormal (e i)) x := by
  rw [P.hull_eq] at hx
  exact ordered_cyclic_nonnegative_real_point_minimum e horder P.vertex P.edgeLength
    (fun k => (P.length_pos k).le) P.edge_eq x hx

-- the complete real facet is exactly the actual cyclic edge, with no supplied face description.
theorem ordered_cyclic_facet_is_actual_edge {n : ℕ} [NeZero n]
    (e : ZMod n → Site) (horder : CyclicEdgeOrder e) (F : Finset Site)
    (P : OrderedCyclicLatticePolygon e F) (i : ZMod n) :
    normalFace (latticeHull F) (latticeNormal (directionNormal (e i)))
        (directionNormal (e i) (P.vertex i) : ℝ) =
      lineInterval (latticeEmbedding (P.vertex i)) (latticeEmbedding (e i)) 0
        (P.edgeLength i : ℝ) := by
  rw [P.hull_eq]
  exact ordered_cyclic_nonnegative_walk_face_is_edge e horder P.vertex P.edgeLength
    (fun k => (P.length_pos k).le) P.edge_eq i

end KumarNivat
