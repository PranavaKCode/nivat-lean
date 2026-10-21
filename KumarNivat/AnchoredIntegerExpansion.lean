module

public import KumarNivat.AnchoredCyclicFacesResidual
public import Mathlib.Algebra.Group.Torsion

@[expose] public section

namespace KumarNivat

-- at the final cleared level both moving endpoints are actual lattice points.
def integerFacetExpansionVertex {n : ℕ} [NeZero n] (e : ZMod n → Site)
    (F : Finset Site) (P : OrderedCyclicLatticePolygon e F) (i k : ZMod n) : Site :=
  if k = i then P.vertex k + determinant (e i) (e (i + 1)) • e (i - 1)
  else if k = i + 1 then P.vertex k - determinant (e (i - 1)) (e i) • e (i + 1)
  else P.vertex k

-- the final integer relaxation modifies precisely the same three primitive edge lengths.
def integerFacetExpansionLength {n : ℕ} [NeZero n] (e : ZMod n → Site)
    (F : Finset Site) (P : OrderedCyclicLatticePolygon e F) (i k : ZMod n) : ℤ :=
  if k = i - 1 then P.edgeLength k + determinant (e i) (e (i + 1))
  else if k = i then P.edgeLength k - determinant (e (i - 1)) (e (i + 1))
  else if k = i + 1 then P.edgeLength k + determinant (e (i - 1)) (e i)
  else P.edgeLength k

-- the previously constructed cleared vertices are exactly the dilation of these integer vertices.
theorem scaled_final_facet_vertices {n : ℕ} [NeZero n] (e : ZMod n → Site)
    (F : Finset Site) (P : OrderedCyclicLatticePolygon e F) (i : ZMod n) :
    ∀ k, scaledFacetRelaxationVertex e F P i (cyclicFacetRelaxationScale e i) k =
      cyclicFacetRelaxationScale e i • integerFacetExpansionVertex e F P i k := by
  intro k
  unfold scaledFacetRelaxationVertex integerFacetExpansionVertex
  split_ifs <;> simp only [smul_add, smul_sub, smul_smul]

-- the same final dilation identity holds for every changed and unchanged edge length.
theorem scaled_final_facet_lengths {n : ℕ} [NeZero n] (e : ZMod n → Site)
    (F : Finset Site) (P : OrderedCyclicLatticePolygon e F) (i : ZMod n) :
    ∀ k, scaledFacetRelaxationLength e F P i (cyclicFacetRelaxationScale e i) k =
      cyclicFacetRelaxationScale e i * integerFacetExpansionLength e F P i k := by
  intro k
  unfold scaledFacetRelaxationLength integerFacetExpansionLength
  split_ifs <;> ring

-- injective integer dilation transfers the checked closed-walk equations to the original plane.
theorem integer_facet_expansion_edge_equations {n : ℕ} [NeZero n]
    (e : ZMod n → Site) (horder : CyclicEdgeOrder e) (F : Finset Site)
    (P : OrderedCyclicLatticePolygon e F) (i : ZMod n) :
    ∀ k, integerFacetExpansionVertex e F P i (k + 1) =
      integerFacetExpansionVertex e F P i k + integerFacetExpansionLength e F P i k • e k := by
  intro k
  have he := scaled_facet_relaxation_edge_equations e horder F P i (cyclicFacetRelaxationScale e i) k
  rw [scaled_final_facet_vertices, scaled_final_facet_vertices, scaled_final_facet_lengths,
    ← smul_smul, ← smul_add] at he
  exact zsmul_right_injective (ne_of_gt (cyclic_facet_relaxation_scale_positive e horder i)) he

-- the actual unscaled expansion still dominates every original newton edge length.
theorem integer_facet_expansion_lengths_dominate {n : ℕ} [NeZero n]
    (e : ZMod n → Site) (horder : CyclicEdgeOrder e) (Z F : Finset Site)
    (Q : OrderedCyclicLatticePolygon e Z) (P : OrderedCyclicLatticePolygon e F)
    (hlen : ∀ k, Q.edgeLength k ≤ P.edgeLength k) (i : ZMod n)
    (hbuffer : Q.edgeLength i + |determinant (e (i - 1)) (e (i + 1))| + 1 ≤ P.edgeLength i) :
    ∀ k, Q.edgeLength k ≤ integerFacetExpansionLength e F P i k := by
  intro k
  have hM := cyclic_facet_relaxation_scale_positive e horder i
  have hscaled := scaled_facet_relaxation_lengths_dominate e horder Z F Q P hlen i
    (cyclicFacetRelaxationScale e i) hM.le le_rfl hbuffer k
  rw [scaled_final_facet_lengths] at hscaled
  nlinarith

-- relaxing a nonnegative number of inward levels includes the entire original polygon hull.
theorem cyclic_facet_relaxed_region_contains_original {n : ℕ} [NeZero n]
    (e : ZMod n → Site) (horder : CyclicEdgeOrder e) (F : Finset Site)
    (P : OrderedCyclicLatticePolygon e F) (i : ZMod n) (j : ℤ) (hj : 0 ≤ j) :
    latticeHull F ⊆ cyclicFacetRelaxedRegion e F P i j := by
  intro x hx k _hk
  have hnormal := ordered_cyclic_real_point_normal_minimum e horder F P x hx k
  have hcut : cyclicFacetRelaxedCut e F P i j k ≤ directionNormal (e k) (P.vertex k) := by
    unfold cyclicFacetRelaxedCut
    apply sub_le_self
    split_ifs <;> omega
  exact (Int.cast_le.mpr hcut).trans hnormal

-- saturating the unscaled walk produces exactly the same final relaxed region in original coordinates.
theorem exists_actual_integer_facet_expansion {n : ℕ} [NeZero n]
    (e : ZMod n → Site) (horder : CyclicEdgeOrder e) (Z F : Finset Site)
    (Q : OrderedCyclicLatticePolygon e Z) (P : OrderedCyclicLatticePolygon e F)
    (hlen : ∀ k, Q.edgeLength k ≤ P.edgeLength k) (i : ZMod n)
    (hbuffer : Q.edgeLength i + |determinant (e (i - 1)) (e (i + 1))| + 1 ≤ P.edgeLength i) :
    ∃ W : Finset Site, LatticeConvex W ∧ ∃ R : OrderedCyclicLatticePolygon e W,
      R.vertex = integerFacetExpansionVertex e F P i ∧
      R.edgeLength = integerFacetExpansionLength e F P i ∧
      latticeHull W = cyclicFacetRelaxedRegion e F P i (cyclicFacetRelaxationScale e i) ∧
      (∀ k, Q.edgeLength k ≤ R.edgeLength k) ∧ F ⊆ W := by
  have hM := cyclic_facet_relaxation_scale_positive e horder i
  have hMR : (cyclicFacetRelaxationScale e i : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hM
  have hdom := integer_facet_expansion_lengths_dominate e horder Z F Q P hlen i hbuffer
  have hpos : ∀ k, 0 < integerFacetExpansionLength e F P i k :=
    fun k => lt_of_lt_of_le (Q.length_pos k) (hdom k)
  obtain ⟨W, hW, R, hv, hr⟩ := exists_saturated_positive_cyclic_walk e
    (integerFacetExpansionVertex e F P i) (integerFacetExpansionLength e F P i) hpos
    (integer_facet_expansion_edge_equations e horder F P i)
  obtain ⟨S, _hS, T, hTv, _hTr, hSHull⟩ := exists_actual_scaled_facet_relaxation e horder Z F Q P hlen i
    (cyclicFacetRelaxationScale e i) hM.le le_rfl hbuffer
  have hvertices : (fun k => latticeEmbedding (cyclicFacetRelaxationScale e i • R.vertex k)) =
      (fun k => latticeEmbedding (T.vertex k)) := by
    funext k
    rw [hv, hTv, scaled_final_facet_vertices]
  have hscaled : (fun x : RealPlane => (cyclicFacetRelaxationScale e i : ℝ) • x) '' latticeHull W =
      (fun x : RealPlane => (cyclicFacetRelaxationScale e i : ℝ) • x) ''
        cyclicFacetRelaxedRegion e F P i (cyclicFacetRelaxationScale e i) := by
    rw [R.hull_eq, real_dilation_integer_walk_hull, hvertices, ← T.hull_eq, hSHull]
  have hHull : latticeHull W = cyclicFacetRelaxedRegion e F P i (cyclicFacetRelaxationScale e i) := by
    have he := congrArg (fun S : Set RealPlane =>
      (fun x : RealPlane => (cyclicFacetRelaxationScale e i : ℝ)⁻¹ • x) '' S) hscaled
    simpa only [inverse_real_dilation_image _ hMR] using he
  refine ⟨W, hW, R, hv, hr, hHull, ?_, ?_⟩
  · intro k
    rw [hr]
    exact hdom k
  · intro g hg
    apply hW g
    rw [hHull]
    exact cyclic_facet_relaxed_region_contains_original e horder F P i _ hM.le
      (subset_convexHull ℝ _ ⟨g, hg, rfl⟩)

-- the moved actual lattice vertex lies strictly beyond the original supporting line.
theorem integer_facet_expansion_moved_vertex_level {n : ℕ} [NeZero n]
    (e : ZMod n → Site) (F : Finset Site) (P : OrderedCyclicLatticePolygon e F) (i : ZMod n) :
    directionNormal (e i) (integerFacetExpansionVertex e F P i i) =
      directionNormal (e i) (P.vertex i) - cyclicFacetRelaxationScale e i := by
  have hreverse : directionNormal (e i) (e (i - 1)) = -determinant (e (i - 1)) (e i) := by
    change determinant (e i) (e (i - 1)) = -determinant (e (i - 1)) (e i)
    simp only [determinant]
    ring
  simp only [integerFacetExpansionVertex, ite_true, map_add, map_zsmul, smul_eq_mul, hreverse]
  dsimp [cyclicFacetRelaxationScale]
  ring

-- every actual polygon realizing the constructed walk is a genuine strict finite enlargement.
theorem integer_facet_expansion_strict {n : ℕ} [NeZero n]
    (e : ZMod n → Site) (horder : CyclicEdgeOrder e) (F W : Finset Site)
    (P : OrderedCyclicLatticePolygon e F) (R : OrderedCyclicLatticePolygon e W) (i : ZMod n)
    (hv : R.vertex = integerFacetExpansionVertex e F P i) : F ≠ W := by
  intro he
  have hvertex : integerFacetExpansionVertex e F P i i ∈ F := by
    have hWvertex : integerFacetExpansionVertex e F P i i ∈ W := by
      rw [← hv]
      exact R.vertex_mem i
    exact he.symm ▸ hWvertex
  have hmin := ordered_cyclic_real_point_normal_minimum e horder F P _
    (subset_convexHull ℝ _ ⟨_, hvertex, rfl⟩) i
  rw [latticeNormal_embedding, integer_facet_expansion_moved_vertex_level] at hmin
  have hbound : directionNormal (e i) (P.vertex i) ≤
      directionNormal (e i) (P.vertex i) - cyclicFacetRelaxationScale e i := by exact_mod_cast hmin
  have hM := cyclic_facet_relaxation_scale_positive e horder i
  omega

end KumarNivat
