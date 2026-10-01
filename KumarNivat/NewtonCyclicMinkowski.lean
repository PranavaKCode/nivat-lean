import KumarNivat.NewtonCyclicNormals

namespace KumarNivat

open scoped Pointwise

-- common maxima from the actual cyclic order identify the hull of vertexwise sums with the full minkowski sum.
theorem ordered_cyclic_walk_minkowski {n : ℕ} [NeZero n]
    (e : ZMod n → Site) (horder : CyclicEdgeOrder e)
    (v w : ZMod n → Site) (r d : ZMod n → ℤ)
    (hr : ∀ i, 0 < r i) (hd : ∀ i, 0 ≤ d i)
    (hv : ∀ i, v (i + 1) = v i + r i • e i)
    (hw : ∀ i, w (i + 1) = w i + d i • e i) :
    convexHull ℝ (Set.range (fun i => latticeEmbedding (v i + w i))) =
      convexHull ℝ (Set.range (fun i => latticeEmbedding (v i))) +
        convexHull ℝ (Set.range (fun i => latticeEmbedding (w i))) := by
  classical
  let A := Set.range (fun i => latticeEmbedding (v i))
  let B := Set.range (fun i => latticeEmbedding (w i))
  let C := Set.range (fun i => latticeEmbedding (v i + w i))
  have hleft : convexHull ℝ C ⊆ convexHull ℝ A + convexHull ℝ B := by
    apply convexHull_min ?_ ((convex_convexHull ℝ _).add (convex_convexHull ℝ _))
    rintro _ ⟨i, rfl⟩
    change latticeEmbedding (v i + w i) ∈ convexHull ℝ A + convexHull ℝ B
    rw [latticeEmbedding_add]
    exact Set.add_mem_add (subset_convexHull ℝ _ ⟨i, rfl⟩) (subset_convexHull ℝ _ ⟨i, rfl⟩)
  have hgen : A + B ⊆ convexHull ℝ C := by
    rintro _ ⟨_x, ⟨i, rfl⟩, _y, ⟨j, rfl⟩, rfl⟩
    by_contra hn
    have hclosed : IsClosed (convexHull ℝ C) :=
      (Set.finite_range (fun i => latticeEmbedding (v i + w i))).isClosed_convexHull ℝ
    obtain ⟨L, t, hbelow, habove⟩ := geometric_hahn_banach_closed_point
      (convex_convexHull ℝ _) hclosed hn
    obtain ⟨k, hkV, hkW⟩ := ordered_cyclic_common_linear_maximum e horder v w r d hr hd hv hw L.toLinearMap
    have hmax : L (latticeEmbedding (v i) + latticeEmbedding (w j)) ≤
        L (latticeEmbedding (v k + w k)) := by
      rw [latticeEmbedding_add, map_add, map_add]
      exact add_le_add (hkV i) (hkW j)
    have hlow := hbelow (latticeEmbedding (v k + w k)) (subset_convexHull ℝ _ ⟨k, rfl⟩)
    linarith
  have hright : convexHull ℝ A + convexHull ℝ B ⊆ convexHull ℝ C := by
    rw [← convexHull_add]
    exact convexHull_min hgen (convex_convexHull ℝ _)
  exact Set.Subset.antisymm hleft hright

-- subtracting coordinatewise smaller cyclic edge lengths constructs the compact convex residual itself.
theorem ordered_cyclic_edge_envelope_minkowski {n : ℕ} [NeZero n]
    (e : ZMod n → Site) (horder : CyclicEdgeOrder e) (Z F : Finset Site)
    (Q : OrderedCyclicLatticePolygon e Z) (P : OrderedCyclicLatticePolygon e F)
    (hlen : ∀ i, Q.edgeLength i ≤ P.edgeLength i) :
    ∃ C : Set RealPlane,
      C = convexHull ℝ (Set.range (fun i => latticeEmbedding (P.vertex i - Q.vertex i))) ∧
      Convex ℝ C ∧ IsCompact C ∧ C.Nonempty ∧ latticeHull F = latticeHull Z + C := by
  let w := fun i => P.vertex i - Q.vertex i
  let d := fun i => P.edgeLength i - Q.edgeLength i
  have hd : ∀ i, 0 ≤ d i := fun i => sub_nonneg.mpr (hlen i)
  have hw : ∀ i, w (i + 1) = w i + d i • e i := by
    intro i
    dsimp [w, d]
    rw [P.edge_eq, Q.edge_eq, sub_smul]
    abel
  have hsum := ordered_cyclic_walk_minkowski e horder Q.vertex w Q.edgeLength d
    Q.length_pos hd Q.edge_eq hw
  have he : (fun i => latticeEmbedding (Q.vertex i + w i)) =
      (fun i => latticeEmbedding (P.vertex i)) := by
    funext i
    congr 1
    dsimp [w]
    abel
  rw [he, ← P.hull_eq, ← Q.hull_eq] at hsum
  let C := convexHull ℝ (Set.range (fun i => latticeEmbedding (w i)))
  have hnonempty : C.Nonempty :=
    ⟨latticeEmbedding (w 0), subset_convexHull ℝ _ ⟨0, rfl⟩⟩
  exact ⟨C, rfl, convex_convexHull ℝ _,
    (Set.finite_range (fun i => latticeEmbedding (w i))).isCompact_convexHull ℝ, hnonempty, hsum⟩

-- a shared actual anchor puts zero in the constructed residual and proves polygon inclusion.
theorem ordered_cyclic_anchored_minkowski_inclusion {n : ℕ} [NeZero n]
    (e : ZMod n → Site) (horder : CyclicEdgeOrder e) (Z F : Finset Site)
    (Q : OrderedCyclicLatticePolygon e Z) (P : OrderedCyclicLatticePolygon e F)
    (hlen : ∀ i, Q.edgeLength i ≤ P.edgeLength i) (i₀ : ZMod n)
    (hanchor : P.vertex i₀ = Q.vertex i₀) :
    ∃ C : Set RealPlane, Convex ℝ C ∧ IsCompact C ∧ (0 : RealPlane) ∈ C ∧
      latticeHull F = latticeHull Z + C ∧ latticeHull Z ⊆ latticeHull F := by
  obtain ⟨C, hC, hconv, hcompact, _hnonempty, hsum⟩ :=
    ordered_cyclic_edge_envelope_minkowski e horder Z F Q P hlen
  have h0 : (0 : RealPlane) ∈ C := by
    rw [hC]
    have he0 : latticeEmbedding (P.vertex i₀ - Q.vertex i₀) = (0 : RealPlane) := by
      rw [hanchor, sub_self]
      ext <;> simp [latticeEmbedding]
    rw [← he0]
    exact subset_convexHull ℝ _ ⟨i₀, rfl⟩
  refine ⟨C, hconv, hcompact, h0, hsum, ?_⟩
  intro z hz
  rw [hsum]
  simpa only [add_zero] using Set.add_mem_add hz h0

-- lattice convexity turns the proved real inclusion into inclusion of the actual finite observation sets.
theorem ordered_cyclic_anchored_lattice_inclusion {n : ℕ} [NeZero n]
    (e : ZMod n → Site) (horder : CyclicEdgeOrder e) (Z F : Finset Site)
    (Q : OrderedCyclicLatticePolygon e Z) (P : OrderedCyclicLatticePolygon e F)
    (hlen : ∀ i, Q.edgeLength i ≤ P.edgeLength i) (i₀ : ZMod n)
    (hanchor : P.vertex i₀ = Q.vertex i₀) (hF : LatticeConvex F) : Z ⊆ F := by
  obtain ⟨_C, _hconv, _hcompact, _h0, _hsum, hsub⟩ :=
    ordered_cyclic_anchored_minkowski_inclusion e horder Z F Q P hlen i₀ hanchor
  intro z hz
  exact hF z (hsub (subset_convexHull ℝ _ ⟨z, hz, rfl⟩))

end KumarNivat
