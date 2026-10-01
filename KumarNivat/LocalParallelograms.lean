import KumarNivat.SegmentSummandGeometry
import KumarNivat.ExposedPolygonFaces
import KumarNivat.LatticeRowRuns

namespace KumarNivat

open scoped Pointwise

-- the local observation parallelogram uses the actual generating edge and the opposite-edge segment length.
def latticeParallelogram (q₀ a b : Site) (r t : ℕ) : Set RealPlane :=
  lineInterval (latticeEmbedding q₀) (latticeEmbedding b) 0 (t : ℝ) +
    lineInterval 0 (latticeEmbedding a) 0 (r : ℝ)

-- a face minimizing a strictly increasing normal lies in the residual summand itself.
theorem positive_summand_supporting_face_subset_residual (P C : Set RealPlane)
    (a : Site) (r m : ℝ) (hr : 0 ≤ r) (μ : Site →+ ℤ) (ha : 0 < μ a)
    (hsum : P = lineInterval 0 (latticeEmbedding a) 0 r + C)
    (hmin : ∀ z ∈ P, m ≤ latticeNormal μ z) :
    normalFace P (latticeNormal μ) m ⊆ C := by
  intro z hz
  have hzmem := hz.1
  rw [hsum] at hzmem
  obtain ⟨w, hw, c, hc, he⟩ := Set.mem_add.mp hzmem
  obtain ⟨s, hs, hws⟩ := hw
  have hzero : (0 : RealPlane) ∈ lineInterval 0 (latticeEmbedding a) 0 r :=
    ⟨0, ⟨le_rfl, hr⟩, by simp only [zero_smul, add_zero]⟩
  have hcmem : c ∈ P := by
    rw [hsum]
    simpa only [zero_add] using Set.add_mem_add hzero hc
  have hcbound := hmin c hcmem
  have helevel := hz.2
  have hzsite : z = s • latticeEmbedding a + c := by
    change 0 + s • latticeEmbedding a = w at hws
    rw [← he, ← hws, zero_add]
  rw [hzsite, map_add, map_smul, latticeNormal_embedding, smul_eq_mul] at helevel
  have hapos : (0 : ℝ) < (μ a : ℝ) := by exact_mod_cast ha
  have hs₀ : s = 0 := by nlinarith [hs.1]
  simpa only [hzsite, hs₀, zero_smul, zero_add] using hc

-- the generated face thickens along the opposite-edge summand into a parallelogram contained in the original hull.
theorem supporting_edge_parallelogram_subset_hull (S : Finset Site) (a b q₀ : Site)
    (r t : ℕ) (C : Set RealPlane)
    (hsum : latticeHull S = lineInterval 0 (latticeEmbedding a) 0 (r : ℝ) + C)
    (μ : Site →+ ℤ) (m : ℤ) (ha : 0 < μ a) (hb : μ b = 0)
    (hmin : ∀ u ∈ S, m ≤ μ u) (hq₀ : q₀ ∈ S) (hq₁ : q₀ + (t : ℤ) • b ∈ S)
    (hq₀level : μ q₀ = m) :
    latticeParallelogram q₀ a b r t ⊆ latticeHull S := by
  have hline : lineInterval (latticeEmbedding q₀) (latticeEmbedding b) 0 (t : ℝ) ⊆
      normalFace (latticeHull S) (latticeNormal μ) (m : ℝ) := by
    intro z hz
    have hsegment := lineInterval_subset_convex_set (latticeHull S) (convex_convexHull ℝ _)
      (latticeEmbedding q₀) (latticeEmbedding b) 0 (t : ℝ) (Nat.cast_nonneg t)
      (by simpa only [latticeHull, zero_smul, add_zero] using
          (subset_convexHull ℝ (latticeEmbedding '' (S : Set Site)) ⟨q₀, hq₀, rfl⟩))
      (by rw [← Int.cast_natCast t, ← latticeEmbedding_zsmul, ← latticeEmbedding_add]
          exact subset_convexHull ℝ (latticeEmbedding '' (S : Set Site)) ⟨q₀ + (t : ℤ) • b, hq₁, rfl⟩)
    refine ⟨hsegment hz, ?_⟩
    obtain ⟨s, _hs, rfl⟩ := hz
    rw [map_add, map_smul, latticeNormal_embedding, latticeNormal_embedding, hq₀level, hb,
      Int.cast_zero, smul_zero, add_zero]
  have hfaceC := positive_summand_supporting_face_subset_residual (latticeHull S) C a (r : ℝ)
    (m : ℝ) (Nat.cast_nonneg r) μ ha hsum (lower_face_hull_bound S μ m hmin)
  intro z hz
  obtain ⟨u, hu, v, hv, rfl⟩ := Set.mem_add.mp hz
  rw [hsum]
  simpa only [add_comm] using Set.add_mem_add hv (hfaceC (hline hu))

-- a b-parallel row through the local parallelogram contains an actual consecutive off-face lattice block.
theorem off_face_row_run_of_contained_parallelogram (S : Finset Site) (hS : LatticeConvex S)
    (q₀ a b : Site) (r t : ℕ) (ht : 0 < t)
    (hsub : latticeParallelogram q₀ a b r t ⊆ latticeHull S)
    (μ : Site →+ ℤ) (m : ℤ) (hb : μ b = 0)
    (g : Site) (hg : latticeEmbedding g ∈ latticeParallelogram q₀ a b r t) (hgm : μ g ≠ m) :
    ∃ E : Site, ∃ d : ℤ, g = E + d • b ∧ E ∈ S \ lowerLatticeFace S μ m ∧
      ∀ i : Fin t, E + (i.val : ℤ) • b ∈ S \ lowerLatticeFace S μ m := by
  let C := (fun z : RealPlane => latticeEmbedding q₀ + z) ''
    lineInterval 0 (latticeEmbedding a) 0 (r : ℝ)
  have hrewrite : latticeParallelogram q₀ a b r t =
      lineInterval 0 (latticeEmbedding b) 0 (t : ℝ) + C := by
    ext z
    constructor
    · intro hz
      obtain ⟨u, ⟨s, hs, rfl⟩, v, hv, he⟩ := Set.mem_add.mp hz
      refine Set.mem_add.mpr ⟨s • latticeEmbedding b, ⟨s, hs, by simp only [zero_add]⟩,
        latticeEmbedding q₀ + v, ⟨v, hv, rfl⟩, ?_⟩
      change (latticeEmbedding q₀ + s • latticeEmbedding b) + v = z at he
      rw [← he]
      ac_rfl
    · intro hz
      obtain ⟨u, ⟨s, hs, rfl⟩, v, ⟨w, hw, rfl⟩, he⟩ := Set.mem_add.mp hz
      refine Set.mem_add.mpr ⟨latticeEmbedding q₀ + s • latticeEmbedding b, ⟨s, hs, rfl⟩, w, hw, ?_⟩
      rw [← he]
      simp only [zero_add]
      abel
  rw [hrewrite] at hg
  obtain ⟨u, ⟨s, _hs, rfl⟩, v, hv, he⟩ := Set.mem_add.mp hg
  simp only [zero_add] at he
  obtain ⟨E, d, hsite, hE, hrun⟩ := lattice_row_run_from_residual_line_point_of_subset S hS b t ht C
    (by rw [← hrewrite]; exact hsub) g s v hv he
  have hElevel : μ E = μ g := by rw [hsite, map_add, map_zsmul, hb, smul_zero, add_zero]
  refine ⟨E, d, hsite, Finset.mem_sdiff.mpr ⟨hE, ?_⟩, ?_⟩
  · intro hf
    exact hgm (hElevel.symm.trans (Finset.mem_filter.mp hf).2)
  · intro i
    refine Finset.mem_sdiff.mpr ⟨hrun i, ?_⟩
    intro hf
    have hlevel : μ (E + (i.val : ℤ) • b) = μ g := by
      rw [map_add, map_zsmul, hb, smul_zero, add_zero, hElevel]
    exact hgm (hlevel.symm.trans (Finset.mem_filter.mp hf).2)

end KumarNivat
