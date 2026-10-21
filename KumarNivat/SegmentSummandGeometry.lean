module

public import KumarNivat.PrimitiveLineSpans
public import KumarNivat.ConvexNormalSlices
public import KumarNivat.PairedDirections

@[expose] public section

namespace KumarNivat

open scoped Pointwise

-- convexity fills a parameter interval once both of its actual endpoints are present.
theorem lineInterval_subset_convex_set (P : Set RealPlane) (hP : Convex ℝ P)
    (a v : RealPlane) (s t : ℝ) (hst : s ≤ t)
    (hs : a + s • v ∈ P) (ht : a + t • v ∈ P) : lineInterval a v s t ⊆ P := by
  rw [lineInterval_eq_segment a v s t hst]
  exact hP.segment_subset hs ht

-- opposite row anchors give a genuine segment summand by eroding the convex set by that segment.
theorem primitive_segment_summand_of_opposite_anchors (P : Set RealPlane) (hP : Convex ℝ P)
    (p : Site) (hprimitive : Int.gcd p.1 p.2 = 1) (r : ℝ) (hr : 0 ≤ r)
    (m M : ℝ) (a₀ a₁ : RealPlane)
    (ha₀ : a₀ ∈ P) (ha₀r : a₀ + r • latticeEmbedding p ∈ P)
    (ha₁ : a₁ ∈ P) (ha₁r : a₁ + r • latticeEmbedding p ∈ P)
    (h₀ : latticeNormal (directionNormal p) a₀ = m)
    (h₁ : latticeNormal (directionNormal p) a₁ = M)
    (hbounds : ∀ x ∈ P, m ≤ latticeNormal (directionNormal p) x ∧
      latticeNormal (directionNormal p) x ≤ M) :
    ∃ C : Set RealPlane, Convex ℝ C ∧ P = lineInterval 0 (latticeEmbedding p) 0 r + C := by
  let C : Set RealPlane := {a | a ∈ P ∧ a + r • latticeEmbedding p ∈ P}
  have hC : Convex ℝ C := hP.inter (hP.translate_preimage_left (r • latticeEmbedding p))
  refine ⟨C, hC, ?_⟩
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨a, ha, hlevel⟩ := convex_point_on_intermediate_normal_level C hC
      (latticeNormal (directionNormal p)) m M a₀ a₁ ⟨ha₀, ha₀r⟩ ⟨ha₁, ha₁r⟩ h₀ h₁
      (latticeNormal (directionNormal p) x) (hbounds x hx)
    obtain ⟨s, hsx⟩ := real_points_on_same_primitive_normal p hprimitive a x hlevel.symm
    by_cases hs₀ : 0 ≤ s
    · by_cases hsr : s ≤ r
      · refine Set.mem_add.mpr ⟨s • latticeEmbedding p,
          ⟨s, ⟨hs₀, hsr⟩, by simp only [zero_add]⟩, a, ha, ?_⟩
        simpa only [add_comm] using hsx.symm
      · have hspan := lineInterval_subset_convex_set P hP a (latticeEmbedding p) 0 s hs₀
          (by simpa only [zero_smul, add_zero] using ha.1) (by rw [← hsx]; exact hx)
        let c := x - r • latticeEmbedding p
        have hc : c ∈ C := by
          refine ⟨hspan ?_, ?_⟩
          · refine ⟨s - r, ⟨by linarith, by linarith⟩, ?_⟩
            dsimp [c]
            rw [hsx, sub_smul]
            abel
          · dsimp [c]
            simpa only [sub_add_cancel] using hx
        refine Set.mem_add.mpr ⟨r • latticeEmbedding p,
          ⟨r, ⟨hr, le_rfl⟩, by simp only [zero_add]⟩, c, hc, ?_⟩
        dsimp [c]
        abel
    · have hsr : s ≤ r := by linarith
      have hspan := lineInterval_subset_convex_set P hP a (latticeEmbedding p) s r hsr
        (by rw [← hsx]; exact hx) ha.2
      have hxr : x + r • latticeEmbedding p ∈ P := by
        apply hspan
        refine ⟨s + r, ⟨by linarith, by linarith⟩, ?_⟩
        change a + (s + r) • latticeEmbedding p = x + r • latticeEmbedding p
        rw [hsx, add_smul]
        ac_rfl
      exact Set.mem_add.mpr ⟨0, ⟨0, ⟨le_rfl, hr⟩, by simp only [zero_smul, add_zero]⟩,
        x, ⟨hx, hxr⟩, by simp only [zero_add]⟩
  · intro x hx
    obtain ⟨w, ⟨s, hs, rfl⟩, a, ha, rfl⟩ := Set.mem_add.mp hx
    have hspan := lineInterval_subset_convex_set P hP a (latticeEmbedding p) 0 r hr
      (by simpa only [zero_smul, add_zero] using ha.1) ha.2
    have hpoint : a + s • latticeEmbedding p ∈ lineInterval a (latticeEmbedding p) 0 r := ⟨s, hs, rfl⟩
    simpa only [zero_add, add_zero, add_comm] using hspan hpoint

-- the two actual supporting-face counts produce enough anchors for the polygon's segment summand.
theorem segment_summand_of_opposite_face_cardinalities (S : Finset Site) (hS : LatticeConvex S)
    (p : Site) (hprimitive : Int.gcd p.1 p.2 = 1) (m M : ℤ)
    (hbounds : ∀ u ∈ S, m ≤ directionNormal p u ∧ directionNormal p u ≤ M)
    (r : ℕ) (hlower : r + 1 ≤ (lowerLatticeFace S (directionNormal p) m).card)
    (hupper : r + 1 ≤ (lowerLatticeFace S (-directionNormal p) (-M)).card) :
    ∃ C : Set RealPlane, Convex ℝ C ∧
      latticeHull S = lineInterval 0 (latticeEmbedding p) 0 (r : ℝ) + C := by
  classical
  obtain ⟨a₀, ha₀, ha₀r⟩ := lattice_segment_anchor_of_collinear_cardinality S
    (lowerLatticeFace S (directionNormal p) m) hS (Finset.filter_subset _ _) p hprimitive m
    (fun u hu => (Finset.mem_filter.mp hu).2) r hlower
  have hupperlevel : ∀ u ∈ lowerLatticeFace S (-directionNormal p) (-M), directionNormal p u = M := by
    intro u hu
    have he := (Finset.mem_filter.mp hu).2
    change -directionNormal p u = -M at he
    exact neg_inj.mp he
  obtain ⟨a₁, ha₁, ha₁r⟩ := lattice_segment_anchor_of_collinear_cardinality S
    (lowerLatticeFace S (-directionNormal p) (-M)) hS (Finset.filter_subset _ _) p hprimitive M
    hupperlevel r hupper
  have hullmem (u : Site) (hu : u ∈ S) : latticeEmbedding u ∈ latticeHull S := subset_convexHull ℝ _ ⟨u, hu, rfl⟩
  have hsub : latticeEmbedding '' (S : Set Site) ⊆
      {z : RealPlane | (m : ℝ) ≤ latticeNormal (directionNormal p) z ∧
        latticeNormal (directionNormal p) z ≤ (M : ℝ)} := by
    rintro _ ⟨u, hu, rfl⟩
    change (m : ℝ) ≤ latticeNormal (directionNormal p) (latticeEmbedding u) ∧
      latticeNormal (directionNormal p) (latticeEmbedding u) ≤ (M : ℝ)
    rw [latticeNormal_embedding]
    exact ⟨by exact_mod_cast (hbounds u hu).1, by exact_mod_cast (hbounds u hu).2⟩
  have hhullbounds : ∀ z ∈ latticeHull S, (m : ℝ) ≤ latticeNormal (directionNormal p) z ∧
      latticeNormal (directionNormal p) z ≤ (M : ℝ) :=
    convexHull_min hsub ((convex_Icc (m : ℝ) (M : ℝ)).linear_preimage (latticeNormal (directionNormal p)))
  apply primitive_segment_summand_of_opposite_anchors (latticeHull S) (convex_convexHull ℝ _) p hprimitive
    (r : ℝ) (Nat.cast_nonneg r) (m : ℝ) (M : ℝ) (latticeEmbedding a₀) (latticeEmbedding a₁)
  · exact hullmem a₀ (Finset.mem_filter.mp ha₀).1
  · simpa only [latticeEmbedding_add, latticeEmbedding_zsmul, Int.cast_natCast] using hullmem _ ha₀r
  · exact hullmem a₁ (Finset.mem_filter.mp ha₁).1
  · simpa only [latticeEmbedding_add, latticeEmbedding_zsmul, Int.cast_natCast] using hullmem _ ha₁r
  · rw [latticeNormal_embedding, (Finset.mem_filter.mp ha₀).2]
  · rw [latticeNormal_embedding, hupperlevel a₁ ha₁]
  · exact hhullbounds

end KumarNivat
