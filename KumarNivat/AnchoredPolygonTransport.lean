import KumarNivat.AnchoredMaximalCyclic
import KumarNivat.NewtonEnvelopeAffine

namespace KumarNivat

-- actual positive integer affinities carry both the lattice vertices and their primitive edge lengths.
noncomputable def orderedCyclicPolygonPositiveAffinity {n : ℕ} [NeZero n]
    (e : ZMod n → Site) (F Q : Finset Site) (P : OrderedCyclicLatticePolygon e F)
    (d : ℤ) (hd : 0 < d) (U : Site) (hQ : LatticeConvex Q)
    (hHull : latticeHull Q = (fun z : RealPlane => latticeEmbedding U + (d : ℝ) • z) '' latticeHull F) :
    OrderedCyclicLatticePolygon e Q where
  vertex i := U + d • P.vertex i
  edgeLength i := d * P.edgeLength i
  length_pos i := mul_pos hd (P.length_pos i)
  edge_eq i := by
    rw [P.edge_eq, smul_add, smul_smul]
    abel
  vertex_mem i := by
    apply hQ
    rw [hHull]
    refine ⟨latticeEmbedding (P.vertex i), subset_convexHull ℝ _ ⟨P.vertex i, P.vertex_mem i, rfl⟩, ?_⟩
    rw [latticeEmbedding_add, latticeEmbedding_zsmul]
  hull_eq := by
    let T : RealPlane →ᵃ[ℝ] RealPlane :=
      { toFun := fun z => latticeEmbedding U + (d : ℝ) • z
        linear := (d : ℝ) • LinearMap.id
        map_vadd' := by
          intro z w
          change latticeEmbedding U + (d : ℝ) • (w + z) =
            (d : ℝ) • w + (latticeEmbedding U + (d : ℝ) • z)
          rw [smul_add]
          abel }
    have hgen : T '' Set.range (fun i => latticeEmbedding (P.vertex i)) =
        Set.range (fun i => latticeEmbedding (U + d • P.vertex i)) := by
      ext z
      constructor
      · rintro ⟨_x, ⟨i, rfl⟩, rfl⟩
        refine ⟨i, ?_⟩
        change latticeEmbedding (U + d • P.vertex i) = T (latticeEmbedding (P.vertex i))
        rw [latticeEmbedding_add, latticeEmbedding_zsmul]
        rfl
      · rintro ⟨i, rfl⟩
        refine ⟨latticeEmbedding (P.vertex i), ⟨i, rfl⟩, ?_⟩
        change latticeEmbedding U + (d : ℝ) • latticeEmbedding (P.vertex i) =
          latticeEmbedding (U + d • P.vertex i)
        rw [latticeEmbedding_add, latticeEmbedding_zsmul]
    rw [hHull, P.hull_eq]
    change T '' convexHull ℝ (Set.range (fun i => latticeEmbedding (P.vertex i))) = _
    rw [T.image_convexHull, hgen]

-- translating the full finite observation set preserves lattice convexity.
theorem latticeConvex_integer_translation (F : Finset Site) (hF : LatticeConvex F) (U : Site) :
    LatticeConvex (F.image (fun g => U + g)) := by
  classical
  intro g hg
  have hHull : latticeHull (F.image (fun g => U + g)) =
      (fun z : RealPlane => latticeEmbedding U + z) '' latticeHull F := by
    simpa only [one_smul, Int.cast_one] using latticeHull_integer_affinity F 1 U
  rw [hHull] at hg
  obtain ⟨z, hz, he⟩ := hg
  have hsub : latticeEmbedding (g - U) = z := by
    rw [latticeEmbedding_sub, ← he]
    change latticeEmbedding U + z - latticeEmbedding U = z
    abel
  have hm : g - U ∈ F := hF _ (hsub.symm ▸ hz)
  exact Finset.mem_image.mpr ⟨g - U, hm, by abel⟩

-- translation keeps the same primitive fan and every actual edge length.
noncomputable def orderedCyclicPolygonTranslation {n : ℕ} [NeZero n]
    (e : ZMod n → Site) (F : Finset Site) (P : OrderedCyclicLatticePolygon e F)
    (hF : LatticeConvex F) (U : Site) :
    OrderedCyclicLatticePolygon e (F.image (fun g => U + g)) :=
  orderedCyclicPolygonPositiveAffinity e F (F.image (fun g => U + g)) P 1 (by norm_num) U
    (latticeConvex_integer_translation F hF U)
    (by simpa only [one_smul, Int.cast_one] using latticeHull_integer_affinity F 1 U)

-- a boundary site forces the final endpoint of the actual tangent edge onto that same supporting line.
theorem ordered_cyclic_tangent_endpoint_on_boundary {n : ℕ} [NeZero n]
    (e : ZMod n → Site) (horder : CyclicEdgeOrder e) (M : Finset Site)
    (P : OrderedCyclicLatticePolygon e M) (G : Site) (hG : G ∈ M) (cut : ℤ)
    (hcut : directionNormal (e 0) G = cut)
    (hhalf : ∀ g ∈ M, cut ≤ directionNormal (e 0) g) :
    directionNormal (e 0) (P.vertex 1) = cut := by
  have hg : latticeEmbedding G ∈ latticeHull M := subset_convexHull ℝ _ ⟨G, hG, rfl⟩
  rw [P.hull_eq, ordered_cyclic_walk_facet_presentation e horder P.vertex
    P.edgeLength P.length_pos P.edge_eq] at hg
  have hmin := hg 0
  rw [latticeNormal_embedding, hcut] at hmin
  have hminZ : directionNormal (e 0) (P.vertex 0) ≤ cut := by exact_mod_cast hmin
  have hzero : directionNormal (e 0) (P.vertex 0) = cut :=
    le_antisymm hminZ (hhalf _ (P.vertex_mem 0))
  have he := P.edge_eq 0
  simp only [zero_add] at he
  rw [he, map_add, map_zsmul, directionNormal_self, smul_zero, add_zero, hzero]

-- primitivity gives the actual integer anchor shift; no independent anchor parameter is assumed.
theorem ordered_cyclic_tangent_anchor_shift {n : ℕ} [NeZero n]
    (e : ZMod n → Site) (horder : CyclicEdgeOrder e) (M : Finset Site)
    (P : OrderedCyclicLatticePolygon e M) (G : Site) (hG : G ∈ M) (cut : ℤ)
    (hprimitive : Int.gcd (e 0).1 (e 0).2 = 1)
    (hcut : directionNormal (e 0) G = cut)
    (hhalf : ∀ g ∈ M, cut ≤ directionNormal (e 0) g) :
    ∃ k : ℤ, P.vertex 1 = G + k • e 0 := by
  obtain ⟨τ, _hτ, hker⟩ := primitive_direction_coordinate (e 0) hprimitive
  have he := ordered_cyclic_tangent_endpoint_on_boundary e horder M P G hG cut hcut hhalf
  have hn : directionNormal (e 0) (P.vertex 1 - G) = 0 := by rw [map_sub, he, hcut, sub_self]
  refine ⟨τ (P.vertex 1 - G), ?_⟩
  have hline := hker _ hn
  rw [← hline]
  abel

-- the translated polygon retains the actual shifted match with one phase of the original reference.
theorem agreement_on_tangent_anchored_polygon {A : Type*} (c w : Site → A)
    (M : Finset Site) (u a : Site) (k : ℤ) (hagree : ∀ g ∈ M, shift u c g = w g) :
    ∀ g ∈ M.image (fun h => -k • a + h),
      shift (u + k • a) c g = shift (k • a) w g := by
  classical
  intro g hg
  obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hg
  have hleft : -k • a + h + (u + k • a) = h + u := by rw [neg_smul]; abel
  have hright : -k • a + h + k • a = h := by rw [neg_smul]; abel
  simpa only [shift, hleft, hright] using hagree h hh

-- the actual boundary endpoint chooses an integer translation and produces the shared anchored polygon and match.
theorem exists_tangent_anchored_cyclic_polygon {A : Type*} {n : ℕ} [NeZero n]
    (c w : Site → A) (u : Site) (e : ZMod n → Site) (horder : CyclicEdgeOrder e)
    (M : Finset Site) (P : OrderedCyclicLatticePolygon e M) (hM : LatticeConvex M)
    (G : Site) (hG : G ∈ M) (cut : ℤ) (hprimitive : Int.gcd (e 0).1 (e 0).2 = 1)
    (hcut : directionNormal (e 0) G = cut)
    (hhalf : ∀ g ∈ M, cut ≤ directionNormal (e 0) g)
    (hagree : ∀ g ∈ M, shift u c g = w g) :
    ∃ k : ℤ, ∃ Q : OrderedCyclicLatticePolygon e (M.image (fun g => -k • e 0 + g)),
      Q.vertex 1 = G ∧ (∀ i, Q.edgeLength i = P.edgeLength i) ∧
      LatticeConvex (M.image (fun g => -k • e 0 + g)) ∧
      (∀ g ∈ M.image (fun g => -k • e 0 + g), cut ≤ directionNormal (e 0) g) ∧
      ∀ g ∈ M.image (fun g => -k • e 0 + g),
        shift (u + k • e 0) c g = shift (k • e 0) w g := by
  classical
  obtain ⟨k, hk⟩ := ordered_cyclic_tangent_anchor_shift e horder M P G hG cut hprimitive hcut hhalf
  let Q := orderedCyclicPolygonTranslation e M P hM (-k • e 0)
  refine ⟨k, Q, ?_, ?_, latticeConvex_integer_translation M hM (-k • e 0), ?_,
    agreement_on_tangent_anchored_polygon c w M u (e 0) k hagree⟩
  · change -k • e 0 + (1 : ℤ) • P.vertex 1 = G
    rw [one_smul, hk, neg_smul]
    abel
  · intro i
    change 1 * P.edgeLength i = P.edgeLength i
    exact one_mul _
  · intro g hg
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hg
    rw [map_add, map_zsmul, directionNormal_self, smul_zero, zero_add]
    exact hhalf h hh

end KumarNivat
