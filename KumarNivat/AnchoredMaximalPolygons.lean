module

public import KumarNivat.AnchoredMaximalCoordinates

@[expose] public section

namespace KumarNivat

-- the actual fixed oriented edge normals describe the entire lattice polygon hull.
def HasIntegerFacetPresentation {I : Type*} (J : Finset I) (μ : I → Site →+ ℤ)
    (P : Finset Site) : Prop :=
  ∃ cut : I → ℤ, latticeHull P =
    {z : RealPlane | ∀ i ∈ J, (cut i : ℝ) ≤ latticeNormal (μ i) z}

-- the finitely many possible separating slopes give one uniform right-coordinate bound.
noncomputable def rightFacetCoordinateBound {I : Type*} (J : Finset I)
    (μ : I → Site →+ ℤ) (W : ℤ) (q v : Site) : ℤ :=
  (∑ i ∈ J, (|μ i q| + W * |μ i v|)) + 1

-- each actual facet's bound is below the same nonnegative finite sum.
theorem right_facet_coordinate_bound_data {I : Type*} (J : Finset I)
    (μ : I → Site →+ ℤ) (W : ℤ) (hW : 0 ≤ W) (q v : Site) :
    0 ≤ rightFacetCoordinateBound J μ W q v ∧
      ∀ i ∈ J, |μ i q| + W * |μ i v| ≤ rightFacetCoordinateBound J μ W q v := by
  classical
  have hterm : ∀ i, 0 ≤ |μ i q| + W * |μ i v| :=
    fun _ => add_nonneg (abs_nonneg _) (mul_nonneg hW (abs_nonneg _))
  have hsum : 0 ≤ ∑ i ∈ J, (|μ i q| + W * |μ i v|) :=
    Finset.sum_nonneg (fun i _ => hterm i)
  refine ⟨by dsimp [rightFacetCoordinateBound]; omega, ?_⟩
  intro i hi
  have hsingle : |μ i q| + W * |μ i v| ≤ ∑ j ∈ J, (|μ j q| + W * |μ j v|) :=
    Finset.single_le_sum (fun j _ => hterm j) hi
  dsimp [rightFacetCoordinateBound]
  omega

-- a retained disagreement excludes the polygon through an actual right-facing facet.
theorem retained_disagreement_separating_facet {A I : Type*}
    (z w : Site → A) (F P : Finset Site) (a q : Site)
    (hP : LatticeConvex P) (hFP : F ⊆ P) (hq : q ∈ polygonHalfStrip F a)
    (hqfail : z q ≠ w q) (hagree : ∀ g ∈ P, z g = w g)
    (J : Finset I) (μ : I → Site →+ ℤ) (hfacets : HasIntegerFacetPresentation J μ P) :
    ∃ i ∈ J, μ i a < 0 ∧ ∀ g ∈ P, μ i q < μ i g := by
  classical
  obtain ⟨cut, hHull⟩ := hfacets
  have hnormal (g : Site) (hg : g ∈ P) : ∀ i ∈ J, cut i ≤ μ i g := by
    have hmem : latticeEmbedding g ∈ latticeHull P := subset_convexHull ℝ _ ⟨g, hg, rfl⟩
    rw [hHull] at hmem
    intro i hi
    have hreal := hmem i hi
    rw [latticeNormal_embedding] at hreal
    exact_mod_cast hreal
  have houtside : latticeEmbedding q ∉ latticeHull P := by
    intro hqin
    exact hqfail (hagree q (hP q hqin))
  rw [hHull] at houtside
  simp only [Set.mem_ofPred_eq, latticeNormal_embedding, Int.cast_le] at houtside
  push Not at houtside
  obtain ⟨i, hi, hviolated⟩ := houtside
  have hright : μ i a < 0 := by
    obtain ⟨⟨u, n⟩, he⟩ := hq
    change u.val + (0 + (n : ℤ)) • a = q at he
    have hbase := hnormal u.val (hFP u.property) i hi
    have hqvalue : μ i q = μ i u.val + (n : ℤ) * μ i a := by
      rw [← he, map_add, map_zsmul, smul_eq_mul, zero_add]
    by_contra hnot
    have hnonnegative : 0 ≤ (n : ℤ) * μ i a :=
      mul_nonneg (Int.natCast_nonneg n) (le_of_not_gt hnot)
    rw [hqvalue] at hviolated
    omega
  exact ⟨i, hi, hright, fun g hg => hviolated.trans_le (hnormal g hg i hi)⟩

-- every actual agreement polygon lies in a uniform integer rectangle of the primitive frame.
theorem fixed_normal_agreement_polygon_coordinate_bounds {A I : Type*}
    (z w : Site → A) (F P : Finset Site) (a v q : Site)
    (hav : determinant a v = 1) (hP : LatticeConvex P) (hFP : F ⊆ P)
    (hstrip : ∀ g ∈ P, g ∈ polygonHalfStrip F a)
    (hq : q ∈ polygonHalfStrip F a) (hqfail : z q ≠ w q)
    (hagree : ∀ g ∈ P, z g = w g) (J : Finset I) (μ : I → Site →+ ℤ)
    (hfacets : HasIntegerFacetPresentation J μ P) :
    ∀ g ∈ P,
      |directionNormal a g| ≤ polygonCoordinateBound F (directionNormal a) (-directionNormal v) ∧
      -polygonCoordinateBound F (directionNormal a) (-directionNormal v) ≤ (-directionNormal v) g ∧
      (-directionNormal v) g ≤ rightFacetCoordinateBound J μ
        (polygonCoordinateBound F (directionNormal a) (-directionNormal v)) q v := by
  obtain ⟨i, hi, hright, hseparate⟩ :=
    retained_disagreement_separating_facet z w F P a q hP hFP hq hqfail hagree J μ hfacets
  have hW := (polygon_coordinate_bound_data F (directionNormal a) (-directionNormal v)).1
  have hbound := right_facet_coordinate_bound_data J μ
    (polygonCoordinateBound F (directionNormal a) (-directionNormal v)) hW q v
  intro g hg
  have hstripbounds := polygon_half_strip_coordinate_bounds F a (directionNormal a)
    (-directionNormal v) (directionNormal_self a) (tangent_frame_coordinate_at_tangent a v hav)
    g (hstrip g hg)
  exact ⟨hstripbounds.1, hstripbounds.2,
    (separating_right_facet_coordinate_bound a v g q hav (μ i) _ hW hstripbounds.1
      hright (hseparate g hg)).trans (hbound.2 i hi)⟩

-- finite width and the retained failure produce an actual finite bounding set of lattice sites.
theorem fixed_normal_agreement_polygons_bounded {A I : Type*}
    (z w : Site → A) (F : Finset Site) (a : Site)
    (hprimitive : Int.gcd a.1 a.2 = 1) (q : Site)
    (hq : q ∈ polygonHalfStrip F a) (hqfail : z q ≠ w q)
    (J : Finset I) (μ : I → Site →+ ℤ) :
    ∃ box : Finset Site, ∀ P : Finset Site, LatticeConvex P → F ⊆ P →
      (∀ g ∈ P, g ∈ polygonHalfStrip F a) →
      (∀ g ∈ P, z g = w g) → HasIntegerFacetPresentation J μ P → P ⊆ box := by
  classical
  obtain ⟨τ, hτ, _hker⟩ := primitive_direction_coordinate a hprimitive
  obtain ⟨v, hav⟩ := primitive_basis_of_line_coordinate a τ hτ
  let ν := directionNormal a
  let τ' := -directionNormal v
  let W := polygonCoordinateBound F ν τ'
  let U := rightFacetCoordinateBound J μ W q v
  let rectangle : Set Site := Set.Icc (-W) W ×ˢ Set.Icc (-W) U
  have hrectangle : rectangle.Finite := (Set.finite_Icc _ _).prod (Set.finite_Icc _ _)
  let domain : Set Site := (ν.prod τ') ⁻¹' rectangle
  have hdomain : domain.Finite :=
    hrectangle.preimage (tangent_frame_coordinates_injective a v hav).injOn
  refine ⟨hdomain.toFinset, ?_⟩
  intro P hP hFP hstrip hagree hfacets g hg
  have hcoordinates := fixed_normal_agreement_polygon_coordinate_bounds z w F P a v q hav
    hP hFP hstrip hq hqfail hagree J μ hfacets g hg
  apply hdomain.mem_toFinset.mpr
  change (-W ≤ ν g ∧ ν g ≤ W) ∧ (-W ≤ τ' g ∧ τ' g ≤ U)
  exact ⟨abs_le.mp hcoordinates.1, hcoordinates.2⟩

-- the shape predicate preserves all original newton-envelope and oriented-edge metadata.
def AnchoredAgreementCandidate {A I : Type*} (z w : Site → A) (F : Finset Site)
    (a : Site) (J : Finset I) (μ : I → Site →+ ℤ)
    (Shape : Finset Site → Prop) (P : Finset Site) : Prop :=
  Shape P ∧ LatticeConvex P ∧ F ⊆ P ∧ (∀ g ∈ P, g ∈ polygonHalfStrip F a) ∧
    HasIntegerFacetPresentation J μ P ∧ ∀ g ∈ P, z g = w g

-- a retained half-strip failure makes the actual candidate family finite, without a boundedness premise.
theorem anchored_agreement_candidates_finite {A I : Type*}
    (z w : Site → A) (F : Finset Site) (a : Site)
    (hprimitive : Int.gcd a.1 a.2 = 1) (J : Finset I) (μ : I → Site →+ ℤ)
    (Shape : Finset Site → Prop)
    (hfail : ∃ q ∈ polygonHalfStrip F a, z q ≠ w q) :
    {P : Finset Site | AnchoredAgreementCandidate z w F a J μ Shape P}.Finite := by
  classical
  obtain ⟨q, hq, hqfail⟩ := hfail
  obtain ⟨box, hbox⟩ := fixed_normal_agreement_polygons_bounded z w F a hprimitive q hq hqfail J μ
  apply box.powerset.finite_toSet.subset
  intro P hP
  obtain ⟨_hShape, hconvex, hFP, hstrip, hfacets, hagree⟩ := hP
  exact Finset.mem_powerset.mpr (hbox P hconvex hFP hstrip hagree hfacets)

-- the finite derived candidate family has a largest-cardinality member and hence an inclusion-maximal polygon.
theorem exists_anchored_maximal_agreement_polygon {A I : Type*}
    (z w : Site → A) (F : Finset Site) (a : Site)
    (hprimitive : Int.gcd a.1 a.2 = 1) (J : Finset I) (μ : I → Site →+ ℤ)
    (Shape : Finset Site → Prop) (hShapeF : Shape F) (hF : LatticeConvex F)
    (hfacetsF : HasIntegerFacetPresentation J μ F) (hagreeF : ∀ g ∈ F, z g = w g)
    (hfail : ∃ q ∈ polygonHalfStrip F a, z q ≠ w q) :
    ∃ M : Finset Site, AnchoredAgreementCandidate z w F a J μ Shape M ∧
      ∀ P : Finset Site, AnchoredAgreementCandidate z w F a J μ Shape P → M ⊆ P → P = M := by
  classical
  have hfinite := anchored_agreement_candidates_finite z w F a hprimitive J μ Shape hfail
  have hFcandidate : AnchoredAgreementCandidate z w F a J μ Shape F := by
    refine ⟨hShapeF, hF, Finset.Subset.refl F, ?_, hfacetsF, hagreeF⟩
    intro g hg
    change ∃ u : F × ℕ, u.1.val + (0 + (u.2 : ℤ)) • a = g
    exact ⟨(⟨g, hg⟩, 0), by simp⟩
  have hnonempty : hfinite.toFinset.Nonempty :=
    ⟨F, hfinite.mem_toFinset.mpr hFcandidate⟩
  obtain ⟨M, hM, hmax⟩ := hfinite.toFinset.exists_max_image Finset.card hnonempty
  refine ⟨M, hfinite.mem_toFinset.mp hM, ?_⟩
  intro P hP hMP
  exact (Finset.eq_of_subset_of_card_le hMP (hmax P (hfinite.mem_toFinset.mpr hP))).symm

end KumarNivat
