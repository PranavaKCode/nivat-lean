module

public import KumarNivat.AnchoredMaximalOrbit

@[expose] public section

namespace KumarNivat

open scoped Pointwise

-- the actual forward ray is convex in the original real lattice plane.
theorem anchored_forward_ray_convex (a : Site) :
    Convex ℝ (lineRay 0 (latticeEmbedding a) 0) := by
  rintro x ⟨t, ht, rfl⟩ y ⟨u, hu, rfl⟩ r s hr hs _hrs
  change (0 : ℝ) ≤ t at ht
  change (0 : ℝ) ≤ u at hu
  refine ⟨r * t + s * u, ?_, ?_⟩
  · exact add_nonneg (mul_nonneg hr ht) (mul_nonneg hs hu)
  · change 0 + (r * t + s * u) • latticeEmbedding a =
      r • (0 + t • latticeEmbedding a) + s • (0 + u • latticeEmbedding a)
    simp only [zero_add, add_smul, mul_smul]

-- containment of the actual lattice sites controls the entire convex polygon hull.
theorem latticeConvex_hull_inclusion_iff (P Q : Finset Site) (hQ : LatticeConvex Q) :
    P ⊆ Q ↔ latticeHull P ⊆ latticeHull Q := by
  constructor
  · intro hPQ
    exact convexHull_mono (Set.image_mono (by exact hPQ))
  · intro hPQ g hg
    exact hQ g (hPQ (subset_convexHull ℝ _ ⟨g, hg, rfl⟩))

-- integer forward translates put every point of the candidate hull in the real half-strip.
theorem polygon_lattice_half_strip_implies_hull_containment (F P : Finset Site) (a : Site)
    (hstrip : ∀ g ∈ P, g ∈ polygonHalfStrip F a) :
    latticeHull P ⊆ latticeHull F + lineRay 0 (latticeEmbedding a) 0 := by
  apply convexHull_min _ ((convex_convexHull ℝ _).add (anchored_forward_ray_convex a))
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨⟨u, n⟩, he⟩ := hstrip g hg
  change u.val + (0 + (n : ℤ)) • a = g at he
  rw [← he, latticeEmbedding_add, latticeEmbedding_zsmul]
  have hbase : latticeEmbedding u.val ∈ latticeHull F :=
    subset_convexHull ℝ _ ⟨u.val, u.property, rfl⟩
  apply Set.add_mem_add hbase
  refine ⟨(n : ℝ), ?_, ?_⟩
  · change (0 : ℝ) ≤ (n : ℝ)
    exact Nat.cast_nonneg n
  · simp only [zero_add, Int.cast_natCast]

-- the checked unit tangent summand identifies the geometric and lattice candidate conditions.
theorem polygon_half_strip_hull_containment_iff (F P : Finset Site) (hF : LatticeConvex F)
    (a : Site) (C : Set RealPlane)
    (hunit : latticeHull F = lineInterval 0 (latticeEmbedding a) 0 1 + C) :
    (∀ g ∈ P, g ∈ polygonHalfStrip F a) ↔
      latticeHull P ⊆ latticeHull F + lineRay 0 (latticeEmbedding a) 0 := by
  constructor
  · exact polygon_lattice_half_strip_implies_hull_containment F P a
  · intro hHull g hg
    have hreal := hHull (subset_convexHull ℝ _ ⟨g, hg, rfl⟩)
    have hsite : g ∈ {g : Site |
        latticeEmbedding g ∈ latticeHull F + lineRay 0 (latticeEmbedding a) 0} := hreal
    rw [geometric_polygon_half_strip_eq_integer_translates F hF a C hunit] at hsite
    exact hsite

-- maximality is for the actual convex polygons between the initial polygon and its real forward half-strip.
theorem exists_anchored_maximal_geometric_agreement_polygon {A I : Type*}
    (z w : Site → A) (F : Finset Site) (a : Site)
    (hprimitive : Int.gcd a.1 a.2 = 1) (J : Finset I) (μ : I → Site →+ ℤ)
    (Shape : Finset Site → Prop) (hShapeF : Shape F) (hF : LatticeConvex F)
    (hfacetsF : HasIntegerFacetPresentation J μ F) (hagreeF : ∀ g ∈ F, z g = w g)
    (C : Set RealPlane)
    (hunit : latticeHull F = lineInterval 0 (latticeEmbedding a) 0 1 + C)
    (hfail : ∃ q ∈ polygonHalfStrip F a, z q ≠ w q) :
    ∃ M : Finset Site, Shape M ∧ LatticeConvex M ∧
      latticeHull F ⊆ latticeHull M ∧
      latticeHull M ⊆ latticeHull F + lineRay 0 (latticeEmbedding a) 0 ∧
      HasIntegerFacetPresentation J μ M ∧ (∀ g ∈ M, z g = w g) ∧
      ∀ P : Finset Site, Shape P → LatticeConvex P → latticeHull F ⊆ latticeHull P →
        latticeHull P ⊆ latticeHull F + lineRay 0 (latticeEmbedding a) 0 →
        HasIntegerFacetPresentation J μ P → (∀ g ∈ P, z g = w g) →
        latticeHull M ⊆ latticeHull P → latticeHull P = latticeHull M := by
  obtain ⟨M, hM, hmax⟩ := exists_anchored_maximal_agreement_polygon z w F a hprimitive
    J μ Shape hShapeF hF hfacetsF hagreeF hfail
  obtain ⟨hShapeM, hconvexM, hFM, hstripM, hfacetsM, hagreeM⟩ := hM
  refine ⟨M, hShapeM, hconvexM, (latticeConvex_hull_inclusion_iff F M hconvexM).mp hFM,
    polygon_lattice_half_strip_implies_hull_containment F M a hstripM, hfacetsM, hagreeM, ?_⟩
  intro P hShapeP hP hFP hstripP hfacetsP hagreeP hMP
  have hPcand : AnchoredAgreementCandidate z w F a J μ Shape P :=
    ⟨hShapeP, hP, (latticeConvex_hull_inclusion_iff F P hP).mpr hFP,
      (polygon_half_strip_hull_containment_iff F P hF a C hunit).mpr hstripP, hfacetsP, hagreeP⟩
  rw [hmax P hPcand ((latticeConvex_hull_inclusion_iff M P hP).mpr hMP)]

-- positive integer dilations and lattice translations preserve the fixed fan with integer supporting levels.
theorem integer_facet_presentation_positive_affinity {I : Type*}
    (T P : Finset Site) (J : Finset I) (μ : I → Site →+ ℤ)
    (hT : HasIntegerFacetPresentation J μ T) (n : ℤ) (hn : 0 < n) (U : Site)
    (hHull : latticeHull P = (fun z : RealPlane => latticeEmbedding U + (n : ℝ) • z) '' latticeHull T) :
    HasIntegerFacetPresentation J μ P := by
  obtain ⟨cut, hT⟩ := hT
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  refine ⟨fun i => μ i U + n * cut i, ?_⟩
  rw [hHull]
  apply Set.Subset.antisymm
  · rintro x ⟨z, hz, rfl⟩
    rw [hT] at hz
    intro i hi
    change ((μ i U + n * cut i : ℤ) : ℝ) ≤
      latticeNormal (μ i) (latticeEmbedding U + (n : ℝ) • z)
    rw [map_add, map_smul, latticeNormal_embedding, smul_eq_mul]
    push_cast
    have hscaled : (n : ℝ) * (cut i : ℝ) ≤ (n : ℝ) * latticeNormal (μ i) z :=
      mul_le_mul_of_nonneg_left (hz i hi) hnR.le
    exact add_le_add (le_refl (μ i U : ℝ)) hscaled
  · intro x hx
    let z : RealPlane := (n : ℝ)⁻¹ • (x - latticeEmbedding U)
    have hz : z ∈ latticeHull T := by
      rw [hT]
      intro i hi
      have hreal := hx i hi
      change ((μ i U + n * cut i : ℤ) : ℝ) ≤ latticeNormal (μ i) x at hreal
      push_cast at hreal
      change (cut i : ℝ) ≤ latticeNormal (μ i) ((n : ℝ)⁻¹ • (x - latticeEmbedding U))
      rw [map_smul, map_sub, latticeNormal_embedding, smul_eq_mul, ← div_eq_inv_mul]
      apply (le_div_iff₀ hnR).mpr
      nlinarith
    refine ⟨z, hz, ?_⟩
    change latticeEmbedding U + (n : ℝ) • ((n : ℝ)⁻¹ • (x - latticeEmbedding U)) = x
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hnR), one_smul]
    abel

end KumarNivat
