import KumarNivat.AnchoredMaximalPolygons
import KumarNivat.OrbitLanguage

namespace KumarNivat

-- an actual orbit-closure reference occurs on each finite initial agreement polygon.
theorem orbit_reference_matches_finite_polygon {A : Type*} [TopologicalSpace A]
    [DiscreteTopology A] (c w : Site → A) (hw : w ∈ orbitClosure c) (F : Finset Site) :
    ∃ u : Site, ∀ g ∈ F, shift u c g = w g := by
  obtain ⟨u, hu⟩ := languageContained_of_mem_orbitClosure c w hw F 0
  refine ⟨u, ?_⟩
  intro g hg
  have he := hu g hg
  simpa only [shift, zero_add, add_zero, add_comm] using he.symm

-- no matching half-strip supplies the retained failure for the chosen finite match and hence a maximal polygon.
theorem exists_orbit_shift_maximal_agreement_polygon {A I : Type*} [TopologicalSpace A]
    [DiscreteTopology A] (c w : Site → A) (hw : w ∈ orbitClosure c)
    (F : Finset Site) (a : Site) (hprimitive : Int.gcd a.1 a.2 = 1)
    (J : Finset I) (μ : I → Site →+ ℤ) (Shape : Finset Site → Prop)
    (hShapeF : Shape F) (hF : LatticeConvex F)
    (hfacetsF : HasIntegerFacetPresentation J μ F)
    (hnoHalfStrip : ∀ u : Site, ¬ ∀ g ∈ polygonHalfStrip F a, shift u c g = w g) :
    ∃ u : Site, ∃ M : Finset Site,
      AnchoredAgreementCandidate (shift u c) w F a J μ Shape M ∧
      ∀ P : Finset Site, AnchoredAgreementCandidate (shift u c) w F a J μ Shape P →
        M ⊆ P → P = M := by
  classical
  obtain ⟨u, hu⟩ := orbit_reference_matches_finite_polygon c w hw F
  have hfail : ∃ q ∈ polygonHalfStrip F a, shift u c q ≠ w q := by
    have hnot := hnoHalfStrip u
    push Not at hnot
    exact hnot
  obtain ⟨M, hM, hmax⟩ := exists_anchored_maximal_agreement_polygon (shift u c) w
    F a hprimitive J μ Shape hShapeF hF hfacetsF hu hfail
  exact ⟨u, M, hM, hmax⟩

-- the half-strip retains the original boundary-normal half-plane exactly.
theorem forward_half_strip_in_parallel_halfplane (F : Finset Site) (a : Site)
    (ν : Site →+ ℤ) (β : ℤ) (hνa : ν a = 0) (hF : ∀ g ∈ F, β ≤ ν g) :
    ∀ g ∈ polygonHalfStrip F a, β ≤ ν g := by
  intro g hg
  obtain ⟨⟨u, n⟩, he⟩ := hg
  change u.val + (0 + (n : ℤ)) • a = g at he
  rw [← he, map_add, map_zsmul, hνa, smul_zero, add_zero]
  exact hF u.val u.property

-- the selected actual maximal polygon stays in the reference half-plane and keeps the initial boundary sites.
theorem anchored_agreement_candidate_in_halfplane {A I : Type*}
    (z w : Site → A) (F M : Finset Site) (a : Site) (J : Finset I)
    (μ : I → Site →+ ℤ) (Shape : Finset Site → Prop)
    (hM : AnchoredAgreementCandidate z w F a J μ Shape M)
    (ν : Site →+ ℤ) (β : ℤ) (hνa : ν a = 0) (hF : ∀ g ∈ F, β ≤ ν g) :
    (∀ g ∈ M, β ≤ ν g) ∧ F ⊆ M := by
  obtain ⟨_hShape, _hconvex, hFM, hstrip, _hfacets, _hagree⟩ := hM
  exact ⟨fun g hg => forward_half_strip_in_parallel_halfplane F a ν β hνa hF g (hstrip g hg), hFM⟩

end KumarNivat
