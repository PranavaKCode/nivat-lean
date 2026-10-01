import KumarNivat.AnchoredMaximalOrbit
import KumarNivat.NewtonCyclicFacets

namespace KumarNivat

open scoped Pointwise

-- the envelope keeps its actual fixed cyclic edge directions and the same compact convex newton summand.
def AnchoredCyclicEnvelope {n : ℕ} [NeZero n] (e : ZMod n → Site)
    (Z : Set RealPlane) (P : Finset Site) : Prop :=
  Nonempty (OrderedCyclicLatticePolygon e P) ∧
    ∃ C : Set RealPlane, Convex ℝ C ∧ IsCompact C ∧ C.Nonempty ∧ latticeHull P = Z + C

-- these are the actual source polygons between the initial base and its forward half-strip.
def AnchoredCyclicAgreement {A : Type*} {n : ℕ} [NeZero n]
    (z w : Site → A) (F : Finset Site) (a : Site) (e : ZMod n → Site)
    (Z : Set RealPlane) (P : Finset Site) : Prop :=
  AnchoredCyclicEnvelope e Z P ∧ LatticeConvex P ∧ F ⊆ P ∧
    (∀ g ∈ P, g ∈ polygonHalfStrip F a) ∧ ∀ g ∈ P, z g = w g

-- the checked cyclic support geometry supplies every candidate's exact integer facet presentation.
theorem anchored_cyclic_candidate_iff {A : Type*} {n : ℕ} [NeZero n]
    (z w : Site → A) (F : Finset Site) (a : Site) (e : ZMod n → Site)
    (horder : CyclicEdgeOrder e) (Z : Set RealPlane) (P : Finset Site) :
    AnchoredCyclicAgreement z w F a e Z P ↔
      AnchoredAgreementCandidate z w F a Finset.univ (fun i => directionNormal (e i))
        (AnchoredCyclicEnvelope e Z) P := by
  constructor
  · rintro ⟨henvelope, hconvex, hFP, hstrip, hagree⟩
    obtain ⟨poly⟩ := henvelope.1
    exact ⟨henvelope, hconvex, hFP, hstrip,
      ordered_cyclic_polygon_integer_facets e horder P poly, hagree⟩
  · rintro ⟨henvelope, hconvex, hFP, hstrip, _hfacets, hagree⟩
    exact ⟨henvelope, hconvex, hFP, hstrip, hagree⟩

-- a finite match with a retained half-strip failure has a maximal actual cyclic newton envelope.
theorem exists_anchored_maximal_cyclic_envelope {A : Type*} {n : ℕ} [NeZero n]
    (z w : Site → A) (F : Finset Site) (a : Site)
    (hprimitive : Int.gcd a.1 a.2 = 1) (e : ZMod n → Site) (horder : CyclicEdgeOrder e)
    (Z : Set RealPlane) (hEnvelopeF : AnchoredCyclicEnvelope e Z F) (hF : LatticeConvex F)
    (hagreeF : ∀ g ∈ F, z g = w g)
    (hfail : ∃ q ∈ polygonHalfStrip F a, z q ≠ w q) :
    ∃ M : Finset Site, AnchoredCyclicAgreement z w F a e Z M ∧
      ∀ P : Finset Site, AnchoredCyclicAgreement z w F a e Z P → M ⊆ P → P = M := by
  obtain ⟨polyF⟩ := hEnvelopeF.1
  have hfacetsF := ordered_cyclic_polygon_integer_facets e horder F polyF
  obtain ⟨M, hM, hmax⟩ := exists_anchored_maximal_agreement_polygon z w F a hprimitive
    Finset.univ (fun i => directionNormal (e i)) (AnchoredCyclicEnvelope e Z)
    hEnvelopeF hF hfacetsF hagreeF hfail
  refine ⟨M, (anchored_cyclic_candidate_iff z w F a e horder Z M).mpr hM, ?_⟩
  intro P hP hMP
  exact hmax P ((anchored_cyclic_candidate_iff z w F a e horder Z P).mp hP) hMP

-- the reference's actual orbit language chooses the matching translate before the maximal source polygon.
theorem exists_orbit_shift_maximal_cyclic_envelope {A : Type*} [TopologicalSpace A]
    [DiscreteTopology A] {n : ℕ} [NeZero n]
    (c w : Site → A) (hw : w ∈ orbitClosure c) (F : Finset Site) (a : Site)
    (hprimitive : Int.gcd a.1 a.2 = 1) (e : ZMod n → Site) (horder : CyclicEdgeOrder e)
    (Z : Set RealPlane) (hEnvelopeF : AnchoredCyclicEnvelope e Z F) (hF : LatticeConvex F)
    (hnoHalfStrip : ∀ u : Site, ¬ ∀ g ∈ polygonHalfStrip F a, shift u c g = w g) :
    ∃ u : Site, ∃ M : Finset Site, AnchoredCyclicAgreement (shift u c) w F a e Z M ∧
      ∀ P : Finset Site, AnchoredCyclicAgreement (shift u c) w F a e Z P → M ⊆ P → P = M := by
  classical
  obtain ⟨u, hu⟩ := orbit_reference_matches_finite_polygon c w hw F
  have hfail : ∃ q ∈ polygonHalfStrip F a, shift u c q ≠ w q := by
    have hnot := hnoHalfStrip u
    push Not at hnot
    exact hnot
  obtain ⟨M, hM, hmax⟩ := exists_anchored_maximal_cyclic_envelope (shift u c) w F a
    hprimitive e horder Z hEnvelopeF hF hu hfail
  exact ⟨u, M, hM, hmax⟩

end KumarNivat
