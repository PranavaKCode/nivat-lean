import KumarNivat.AnchoredIntegerExpansionSupports
import KumarNivat.NewtonSingleRayFacets
import KumarNivat.NewtonEnvelopeUnitSegments

namespace KumarNivat

open scoped Pointwise

-- the moved facet decreases on the ray, so every facet defining the original half-strip stays unchanged.
theorem cyclic_facet_relaxed_region_subset_base_halfstrip {q : ℕ} [NeZero q]
    (e : ZMod (2 * q) → Site) (hfan : AnchoredChainFanOrder e) (F T : Finset Site)
    (B : OrderedCyclicLatticePolygon e F) (P : OrderedCyclicLatticePolygon e T)
    (hFT : F ⊆ T) (hstrip : ∀ g ∈ T, g ∈ polygonHalfStrip F (e 0))
    (i : ZMod (2 * q)) (j : ℤ) (hnegative : directionNormal (e i) (e 0) < 0) :
    cyclicFacetRelaxedRegion e T P i j ⊆ latticeHull F + lineRay 0 (latticeEmbedding (e 0)) 0 := by
  intro x hx
  rw [single_factor_ray_facet_presentation e hfan.order hfan.opposite F B]
  intro k hk
  have hki : k ≠ i := by intro he; subst k; omega
  have hlevel := anchored_halfstrip_surviving_supports_equal e hfan.order F T B P (e 0) hFT hstrip k hk
  have hb := hx k (Finset.mem_univ k)
  change (cyclicFacetRelaxedCut e T P i j k : ℝ) ≤ latticeNormal (directionNormal (e k)) x at hb
  simp only [cyclicFacetRelaxedCut, ite_eq_right hki, sub_zero, hlevel] at hb
  exact hb

-- the actual original factor's unit summand converts the preserved real half-strip to integer forward translates.
theorem anchored_integer_facet_expansion_lattice_halfstrip {K : Type*} [CommRing K]
    [Nontrivial K] [NoZeroDivisors K] {q : ℕ} [NeZero q]
    (hs : List Site) (hdirs : ∀ h ∈ hs, h ≠ 0)
    (hpairs : hs.Pairwise (fun p r => determinant p r ≠ 0))
    (e : ZMod (2 * q) → Site) (hfan : AnchoredChainFanOrder e)
    (hprimitive : Int.gcd (e 0).1 (e 0).2 = 1) (p : Site) (hpmem : p ∈ hs)
    (hparallel : determinant (e 0) p = 0) (F T W : Finset Site) (hF : LatticeConvex F)
    (hEnvelopeF : AnchoredCyclicEnvelope e (latticeHull (differenceProduct (K := K) hs).coeff.support) F)
    (P : OrderedCyclicLatticePolygon e T) (hFT : F ⊆ T)
    (hstrip : ∀ g ∈ T, g ∈ polygonHalfStrip F (e 0))
    (b : ℕ) (hb₀ : 0 < b) (hbq : b < q)
    (hHullW : latticeHull W = cyclicFacetRelaxedRegion e T P (b : ZMod (2 * q))
      (cyclicFacetRelaxationScale e (b : ZMod (2 * q)))) :
    ∀ g ∈ W, g ∈ polygonHalfStrip F (e 0) := by
  obtain ⟨B⟩ := hEnvelopeF.1
  have hreal := cyclic_facet_relaxed_region_subset_base_halfstrip e hfan F T B P hFT hstrip
    (b : ZMod (2 * q)) (cyclicFacetRelaxationScale e (b : ZMod (2 * q)))
    (anchored_integer_expansion_moving_normal_negative e hfan b hb₀ hbq)
  have hsites := anchored_cyclic_base_half_strip_eq_integer_translates (K := K)
    hs hdirs hpairs e hprimitive p hpmem hparallel F hF hEnvelopeF
  intro g hg
  have hpoint : latticeEmbedding g ∈ latticeHull F + lineRay 0 (latticeEmbedding (e 0)) 0 := by
    apply hreal
    rw [← hHullW]
    exact subset_convexHull ℝ _ ⟨g, hg, rfl⟩
  have hsite : g ∈ {g : Site | latticeEmbedding g ∈ latticeHull F + lineRay 0 (latticeEmbedding (e 0)) 0} := hpoint
  rwa [hsites] at hsite

end KumarNivat
