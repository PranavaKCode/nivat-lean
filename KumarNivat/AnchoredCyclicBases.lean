import KumarNivat.AnchoredPolygonTransport
import KumarNivat.NewtonEnvelopeBases

namespace KumarNivat

open scoped Pointwise

-- the actual newton hull's cyclic vertices transfer to every constructed half-plane base.
theorem actual_newton_halfplane_cyclic_base {K : Type*} [CommRing K] [Nontrivial K]
    [NoZeroDivisors K] {n : ℕ} [NeZero n]
    (hs : List Site) (hlen : 2 ≤ hs.length) (hdirs : ∀ h ∈ hs, h ≠ 0)
    (hpairs : hs.Pairwise (fun p q => determinant p q ≠ 0))
    (e : ZMod n → Site)
    (P : OrderedCyclicLatticePolygon e (differenceProduct (K := K) hs).coeff.support)
    (hprimitive : Int.gcd (e 0).1 (e 0).2 = 1) (p : Site) (hpmem : p ∈ hs)
    (hparallel : determinant (e 0) p = 0) (cut : ℤ) (S : Finset Site)
    (hS : ∀ g ∈ S, cut ≤ directionNormal (e 0) g) :
    ∃ F : Finset Site, LatticeConvex F ∧ S ⊆ F ∧
      (∀ g ∈ F, cut ≤ directionNormal (e 0) g) ∧
      AnchoredCyclicEnvelope e (latticeHull (differenceProduct (K := K) hs).coeff.support) F ∧
      ∃ Q : OrderedCyclicLatticePolygon e F,
        (∀ i, P.edgeLength i ≤ Q.edgeLength i) ∧
        ∃ B : Site, directionNormal (e 0) B = cut ∧ B ∈ F := by
  obtain ⟨F, hF, hSF, hhalf, N, U, B, hN, hB, hBF, _hplus, _hminus,
    hHull, C, _hC, hconvex, hcompact, hnonempty, hsum⟩ :=
    actual_newton_halfplane_base (K := K) hs hlen hdirs hpairs (e 0) hprimitive p hpmem hparallel cut S hS
  have hd : (0 : ℤ) < 2 * (N : ℤ) := by omega
  have hHull' : latticeHull F =
      (fun z : RealPlane => latticeEmbedding U + ((2 * (N : ℤ) : ℤ) : ℝ) • z) ''
        latticeHull (differenceProduct (K := K) hs).coeff.support := by
    simpa only [Int.cast_mul, Int.cast_ofNat, Int.cast_natCast] using hHull
  let Q := orderedCyclicPolygonPositiveAffinity e (differenceProduct (K := K) hs).coeff.support F P
    (2 * (N : ℤ)) hd U hF hHull'
  refine ⟨F, hF, hSF, hhalf, ⟨⟨Q⟩, C, hconvex, hcompact, hnonempty, hsum⟩,
    Q, ?_, B, hB, hBF⟩
  intro i
  change P.edgeLength i ≤ (2 * (N : ℤ)) * P.edgeLength i
  exact le_mul_of_one_le_left (le_of_lt (P.length_pos i)) (by omega)

-- one finite exhaustion step first constructs a genuine cyclic base and then its actual maximal agreement extension.
theorem exists_maximal_cyclic_polygon_containing_halfplane_data {K : Type*} [CommRing K]
    [Nontrivial K] [NoZeroDivisors K] [TopologicalSpace K] [DiscreteTopology K]
    {n : ℕ} [NeZero n]
    (c w : Site → K) (hw : w ∈ orbitClosure c)
    (hs : List Site) (hlen : 2 ≤ hs.length) (hdirs : ∀ h ∈ hs, h ≠ 0)
    (hpairs : hs.Pairwise (fun p q => determinant p q ≠ 0))
    (e : ZMod n → Site) (horder : CyclicEdgeOrder e)
    (P : OrderedCyclicLatticePolygon e (differenceProduct (K := K) hs).coeff.support)
    (hprimitive : Int.gcd (e 0).1 (e 0).2 = 1) (p : Site) (hpmem : p ∈ hs)
    (hparallel : determinant (e 0) p = 0) (cut : ℤ) (S : Finset Site)
    (hS : ∀ g ∈ S, cut ≤ directionNormal (e 0) g)
    (hnoHalfStrip : ∀ F : Finset Site,
      AnchoredCyclicEnvelope e (latticeHull (differenceProduct (K := K) hs).coeff.support) F →
      LatticeConvex F → (∀ g ∈ F, cut ≤ directionNormal (e 0) g) →
      ∀ u : Site, ¬ ∀ g ∈ polygonHalfStrip F (e 0), shift u c g = w g) :
    ∃ F M : Finset Site, ∃ u : Site, LatticeConvex F ∧ S ⊆ F ∧
      (∀ g ∈ F, cut ≤ directionNormal (e 0) g) ∧
      AnchoredCyclicEnvelope e (latticeHull (differenceProduct (K := K) hs).coeff.support) F ∧
      AnchoredCyclicAgreement (shift u c) w F (e 0) e
        (latticeHull (differenceProduct (K := K) hs).coeff.support) M ∧
      (∀ g ∈ M, cut ≤ directionNormal (e 0) g) ∧
      ∀ Q : Finset Site, AnchoredCyclicAgreement (shift u c) w F (e 0) e
        (latticeHull (differenceProduct (K := K) hs).coeff.support) Q → M ⊆ Q → Q = M := by
  obtain ⟨F, hF, hSF, hhalf, hEnvelope, _hEdges⟩ := actual_newton_halfplane_cyclic_base
    (K := K) hs hlen hdirs hpairs e P hprimitive p hpmem hparallel cut S hS
  obtain ⟨u, M, hM, hmax⟩ := exists_orbit_shift_maximal_cyclic_envelope c w hw F (e 0)
    hprimitive e horder (latticeHull (differenceProduct (K := K) hs).coeff.support)
      hEnvelope hF (hnoHalfStrip F hEnvelope hF hhalf)
  refine ⟨F, M, u, hF, hSF, hhalf, hEnvelope, hM, ?_, hmax⟩
  intro g hg
  exact forward_half_strip_in_parallel_halfplane F (e 0) (directionNormal (e 0)) cut
    (directionNormal_self _) hhalf g (hM.2.2.2.1 g hg)

end KumarNivat
