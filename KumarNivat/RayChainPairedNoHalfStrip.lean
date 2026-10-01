import KumarNivat.RayChainPairedActual
import KumarNivat.NewtonEnvelopeUnitSegments
import KumarNivat.FilterCount

namespace KumarNivat

open scoped Pointwise

-- the proved matching branch excludes every translated geometric newton half-strip under the original no-pair assumption.
theorem no_geometric_newton_half_strip_agreement_of_no_pair {K : Type*}
    [CommRing K] [Nontrivial K] [NoZeroDivisors K] [TopologicalSpace K] [DiscreteTopology K]
    (c w : Site → K) (hc : (Set.range c).Finite) (hnopair : ¬ HasPairedOneSidedDirection c)
    (hnot : ¬ ∃ v : Site, v ≠ 0 ∧ IsPeriod c v)
    (hs : List Site) (hlen : 2 ≤ hs.length) (hdirs : ∀ p ∈ hs, p ≠ 0)
    (hpairs : hs.Pairwise (fun p r => determinant p r ≠ 0))
    (hann : laurentAct (differenceProduct hs) c = 0)
    (a : Site) (ha : Int.gcd a.1 a.2 = 1) (pa : Site) (hpa : pa ∈ hs)
    (haparallel : determinant a pa = 0) (l : ℕ) (hl : 0 < l) (hw : IsPeriod w ((l : ℤ) • a))
    (F : Finset Site) (hF : LatticeConvex F) (C₀ : Set RealPlane) (hC₀ : C₀.Nonempty)
    (hbase : latticeHull F = latticeHull (differenceProduct (K := K) hs).coeff.support + C₀) :
    ∀ u : Site, ¬ ∀ g : Site, latticeEmbedding g ∈ latticeHull F + lineRay 0 (latticeEmbedding a) 0 → shift u c g = w g := by
  intro u hmatch
  have hx : shift u c ∈ orbitClosure c := subset_closure (Set.mem_range.mpr ⟨u, rfl⟩)
  have hnotshift : ¬ ∃ v : Site, v ≠ 0 ∧ IsPeriod (shift u c) v := by
    rintro ⟨v, hv, hperiod⟩
    have hback := hperiod.shift (-u)
    have hglobal : IsPeriod c v := by
      simpa only [IsPeriod, shift, add_assoc, neg_add_cancel, add_zero] using hback
    exact hnot ⟨v, hv, hglobal⟩
  exact hnopair (matching_newton_half_strip_forces_paired_direction c (shift u c) w hc hx hnopair hnotshift
    hs hlen hdirs hpairs hann a ha pa hpa haparallel l hl hw F hF C₀ hC₀ hbase hmatch)

-- the original unit segment converts this proved exclusion to the source's integer half-strip definition.
theorem no_polygon_newton_half_strip_agreement_of_no_pair {K : Type*}
    [CommRing K] [Nontrivial K] [NoZeroDivisors K] [TopologicalSpace K] [DiscreteTopology K]
    (c w : Site → K) (hc : (Set.range c).Finite) (hnopair : ¬ HasPairedOneSidedDirection c)
    (hnot : ¬ ∃ v : Site, v ≠ 0 ∧ IsPeriod c v)
    (hs : List Site) (hlen : 2 ≤ hs.length) (hdirs : ∀ p ∈ hs, p ≠ 0)
    (hpairs : hs.Pairwise (fun p r => determinant p r ≠ 0))
    (hann : laurentAct (differenceProduct hs) c = 0)
    (a : Site) (ha : Int.gcd a.1 a.2 = 1) (pa : Site) (hpa : pa ∈ hs)
    (haparallel : determinant a pa = 0) (l : ℕ) (hl : 0 < l) (hw : IsPeriod w ((l : ℤ) • a))
    (F : Finset Site) (hF : LatticeConvex F) (C₀ : Set RealPlane) (hC₀ : C₀.Nonempty)
    (hbase : latticeHull F = latticeHull (differenceProduct (K := K) hs).coeff.support + C₀) :
    ∀ u : Site, ¬ ∀ g ∈ polygonHalfStrip F a, shift u c g = w g := by
  have hhalf := newton_envelope_half_strip_eq_integer_translates (K := K) hs hdirs hpairs a ha pa hpa haparallel F hF C₀ hbase
  intro u hmatch
  apply no_geometric_newton_half_strip_agreement_of_no_pair c w hc hnopair hnot hs hlen hdirs hpairs hann
    a ha pa hpa haparallel l hl hw F hF C₀ hC₀ hbase u
  intro g hg
  apply hmatch g
  rw [← hhalf]
  exact hg

-- every actual cyclic base inherits the uniform no-matching premise needed by the anchored source construction.
theorem no_anchored_cyclic_half_strip_agreement_of_no_pair {K : Type*}
    [CommRing K] [Nontrivial K] [NoZeroDivisors K] [TopologicalSpace K] [DiscreteTopology K]
    {n : ℕ} [NeZero n]
    (c w : Site → K) (hc : (Set.range c).Finite) (hnopair : ¬ HasPairedOneSidedDirection c)
    (hnot : ¬ ∃ v : Site, v ≠ 0 ∧ IsPeriod c v)
    (hs : List Site) (hlen : 2 ≤ hs.length) (hdirs : ∀ p ∈ hs, p ≠ 0)
    (hpairs : hs.Pairwise (fun p r => determinant p r ≠ 0))
    (hann : laurentAct (differenceProduct hs) c = 0)
    (e : ZMod n → Site) (ha : Int.gcd (e 0).1 (e 0).2 = 1)
    (pa : Site) (hpa : pa ∈ hs) (haparallel : determinant (e 0) pa = 0)
    (l : ℕ) (hl : 0 < l) (hw : IsPeriod w ((l : ℤ) • e 0))
    (F : Finset Site) (hF : LatticeConvex F)
    (hEnvelope : AnchoredCyclicEnvelope e (latticeHull (differenceProduct (K := K) hs).coeff.support) F) :
    ∀ u : Site, ¬ ∀ g ∈ polygonHalfStrip F (e 0), shift u c g = w g := by
  obtain ⟨_hpoly, C₀, _hconvex, _hcompact, hC₀, hbase⟩ := hEnvelope
  exact no_polygon_newton_half_strip_agreement_of_no_pair c w hc hnopair hnot hs hlen hdirs hpairs hann
    (e 0) ha pa hpa haparallel l hl hw F hF C₀ hC₀ hbase

end KumarNivat
