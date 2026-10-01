import KumarNivat.MainMatchingBackgroundActual
import KumarNivat.InitialWedgeFromHalfStrip
import KumarNivat.NewtonEnvelopeUnitSegments
import KumarNivat.AnchoredSourceSequences
import KumarNivat.FilterCount

namespace KumarNivat

open scoped Pointwise

-- a matched original-newton integer half-strip constructs the background on the same actual shifted nonperiodic configuration.
theorem matching_newton_half_strip_background_on_same_shift {K : Type*}
    [CommRing K] [Nontrivial K] [NoZeroDivisors K] [TopologicalSpace K] [DiscreteTopology K]
    (c w : Site → K) (hc : (Set.range c).Finite)
    (hnot : ¬ ∃ v : Site, v ≠ 0 ∧ IsPeriod c v)
    (hs : List Site) (hlen : 2 ≤ hs.length) (hdirs : ∀ h ∈ hs, h ≠ 0)
    (hpairs : hs.Pairwise (fun h k => determinant h k ≠ 0))
    (hann : laurentAct (differenceProduct hs) c = 0)
    (R S : Finset Site) (hgen : GeneratingPolygon c R S)
    (a : Site) (ha : Int.gcd a.1 a.2 = 1) (pa : Site) (hpa : pa ∈ hs)
    (haparallel : determinant a pa = 0) (m M : ℤ)
    (hbounds : ∀ v ∈ S, m ≤ directionNormal a v ∧ directionNormal a v ≤ M)
    (hlower : 2 ≤ (lowerLatticeFace S (directionNormal a) m).card)
    (hupper : 2 ≤ (lowerLatticeFace S (-directionNormal a) (-M)).card)
    (l : ℕ) (hl : 0 < l) (hw : IsPeriod w ((l : ℤ) • a))
    (F : Finset Site) (hF : LatticeConvex F) (C₀ : Set RealPlane) (hC₀ : C₀.Nonempty)
    (hbase : latticeHull F = latticeHull (differenceProduct (K := K) hs).coeff.support + C₀)
    (u : Site) (hmatch : ∀ g ∈ polygonHalfStrip F a, shift u c g = w g) :
    shift u c ∈ orbitClosure c ∧ (¬ ∃ p : Site, p ≠ 0 ∧ IsPeriod (shift u c) p) ∧
      ∃ d : Site, Int.gcd d.1 d.2 = 1 ∧ 0 < determinant a d ∧
        (∃ h ∈ hs, determinant d h = 0) ∧ Function.Injective ((directionNormal a).prod (-directionNormal d)) ∧
        ∃ E : Site, ∃ B : Site → K, FullyPeriodic B ∧
          AgreesOnWedge (directionNormal a) (-directionNormal d) (directionNormal a E)
            ((-directionNormal d) E) (shift u c) B ∧ Set.range B ⊆ Set.range (shift u c) := by
  have hx : shift u c ∈ orbitClosure c := subset_closure (Set.mem_range.mpr ⟨u, rfl⟩)
  have hnotshift : ¬ ∃ v : Site, v ≠ 0 ∧ IsPeriod (shift u c) v := by
    rintro ⟨v, hv, hperiod⟩
    have hback := hperiod.shift (-u)
    have hglobal : IsPeriod c v := by
      simpa only [IsPeriod, shift, add_assoc, neg_add_cancel, add_zero] using hback
    exact hnot ⟨v, hv, hglobal⟩
  have hxlang := languageContained_of_mem_orbitClosure c (shift u c) hx
  have hxann : laurentAct (differenceProduct hs) (shift u c) = 0 := by
    rw [laurentAct_shift, hann]
    rfl
  have hhalf := newton_envelope_half_strip_eq_integer_translates (K := K) hs hdirs hpairs a ha pa hpa haparallel F hF C₀ hbase
  have hgeometric : ∀ g : Site, latticeEmbedding g ∈ latticeHull F + lineRay 0 (latticeEmbedding a) 0 →
      shift u c g = w g := by
    intro g hg
    apply hmatch g
    rw [← hhalf]
    exact hg
  obtain ⟨N, b, μ, G, hN, hb, hab, hμb, hμa, ⟨pb, hpb, hbparallel⟩, hbetween, hperiod⟩ :=
    initial_wedge_from_newton_half_strip (shift u c) w hs hlen hdirs hpairs hxann a ha pa hpa haparallel
      l hl hw F hF C₀ hC₀ hbase hgeometric
  exact ⟨hx, hnotshift, background_wedge_of_actual_initial_newton_period c (shift u c) hc hxlang
    hs hlen hdirs hpairs hxann hnotshift R S hgen a b G ha hb hab μ hμb hμa pa pb hpa hpb
    haparallel hbparallel hbetween m M hbounds hlower hupper N hN hperiod⟩

-- an intrinsic original cyclic envelope provides the exact residual internally for the manuscript's matching branch.
theorem matching_original_cyclic_half_strip_background_on_same_shift {K : Type*}
    [CommRing K] [Nontrivial K] [NoZeroDivisors K] [TopologicalSpace K] [DiscreteTopology K]
    (c w : Site → K) (hc : (Set.range c).Finite)
    (hnot : ¬ ∃ v : Site, v ≠ 0 ∧ IsPeriod c v)
    (hs : List Site) (hlen : 2 ≤ hs.length) (hdirs : ∀ h ∈ hs, h ≠ 0)
    (hpairs : hs.Pairwise (fun h k => determinant h k ≠ 0))
    (hann : laurentAct (differenceProduct hs) c = 0)
    (R S : Finset Site) (hgen : GeneratingPolygon c R S)
    (a : Site) (ha : Int.gcd a.1 a.2 = 1) (pa : Site) (hpa : pa ∈ hs)
    (haparallel : determinant a pa = 0) (m M : ℤ)
    (hbounds : ∀ v ∈ S, m ≤ directionNormal a v ∧ directionNormal a v ≤ M)
    (hlower : 2 ≤ (lowerLatticeFace S (directionNormal a) m).card)
    (hupper : 2 ≤ (lowerLatticeFace S (-directionNormal a) (-M)).card)
    (l : ℕ) (hl : 0 < l) (hw : IsPeriod w ((l : ℤ) • a))
    (F : Finset Site) (hF : LatticeConvex F) (hOriginal : OriginalNewtonCyclicEnvelope (K := K) hs F)
    (u : Site) (hmatch : ∀ g ∈ polygonHalfStrip F a, shift u c g = w g) :
    shift u c ∈ orbitClosure c ∧ (¬ ∃ p : Site, p ≠ 0 ∧ IsPeriod (shift u c) p) ∧
      ∃ d : Site, Int.gcd d.1 d.2 = 1 ∧ 0 < determinant a d ∧
        (∃ h ∈ hs, determinant d h = 0) ∧ Function.Injective ((directionNormal a).prod (-directionNormal d)) ∧
        ∃ E : Site, ∃ B : Site → K, FullyPeriodic B ∧
          AgreesOnWedge (directionNormal a) (-directionNormal d) (directionNormal a E)
            ((-directionNormal d) E) (shift u c) B ∧ Set.range B ⊆ Set.range (shift u c) := by
  classical
  obtain ⟨q, hq, _hqeq, _e, _hfan, _hprimitive, _hsource, _hcover, _hP, hEnvelope⟩ := hOriginal
  let _ : NeZero q := ⟨by omega⟩
  obtain ⟨_hFpoly, C₀, _hconvex, _hcompact, hC₀, hbase⟩ := hEnvelope
  exact matching_newton_half_strip_background_on_same_shift c w hc hnot hs hlen hdirs hpairs hann
    R S hgen a ha pa hpa haparallel m M hbounds hlower hupper l hl hw F hF C₀ hC₀ hbase u hmatch

end KumarNivat
