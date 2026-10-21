module

public import KumarNivat.AnchoredConstructedChain
public import KumarNivat.NewtonCyclicFactorOriginalAligned

@[expose] public section

namespace KumarNivat

-- the original factor product determines its actual fan and convex newton envelope, independently of a chosen starting edge.
def OriginalNewtonCyclicEnvelope {K : Type*} [CommRing K] (hs : List Site) (F : Finset Site) : Prop :=
  ∃ q : ℕ, ∃ hq : 2 ≤ q,
    let _ : NeZero q := ⟨by omega⟩
    q = hs.length ∧ ∃ e : ZMod (2 * q) → Site, AnchoredChainFanOrder e ∧
      (∀ i, Int.gcd (e i).1 (e i).2 = 1) ∧
      (∀ i, ∃ g ∈ hs, determinant (e i) g = 0) ∧
      (∀ g ∈ hs, ∃ i, determinant (e i) g = 0) ∧
      Nonempty (OrderedCyclicLatticePolygon e (differenceProduct (K := K) hs).coeff.support) ∧
      AnchoredCyclicEnvelope e (latticeHull (differenceProduct (K := K) hs).coeff.support) F

-- the manuscript's no-matching case now constructs its actual maximal anchored sequence directly from the original factors.
theorem exists_source_anchored_maximal_sequence {K : Type*} [CommRing K] [Nontrivial K]
    [NoZeroDivisors K] [TopologicalSpace K] [DiscreteTopology K]
    (c w : Site → K) (hw : w ∈ orbitClosure c)
    (hs : List Site) (hlen : 2 ≤ hs.length) (hdirs : ∀ h ∈ hs, h ≠ 0)
    (hpairs : hs.Pairwise (fun p r => determinant p r ≠ 0))
    (a : Site) (hprimitive : Int.gcd a.1 a.2 = 1) (p : Site) (hpmem : p ∈ hs)
    (hparallel : determinant a p = 0) (cut : ℤ) (G : Site) (hGcut : directionNormal a G = cut)
    (l : ℕ) (hl : 0 < l) (hperiod : IsPeriod w ((l : ℤ) • a))
    (hnoHalfStrip : ∀ F : Finset Site, OriginalNewtonCyclicEnvelope (K := K) hs F →
      LatticeConvex F → (∀ g ∈ F, cut ≤ directionNormal a g) →
      ∀ u : Site, ¬ ∀ g ∈ polygonHalfStrip F a, shift u c g = w g) :
    ∃ q : ℕ, ∃ hq : 2 ≤ q,
      let _ : NeZero q := ⟨by omega⟩
      q = hs.length ∧ ∃ e : ZMod (2 * q) → Site, e 0 = a ∧ AnchoredChainFanOrder e ∧
        (∀ i, Int.gcd (e i).1 (e i).2 = 1) ∧
        (∀ i, ∃ g ∈ hs, determinant (e i) g = 0) ∧
        (∀ g ∈ hs, ∃ i, determinant (e i) g = 0) ∧
        Nonempty (OrderedCyclicLatticePolygon e (differenceProduct (K := K) hs).coeff.support) ∧
        ∃ r : ℤ, 0 ≤ r ∧ r < (l : ℤ) ∧
          Nonempty (AnchoredCyclicMaximalSequence c (shift (r • a) w) e
            (latticeHull (differenceProduct (K := K) hs).coeff.support) G) := by
  classical
  obtain ⟨q, hq, hmodel⟩ := actual_original_cyclic_model_with_prescribed_factor (K := K)
    hs hlen hdirs hpairs a hprimitive p hpmem hparallel
  let _ : NeZero q := ⟨by omega⟩
  obtain ⟨hqeq, e, hfirst, hfan, hprimitives, hsource, hcover, hP⟩ := hmodel
  have hprimitiveE : Int.gcd (e 0).1 (e 0).2 = 1 := by rw [hfirst]; exact hprimitive
  have hparallelE : determinant (e 0) p = 0 := by rw [hfirst]; exact hparallel
  have hGcutE : directionNormal (e 0) G = cut := by rw [hfirst]; exact hGcut
  have hperiodE : IsPeriod w ((l : ℤ) • e 0) := by rw [hfirst]; exact hperiod
  have hnoE : ∀ F : Finset Site,
      AnchoredCyclicEnvelope e (latticeHull (differenceProduct (K := K) hs).coeff.support) F →
      LatticeConvex F → (∀ g ∈ F, cut ≤ directionNormal (e 0) g) →
      ∀ u : Site, ¬ ∀ g ∈ polygonHalfStrip F (e 0), shift u c g = w g := by
    intro F hEnvelope hF hhalf
    have hOriginal : OriginalNewtonCyclicEnvelope (K := K) hs F :=
      ⟨q, hq, hqeq, e, hfan, hprimitives, hsource, hcover, hP, hEnvelope⟩
    rw [hfirst] at hhalf ⊢
    exact hnoHalfStrip F hOriginal hF hhalf
  obtain ⟨r, hr₀, hr₁, hseq⟩ := exists_actual_anchored_maximal_sequence c w hw hs hlen hdirs hpairs
    e hfan (Classical.choice hP) hprimitiveE p hpmem hparallelE cut G hGcutE l hl hperiodE hnoE
  rw [hfirst] at hseq
  exact ⟨q, hq, hqeq, e, hfirst, hfan, hprimitives, hsource, hcover, hP, r, hr₀, hr₁, hseq⟩

end KumarNivat
