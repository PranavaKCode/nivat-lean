module

public import KumarNivat.AnchoredPreparedChains
public import KumarNivat.AnchoredRetainedFailures
public import KumarNivat.AnchoredRelaxedChainUnionsResidual

@[expose] public section

open Filter Topology

namespace KumarNivat

open scoped Pointwise

-- a primitive tangent has an actual lattice point on every integer supporting line.
theorem primitive_direction_normal_surjective (a : Site) (ha : Int.gcd a.1 a.2 = 1) (cut : ℤ) :
    ∃ G : Site, directionNormal a G = cut := by
  have hbezout := Int.gcd_eq_gcd_ab a.1 a.2
  rw [ha, Nat.cast_one] at hbezout
  refine ⟨(-cut * Int.gcdB a.1 a.2, cut * Int.gcdA a.1 a.2), ?_⟩
  change a.1 * (cut * Int.gcdA a.1 a.2) - a.2 * (-cut * Int.gcdB a.1 a.2) = cut
  nlinarith [congrArg (fun z : ℤ => cut * z) hbezout]

-- actual maximality constructs one nonperiodic orbit point, its bounded failed enlargement and every needed newton summand.
theorem AnchoredCyclicMaximalSequence.nonperiodic_relaxed_chain_limit {K : Type*}
    [CommRing K] [Nontrivial K] [NoZeroDivisors K] [TopologicalSpace K] [DiscreteTopology K]
    {q : ℕ} [NeZero q] (hs : List Site) (hdirs : ∀ p ∈ hs, p ≠ 0)
    (hpairs : hs.Pairwise (fun p r => determinant p r ≠ 0))
    (e : ZMod (2 * q) → Site) (hfan : AnchoredChainFanOrder e)
    (hprimitive : ∀ i, Int.gcd (e i).1 (e i).2 = 1)
    (hsource : ∀ i, ∃ p ∈ hs, determinant (e i) p = 0)
    (c w : Site → K) (G : Site)
    (seq : AnchoredCyclicMaximalSequence c w e (latticeHull (differenceProduct (K := K) hs).coeff.support) G)
    (Q : OrderedCyclicLatticePolygon e (differenceProduct (K := K) hs).coeff.support)
    (hc : (Set.range c).Finite) (hcann : laurentAct (differenceProduct hs) c = 0)
    (hwann : laurentAct (differenceProduct hs) w = 0)
    (l : ℕ) (hl : 0 < l) (hperiod : IsPeriod w ((l : ℤ) • e 0))
    (hnotFull : ¬ FullyRegionallyPeriodic w {g | directionNormal (e 0) G ≤ directionNormal (e 0) g}) :
    ∃ b : ℕ, 0 < b ∧ b < q ∧ ∃ fixed : ℕ → ℤ,
      fixed 0 = directionNormal (e 0) G ∧ ∃ M : ℕ, 0 < M ∧ ∃ θ ∈ orbitClosure c,
        (¬ ∃ p : Site, p ≠ 0 ∧ IsPeriod θ p) ∧
        (∀ g : Site, latticeEmbedding g ∈ anchoredRelaxedChainRegion e fixed b 0 → θ g = w g) ∧
        (∃ g : Site, latticeEmbedding g ∈ anchoredRelaxedChainRegion e fixed b (M : ℤ) ∧ θ g ≠ w g) ∧
        ∀ j : ℕ, j ≤ M → ∃ C : Set RealPlane,
          anchoredRelaxedChainRegion e fixed b (j : ℤ) =
            latticeHull (differenceProduct (K := K) hs).coeff.support + C := by
  obtain ⟨b, hb₀, hbq, d, B, fixed, hB, hbuffer, hbdiv, hfixed₀, _hfixedb, hfixed, _hUnion⟩ :=
    seq.prepared_chain hfan (differenceProduct (K := K) hs).coeff.support Q
  let tail := seq.tail d
  obtain ⟨p, hpmem, hparallel⟩ := hsource 0
  obtain ⟨θ, hθ, hagree, hfailure, hnot⟩ := tail.retained_nonperiodic_relaxed_failure
    hs hdirs hpairs e hfan c w G Q (hprimitive 0) p hpmem hparallel b hb₀ hbq
    (hprimitive (b : ZMod (2 * q))) B hB hbuffer hbdiv fixed hfixed₀ hfixed hc hcann hwann
    l hl hperiod hnotFull
  let M := (cyclicFacetRelaxationScale e (b : ZMod (2 * q))).toNat
  have hscale := cyclic_facet_relaxation_scale_positive e hfan.order (b : ZMod (2 * q))
  have hM : 0 < M := by dsimp [M]; omega
  have hcast : (M : ℤ) = cyclicFacetRelaxationScale e (b : ZMod (2 * q)) :=
    Int.toNat_of_nonneg hscale.le
  refine ⟨b, hb₀, hbq, fixed, hfixed₀, M, hM, θ, hθ, hnot, ?_, ?_, ?_⟩
  · intro g hg
    apply hagree g
    have hzero := tail.relaxed_chain_union hfan b hb₀ hbq hbdiv B (Eventually.of_forall hB) fixed hfixed 0
    have hregions : (fun N => cyclicFacetRelaxedRegion e (tail.polygon N) (tail.cyclic N)
        (b : ZMod (2 * q)) 0) = fun N => latticeHull (tail.polygon N) := by
      funext N
      exact cyclic_facet_relaxed_region_zero e hfan.order (tail.polygon N) (tail.cyclic N) _
    rw [hregions] at hzero
    rwa [hzero]
  · rwa [hcast]
  · intro j hj
    obtain ⟨C, _hCdef, _hCconvex, _hCnonempty, hsum⟩ := tail.relaxed_chain_original_newton_envelope_nat
      hfan Q b hb₀ hbq hbdiv B (Eventually.of_forall hB) fixed hfixed hbuffer j hj
    exact ⟨C, hsum⟩

end KumarNivat
