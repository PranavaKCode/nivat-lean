module

public import KumarNivat.AnchoredCyclicSeedFailuresSequence
public import KumarNivat.AnchoredRelaxedChainUnions
public import KumarNivat.AnchoredSequenceLimits

@[expose] public section

open Filter Topology

namespace KumarNivat

-- the actual recurrence witnesses lie in the final relaxed chain and in the original reference half-plane.
theorem AnchoredCyclicMaximalSequence.fixed_failure_set_in_relaxed_chain {K : Type*}
    [CommRing K] [Nontrivial K] [NoZeroDivisors K] {q : ℕ} [NeZero q]
    (hs : List Site) (hdirs : ∀ p ∈ hs, p ≠ 0)
    (hpairs : hs.Pairwise (fun p r => determinant p r ≠ 0))
    (e : ZMod (2 * q) → Site) (hfan : AnchoredChainFanOrder e) (c w : Site → K) (G : Site)
    (seq : AnchoredCyclicMaximalSequence c w e (latticeHull (differenceProduct (K := K) hs).coeff.support) G)
    (Q : OrderedCyclicLatticePolygon e (differenceProduct (K := K) hs).coeff.support)
    (hprimitive₀ : Int.gcd (e 0).1 (e 0).2 = 1) (p : Site) (hpmem : p ∈ hs)
    (hparallel : determinant (e 0) p = 0) (b : ℕ) (hb₀ : 0 < b) (hbq : b < q)
    (hprimitive : Int.gcd (e (b : ZMod (2 * q))).1 (e (b : ZMod (2 * q))).2 = 1)
    (B : Site) (hB : ∀ N, (seq.cyclic N).vertex (b : ZMod (2 * q)) = B)
    (hbuffer : ∀ N, Q.edgeLength (b : ZMod (2 * q)) +
      |determinant (e ((b : ZMod (2 * q)) - 1)) (e ((b : ZMod (2 * q)) + 1))| + 1 ≤
        (seq.cyclic N).edgeLength (b : ZMod (2 * q)))
    (hbdiv : Tendsto (fun N => ((seq.cyclic N).edgeLength (b : ZMod (2 * q))).toNat) atTop atTop)
    (fixed : ℕ → ℤ)
    (hfixed : ∀ i : ℕ, i ≤ b → ∀ᶠ N in atTop,
      anchoredCyclicSupport e (seq.polygon N) (seq.cyclic N) i = fixed i)
    (hcann : laurentAct (differenceProduct hs) c = 0)
    (hwann : laurentAct (differenceProduct hs) w = 0) :
    ∃ E : Finset Site,
      (∀ N, ∃ g ∈ E, shift (seq.sourceShift N) c g ≠ w g) ∧
      (∀ g ∈ E, latticeEmbedding g ∈ anchoredRelaxedChainRegion e fixed b
        (cyclicFacetRelaxationScale e (b : ZMod (2 * q)))) ∧
      ∀ g ∈ E, fixed 0 ≤ directionNormal (e 0) g := by
  obtain ⟨E, hfail, _hlevels, hplaced⟩ := anchored_maximal_sequence_has_fixed_facet_failures
    hs hdirs hpairs e hfan c w G seq Q hprimitive₀ p hpmem hparallel b hb₀ hbq
    hprimitive B hB hbuffer hcann hwann
  have hUnion := seq.relaxed_chain_union hfan b hb₀ hbq hbdiv B (Eventually.of_forall hB)
    fixed hfixed (cyclicFacetRelaxationScale e (b : ZMod (2 * q)))
  have hscale : 0 < cyclicFacetRelaxationScale e (b : ZMod (2 * q)) :=
    cyclic_facet_relaxation_scale_positive e hfan.order _
  have hcast : ((cyclicFacetRelaxationScale e (b : ZMod (2 * q))).toNat : ℤ) =
      cyclicFacetRelaxationScale e (b : ZMod (2 * q)) := Int.toNat_of_nonneg hscale.le
  have hEregion : ∀ g ∈ E, latticeEmbedding g ∈ anchoredRelaxedChainRegion e fixed b
      (cyclicFacetRelaxationScale e (b : ZMod (2 * q))) := by
    intro g hg
    obtain ⟨j, _hj₀, hjM, hj⟩ := hplaced 0 g hg
    have hle : (j : ℤ) ≤ cyclicFacetRelaxationScale e (b : ZMod (2 * q)) := by omega
    rw [← hUnion]
    exact Set.mem_iUnion.mpr ⟨0,
      cyclic_facet_relaxed_region_monotone e (seq.polygon 0) (seq.cyclic 0)
        (b : ZMod (2 * q)) hle hj.1⟩
  refine ⟨E, hfail, hEregion, ?_⟩
  intro g hg
  have hhalf := anchored_relaxed_chain_keeps_reference_halfplane e fixed b hb₀
    (cyclicFacetRelaxationScale e (b : ZMod (2 * q))) (hEregion g hg)
  change (fixed 0 : ℝ) ≤ latticeNormal (directionNormal (e 0)) (latticeEmbedding g) at hhalf
  rw [latticeNormal_embedding] at hhalf
  exact_mod_cast hhalf

-- compactness retains an actual disagreement in the relaxed chain while preserving agreement on every old polygon.
theorem AnchoredCyclicMaximalSequence.retained_relaxed_failure {K : Type*}
    [CommRing K] [Nontrivial K] [NoZeroDivisors K] [TopologicalSpace K] [DiscreteTopology K]
    {q : ℕ} [NeZero q] (hs : List Site) (hdirs : ∀ p ∈ hs, p ≠ 0)
    (hpairs : hs.Pairwise (fun p r => determinant p r ≠ 0))
    (e : ZMod (2 * q) → Site) (hfan : AnchoredChainFanOrder e) (c w : Site → K) (G : Site)
    (seq : AnchoredCyclicMaximalSequence c w e (latticeHull (differenceProduct (K := K) hs).coeff.support) G)
    (Q : OrderedCyclicLatticePolygon e (differenceProduct (K := K) hs).coeff.support)
    (hprimitive₀ : Int.gcd (e 0).1 (e 0).2 = 1) (p : Site) (hpmem : p ∈ hs)
    (hparallel : determinant (e 0) p = 0) (b : ℕ) (hb₀ : 0 < b) (hbq : b < q)
    (hprimitive : Int.gcd (e (b : ZMod (2 * q))).1 (e (b : ZMod (2 * q))).2 = 1)
    (B : Site) (hB : ∀ N, (seq.cyclic N).vertex (b : ZMod (2 * q)) = B)
    (hbuffer : ∀ N, Q.edgeLength (b : ZMod (2 * q)) +
      |determinant (e ((b : ZMod (2 * q)) - 1)) (e ((b : ZMod (2 * q)) + 1))| + 1 ≤
        (seq.cyclic N).edgeLength (b : ZMod (2 * q)))
    (hbdiv : Tendsto (fun N => ((seq.cyclic N).edgeLength (b : ZMod (2 * q))).toNat) atTop atTop)
    (fixed : ℕ → ℤ)
    (hfixed : ∀ i : ℕ, i ≤ b → ∀ᶠ N in atTop,
      anchoredCyclicSupport e (seq.polygon N) (seq.cyclic N) i = fixed i)
    (hc : (Set.range c).Finite) (hcann : laurentAct (differenceProduct hs) c = 0)
    (hwann : laurentAct (differenceProduct hs) w = 0) :
    ∃ θ ∈ orbitClosure c,
      (∀ g : Site, latticeEmbedding g ∈ ⋃ N, latticeHull (seq.polygon N) → θ g = w g) ∧
      ∃ g : Site, latticeEmbedding g ∈ anchoredRelaxedChainRegion e fixed b
        (cyclicFacetRelaxationScale e (b : ZMod (2 * q))) ∧ θ g ≠ w g := by
  obtain ⟨E, hfail, hEregion, _hEhalf⟩ := seq.fixed_failure_set_in_relaxed_chain
    hs hdirs hpairs e hfan c w G Q hprimitive₀ p hpmem hparallel b hb₀ hbq hprimitive
    B hB hbuffer hbdiv fixed hfixed hcann hwann
  obtain ⟨θ, hθ, _φ, _hφ, _hlimit, hagree, g, hg, hneq⟩ :=
    seq.retained_orbit_limit hc E (Eventually.of_forall hfail)
  exact ⟨θ, hθ, hagree, g, hEregion g hg, hneq⟩

-- the same retained finite witness also prevents any new global period when the reference half-plane is not fully periodic.
theorem AnchoredCyclicMaximalSequence.retained_nonperiodic_relaxed_failure {K : Type*}
    [CommRing K] [Nontrivial K] [NoZeroDivisors K] [TopologicalSpace K] [DiscreteTopology K]
    {q : ℕ} [NeZero q] (hs : List Site) (hdirs : ∀ p ∈ hs, p ≠ 0)
    (hpairs : hs.Pairwise (fun p r => determinant p r ≠ 0))
    (e : ZMod (2 * q) → Site) (hfan : AnchoredChainFanOrder e) (c w : Site → K) (G : Site)
    (seq : AnchoredCyclicMaximalSequence c w e (latticeHull (differenceProduct (K := K) hs).coeff.support) G)
    (Q : OrderedCyclicLatticePolygon e (differenceProduct (K := K) hs).coeff.support)
    (hprimitive₀ : Int.gcd (e 0).1 (e 0).2 = 1) (p : Site) (hpmem : p ∈ hs)
    (hparallel : determinant (e 0) p = 0) (b : ℕ) (hb₀ : 0 < b) (hbq : b < q)
    (hprimitive : Int.gcd (e (b : ZMod (2 * q))).1 (e (b : ZMod (2 * q))).2 = 1)
    (B : Site) (hB : ∀ N, (seq.cyclic N).vertex (b : ZMod (2 * q)) = B)
    (hbuffer : ∀ N, Q.edgeLength (b : ZMod (2 * q)) +
      |determinant (e ((b : ZMod (2 * q)) - 1)) (e ((b : ZMod (2 * q)) + 1))| + 1 ≤
        (seq.cyclic N).edgeLength (b : ZMod (2 * q)))
    (hbdiv : Tendsto (fun N => ((seq.cyclic N).edgeLength (b : ZMod (2 * q))).toNat) atTop atTop)
    (fixed : ℕ → ℤ) (hfixed₀ : fixed 0 = directionNormal (e 0) G)
    (hfixed : ∀ i : ℕ, i ≤ b → ∀ᶠ N in atTop,
      anchoredCyclicSupport e (seq.polygon N) (seq.cyclic N) i = fixed i)
    (hc : (Set.range c).Finite) (hcann : laurentAct (differenceProduct hs) c = 0)
    (hwann : laurentAct (differenceProduct hs) w = 0)
    (l : ℕ) (hl : 0 < l) (hperiod : IsPeriod w ((l : ℤ) • e 0))
    (hnotFull : ¬ FullyRegionallyPeriodic w {g | directionNormal (e 0) G ≤ directionNormal (e 0) g}) :
    ∃ θ ∈ orbitClosure c,
      (∀ g : Site, latticeEmbedding g ∈ ⋃ N, latticeHull (seq.polygon N) → θ g = w g) ∧
      (∃ g : Site, latticeEmbedding g ∈ anchoredRelaxedChainRegion e fixed b
        (cyclicFacetRelaxationScale e (b : ZMod (2 * q))) ∧ θ g ≠ w g) ∧
      ¬ ∃ p : Site, p ≠ 0 ∧ IsPeriod θ p := by
  obtain ⟨E, hfail, hEregion, hEhalf⟩ := seq.fixed_failure_set_in_relaxed_chain
    hs hdirs hpairs e hfan c w G Q hprimitive₀ p hpmem hparallel b hb₀ hbq hprimitive
    B hB hbuffer hbdiv fixed hfixed hcann hwann
  have hE : ∀ g ∈ E, directionNormal (e 0) G ≤ directionNormal (e 0) g := by
    simpa only [hfixed₀] using hEhalf
  obtain ⟨θ, hθ, hagree, ⟨g, hg, hneq⟩, hnot⟩ := seq.retained_nonperiodic_limit
    hfan hc hprimitive₀ l hl hperiod hnotFull E hE (Eventually.of_forall hfail)
  exact ⟨θ, hθ, hagree, ⟨g, hEregion g hg, hneq⟩, hnot⟩

end KumarNivat
