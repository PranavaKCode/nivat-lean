import KumarNivat.ColleAnchoredPreparationData
import KumarNivat.AnchoredPreparedChains
import KumarNivat.AnchoredRetainedFailures
import KumarNivat.AnchoredSeedFailureLayers
import KumarNivat.AnchoredRelaxedChainUnionsResidual

open Filter Topology

namespace KumarNivat

-- the actual source sequence constructs its retained failed facet without any supplied limit or relaxed summand.
theorem exists_colle_anchored_retained_facet (c : Site → ℤ) (hs : List Site)
    {q : ℕ} [NeZero q] (e : ZMod (2 * q) → Site) (D : ColleAnchoredSourceData c hs e) :
    Nonempty (ColleAnchoredRetainedFacet c hs e D.reference) := by
  obtain ⟨b, hb₀, hbq, d, B, fixed, hB, hbuffer, hbdiv, _hfixed₀, _hfixedb, hfixed, hUnion⟩ :=
    D.source_sequence.prepared_chain D.fan_order (differenceProduct (K := ℤ) hs).coeff.support D.newton_polygon
  let seq := D.source_sequence.tail d
  obtain ⟨p, hpmem, hparallel⟩ := D.factor_source 0
  obtain ⟨θ, hθ, hagree, hfailure⟩ := seq.retained_relaxed_failure hs D.factor_nonzero D.factor_distinct
    e D.fan_order c D.reference 0 D.newton_polygon (D.primitive 0) p hpmem hparallel b hb₀ hbq
    (D.primitive (b : ZMod (2 * q))) B hB hbuffer hbdiv fixed hfixed D.finite
    D.product_annihilates D.reference_product_annihilates
  let ν := directionNormal (e (b : ZMod (2 * q)))
  let μ := fun i : ℕ => directionNormal (e (i : ZMod (2 * q)))
  let M := (cyclicFacetRelaxationScale e (b : ZMod (2 * q))).toNat
  have hscale := cyclic_facet_relaxation_scale_positive e D.fan_order.order (b : ZMod (2 * q))
  have hcast : (M : ℤ) = cyclicFacetRelaxationScale e (b : ZMod (2 * q)) :=
    Int.toNat_of_nonneg hscale.le
  have hstart : ∀ g : Site, latticeEmbedding g ∈
      inwardLayerRegion ν (fixed b) (Finset.range b) μ fixed → θ g = D.reference g := by
    intro g hg
    apply hagree g
    rw [hUnion]
    have hzero : anchoredRelaxedChainRegion e fixed b 0 =
        finiteInwardRegion (Finset.range (b + 1)) μ fixed := by
      have hcuts : anchoredRelaxedChainCut fixed b 0 = fixed := by
        funext i
        simp only [anchoredRelaxedChainCut, ite_self, sub_zero]
      rw [anchoredRelaxedChainRegion, hcuts]
    rw [← hzero, anchored_relaxed_chain_as_inward_layer]
    simpa only [sub_zero] using hg
  have hfailed : ∃ g : Site, latticeEmbedding g ∈
      inwardLayerRegion ν (fixed b - (M : ℤ)) (Finset.range b) μ fixed ∧ θ g ≠ D.reference g := by
    rw [← hcast] at hfailure
    simpa only [anchored_relaxed_chain_as_inward_layer] using hfailure
  obtain ⟨j, _hj₀, hjM, g, _hlevel, hg, hneq, hnext⟩ :=
    first_failed_inward_layer_with_bounded_failure θ D.reference ν (fixed b)
      (Finset.range b) μ fixed M hstart hfailed
  obtain ⟨C, _hCdef, _hCconvex, _hCnonempty, hsum⟩ :=
    seq.relaxed_chain_original_newton_envelope_nat D.fan_order D.newton_polygon b hb₀ hbq hbdiv
      B (Eventually.of_forall hB) fixed hfixed hbuffer j hjM
  rw [anchored_relaxed_chain_as_inward_layer] at hsum
  refine ⟨{
    index := b
    index_positive := hb₀
    index_lt := hbq
    point := θ
    point_orbit := hθ
    level := fixed b - (j : ℤ)
    fixed := fixed
    residual := C
    newton_sum := hsum
    interior_agrees := ?_
    failure := ⟨g, hg, hneq⟩
  }⟩
  intro u hu hνu
  apply hnext u
  have hsite := (mem_inwardLayerRegion_lattice ν _ (Finset.range b) μ fixed u).mp hu
  exact (mem_inwardLayerRegion_lattice ν _ (Finset.range b) μ fixed u).mpr ⟨hνu, hsite.2⟩

-- the retained facet closes the paired-direction conclusion for the actual anchored source data.
theorem paired_direction_of_actual_anchored_source (c : Site → ℤ) (hs : List Site)
    {q : ℕ} [NeZero q] (e : ZMod (2 * q) → Site) (D : ColleAnchoredSourceData c hs e) :
    HasPairedOneSidedDirection c := by
  obtain ⟨R⟩ := exists_colle_anchored_retained_facet c hs e D
  exact paired_direction_of_colle_retained_facet c hs e D R

end KumarNivat
