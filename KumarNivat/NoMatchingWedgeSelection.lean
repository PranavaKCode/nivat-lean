import KumarNivat.AnchoredSourceSequences
import KumarNivat.AnchoredNonperiodicChainSelection
import KumarNivat.AnchoredNonperiodicLimit
import KumarNivat.AnchoredRetainedPeriodFailures
import KumarNivat.AnchoredFailedPeriodWedge
import Mathlib.Topology.Instances.Int

namespace KumarNivat

-- the no-matching branch constructs the same nonperiodic orbit point and its fully periodic wedge background.
theorem nonperiodic_wedge_of_no_matching_original_half_strip
    (c w : Site → ℤ) (hc : (Set.range c).Finite) (hw : w ∈ orbitClosure c)
    (hs : List Site) (hlen : 2 ≤ hs.length) (hdirs : ∀ p ∈ hs, p ≠ 0)
    (hpairs : hs.Pairwise (fun p r => determinant p r ≠ 0))
    (hann : laurentAct (differenceProduct hs) c = 0)
    (R S : Finset Site) (hgen : GeneratingPolygon c R S)
    (a : Site) (hprimitive : Int.gcd a.1 a.2 = 1) (p : Site) (hpmem : p ∈ hs)
    (hparallel : determinant a p = 0)
    (m M : ℤ) (hbounds : ∀ g ∈ S, m ≤ directionNormal a g ∧ directionNormal a g ≤ M)
    (hlower : 2 ≤ (lowerLatticeFace S (directionNormal a) m).card)
    (hupper : 2 ≤ (lowerLatticeFace S (-directionNormal a) (-M)).card)
    (cut : ℤ) (l : ℕ) (hl : 0 < l) (hperiod : IsPeriod w ((l : ℤ) • a))
    (hnotFull : ¬ FullyRegionallyPeriodic w {g | cut ≤ directionNormal a g})
    (hnoHalfStrip : ∀ F : Finset Site, OriginalNewtonCyclicEnvelope (K := ℤ) hs F →
      LatticeConvex F → (∀ g ∈ F, cut ≤ directionNormal a g) →
      ∀ u : Site, ¬ ∀ g ∈ polygonHalfStrip F a, shift u c g = w g) :
    ∃ θ ∈ orbitClosure c, (¬ ∃ v : Site, v ≠ 0 ∧ IsPeriod θ v) ∧
      ∃ B : Site → ℤ, FullyPeriodic B ∧ ∃ ell μ : Site →+ ℤ, ∃ r s : ℤ,
        Function.Injective (ell.prod μ) ∧ AgreesOnWedge ell μ r s θ B := by
  obtain ⟨G, hG⟩ := primitive_direction_normal_surjective a hprimitive cut
  obtain ⟨q, hq, hdata⟩ := exists_source_anchored_maximal_sequence c w hw hs hlen hdirs hpairs
    a hprimitive p hpmem hparallel cut G hG l hl hperiod hnoHalfStrip
  let _ : NeZero q := ⟨by omega⟩
  obtain ⟨_hqeq, e, he₀, hfan, hprimitives, hsource, _hcover, ⟨Q⟩, r, _hr₀, _hrl, ⟨seq⟩⟩ := hdata
  let phase := shift (r • a) w
  have hphasePeriod : IsPeriod phase ((l : ℤ) • e 0) := by
    rw [he₀]
    exact anchored_reference_phase_period w a l hperiod r
  have hphaseNotFull : ¬ FullyRegionallyPeriodic phase
      {g | directionNormal (e 0) G ≤ directionNormal (e 0) g} := by
    rw [he₀, hG]
    exact halfplane_phase_not_fully_regionally_periodic w (directionNormal a) cut a
      (directionNormal_self a) r hnotFull
  have hwann : laurentAct (differenceProduct hs) w = 0 := funext
    (annihilator_inherited_of_language w c (languageContained_of_mem_orbitClosure c w hw)
      (differenceProduct hs).coeff (congrFun hann))
  have hphaseAnn : laurentAct (differenceProduct hs) phase = 0 := by
    dsimp [phase]
    rw [laurentAct_shift, hwann]
    rfl
  obtain ⟨b, hb₀, hbq, fixed, _hfixed₀, L, _hL, θ, hθ, hnot, hagree, hfailure, hsums⟩ :=
    seq.nonperiodic_relaxed_chain_limit hs hdirs hpairs e hfan hprimitives hsource c phase G Q
      hc hann hphaseAnn l hl hphasePeriod hphaseNotFull
  obtain ⟨j, _hj₀, hjL, g, _hlevel, hg, hneq, hnext, _hregional⟩ :=
    anchored_retained_old_period_first_failure θ phase e hfan fixed b hb₀ hbq l hl
      hphasePeriod hagree L hfailure
  obtain ⟨C, hsum⟩ := hsums j hjL
  rw [anchored_relaxed_chain_as_inward_layer] at hsum hg
  let β := fixed b - (j : ℤ)
  have hnext' : ∀ u : Site, latticeEmbedding u ∈
      inwardLayerRegion (directionNormal (e (b : ZMod (2 * q)))) (β + 1) (Finset.range b)
        (fun i => directionNormal (e (i : ZMod (2 * q)))) fixed →
      θ u = shift ((l : ℤ) • (-e 0)) θ u := by
    intro u hu
    apply hnext u
    rw [anchored_relaxed_chain_as_inward_layer]
    have hcut : fixed b - ((j : ℤ) - 1) = β + 1 := by dsimp [β]; omega
    rwa [hcut]
  have hlang := languageContained_of_mem_orbitClosure c θ hθ
  have hθann : laurentAct (differenceProduct hs) θ = 0 := funext
    (annihilator_inherited_of_language θ c hlang (differenceProduct hs).coeff (congrFun hann))
  obtain ⟨hinj, E, B, hB, hwedge, _hrange⟩ := anchored_failed_period_background_wedge
    c θ hc hlang hs hdirs hθann R S hgen e hfan b hb₀ hbq (hprimitives 0)
    (hprimitives (b : ZMod (2 * q))) m M (by rwa [he₀]) (by rwa [he₀]) (by rwa [he₀])
    fixed β C hsum l hl hnext' ⟨g, hg, hneq⟩
  exact ⟨θ, hθ, hnot, B, hB, directionNormal (e 0), directionNormal (e (b : ZMod (2 * q))),
    directionNormal (e 0) E, directionNormal (e (b : ZMod (2 * q))) E, hinj, hwedge⟩

end KumarNivat
