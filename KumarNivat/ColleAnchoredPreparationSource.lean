module

public import KumarNivat.ColleAnchoredPreparationData
public import KumarNivat.PairedStructureFiberSymmetry
public import KumarNivat.RayChainPairedNoHalfStrip
public import KumarNivat.NewtonCyclicFactorOriginalModel
public import KumarNivat.NonperiodicProductLengths

@[expose] public section

namespace KumarNivat

open scoped Pointwise

-- a nonzero original integer annihilator and no-pair contradiction construct every source input and its shared periodic phase.
theorem exists_colle_anchored_source_data_of_integer_annihilator_no_pair
    (c : Site → ℤ) (hc : (Set.range c).Finite) (f : Laurent ℤ) (hf : f ≠ 0)
    (hann : laurentAct f c = 0) (hnotfull : ¬ FullyPeriodic c)
    (hnopair : ¬ HasPairedOneSidedDirection c) :
    ∃ hs : List Site, ∃ q : ℕ, ∃ hq : 2 ≤ q,
      let _ : NeZero q := ⟨by omega⟩
      ∃ e : ZMod (2 * q) → Site, Nonempty (ColleAnchoredSourceData c hs e) := by
  classical
  have hnot := nonperiodic_of_no_pair_not_fullyPeriodic c hc hnopair hnotfull
  obtain ⟨hs, _hnil, hpairs, hdirs, hprod⟩ := integer_annihilator_distinct_difference_product c hc f hf hann
  have hlen := nonperiodic_difference_product_has_two_factors c hnot hs hdirs hprod
  obtain ⟨q, hq, hqeq, e, horder, hanti, hstrict, hprimitive, hsource, hcover, ⟨P⟩⟩ :=
    actual_original_difference_product_cyclic_model (K := ℤ) hs hlen hdirs hpairs
  let _ : NeZero q := ⟨by omega⟩
  have hfan : AnchoredChainFanOrder e :=
    ⟨horder, hanti, fun i d hd₀ hdq => ne_of_gt (hstrict i d hd₀ hdq)⟩
  obtain ⟨p, hpmem, hparallel⟩ := hsource 0
  obtain ⟨w, hw, hwfull⟩ := exists_fullyPeriodic_orbit_point_of_integer_annihilator_no_pair c hc f hf hann hnopair
  obtain ⟨l, hl, hwperiod⟩ := hwfull.exists_period_multiple (e 0)
  have hno : ∀ F : Finset Site,
      AnchoredCyclicEnvelope e (latticeHull (differenceProduct (K := ℤ) hs).coeff.support) F →
        LatticeConvex F → (∀ g ∈ F, (0 : ℤ) ≤ directionNormal (e 0) g) →
          ∀ u : Site, ¬ ∀ g ∈ polygonHalfStrip F (e 0), shift u c g = w g := by
    intro F hEnvelope hF _hhalf
    exact no_anchored_cyclic_half_strip_agreement_of_no_pair c w hc hnopair hnot hs hlen hdirs hpairs hprod
      e (hprimitive 0) p hpmem hparallel l hl hwperiod F hF hEnvelope
  obtain ⟨r, _hr₀, _hr₁, hseq⟩ := exists_actual_anchored_maximal_sequence c w hw hs hlen hdirs hpairs
    e hfan P (hprimitive 0) p hpmem hparallel 0 0 (map_zero _) l hl hwperiod hno
  let B := shift (r • e 0) w
  have hB : B ∈ orbitClosure c := orbitClosure_shift_mem c w hw (r • e 0)
  have hBfull : FullyPeriodic B := by
    obtain ⟨u, v, huv, hu, hv⟩ := hwfull
    exact ⟨u, v, huv, hu.shift (r • e 0), hv.shift (r • e 0)⟩
  have hBperiod : IsPeriod B ((l : ℤ) • e 0) := hwperiod.shift (r • e 0)
  have hBlang := languageContained_of_mem_orbitClosure c B hB
  have hBprod : laurentAct (differenceProduct hs) B = 0 := funext
    (annihilator_inherited_of_language B c hBlang (differenceProduct hs).coeff (congrFun hprod))
  have hBoriginal : laurentAct f B = 0 := funext
    (annihilator_inherited_of_language B c hBlang f.coeff (congrFun hann))
  refine ⟨hs, q, hq, e, ⟨{
    finite := hc
    nonperiodic := hnot
    length_two := hlen
    factor_nonzero := hdirs
    factor_distinct := hpairs
    product_annihilates := hprod
    fan_size := hq
    fan_length := hqeq
    fan_order := hfan
    primitive := hprimitive
    factor_source := hsource
    factor_cover := hcover
    newton_polygon := P
    reference := B
    reference_orbit := hB
    reference_full := hBfull
    reference_language := hBlang
    reference_finite := finite_range_of_language B c hc hBlang
    reference_product_annihilates := hBprod
    original_operator := f
    original_operator_nonzero := hf
    original_annihilates := hann
    reference_original_annihilates := hBoriginal
    periodLength := l
    period_positive := hl
    reference_period := hBperiod
    no_half_strip := ?_
    source_sequence := Classical.choice hseq
  }⟩⟩
  intro F hEnvelope hF
  exact no_anchored_cyclic_half_strip_agreement_of_no_pair c B hc hnopair hnot hs hlen hdirs hpairs hprod
    e (hprimitive 0) p hpmem hparallel l hl hBperiod F hF hEnvelope

end KumarNivat
