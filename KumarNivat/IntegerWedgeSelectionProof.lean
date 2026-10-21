module

public import KumarNivat.CollePairedDirection
public import KumarNivat.LowComplexityPeriodicReference
public import KumarNivat.MainMatchingBackgroundHalfStrip
public import KumarNivat.NoMatchingWedgeSelection
public import KumarNivat.NonperiodicProductLengths
public import KumarNivat.FinalDeduction
public import KumarNivat.DivisorPeriods

@[expose] public section

namespace KumarNivat

-- the paired-direction input and both actual half-strip cases construct the paper's nonperiodic periodic-background wedge.
theorem integer_wedge_selection : IntegerWedgeSelection := by
  classical
  intro c hc hnot k n hk hn hlow
  obtain ⟨ts, _htlen, htpairs, htdirs, htann⟩ := nonperiodic_low_complexity_product_data
    c hc hnot (rectangle k n) (by simpa only [card_rectangle] using hlow)
  have hnotFull : ¬ FullyPeriodic c := fun hfull => hnot (FullyPeriodic.exists_nonzero_period c hfull)
  have hpair := paired_direction_of_integer_annihilator_not_fullyPeriodic c hc (differenceProduct ts)
    (differenceProduct_ne_zero ts htdirs) htann hnotFull
  obtain ⟨S, hgen, hs, _hhs, hpairs, hdirs, hann, a, p, _hane, hprimitive, hpmem, _hpne, hparallel,
      m, M, _hwidth, hbounds, hlower, hshorter, cut, w, hw, l, hl, hperiod, hnotReference⟩ :=
    integer_low_complexity_periodic_reference c hc hnot k n (by omega) (by omega) hlow hpair
  have hlen := nonperiodic_difference_product_has_two_factors c hnot hs hdirs hann
  have hupper : 2 ≤ (lowerLatticeFace S (-directionNormal a) (-M)).card := hlower.trans hshorter
  by_cases hmatch : ∃ F : Finset Site, OriginalNewtonCyclicEnvelope (K := ℤ) hs F ∧
      LatticeConvex F ∧ ∃ u : Site, ∀ g ∈ polygonHalfStrip F a, shift u c g = w g
  · obtain ⟨F, hOriginal, hF, u, hagree⟩ := hmatch
    obtain ⟨hθ, hθnot, d, _hd, _had, _hdsource, hinj, E, B, hB, hwedge, _hrange⟩ :=
      matching_original_cyclic_half_strip_background_on_same_shift c w hc hnot hs hlen hdirs hpairs hann
        (rectangle k n) S hgen a hprimitive p hpmem hparallel m M hbounds hlower hupper
        l hl hperiod F hF hOriginal u hagree
    exact ⟨shift u c, hθ, hθnot, B, hB, directionNormal a, -directionNormal d,
      directionNormal a E, (-directionNormal d) E, hinj, hwedge⟩
  · apply nonperiodic_wedge_of_no_matching_original_half_strip c w hc hw hs hlen hdirs hpairs hann
      (rectangle k n) S hgen a hprimitive p hpmem hparallel m M hbounds hlower hupper
      cut l hl hperiod hnotReference
    intro F hOriginal hF _hhalf u hagree
    exact hmatch ⟨F, hOriginal, hF, u, hagree⟩

end KumarNivat
