module

public import KumarNivat.PeriodicReferenceChoice
public import KumarNivat.LowComplexityInitialBand

@[expose] public section

namespace KumarNivat

-- lemma 5.4 now follows from the original rectangle hypotheses and the explicitly supplied paired direction.
theorem integer_low_complexity_periodic_reference (c : Site → ℤ) (hc : (Set.range c).Finite)
    (hnot : ¬ ∃ v : Site, v ≠ 0 ∧ IsPeriod c v) (k n : ℕ) (hk : 0 < k) (hn : 0 < n)
    (hlow : complexity c (rectangle k n) ≤ k * n) (hpair : HasPairedOneSidedDirection c) :
    ∃ S : Finset Site, GeneratingPolygon c (rectangle k n) S ∧
      ∃ hs : List Site, hs ≠ [] ∧ hs.Pairwise (fun a b => determinant a b ≠ 0) ∧
        (∀ h ∈ hs, h ≠ 0) ∧ laurentAct (differenceProduct hs) c = 0 ∧
        ∃ p h : Site, p ≠ 0 ∧ Int.gcd p.1 p.2 = 1 ∧ h ∈ hs ∧ h ≠ 0 ∧ determinant p h = 0 ∧
          ∃ m M : ℤ, m < M ∧ (∀ u ∈ S, m ≤ directionNormal p u ∧ directionNormal p u ≤ M) ∧
            2 ≤ (lowerLatticeFace S (directionNormal p) m).card ∧
            (lowerLatticeFace S (directionNormal p) m).card ≤
              (lowerLatticeFace S (-directionNormal p) (-M)).card ∧
            ∃ β : ℤ, ∃ w : Site → ℤ, w ∈ orbitClosure c ∧
              ∃ l : ℕ, 0 < l ∧ IsPeriod w ((l : ℤ) • p) ∧
                ¬ FullyRegionallyPeriodic w {g | β ≤ directionNormal p g} := by
  obtain ⟨S, hgen, hs, hhs, hpairs, hdirs, hann, p, h, hp, hprimitive, hh, hhne, hdet,
      _hNE, _hNEneg, m, M, hwidth, hbounds, hlower, hshorter,
      x, y, hx, hy, β, g₀, s, _hβ, hg₀, hneq, hspos, hsbound, hhalf, hxband, hyband⟩ :=
    integer_low_complexity_initial_band c hc hnot k n hk hn hlow hpair
  obtain ⟨w, hw, l, hl, hwperiod, hwnotfull⟩ := periodic_reference_of_initial_band_pair c x y hc hx hy
    hs hdirs hpairs hann (rectangle k n) S hgen p hprimitive m M hbounds hlower hshorter β hhalf
      g₀ hg₀ hneq s hspos hsbound hxband hyband
  exact ⟨S, hgen, hs, hhs, hpairs, hdirs, hann, p, h, hp, hprimitive, hh, hhne, hdet,
    m, M, hwidth, hbounds, hlower, hshorter, β, w, hw, l, hl, hwperiod, hwnotfull⟩

end KumarNivat
