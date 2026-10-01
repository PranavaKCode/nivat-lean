import KumarNivat.InitialPeriodicBand
import KumarNivat.OrientedPairedData
import KumarNivat.KariSzabados
import KumarNivat.SquarefreeProducts

namespace KumarNivat

-- the original rectangle hypotheses now give the full starting-band data once the paired direction is supplied.
theorem integer_low_complexity_initial_band (c : Site → ℤ) (hc : (Set.range c).Finite)
    (hnot : ¬ ∃ v : Site, v ≠ 0 ∧ IsPeriod c v) (k n : ℕ) (hk : 0 < k) (hn : 0 < n)
    (hlow : complexity c (rectangle k n) ≤ k * n) (hpair : HasPairedOneSidedDirection c) :
    ∃ S : Finset Site, GeneratingPolygon c (rectangle k n) S ∧
      ∃ hs : List Site, hs ≠ [] ∧ hs.Pairwise (fun a b => determinant a b ≠ 0) ∧
        (∀ h ∈ hs, h ≠ 0) ∧ laurentAct (differenceProduct hs) c = 0 ∧
        ∃ p h : Site, p ≠ 0 ∧ Int.gcd p.1 p.2 = 1 ∧ h ∈ hs ∧ h ≠ 0 ∧ determinant p h = 0 ∧
          OneSidedNonexpansive c (integerNormalAsReal (directionNormal p)) ∧
          OneSidedNonexpansive c (-integerNormalAsReal (directionNormal p)) ∧
          ∃ m M : ℤ, m < M ∧ (∀ u ∈ S, m ≤ directionNormal p u ∧ directionNormal p u ≤ M) ∧
            2 ≤ (lowerLatticeFace S (directionNormal p) m).card ∧
            (lowerLatticeFace S (directionNormal p) m).card ≤
              (lowerLatticeFace S (-directionNormal p) (-M)).card ∧
            ∃ x y : Site → ℤ, x ∈ orbitClosure c ∧ y ∈ orbitClosure c ∧
              ∃ β : ℤ, ∃ g₀ : Site, ∃ q : ℕ, β < 0 ∧ directionNormal p g₀ = β ∧ x g₀ ≠ y g₀ ∧
                0 < q ∧ q ≤ (lowerLatticeFace S (directionNormal p) m).card - 1 ∧
                (∀ g : Site, β + 1 ≤ directionNormal p g → x g = y g) ∧
                RegionalPeriod x (normalBand (directionNormal p) (β + 1) (β + (M - m))) ((q : ℤ) • p) ∧
                RegionalPeriod y (normalBand (directionNormal p) (β + 1) (β + (M - m))) ((q : ℤ) • p) := by
  obtain ⟨S, hgen⟩ := exists_integer_generating_polygon c hc hnot k n hk hn hlow
  obtain ⟨hs, hhs, hpairs, hdirs, hann⟩ := low_complexity_distinct_difference_product c hc (rectangle k n)
    (by simpa only [card_rectangle] using hlow)
  obtain ⟨p, h, hp, hprimitive, hh, hhne, hdet, hNE, hNEneg, m, M, hbounds, hlower, _hupper, hshorter⟩ :=
    shorter_paired_direction_supporting_data c (rectangle k n) S hgen hs hdirs hann hpair
  obtain ⟨hwidth, x, y, hx, hy, β, g₀, q, hβ, hg₀, hneq, hq, hqr, hhalf, hxper, hyper⟩ :=
    exists_initial_periodic_band c hc (differenceProduct hs) (differenceProduct_ne_zero hs hdirs) hann
      (rectangle k n) S hgen p hprimitive m M hbounds hlower hshorter hNE
  exact ⟨S, hgen, hs, hhs, hpairs, hdirs, hann, p, h, hp, hprimitive, hh, hhne, hdet, hNE, hNEneg,
    m, M, hwidth, hbounds, hlower, hshorter, x, y, hx, hy, β, g₀, q, hβ, hg₀, hneq, hq, hqr, hhalf, hxper, hyper⟩

end KumarNivat
