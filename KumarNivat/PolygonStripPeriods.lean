import KumarNivat.LatticeRowRuns
import KumarNivat.TuplePatternPeriods

namespace KumarNivat

open scoped Pointwise

-- this is the actual union of all integer translates of the finite base window.
def bilateralTranslateStrip (T : Finset Site) (p : Site) : Set Site :=
  Set.range (fun z : T × ℤ => z.1.val + z.2 • p)

-- integer translates of every original row site make the sampled strip exactly the original strip.
theorem sampledStrip_eq_bilateralTranslateStrip (T : Finset Site) (p : Site) (E : T → Site)
    (hmem : ∀ u, E u ∈ T) (hcover : ∀ u, ∃ d : ℤ, u.val = E u + d • p) :
    sampledStrip E p = bilateralTranslateStrip T p := by
  ext g
  constructor
  · rintro ⟨⟨u, n⟩, rfl⟩
    exact ⟨(⟨E u, hmem u⟩, n), rfl⟩
  · rintro ⟨⟨u, n⟩, rfl⟩
    obtain ⟨d, he⟩ := hcover u
    refine ⟨(u, d + n), ?_⟩
    change E u + (d + n) • p = u.val + n • p
    rw [he, add_smul]
    abel

-- the actual segment summand supplies every row run needed by the sharp strip-period argument.
theorem strip_period_of_segment_summand_and_ambiguous_edge {A : Type*}
    (c x : Site → A) (hc : (Set.range c).Finite) (hlang : LanguageContained x c)
    (S : Finset Site) (hS : LatticeConvex S) (p : Site) (r : ℕ) (hr : 0 < r)
    (C : Set RealPlane) (hsum : latticeHull S = lineInterval 0 (latticeEmbedding p) 0 (r : ℝ) + C)
    (ν : Site →+ ℤ) (m : ℤ) (hp : ν p = 0)
    (hbudget : complexity c S - complexity c (S \ lowerLatticeFace S ν m) ≤ r)
    (hambiguous : ∀ n : ℤ, 2 ≤ extensionCount c S (S \ lowerLatticeFace S ν m) Finset.sdiff_subset
      (legalTranslatedPattern c x hlang (S \ lowerLatticeFace S ν m) (n • p))) :
    ∃ q : ℕ, 0 < q ∧ q ≤ r ∧
      RegionalPeriod x (bilateralTranslateStrip (S \ lowerLatticeFace S ν m) p) ((q : ℤ) • p) := by
  obtain ⟨E, hmem, hcover, hfit⟩ := exists_off_face_row_run_selector S hS p r hr C hsum ν m hp
  obtain ⟨q, hq, hqr, hperiod⟩ := strip_period_of_ambiguous_bases c x hc hlang S
    (S \ lowerLatticeFace S ν m) Finset.sdiff_subset E p r hfit hbudget hambiguous
  rw [sampledStrip_eq_bilateralTranslateStrip _ _ E hmem hcover] at hperiod
  exact ⟨q, hq, hqr, hperiod⟩

-- the generating polygon discharges the ambiguity budget at the actual facing-edge length.
theorem strip_period_of_generating_polygon_summand {A : Type*}
    (c x : Site → A) (hc : (Set.range c).Finite) (hlang : LanguageContained x c)
    (R S : Finset Site) (hgen : GeneratingPolygon c R S)
    (ν : Site →+ ℤ) (hν : ν ≠ 0) (m : ℤ) (hmin : ∀ u ∈ S, m ≤ ν u)
    (hface : 2 ≤ (lowerLatticeFace S ν m).card) (p : Site) (hp : ν p = 0)
    (C : Set RealPlane)
    (hsum : latticeHull S = lineInterval 0 (latticeEmbedding p) 0
      (((lowerLatticeFace S ν m).card - 1 : ℕ) : ℝ) + C)
    (hambiguous : ∀ n : ℤ, 2 ≤ extensionCount c S (S \ lowerLatticeFace S ν m) Finset.sdiff_subset
      (legalTranslatedPattern c x hlang (S \ lowerLatticeFace S ν m) (n • p))) :
    ∃ q : ℕ, 0 < q ∧ q ≤ (lowerLatticeFace S ν m).card - 1 ∧
      RegionalPeriod x (bilateralTranslateStrip (S \ lowerLatticeFace S ν m) p) ((q : ℤ) • p) := by
  have hnonempty : (lowerLatticeFace S ν m).Nonempty := Finset.card_pos.mp (by omega)
  exact strip_period_of_segment_summand_and_ambiguous_edge c x hc hlang S hgen.2.1 p
    ((lowerLatticeFace S ν m).card - 1) (by omega) C hsum ν m hp
    (hgen.2.2.2.2 ν hν m hmin hnonempty) hambiguous

end KumarNivat
