import KumarNivat.PolygonNormalBands
import KumarNivat.SegmentSummandGeometry

namespace KumarNivat

open scoped Pointwise

-- the actual min/max faces turn the sampled strip period into a period on the entire normal band.
theorem band_period_of_generating_polygon_summand {A : Type*}
    (c x : Site → A) (hc : (Set.range c).Finite) (hlang : LanguageContained x c)
    (R S : Finset Site) (hgen : GeneratingPolygon c R S) (p : Site)
    (hprimitive : Int.gcd p.1 p.2 = 1) (m M : ℤ)
    (hbounds : ∀ u ∈ S, m ≤ directionNormal p u ∧ directionNormal p u ≤ M)
    (hlower : 2 ≤ (lowerLatticeFace S (directionNormal p) m).card)
    (hupper : (lowerLatticeFace S (-directionNormal p) (-M)).Nonempty)
    (C : Set RealPlane)
    (hsum : latticeHull S = lineInterval 0 (latticeEmbedding p) 0
      (((lowerLatticeFace S (directionNormal p) m).card - 1 : ℕ) : ℝ) + C)
    (hambiguous : ∀ n : ℤ, 2 ≤ extensionCount c S (S \ lowerLatticeFace S (directionNormal p) m) Finset.sdiff_subset
      (legalTranslatedPattern c x hlang (S \ lowerLatticeFace S (directionNormal p) m) (n • p))) :
    ∃ q : ℕ, 0 < q ∧ q ≤ (lowerLatticeFace S (directionNormal p) m).card - 1 ∧
      RegionalPeriod x (normalBand (directionNormal p) (m + 1) M) ((q : ℤ) • p) := by
  have hpne : p ≠ 0 := by rintro rfl; simp at hprimitive
  have hp : directionNormal p p = 0 := by simp [directionNormal, determinant, mul_comm]
  have hlowerne : (lowerLatticeFace S (directionNormal p) m).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨u₀, hu₀⟩ := hlowerne
  obtain ⟨u₁, hu₁⟩ := hupper
  have hu₁level : directionNormal p u₁ = M := by
    have he := (Finset.mem_filter.mp hu₁).2
    change -directionNormal p u₁ = -M at he
    exact neg_inj.mp he
  obtain ⟨q, hq, hqr, hperiod⟩ := strip_period_of_generating_polygon_summand c x hc hlang R S hgen
    (directionNormal p) (directionNormal_ne_zero p hpne) m (fun u hu => (hbounds u hu).1)
    hlower p hp C hsum hambiguous
  have heq := off_face_bilateralTranslateStrip_eq_normalBand S hgen.2.1 p hprimitive
    ((lowerLatticeFace S (directionNormal p) m).card - 1) (by omega) C hsum m M u₀ u₁
    (Finset.mem_filter.mp hu₀).1 (Finset.mem_filter.mp hu₁).1
    (Finset.mem_filter.mp hu₀).2 hu₁level hbounds
  rw [heq] at hperiod
  exact ⟨q, hq, hqr, hperiod⟩

-- the shorter opposite edge supplies its segment summand and period without extra row-run premises.
theorem band_period_of_shorter_opposite_generating_edges {A : Type*}
    (c x : Site → A) (hc : (Set.range c).Finite) (hlang : LanguageContained x c)
    (R S : Finset Site) (hgen : GeneratingPolygon c R S) (p : Site)
    (hprimitive : Int.gcd p.1 p.2 = 1) (m M : ℤ)
    (hbounds : ∀ u ∈ S, m ≤ directionNormal p u ∧ directionNormal p u ≤ M)
    (hlower : 2 ≤ (lowerLatticeFace S (directionNormal p) m).card)
    (hshorter : (lowerLatticeFace S (directionNormal p) m).card ≤
      (lowerLatticeFace S (-directionNormal p) (-M)).card)
    (hambiguous : ∀ n : ℤ, 2 ≤ extensionCount c S (S \ lowerLatticeFace S (directionNormal p) m) Finset.sdiff_subset
      (legalTranslatedPattern c x hlang (S \ lowerLatticeFace S (directionNormal p) m) (n • p))) :
    ∃ q : ℕ, 0 < q ∧ q ≤ (lowerLatticeFace S (directionNormal p) m).card - 1 ∧
      RegionalPeriod x (normalBand (directionNormal p) (m + 1) M) ((q : ℤ) • p) := by
  let r := (lowerLatticeFace S (directionNormal p) m).card - 1
  have hr : r + 1 = (lowerLatticeFace S (directionNormal p) m).card := by dsimp [r]; omega
  obtain ⟨C, _hC, hsum⟩ := segment_summand_of_opposite_face_cardinalities S hgen.2.1 p hprimitive
    m M hbounds r (by rw [hr]) (by rw [hr]; exact hshorter)
  have hupper : (lowerLatticeFace S (-directionNormal p) (-M)).Nonempty := Finset.card_pos.mp (by omega)
  exact band_period_of_generating_polygon_summand c x hc hlang R S hgen p hprimitive m M hbounds
    hlower hupper C hsum hambiguous

end KumarNivat
