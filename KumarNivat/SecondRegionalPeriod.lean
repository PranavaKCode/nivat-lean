import KumarNivat.SecondPeriodFromHalfStrip
import KumarNivat.LocalHalfStripPeriods
import KumarNivat.HighHalfStripRows

namespace KumarNivat

-- the actual generating edges and placed ambiguous bases supply the second regional period without a seed or row-run premise.
theorem second_regional_period_from_ambiguous_edge {A I : Type*} (c x : Site → A)
    (hc : (Set.range c).Finite) (hx : LanguageContained x c)
    (R S : Finset Site) (hgen : GeneratingPolygon c R S) (a b : Site)
    (hprimitiveA : Int.gcd a.1 a.2 = 1) (hprimitiveB : Int.gcd b.1 b.2 = 1)
    (hdet : 0 < determinant a b) (m M cut : ℤ)
    (hbounds : ∀ u ∈ S, m ≤ directionNormal a u ∧ directionNormal a u ≤ M)
    (hlower : 2 ≤ (lowerLatticeFace S (directionNormal a) m).card)
    (hupper : 2 ≤ (lowerLatticeFace S (-directionNormal a) (-M)).card)
    (J : Finset I) (μ : I → Site →+ ℤ) (z : I → ℤ)
    (hμa : ∀ i ∈ J, 0 < μ i a) (hμb : ∀ i ∈ J, 0 ≤ μ i b)
    (p : ℕ) (hp : 0 < p)
    (hperiod : RegionalPeriod x {g | latticeEmbedding g ∈ inwardLayerRegion (directionNormal a) cut J μ z} ((p : ℤ) • a))
    (η : Site →+ ℤ) (hη : η ≠ 0) (mB : ℤ) (hminB : ∀ u ∈ S, mB ≤ η u)
    (hηa : 0 < η a) (hηb : η b = 0) (hfaceB : 2 ≤ (lowerLatticeFace S η mB).card)
    (E₀ : Site) (N : ℤ)
    (hamb : ∀ n : ℤ, N ≤ n → 2 ≤ extensionCount c S (S \ lowerLatticeFace S η mB) Finset.sdiff_subset
      (legalTranslatedPattern c x hx (S \ lowerLatticeFace S η mB) (E₀ + n • b)))
    (hplace : ∀ n : ℤ, N ≤ n → ∀ u ∈ S \ lowerLatticeFace S η mB,
      latticeEmbedding (E₀ + n • b + u) ∈ inwardLayerRegion (directionNormal a) cut J μ z) :
    ∃ T : ℤ, ∃ q : ℕ, cut ≤ T ∧ 0 < q ∧
      RegionalPeriod x {g | latticeEmbedding g ∈ inwardLayerRegion (directionNormal a) T J μ z} ((p : ℤ) • a) ∧
      RegionalPeriod x {g | latticeEmbedding g ∈ inwardLayerRegion (directionNormal a) T J μ z} ((q : ℤ) • b) := by
  classical
  let L := (lowerLatticeFace S (directionNormal a) m).card
  let U := (lowerLatticeFace S (-directionNormal a) (-M)).card
  let r := min (L - 1) (U - 1)
  have hL : 2 ≤ L := hlower
  have hU : 2 ≤ U := hupper
  have hr : 0 < r := by dsimp [r]; omega
  have hLr : r + 1 ≤ L := by dsimp [r]; omega
  have hUr : r + 1 ≤ U := by dsimp [r]; omega
  have hshort : L = r + 1 ∨ U = r + 1 := by
    by_cases horder : L ≤ U
    · left
      dsimp [r]
      rw [Nat.min_eq_left (by omega)]
      omega
    · right
      dsimp [r]
      rw [Nat.min_eq_right (by omega)]
      omega
  obtain ⟨q₀, t, hq₀, _hq₀mem, _hq₁mem, ht, hcard, hsub, _hsites, _E, _hmem, _hcover, _hfit⟩ :=
    exists_generating_local_parallelogram_data c R S hgen a hprimitiveA m M hbounds r hr hLr hUr
      b hprimitiveB η hη mB hminB hηb hηa hfaceB
  obtain ⟨E, _hmem, hcover, k, l, _hk, hl, _hlt, hperiodH, hHR⟩ :=
    local_parallelogram_half_strip_period c x hc hx R S hgen q₀ a b r t ht hsub η hη mB hminB hηb
      hcard E₀ N hamb (inwardLayerRegion (directionNormal a) cut J μ z) hplace
  let H : Set Site := {g | g - E₀ ∈ sampledHalfStrip E b (N + (k : ℤ))}
  have hHstable : ∀ g ∈ H, g + (l : ℤ) • b ∈ H := by
    intro g hg
    have he := sampled_half_strip_forward_nat_step E b (N + (k : ℤ)) l (g - E₀) hg
    change g + (l : ℤ) • b - E₀ ∈ sampledHalfStrip E b (N + (k : ℤ))
    simpa only [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using he
  obtain ⟨j₁, hhigh⟩ := sampled_half_strip_has_high_consecutive_rows S hgen.2.1 q₀ a b hprimitiveA r t ht
    hdet hsub η mB hq₀ hηa hηb E hcover (N + (k : ℤ))
  let j₀ := max cut (directionNormal a E₀ + j₁)
  have hhighH : ∀ j : ℤ, j₀ ≤ j → ∃ F : Site, directionNormal a F = j ∧
      ∀ i : Fin r, F + (i.val : ℤ) • a ∈ H := by
    intro j hj
    have hj₁ : j₁ ≤ j - directionNormal a E₀ := by dsimp [j₀] at hj; omega
    obtain ⟨F, hF, hrun⟩ := hhigh (j - directionNormal a E₀) hj₁
    refine ⟨E₀ + F, ?_, ?_⟩
    · rw [map_add, hF]
      omega
    · intro i
      change E₀ + F + (i.val : ℤ) • a - E₀ ∈ sampledHalfStrip E b (N + (k : ℤ))
      have hsite : E₀ + F + (i.val : ℤ) • a - E₀ = F + (i.val : ℤ) • a := by abel
      rw [hsite]
      exact hrun i
  exact second_period_from_high_seed_half_strip c x hc hx R S hgen a b hprimitiveA hdet m M cut hbounds
    J μ z hμa hμb p hp hperiod r hshort H l hl hHR hHstable hperiodH j₀ (le_max_left _ _) hhighH

end KumarNivat
