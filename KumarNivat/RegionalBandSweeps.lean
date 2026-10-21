module

public import KumarNivat.BandSweepSteps

@[expose] public section

namespace KumarNivat

-- a two-dimensional generating polygon has positive width in every nonzero integer normal.
theorem NoncollinearSites.normal_width_pos {S : Finset Site} (hS : NoncollinearSites S)
    (ν : Site →+ ℤ) (hν : ν ≠ 0) (m M : ℤ) (hbounds : ∀ u ∈ S, m ≤ ν u ∧ ν u ≤ M) : m < M := by
  by_contra hnot
  apply hS.normal_not_constant ν hν m
  intro u hu
  have hb := hbounds u hu
  omega

-- successive generated lower rows extend one repeated band down to the fixed seed threshold.
theorem downward_regional_band_sweep {A I : Type*} (c x y : Site → A)
    (hx : LanguageContained x c) (hy : LanguageContained y c)
    (R S : Finset Site) (hgen : GeneratingPolygon c R S) (a : Site)
    (hprimitive : Int.gcd a.1 a.2 = 1) (m M cut : ℤ)
    (hbounds : ∀ u ∈ S, m ≤ directionNormal a u ∧ directionNormal a u ≤ M)
    (J : Finset I) (μ : I → Site →+ ℤ) (z : I → ℤ) (hμa : ∀ i ∈ J, 0 < μ i a)
    (p : ℕ) (hp : 0 < p)
    (hxper : RegionalPeriod x {g | latticeEmbedding g ∈ inwardLayerRegion (directionNormal a) cut J μ z} ((p : ℤ) • a))
    (hyper : RegionalPeriod y {g | latticeEmbedding g ∈ inwardLayerRegion (directionNormal a) cut J μ z} ((p : ℤ) • a))
    (r : ℕ) (hcard : (lowerLatticeFace S (directionNormal a) m).card = r + 1)
    (j₀ B : ℤ) (hcut : cut ≤ j₀) (hB : j₀ ≤ B)
    (hseeds : ∀ j : ℤ, j₀ ≤ j → ∃ F : Site, directionNormal a F = j ∧
      ∀ N : ℤ, ∃ n : ℤ, N ≤ n ∧ ∀ i : Fin r,
        x (F + (n + (i.val : ℤ)) • a) = y (F + (n + (i.val : ℤ)) • a))
    (hband : ∀ g : Site, latticeEmbedding g ∈ inwardLayerRegion (directionNormal a) cut J μ z →
      B ≤ directionNormal a g → directionNormal a g ≤ B + (M - m) → x g = y g) :
    ∀ g : Site, latticeEmbedding g ∈ inwardLayerRegion (directionNormal a) cut J μ z →
      j₀ ≤ directionNormal a g → directionNormal a g ≤ B + (M - m) → x g = y g := by
  have hdown (n : ℕ) : j₀ ≤ B - (n : ℤ) → ∀ g : Site,
      latticeEmbedding g ∈ inwardLayerRegion (directionNormal a) cut J μ z →
      B - (n : ℤ) ≤ directionNormal a g → directionNormal a g ≤ B + (M - m) → x g = y g := by
    induction n with
    | zero =>
      intro _hn g hg hlo hhi
      exact hband g hg (by simpa only [Nat.cast_zero, sub_zero] using hlo) hhi
    | succ n ih =>
      intro hn g hg hlo hhi
      have hprev : j₀ ≤ B - (n : ℤ) := by omega
      by_cases hglevel : B - (n : ℤ) ≤ directionNormal a g
      · exact ih hprev g hg hglevel hhi
      · let j := B - ((n + 1 : ℕ) : ℤ)
        have hj : j₀ ≤ j := hn
        obtain ⟨F, hF, hseed⟩ := hseeds j hj
        have hrow := lower_regional_row_sweep_step c x y hx hy R S hgen a hprimitive m M cut
          hbounds J μ z hμa p hp hxper hyper r hcard j (hcut.trans hj)
            (fun u hu hlow hhigh => ih hprev u hu (by dsimp [j] at hlow; omega) (by dsimp [j] at hhigh; omega))
              F hF hseed
        exact hrow g hg (by dsimp [j]; omega)
  intro g hg hlo hhi
  exact hdown (B - j₀).toNat (by omega) g hg (by omega) hhi

-- successive generated upper rows extend one repeated band to every higher regional row.
theorem upward_regional_band_sweep {A I : Type*} (c x y : Site → A)
    (hx : LanguageContained x c) (hy : LanguageContained y c)
    (R S : Finset Site) (hgen : GeneratingPolygon c R S) (a : Site)
    (hprimitive : Int.gcd a.1 a.2 = 1) (m M cut : ℤ)
    (hbounds : ∀ u ∈ S, m ≤ directionNormal a u ∧ directionNormal a u ≤ M)
    (J : Finset I) (μ : I → Site →+ ℤ) (z : I → ℤ) (hμa : ∀ i ∈ J, 0 < μ i a)
    (p : ℕ) (hp : 0 < p)
    (hxper : RegionalPeriod x {g | latticeEmbedding g ∈ inwardLayerRegion (directionNormal a) cut J μ z} ((p : ℤ) • a))
    (hyper : RegionalPeriod y {g | latticeEmbedding g ∈ inwardLayerRegion (directionNormal a) cut J μ z} ((p : ℤ) • a))
    (r : ℕ) (hcard : (lowerLatticeFace S (-directionNormal a) (-M)).card = r + 1)
    (j₀ B : ℤ) (hcut : cut ≤ j₀) (hB : j₀ ≤ B)
    (hseeds : ∀ j : ℤ, j₀ ≤ j → ∃ F : Site, directionNormal a F = j ∧
      ∀ N : ℤ, ∃ n : ℤ, N ≤ n ∧ ∀ i : Fin r,
        x (F + (n + (i.val : ℤ)) • a) = y (F + (n + (i.val : ℤ)) • a))
    (hband : ∀ g : Site, latticeEmbedding g ∈ inwardLayerRegion (directionNormal a) cut J μ z →
      B ≤ directionNormal a g → directionNormal a g ≤ B + (M - m) → x g = y g) :
    ∀ g : Site, latticeEmbedding g ∈ inwardLayerRegion (directionNormal a) cut J μ z →
      B ≤ directionNormal a g → x g = y g := by
  have hane : a ≠ 0 := by rintro rfl; simp at hprimitive
  have hwidth := hgen.2.2.1.normal_width_pos (directionNormal a) (directionNormal_ne_zero a hane) m M hbounds
  have hup (n : ℕ) : ∀ g : Site, latticeEmbedding g ∈ inwardLayerRegion (directionNormal a) cut J μ z →
      B ≤ directionNormal a g → directionNormal a g ≤ B + (M - m) + (n : ℤ) → x g = y g := by
    induction n with
    | zero =>
      intro g hg hlo hhi
      exact hband g hg hlo (by simpa only [Nat.cast_zero, add_zero] using hhi)
    | succ n ih =>
      intro g hg hlo hhi
      by_cases hglevel : directionNormal a g ≤ B + (M - m) + (n : ℤ)
      · exact ih g hg hlo hglevel
      · let j := B + (M - m) + ((n + 1 : ℕ) : ℤ)
        have hj : j₀ ≤ j := by dsimp [j]; omega
        obtain ⟨F, hF, hseed⟩ := hseeds j hj
        have hrow := upper_regional_row_sweep_step c x y hx hy R S hgen a hprimitive m M cut
          hbounds J μ z hμa p hp hxper hyper r hcard j (by dsimp [j]; omega)
            (fun u hu hlow hhigh => ih u hu (by dsimp [j] at hlow; omega) (by dsimp [j] at hhigh; omega))
              F hF hseed
        exact hrow g hg (by dsimp [j]; omega)
  intro g hg hlo
  exact hup (directionNormal a g - (B + (M - m))).toNat g hg hlo (by omega)

-- arbitrarily high bands for the same pair let the lower sweep cover every row above the fixed seed threshold.
theorem agreement_from_arbitrarily_high_regional_bands {A I : Type*} (c x y : Site → A)
    (hx : LanguageContained x c) (hy : LanguageContained y c)
    (R S : Finset Site) (hgen : GeneratingPolygon c R S) (a : Site)
    (hprimitive : Int.gcd a.1 a.2 = 1) (m M cut : ℤ)
    (hbounds : ∀ u ∈ S, m ≤ directionNormal a u ∧ directionNormal a u ≤ M)
    (J : Finset I) (μ : I → Site →+ ℤ) (z : I → ℤ) (hμa : ∀ i ∈ J, 0 < μ i a)
    (p : ℕ) (hp : 0 < p)
    (hxper : RegionalPeriod x {g | latticeEmbedding g ∈ inwardLayerRegion (directionNormal a) cut J μ z} ((p : ℤ) • a))
    (hyper : RegionalPeriod y {g | latticeEmbedding g ∈ inwardLayerRegion (directionNormal a) cut J μ z} ((p : ℤ) • a))
    (r : ℕ) (hcard : (lowerLatticeFace S (directionNormal a) m).card = r + 1)
    (j₀ : ℤ) (hcut : cut ≤ j₀)
    (hseeds : ∀ j : ℤ, j₀ ≤ j → ∃ F : Site, directionNormal a F = j ∧
      ∀ N : ℤ, ∃ n : ℤ, N ≤ n ∧ ∀ i : Fin r,
        x (F + (n + (i.val : ℤ)) • a) = y (F + (n + (i.val : ℤ)) • a))
    (hbands : ∀ L : ℤ, ∃ B : ℤ, L ≤ B ∧ ∀ g : Site,
      latticeEmbedding g ∈ inwardLayerRegion (directionNormal a) cut J μ z →
      B ≤ directionNormal a g → directionNormal a g ≤ B + (M - m) → x g = y g) :
    ∀ g : Site, latticeEmbedding g ∈ inwardLayerRegion (directionNormal a) cut J μ z →
      j₀ ≤ directionNormal a g → x g = y g := by
  have hane : a ≠ 0 := by rintro rfl; simp at hprimitive
  have hwidth := hgen.2.2.1.normal_width_pos (directionNormal a) (directionNormal_ne_zero a hane) m M hbounds
  intro g hg hlo
  obtain ⟨B, hB, hband⟩ := hbands (directionNormal a g)
  exact downward_regional_band_sweep c x y hx hy R S hgen a hprimitive m M cut hbounds J μ z hμa
    p hp hxper hyper r hcard j₀ B hcut (hlo.trans hB) hseeds hband g hg hlo (by omega)

end KumarNivat
