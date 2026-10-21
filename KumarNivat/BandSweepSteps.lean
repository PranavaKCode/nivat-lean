module

public import KumarNivat.GeneratedRegionalRows

@[expose] public section

namespace KumarNivat

-- the lower edge fits its nonface inputs in the next known band, so far seeds determine the whole next lower row.
theorem lower_regional_row_sweep_step {A I : Type*} (c x y : Site → A)
    (hx : LanguageContained x c) (hy : LanguageContained y c)
    (R S : Finset Site) (hgen : GeneratingPolygon c R S) (a : Site)
    (hprimitive : Int.gcd a.1 a.2 = 1) (m M cut : ℤ)
    (hbounds : ∀ u ∈ S, m ≤ directionNormal a u ∧ directionNormal a u ≤ M)
    (J : Finset I) (μ : I → Site →+ ℤ) (z : I → ℤ) (hμa : ∀ i ∈ J, 0 < μ i a)
    (p : ℕ) (hp : 0 < p)
    (hxper : RegionalPeriod x {g | latticeEmbedding g ∈ inwardLayerRegion (directionNormal a) cut J μ z} ((p : ℤ) • a))
    (hyper : RegionalPeriod y {g | latticeEmbedding g ∈ inwardLayerRegion (directionNormal a) cut J μ z} ((p : ℤ) • a))
    (r : ℕ) (hcard : (lowerLatticeFace S (directionNormal a) m).card = r + 1)
    (j : ℤ) (hcut : cut ≤ j)
    (hband : ∀ g : Site, latticeEmbedding g ∈ inwardLayerRegion (directionNormal a) cut J μ z →
      j + 1 ≤ directionNormal a g → directionNormal a g ≤ j + (M - m) → x g = y g)
    (F : Site) (hF : directionNormal a F = j)
    (hseeds : ∀ N : ℤ, ∃ n : ℤ, N ≤ n ∧ ∀ i : Fin r,
      x (F + (n + (i.val : ℤ)) • a) = y (F + (n + (i.val : ℤ)) • a)) :
    ∀ g : Site, latticeEmbedding g ∈ inwardLayerRegion (directionNormal a) cut J μ z →
      directionNormal a g = j → x g = y g := by
  have hane : a ≠ 0 := by rintro rfl; simp at hprimitive
  have hν := directionNormal_ne_zero a hane
  have ha : directionNormal a a = 0 := by simp [directionNormal, determinant, mul_comm]
  apply generated_regional_row_from_far_seeds c x y hx hy R S hgen a hprimitive cut J μ z hμa
    p hp hxper hyper (directionNormal a) hν m m ha (fun u hu => (hbounds u hu).1) r hcard
      (fun u hu => (Finset.mem_filter.mp hu).2) j _ _ F hF hseeds
  · intro u hu
    have hb := hbounds u hu
    omega
  · intro u hu g hg hlevel
    obtain ⟨hus, huf⟩ := Finset.mem_sdiff.mp hu
    have hne : directionNormal a u ≠ m := by
      intro he
      exact huf (Finset.mem_filter.mpr ⟨hus, he⟩)
    have hb := hbounds u hus
    exact hband g hg (by omega) (by omega)

-- the upper edge instead fits its nonface inputs below the new row, giving the upward version of the same sweep.
theorem upper_regional_row_sweep_step {A I : Type*} (c x y : Site → A)
    (hx : LanguageContained x c) (hy : LanguageContained y c)
    (R S : Finset Site) (hgen : GeneratingPolygon c R S) (a : Site)
    (hprimitive : Int.gcd a.1 a.2 = 1) (m M cut : ℤ)
    (hbounds : ∀ u ∈ S, m ≤ directionNormal a u ∧ directionNormal a u ≤ M)
    (J : Finset I) (μ : I → Site →+ ℤ) (z : I → ℤ) (hμa : ∀ i ∈ J, 0 < μ i a)
    (p : ℕ) (hp : 0 < p)
    (hxper : RegionalPeriod x {g | latticeEmbedding g ∈ inwardLayerRegion (directionNormal a) cut J μ z} ((p : ℤ) • a))
    (hyper : RegionalPeriod y {g | latticeEmbedding g ∈ inwardLayerRegion (directionNormal a) cut J μ z} ((p : ℤ) • a))
    (r : ℕ) (hcard : (lowerLatticeFace S (-directionNormal a) (-M)).card = r + 1)
    (j : ℤ) (hcut : cut ≤ j - (M - m))
    (hband : ∀ g : Site, latticeEmbedding g ∈ inwardLayerRegion (directionNormal a) cut J μ z →
      j - (M - m) ≤ directionNormal a g → directionNormal a g ≤ j - 1 → x g = y g)
    (F : Site) (hF : directionNormal a F = j)
    (hseeds : ∀ N : ℤ, ∃ n : ℤ, N ≤ n ∧ ∀ i : Fin r,
      x (F + (n + (i.val : ℤ)) • a) = y (F + (n + (i.val : ℤ)) • a)) :
    ∀ g : Site, latticeEmbedding g ∈ inwardLayerRegion (directionNormal a) cut J μ z →
      directionNormal a g = j → x g = y g := by
  have hane : a ≠ 0 := by rintro rfl; simp at hprimitive
  have hν := directionNormal_ne_zero a hane
  have ha : (-directionNormal a) a = 0 := by
    change -directionNormal a a = 0
    simp [directionNormal, determinant, mul_comm]
  have hmin : ∀ u ∈ S, -M ≤ (-directionNormal a) u := by
    intro u hu
    change -M ≤ -directionNormal a u
    have hb := hbounds u hu
    omega
  have hfacelevel : ∀ u ∈ lowerLatticeFace S (-directionNormal a) (-M), directionNormal a u = M := by
    intro u hu
    have he := (Finset.mem_filter.mp hu).2
    change -directionNormal a u = -M at he
    exact neg_inj.mp he
  apply generated_regional_row_from_far_seeds c x y hx hy R S hgen a hprimitive cut J μ z hμa
    p hp hxper hyper (-directionNormal a) (neg_ne_zero.mpr hν) (-M) M ha hmin r hcard hfacelevel j _ _ F hF hseeds
  · intro u hu
    have hb := hbounds u hu
    omega
  · intro u hu g hg hlevel
    obtain ⟨hus, huf⟩ := Finset.mem_sdiff.mp hu
    have hne : directionNormal a u ≠ M := by
      intro he
      apply huf
      refine Finset.mem_filter.mpr ⟨hus, ?_⟩
      change -directionNormal a u = -M
      rw [he]
    have hb := hbounds u hus
    exact hband g hg (by omega) (by omega)

end KumarNivat
