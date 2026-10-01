import KumarNivat.ReflectionPeriods
import KumarNivat.SecondRegionalPeriod

namespace KumarNivat

-- reflection proves the same second-period construction for the opposite orientation of the actual recession rays.
theorem second_regional_period_negative_orientation {A I : Type*} (c x : Site → A)
    (hc : (Set.range c).Finite) (hx : LanguageContained x c)
    (R S : Finset Site) (hgen : GeneratingPolygon c R S) (a b : Site)
    (hprimitiveA : Int.gcd a.1 a.2 = 1) (hprimitiveB : Int.gcd b.1 b.2 = 1)
    (hdet : determinant a b < 0) (m M cut : ℤ)
    (hbounds : ∀ u ∈ S, m ≤ (-directionNormal a) u ∧ (-directionNormal a) u ≤ M)
    (hlower : 2 ≤ (lowerLatticeFace S (-directionNormal a) m).card)
    (hupper : 2 ≤ (lowerLatticeFace S (directionNormal a) (-M)).card)
    (J : Finset I) (μ : I → Site →+ ℤ) (z : I → ℤ)
    (hμa : ∀ i ∈ J, 0 < μ i a) (hμb : ∀ i ∈ J, 0 ≤ μ i b)
    (p : ℕ) (hp : 0 < p)
    (hperiod : RegionalPeriod x {g | latticeEmbedding g ∈ inwardLayerRegion (-directionNormal a) cut J μ z} ((p : ℤ) • a))
    (η : Site →+ ℤ) (hη : η ≠ 0) (mB : ℤ) (hminB : ∀ u ∈ S, mB ≤ η u)
    (hηa : 0 < η a) (hηb : η b = 0) (hfaceB : 2 ≤ (lowerLatticeFace S η mB).card)
    (E₀ : Site) (N : ℤ)
    (hamb : ∀ n : ℤ, N ≤ n → 2 ≤ extensionCount c S (S \ lowerLatticeFace S η mB) Finset.sdiff_subset
      (legalTranslatedPattern c x hx (S \ lowerLatticeFace S η mB) (E₀ + n • b)))
    (hplace : ∀ n : ℤ, N ≤ n → ∀ u ∈ S \ lowerLatticeFace S η mB,
      latticeEmbedding (E₀ + n • b + u) ∈ inwardLayerRegion (-directionNormal a) cut J μ z) :
    ∃ T : ℤ, ∃ q : ℕ, cut ≤ T ∧ 0 < q ∧
      RegionalPeriod x {g | latticeEmbedding g ∈ inwardLayerRegion (-directionNormal a) T J μ z} ((p : ℤ) • a) ∧
      RegionalPeriod x {g | latticeEmbedding g ∈ inwardLayerRegion (-directionNormal a) T J μ z} ((q : ℤ) • b) := by
  let ν := -directionNormal a
  let ca := reflectedConfig c
  let xa := reflectedConfig x
  let Sa := reflectedWindow S
  let μa := fun i => reflectedNormal (μ i)
  have hnormal : directionNormal (siteReflection a) = reflectedNormal ν := directionNormal_siteReflection a
  have hdet' : 0 < determinant (siteReflection a) (siteReflection b) := by
    rw [determinant_siteReflection]
    omega
  have hSa : ∀ u ∈ Sa, m ≤ directionNormal (siteReflection a) u ∧ directionNormal (siteReflection a) u ≤ M := by
    intro u hu
    rw [hnormal]
    exact hbounds (siteReflection u) ((mem_reflectedWindow S u).mp hu)
  have hlow : 2 ≤ (lowerLatticeFace Sa (directionNormal (siteReflection a)) m).card := by
    rw [hnormal, lowerLatticeFace_reflection, reflectedWindow_card]
    exact hlower
  have hhigh : 2 ≤ (lowerLatticeFace Sa (-directionNormal (siteReflection a)) (-M)).card := by
    rw [hnormal, ← reflectedNormal_neg, lowerLatticeFace_reflection, reflectedWindow_card]
    simpa only [ν, neg_neg] using hupper
  have hperiod' : RegionalPeriod xa {g | latticeEmbedding g ∈ inwardLayerRegion
      (directionNormal (siteReflection a)) cut J μa z} ((p : ℤ) • siteReflection a) := by
    rw [hnormal]
    simpa only [map_zsmul] using regional_period_inward_reflection x ν cut J μ z ((p : ℤ) • a) hperiod
  have hmin' : ∀ u ∈ Sa, mB ≤ reflectedNormal η u :=
    fun u hu => hminB (siteReflection u) ((mem_reflectedWindow S u).mp hu)
  have hface' : 2 ≤ (lowerLatticeFace Sa (reflectedNormal η) mB).card := by
    rw [lowerLatticeFace_reflection, reflectedWindow_card]
    exact hfaceB
  have hoff : reflectedWindow (S \ lowerLatticeFace S η mB) = Sa \ lowerLatticeFace Sa (reflectedNormal η) mB := by
    rw [reflectedWindow_sdiff, lowerLatticeFace_reflection]
  have hamb' : ∀ n : ℤ, N ≤ n → 2 ≤ extensionCount ca Sa (Sa \ lowerLatticeFace Sa (reflectedNormal η) mB)
      Finset.sdiff_subset (legalTranslatedPattern ca xa hx.reflection
        (Sa \ lowerLatticeFace Sa (reflectedNormal η) mB) (siteReflection E₀ + n • siteReflection b)) := by
    intro n hn
    have hh := hamb n hn
    rw [← extensionCount_reflection c S (S \ lowerLatticeFace S η mB) Finset.sdiff_subset
      (reflectedWindow_subset Finset.sdiff_subset) (legalTranslatedPattern c x hx _ (E₀ + n • b)),
      legalTranslatedPattern_reflection, map_add, map_zsmul] at hh
    rw [observed_extension_count_base_congr (reflectedConfig c) (reflectedConfig x) hx.reflection
      (reflectedWindow S) (reflectedWindow (S \ lowerLatticeFace S η mB))
      (Sa \ lowerLatticeFace Sa (reflectedNormal η) mB) (reflectedWindow_subset Finset.sdiff_subset)
      Finset.sdiff_subset hoff (siteReflection E₀ + n • siteReflection b)] at hh
    exact hh
  have hplace' : ∀ n : ℤ, N ≤ n → ∀ u ∈ Sa \ lowerLatticeFace Sa (reflectedNormal η) mB,
      latticeEmbedding (siteReflection E₀ + n • siteReflection b + u) ∈
        inwardLayerRegion (directionNormal (siteReflection a)) cut J μa z := by
    intro n hn u hu
    rw [← hoff] at hu
    have hm := hplace n hn (siteReflection u) ((mem_reflectedWindow _ u).mp hu)
    have hh := (mem_inwardLayerRegion_reflected_site ν cut J μ z (E₀ + n • b + siteReflection u)).mpr hm
    rw [map_add, map_add, map_zsmul, siteReflection_twice, ← hnormal] at hh
    exact hh
  obtain ⟨T, q, hT, hq, hpA, hpB⟩ := second_regional_period_from_ambiguous_edge ca xa
    (by rw [reflectedConfig_range]; exact hc) hx.reflection (reflectedWindow R) Sa hgen.reflection
    (siteReflection a) (siteReflection b) (primitive_siteReflection a hprimitiveA)
    (primitive_siteReflection b hprimitiveB) hdet' m M cut hSa hlow hhigh J μa z
    (fun i hi => by change 0 < reflectedNormal (μ i) (siteReflection a); rw [reflectedNormal_reflected_site]; exact hμa i hi)
    (fun i hi => by change 0 ≤ reflectedNormal (μ i) (siteReflection b); rw [reflectedNormal_reflected_site]; exact hμb i hi) p hp hperiod'
    (reflectedNormal η) (reflectedNormal_ne_zero η hη) mB hmin'
    (by simpa only [reflectedNormal_reflected_site] using hηa)
    (by simpa only [reflectedNormal_reflected_site] using hηb) hface'
    (siteReflection E₀) N hamb' hplace'
  rw [hnormal] at hpA hpB
  refine ⟨T, q, hT, hq, ?_, ?_⟩
  · apply regional_period_of_inward_reflection x ν T J μ z ((p : ℤ) • a)
    simpa only [map_zsmul] using hpA
  · apply regional_period_of_inward_reflection x ν T J μ z ((q : ℤ) • b)
    simpa only [map_zsmul] using hpB

end KumarNivat
