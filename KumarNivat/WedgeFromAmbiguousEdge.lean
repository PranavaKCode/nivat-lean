import KumarNivat.SecondRegionalPeriod
import KumarNivat.InwardWedgeBackground

namespace KumarNivat

-- the placed ambiguous edge gives a periodic background on an actual rational wedge of the same selected array.
theorem background_wedge_from_ambiguous_edge {A I : Type*} (c x : Site → A)
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
    Function.Injective ((directionNormal a).prod (-directionNormal b)) ∧
      ∃ E : Site, ∃ B : Site → A, FullyPeriodic B ∧
        AgreesOnWedge (directionNormal a) (-directionNormal b) (directionNormal a E) ((-directionNormal b) E) x B ∧
        Set.range B ⊆ Set.range x := by
  obtain ⟨T, q, _hT, hq, hperiodA, hperiodB⟩ := second_regional_period_from_ambiguous_edge c x hc hx R S hgen
    a b hprimitiveA hprimitiveB hdet m M cut hbounds hlower hupper J μ z hμa hμb p hp hperiod
      η hη mB hminB hηa hηb hfaceB E₀ N hamb hplace
  exact background_on_wedge_of_inward_ray_periods x a b hprimitiveA hdet T J μ z hμa hμb p q hp hq hperiodA hperiodB

end KumarNivat
