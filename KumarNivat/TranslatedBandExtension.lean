module

public import KumarNivat.BoundedBandExtension

@[expose] public section

namespace KumarNivat

-- translating by the unimodular transverse vector places the same row-extension argument at any integer level.
theorem bounded_band_extension_at_level {A : Type*} (c x : Site → A)
    (hc : (Set.range c).Finite) (hx : LanguageContained x c)
    (R S : Finset Site) (hgen : GeneratingPolygon c R S) (p : Site)
    (hprimitive : Int.gcd p.1 p.2 = 1) (m M : ℤ)
    (hbounds : ∀ u ∈ S, m ≤ directionNormal p u ∧ directionNormal p u ≤ M)
    (hlower : 2 ≤ (lowerLatticeFace S (directionNormal p) m).card)
    (hshorter : (lowerLatticeFace S (directionNormal p) m).card ≤
      (lowerLatticeFace S (-directionNormal p) (-M)).card)
    (b : ℤ) (s : ℕ) (hs : 0 < s)
    (hsbound : s ≤ 2 * ((lowerLatticeFace S (directionNormal p) m).card - 1))
    (hperiod : RegionalPeriod x (normalBand (directionNormal p) (b + 1) (b + (M - m))) ((s : ℤ) • p)) :
    ∃ q : ℕ, 0 < q ∧ q ≤ 2 * ((lowerLatticeFace S (directionNormal p) m).card - 1) ∧
      RegionalPeriod x (normalBand (directionNormal p) b (b + (M - m))) ((q : ℤ) • p) := by
  obtain ⟨τ, hτ, _hker⟩ := primitive_direction_coordinate p hprimitive
  obtain ⟨v, hpv⟩ := primitive_basis_of_line_coordinate p τ hτ
  have hv : directionNormal p v = 1 := hpv
  let E := (b - m) • v
  have hE : directionNormal p E = b - m := by
    dsimp [E]
    rw [map_zsmul, hv, smul_eq_mul, mul_one]
  have hinner : {g : Site | g + E ∈ normalBand (directionNormal p) (b + 1) (b + (M - m))} =
      normalBand (directionNormal p) (m + 1) M := by
    ext g
    change (b + 1 ≤ directionNormal p (g + E) ∧ directionNormal p (g + E) ≤ b + (M - m)) ↔
      (m + 1 ≤ directionNormal p g ∧ directionNormal p g ≤ M)
    rw [map_add, hE]
    omega
  have hshift := regional_period_shift x (normalBand (directionNormal p) (b + 1) (b + (M - m)))
    E ((s : ℤ) • p) hperiod
  rw [hinner] at hshift
  obtain ⟨q, hq, hqr, hnew⟩ := bounded_band_extension c (shift E x) hc (hx.shift E) R S hgen
    p hprimitive m M hbounds hlower hshorter s hs hsbound hshift
  have houter : {g : Site | g - E ∈ normalBand (directionNormal p) m M} =
      normalBand (directionNormal p) b (b + (M - m)) := by
    ext g
    change (m ≤ directionNormal p (g - E) ∧ directionNormal p (g - E) ≤ M) ↔
      (b ≤ directionNormal p g ∧ directionNormal p g ≤ b + (M - m))
    rw [map_sub, hE]
    omega
  refine ⟨q, hq, hqr, ?_⟩
  have hback := regional_period_of_shifted_region x (normalBand (directionNormal p) m M) E ((q : ℤ) • p) hnew
  rwa [houter] at hback

end KumarNivat
