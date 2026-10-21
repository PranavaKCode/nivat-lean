module

public import KumarNivat.TranslatedBandExtension
public import KumarNivat.RegionalBackground
public import Mathlib.Data.Nat.Factorial.Basic

@[expose] public section

namespace KumarNivat

-- row extension can change the period, while its positive length stays bounded on every outward band.
theorem outward_bands_have_bounded_periods {A : Type*} (c x : Site → A)
    (hc : (Set.range c).Finite) (hx : LanguageContained x c)
    (R S : Finset Site) (hgen : GeneratingPolygon c R S) (p : Site)
    (hprimitive : Int.gcd p.1 p.2 = 1) (m M : ℤ)
    (hbounds : ∀ u ∈ S, m ≤ directionNormal p u ∧ directionNormal p u ≤ M)
    (hlower : 2 ≤ (lowerLatticeFace S (directionNormal p) m).card)
    (hshorter : (lowerLatticeFace S (directionNormal p) m).card ≤
      (lowerLatticeFace S (-directionNormal p) (-M)).card)
    (β : ℤ) (s : ℕ) (hs : 0 < s)
    (hsbound : s ≤ 2 * ((lowerLatticeFace S (directionNormal p) m).card - 1))
    (hperiod : RegionalPeriod x (normalBand (directionNormal p) (β + 1) (β + (M - m))) ((s : ℤ) • p)) :
    ∀ n : ℕ, ∃ q : ℕ, 0 < q ∧ q ≤ 2 * ((lowerLatticeFace S (directionNormal p) m).card - 1) ∧
      RegionalPeriod x (normalBand (directionNormal p) (β - (n : ℤ) + 1)
        (β - (n : ℤ) + (M - m))) ((q : ℤ) • p) := by
  intro n
  induction n with
  | zero =>
    exact ⟨s, hs, hsbound, by simpa only [Nat.cast_zero, sub_zero] using hperiod⟩
  | succ n ih =>
    obtain ⟨q, hq, hqr, hband⟩ := ih
    obtain ⟨q', hq', hqr', hnew⟩ := bounded_band_extension_at_level c x hc hx R S hgen
      p hprimitive m M hbounds hlower hshorter (β - (n : ℤ)) q hq hqr hband
    refine ⟨q', hq', hqr', ?_⟩
    intro g hg hfit
    have hg' : g ∈ normalBand (directionNormal p) (β - (n : ℤ)) (β - (n : ℤ) + (M - m)) := by
      have hlo := hg.1
      have hhi := hg.2
      simp only [Nat.cast_add, Nat.cast_one] at hlo hhi
      exact ⟨by omega, by omega⟩
    have hfit' : g + (q' : ℤ) • p ∈ normalBand (directionNormal p)
        (β - (n : ℤ)) (β - (n : ℤ) + (M - m)) := by
      have hlo := hfit.1
      have hhi := hfit.2
      simp only [Nat.cast_add, Nat.cast_one] at hlo hhi
      exact ⟨by omega, by omega⟩
    exact hnew g hg' hfit'

-- the factorial of the uniform bound is one positive period on the complete outward half-plane.
theorem outward_halfplane_period {A : Type*} (c x : Site → A)
    (hc : (Set.range c).Finite) (hx : LanguageContained x c)
    (R S : Finset Site) (hgen : GeneratingPolygon c R S) (p : Site)
    (hprimitive : Int.gcd p.1 p.2 = 1) (m M : ℤ)
    (hbounds : ∀ u ∈ S, m ≤ directionNormal p u ∧ directionNormal p u ≤ M)
    (hlower : 2 ≤ (lowerLatticeFace S (directionNormal p) m).card)
    (hshorter : (lowerLatticeFace S (directionNormal p) m).card ≤
      (lowerLatticeFace S (-directionNormal p) (-M)).card)
    (β : ℤ) (s : ℕ) (hs : 0 < s)
    (hsbound : s ≤ 2 * ((lowerLatticeFace S (directionNormal p) m).card - 1))
    (hperiod : RegionalPeriod x (normalBand (directionNormal p) (β + 1) (β + (M - m))) ((s : ℤ) • p)) :
    RegionalPeriod x {g | directionNormal p g ≤ β + (M - m)}
      (((2 * ((lowerLatticeFace S (directionNormal p) m).card - 1)).factorial : ℤ) • p) := by
  have hpne : p ≠ 0 := by rintro rfl; simp at hprimitive
  have hν := directionNormal_ne_zero p hpne
  have hp : directionNormal p p = 0 := by simp [directionNormal, determinant, mul_comm]
  have hwidth : m < M := by
    by_contra hnot
    apply hgen.2.2.1.normal_not_constant (directionNormal p) hν m
    intro u hu
    have hb := hbounds u hu
    omega
  have hbands := outward_bands_have_bounded_periods c x hc hx R S hgen p hprimitive m M
    hbounds hlower hshorter β s hs hsbound hperiod
  intro g hg _hfit
  let n := (β + 1 - directionNormal p g).toNat
  have hgn : g ∈ normalBand (directionNormal p) (β - (n : ℤ) + 1)
      (β - (n : ℤ) + (M - m)) := by
    change directionNormal p g ≤ β + (M - m) at hg
    change β - (n : ℤ) + 1 ≤ directionNormal p g ∧
      directionNormal p g ≤ β - (n : ℤ) + (M - m)
    dsimp [n]
    omega
  obtain ⟨q, hq, hqr, hband⟩ := hbands n
  obtain ⟨a, ha⟩ := Nat.dvd_factorial hq hqr
  have hstable : ∀ z ∈ normalBand (directionNormal p) (β - (n : ℤ) + 1)
      (β - (n : ℤ) + (M - m)), z + (q : ℤ) • p ∈
        normalBand (directionNormal p) (β - (n : ℤ) + 1) (β - (n : ℤ) + (M - m)) := by
    intro z hz
    change β - (n : ℤ) + 1 ≤ directionNormal p (z + (q : ℤ) • p) ∧
      directionNormal p (z + (q : ℤ) • p) ≤ β - (n : ℤ) + (M - m)
    rw [map_add, map_zsmul, hp, smul_zero, add_zero]
    exact hz
  have he := (regional_period_forward_multiples x _ ((q : ℤ) • p) hstable hband a g hgn).2
  have hsite : (a : ℤ) • ((q : ℤ) • p) =
      (((2 * ((lowerLatticeFace S (directionNormal p) m).card - 1)).factorial : ℤ) • p) := by
    rw [ha, Nat.cast_mul, smul_smul, mul_comm]
  simpa only [hsite] using he

end KumarNivat
