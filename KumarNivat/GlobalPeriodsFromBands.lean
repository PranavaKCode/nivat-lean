import KumarNivat.OutwardBandPeriods
import KumarNivat.TangentPeriods

namespace KumarNivat

-- the outward half-plane period globalizes using the actual inherited product annihilator.
theorem global_tangent_period_from_initial_band {K : Type*} [CommRing K]
    [Nontrivial K] [NoZeroDivisors K] (c x : Site → K)
    (hc : (Set.range c).Finite) (hx : LanguageContained x c)
    (hs : List Site) (hdirs : ∀ h ∈ hs, h ≠ 0)
    (hpairs : hs.Pairwise (fun a b => determinant a b ≠ 0))
    (hann : laurentAct (differenceProduct hs) c = 0)
    (R S : Finset Site) (hgen : GeneratingPolygon c R S) (p : Site)
    (hprimitive : Int.gcd p.1 p.2 = 1) (m M : ℤ)
    (hbounds : ∀ u ∈ S, m ≤ directionNormal p u ∧ directionNormal p u ≤ M)
    (hlower : 2 ≤ (lowerLatticeFace S (directionNormal p) m).card)
    (hshorter : (lowerLatticeFace S (directionNormal p) m).card ≤
      (lowerLatticeFace S (-directionNormal p) (-M)).card)
    (β : ℤ) (s : ℕ) (hspos : 0 < s)
    (hsbound : s ≤ 2 * ((lowerLatticeFace S (directionNormal p) m).card - 1))
    (hperiod : RegionalPeriod x (normalBand (directionNormal p) (β + 1) (β + (M - m))) ((s : ℤ) • p)) :
    ∃ l : ℕ, 0 < l ∧ IsPeriod x ((l : ℤ) • p) := by
  have hpne : p ≠ 0 := by rintro rfl; simp at hprimitive
  have hν := directionNormal_ne_zero p hpne
  have hp : directionNormal p p = 0 := by simp [directionNormal, determinant, mul_comm]
  let L := (2 * ((lowerLatticeFace S (directionNormal p) m).card - 1)).factorial
  have hL : 0 < L := Nat.factorial_pos _
  have houter := outward_halfplane_period c x hc hx R S hgen p hprimitive m M
    hbounds hlower hshorter β s hspos hsbound hperiod
  have hregion : {g : Site | directionNormal p g ≤ β + (M - m)} =
      {g : Site | -(β + (M - m)) ≤ (-directionNormal p) g} := by
    ext g
    change (directionNormal p g ≤ β + (M - m)) ↔ -(β + (M - m)) ≤ -directionNormal p g
    omega
  rw [hregion] at houter
  have hxann : laurentAct (differenceProduct hs) x = 0 := by
    funext g
    exact annihilator_inherited_of_language x c hx (differenceProduct hs).coeff
      (fun z => congrFun hann z) g
  obtain ⟨n, hn, hglobal⟩ := global_period_multiple_of_tangent_regional_period x hs hdirs hpairs hxann
    (-directionNormal p) (neg_ne_zero.mpr hν) (-(β + (M - m))) ((L : ℤ) • p)
    (smul_ne_zero (by exact_mod_cast Nat.ne_of_gt hL) hpne)
    (by change -(directionNormal p ((L : ℤ) • p)) = 0; rw [map_zsmul, hp, smul_zero, neg_zero]) houter
  refine ⟨n * L, Nat.mul_pos hn hL, ?_⟩
  simpa only [Nat.cast_mul, smul_smul] using hglobal

end KumarNivat
