module

public import KumarNivat.RowFrames
public import KumarNivat.StableRegions
public import KumarNivat.RegionalRowAgreement
public import KumarNivat.FixedGapRepetitions
public import KumarNivat.HalfplaneBackgrounds

@[expose] public section

namespace KumarNivat

-- equality on the actual finite frame extends to every regional row in its consecutive level band.
theorem regional_band_agreement_of_row_frame_repeat {A : Type*} (x y : Site → A)
    (R : Set Site) (a : Site) (hprimitive : Int.gcd a.1 a.2 = 1) (p : ℕ) (hp : 0 < p)
    (hstable : ∀ g ∈ R, g + (p : ℤ) • a ∈ R)
    (hxper : RegionalPeriod x R ((p : ℤ) • a)) (hyper : RegionalPeriod y R ((p : ℤ) • a))
    (v E : Site) (hv : directionNormal a v = 1) (d : ℕ)
    (hfit : ∀ u ∈ rowFrame E a v p d, u ∈ R)
    (hagree : ∀ u ∈ rowFrame E a v p d, x u = y u) :
    ∀ g ∈ R, directionNormal a E ≤ directionNormal a g →
      directionNormal a g ≤ directionNormal a E + (d : ℤ) → x g = y g := by
  intro g hg hlo hhi
  obtain ⟨F, hF, hblock⟩ := rowFrame_block_on_level E a v p d hv (directionNormal a g) hlo hhi
  have hrow := regional_row_agreement_of_periodic_block x y R a hprimitive p hp hstable hxper hyper F 0
    (fun i => by simpa only [zero_add] using hfit _ (hblock i))
    (fun i => by simpa only [zero_add] using hagree _ (hblock i))
  exact hrow g hg hF.symm

-- a repeated translated frame gives a transverse period on its entire band inside the original working region.
theorem regional_band_period_of_translated_frame_repeat {A : Type*} (x : Site → A)
    (R : Set Site) (a : Site) (hprimitive : Int.gcd a.1 a.2 = 1) (p : ℕ) (hp : 0 < p)
    (hstableA : ∀ g ∈ R, g + (p : ℤ) • a ∈ R) (hperiod : RegionalPeriod x R ((p : ℤ) • a))
    (h : Site) (hstableH : ∀ g ∈ R, g + h ∈ R) (v E : Site)
    (hv : directionNormal a v = 1) (d : ℕ) (hfit : ∀ u ∈ rowFrame E a v p d, u ∈ R)
    (q D : ℕ)
    (hrepeat : ∀ u ∈ rowFrame E a v p d, x ((u + (q : ℤ) • h) + (D : ℤ) • h) = x (u + (q : ℤ) • h)) :
    ∀ g ∈ R, directionNormal a (E + (q : ℤ) • h) ≤ directionNormal a g →
      directionNormal a g ≤ directionNormal a (E + (q : ℤ) • h) + (d : ℤ) →
        x (g + (D : ℤ) • h) = x g := by
  have hshiftstable : ∀ g ∈ R, g + (D : ℤ) • h ∈ R :=
    forward_stable_nat_multiples R h hstableH D
  have hshiftper := regional_period_shift_of_forward_stability x R ((D : ℤ) • h) ((p : ℤ) • a)
    hshiftstable hperiod
  have hfitq : ∀ u ∈ rowFrame (E + (q : ℤ) • h) a v p d, u ∈ R := by
    intro u hu
    rw [rowFrame_translate] at hu
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hu
    exact forward_stable_nat_multiples R h hstableH q w (hfit w hw)
  have hagree : ∀ u ∈ rowFrame (E + (q : ℤ) • h) a v p d, shift ((D : ℤ) • h) x u = x u := by
    intro u hu
    rw [rowFrame_translate] at hu
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hu
    exact hrepeat w hw
  exact regional_band_agreement_of_row_frame_repeat (shift ((D : ℤ) • h) x) x R a hprimitive p hp
    hstableA hshiftper hperiod v (E + (q : ℤ) • h) hv d hfitq hagree

-- one bounded repeat gap supplies whole periodic bands at arbitrarily high levels for the same difference array.
theorem fixed_gap_regional_row_bands {A : Type*} (c x : Site → A)
    (hc : (Set.range c).Finite) (hx : LanguageContained x c)
    (R : Set Site) (a : Site) (hprimitive : Int.gcd a.1 a.2 = 1) (p : ℕ) (hp : 0 < p)
    (hstableA : ∀ g ∈ R, g + (p : ℤ) • a ∈ R) (hperiod : RegionalPeriod x R ((p : ℤ) • a))
    (h : Site) (hheight : 0 < directionNormal a h) (hstableH : ∀ g ∈ R, g + h ∈ R)
    (v E : Site) (hv : directionNormal a v = 1) (d : ℕ) (hfit : ∀ u ∈ rowFrame E a v p d, u ∈ R) :
    ∃ D : ℕ, 0 < D ∧ D ≤ complexity c (rowFrame E a v p d) ∧
      ∀ L : ℤ, ∃ q : ℕ, L ≤ directionNormal a (E + (q : ℤ) • h) ∧
        ∀ g ∈ R, directionNormal a (E + (q : ℤ) • h) ≤ directionNormal a g →
          directionNormal a g ≤ directionNormal a (E + (q : ℤ) • h) + (d : ℤ) →
            x (g + (D : ℤ) • h) = x g := by
  obtain ⟨D, hD, hbound, hrepeats⟩ := fixed_gap_legal_pattern_repetitions c x hc hx (rowFrame E a v p d) h
  refine ⟨D, hD, hbound, ?_⟩
  intro L
  obtain ⟨N, hN⟩ := halfplane_forward_cofinal (directionNormal a) L h hheight E
  obtain ⟨q, hq, hrepeat⟩ := hrepeats N
  exact ⟨q, hN q hq, regional_band_period_of_translated_frame_repeat x R a hprimitive p hp
    hstableA hperiod h hstableH v E hv d hfit q D hrepeat⟩

end KumarNivat
