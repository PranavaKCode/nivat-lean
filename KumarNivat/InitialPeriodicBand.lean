module

public import KumarNivat.PlacedEdgeAmbiguity
public import KumarNivat.FirstDisagreement
public import KumarNivat.ShiftedConfigurations
public import KumarNivat.GeneratingBandPeriods

@[expose] public section

namespace KumarNivat

-- the actual boundary witness places the generating edge and makes the whole inward band periodic.
theorem initial_band_period_from_boundary_disagreement {K : Type*} [CommRing K] [NoZeroDivisors K]
    (c x y : Site → K) (hc : (Set.range c).Finite)
    (hx : LanguageContained x c) (hy : LanguageContained y c)
    (f : Laurent K) (hf : f ≠ 0) (hxann : laurentAct f x = 0) (hyann : laurentAct f y = 0)
    (R S : Finset Site) (hgen : GeneratingPolygon c R S) (p : Site)
    (hprimitive : Int.gcd p.1 p.2 = 1) (m M : ℤ)
    (hbounds : ∀ u ∈ S, m ≤ directionNormal p u ∧ directionNormal p u ≤ M)
    (hlower : 2 ≤ (lowerLatticeFace S (directionNormal p) m).card)
    (hshorter : (lowerLatticeFace S (directionNormal p) m).card ≤
      (lowerLatticeFace S (-directionNormal p) (-M)).card)
    (β : ℤ) (hhalf : ∀ g : Site, β + 1 ≤ directionNormal p g → x g = y g)
    (g₀ : Site) (hg₀ : directionNormal p g₀ = β) (hneq : x g₀ ≠ y g₀) :
    ∃ q : ℕ, 0 < q ∧ q ≤ (lowerLatticeFace S (directionNormal p) m).card - 1 ∧
      RegionalPeriod x (normalBand (directionNormal p) (β + 1) (β + (M - m))) ((q : ℤ) • p) ∧
      RegionalPeriod y (normalBand (directionNormal p) (β + 1) (β + (M - m))) ((q : ℤ) • p) := by
  classical
  have hpne : p ≠ 0 := by rintro rfl; simp at hprimitive
  have hν := directionNormal_ne_zero p hpne
  have hp : directionNormal p p = 0 := by simp [directionNormal, determinant, mul_comm]
  have hface : (lowerLatticeFace S (directionNormal p) m).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨v, hv⟩ := hface
  let E := g₀ - v
  have hE : directionNormal p E = β - m := by
    dsimp [E]
    rw [map_sub, hg₀, (Finset.mem_filter.mp hv).2]
  have hamb := placed_edge_bases_ambiguous_of_boundary_disagreement c x y hc hx hy f hf hxann hyann R S hgen
    (directionNormal p) hν m (fun u hu => (hbounds u hu).1) ⟨v, hv⟩ p hp hprimitive β E hE hhalf g₀ hg₀ hneq
  have hxE : LanguageContained (shift E x) c := hx.shift E
  have hambE (n : ℤ) : 2 ≤ extensionCount c S (S \ lowerLatticeFace S (directionNormal p) m) Finset.sdiff_subset
      (legalTranslatedPattern c (shift E x) hxE (S \ lowerLatticeFace S (directionNormal p) m) (n • p)) := by
    have he : legalTranslatedPattern c (shift E x) hxE (S \ lowerLatticeFace S (directionNormal p) m) (n • p) =
        legalTranslatedPattern c x hx (S \ lowerLatticeFace S (directionNormal p) m) (E + n • p) := by
      apply Subtype.ext
      funext u
      simp only [legalTranslatedPattern, shift, add_assoc, add_comm]
    rw [he]
    exact hamb n
  obtain ⟨q, hq, hqr, hperiod⟩ := band_period_of_shorter_opposite_generating_edges c (shift E x) hc hxE
    R S hgen p hprimitive m M hbounds hlower hshorter hambE
  have hxperiod := regional_period_of_shifted_region x (normalBand (directionNormal p) (m + 1) M)
    E ((q : ℤ) • p) hperiod
  have hregion : {g : Site | g - E ∈ normalBand (directionNormal p) (m + 1) M} =
      normalBand (directionNormal p) (β + 1) (β + (M - m)) := by
    ext g
    change (m + 1 ≤ directionNormal p (g - E) ∧ directionNormal p (g - E) ≤ M) ↔
      (β + 1 ≤ directionNormal p g ∧ directionNormal p g ≤ β + (M - m))
    rw [map_sub, hE]
    omega
  rw [hregion] at hxperiod
  refine ⟨q, hq, hqr, hxperiod, ?_⟩
  intro g hg hgp
  exact (hhalf _ hgp.1).symm.trans ((hxperiod g hg hgp).trans (hhalf g hg.1))

-- one-sided nonexpansiveness supplies the actual orbit points, first outer witness, and sharp initial strip period.
theorem exists_initial_periodic_band (c : Site → ℤ) (hc : (Set.range c).Finite)
    (f : Laurent ℤ) (hf : f ≠ 0) (hann : laurentAct f c = 0)
    (R S : Finset Site) (hgen : GeneratingPolygon c R S) (p : Site)
    (hprimitive : Int.gcd p.1 p.2 = 1) (m M : ℤ)
    (hbounds : ∀ u ∈ S, m ≤ directionNormal p u ∧ directionNormal p u ≤ M)
    (hlower : 2 ≤ (lowerLatticeFace S (directionNormal p) m).card)
    (hshorter : (lowerLatticeFace S (directionNormal p) m).card ≤
      (lowerLatticeFace S (-directionNormal p) (-M)).card)
    (hNE : OneSidedNonexpansive c (integerNormalAsReal (directionNormal p))) :
    m < M ∧ ∃ x y : Site → ℤ, x ∈ orbitClosure c ∧ y ∈ orbitClosure c ∧
      ∃ β : ℤ, ∃ g₀ : Site, ∃ q : ℕ, β < 0 ∧ directionNormal p g₀ = β ∧ x g₀ ≠ y g₀ ∧
        0 < q ∧ q ≤ (lowerLatticeFace S (directionNormal p) m).card - 1 ∧
        (∀ g : Site, β + 1 ≤ directionNormal p g → x g = y g) ∧
        RegionalPeriod x (normalBand (directionNormal p) (β + 1) (β + (M - m))) ((q : ℤ) • p) ∧
        RegionalPeriod y (normalBand (directionNormal p) (β + 1) (β + (M - m))) ((q : ℤ) • p) := by
  have hpne : p ≠ 0 := by rintro rfl; simp at hprimitive
  have hν := directionNormal_ne_zero p hpne
  have hwidth : m < M := by
    by_contra hn
    apply hgen.2.2.1.normal_not_constant (directionNormal p) hν m
    intro u hu
    have hb := hbounds u hu
    omega
  obtain ⟨_hell, x, y, hx, hy, hxy, hagree⟩ := hNE
  have hh : ∀ g : Site, 0 ≤ directionNormal p g → x g = y g := by
    intro g hg
    apply hagree g
    change (0 : ℝ) ≤ (directionNormal p g : ℝ)
    exact_mod_cast hg
  obtain ⟨β, g₀, hβ, hg₀, hneq, hhalf⟩ := first_integer_disagreement_level x y (directionNormal p) hxy hh
  have hxlang := languageContained_of_mem_orbitClosure c x hx
  have hylang := languageContained_of_mem_orbitClosure c y hy
  have hxann : laurentAct f x = 0 := funext
    (annihilator_inherited_of_language x c hxlang f.coeff (fun g => congrFun hann g))
  have hyann : laurentAct f y = 0 := funext
    (annihilator_inherited_of_language y c hylang f.coeff (fun g => congrFun hann g))
  obtain ⟨q, hq, hqr, hxper, hyper⟩ := initial_band_period_from_boundary_disagreement c x y hc hxlang hylang
    f hf hxann hyann R S hgen p hprimitive m M hbounds hlower hshorter β hhalf g₀ hg₀ hneq
  exact ⟨hwidth, x, y, hx, hy, β, g₀, q, hβ, hg₀, hneq, hq, hqr, hhalf, hxper, hyper⟩

end KumarNivat
