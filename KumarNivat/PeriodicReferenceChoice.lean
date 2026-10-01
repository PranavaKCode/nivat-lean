import KumarNivat.HalfplaneBackgrounds
import KumarNivat.GlobalPeriodsFromBands
import KumarNivat.InitialPeriodicBand

namespace KumarNivat

-- two tangent-periodic orbit points cannot both have full regional periodicity across their first disagreement line.
theorem one_member_not_fully_regionally_periodic {A : Type*} (x y : Site → A)
    (p : Site) (hprimitive : Int.gcd p.1 p.2 = 1) (l₁ l₂ : ℕ) (hl₁ : 0 < l₁) (hl₂ : 0 < l₂)
    (hxper : IsPeriod x ((l₁ : ℤ) • p)) (hyper : IsPeriod y ((l₂ : ℤ) • p))
    (β : ℤ) (hhalf : ∀ g : Site, β + 1 ≤ directionNormal p g → x g = y g)
    (g₀ : Site) (hg₀ : directionNormal p g₀ = β) (hneq : x g₀ ≠ y g₀) :
    (¬ FullyRegionallyPeriodic x {g | β ≤ directionNormal p g}) ∨
      (¬ FullyRegionallyPeriodic y {g | β ≤ directionNormal p g}) := by
  classical
  by_cases hfullx : FullyRegionallyPeriodic x {g | β ≤ directionNormal p g}
  · right
    intro hfully
    obtain ⟨B, hB, hagreeB, _hrangeB⟩ := halfplane_background_of_tangent_and_regional_periods x p
      hprimitive l₁ hl₁ hxper β hfullx
    obtain ⟨C, hC, hagreeC, _hrangeC⟩ := halfplane_background_of_tangent_and_regional_periods y p
      hprimitive l₂ hl₂ hyper β hfully
    obtain ⟨τ, hτ, _hker⟩ := primitive_direction_coordinate p hprimitive
    obtain ⟨v, hpv⟩ := primitive_basis_of_line_coordinate p τ hτ
    have hv : 0 < directionNormal p v := by change 0 < determinant p v; rw [hpv]; omega
    have hBC : B = C := fully_periodic_halfplane_agreement B C hB hC (directionNormal p) (β + 1) v hv
      (fun g hg => (hagreeB g (by omega)).trans ((hhalf g hg).trans (hagreeC g (by omega)).symm))
    apply hneq
    exact (hagreeB g₀ (by omega)).symm.trans ((congrFun hBC g₀).trans (hagreeC g₀ (by omega)))
  · exact Or.inl hfullx

-- the actual initial orbit pair supplies a globally tangent-periodic reference with the required non-full half-plane.
theorem periodic_reference_of_initial_band_pair (c x y : Site → ℤ)
    (hc : (Set.range c).Finite) (hx : x ∈ orbitClosure c) (hy : y ∈ orbitClosure c)
    (hs : List Site) (hdirs : ∀ h ∈ hs, h ≠ 0)
    (hpairs : hs.Pairwise (fun a b => determinant a b ≠ 0))
    (hann : laurentAct (differenceProduct hs) c = 0)
    (R S : Finset Site) (hgen : GeneratingPolygon c R S) (p : Site)
    (hprimitive : Int.gcd p.1 p.2 = 1) (m M : ℤ)
    (hbounds : ∀ u ∈ S, m ≤ directionNormal p u ∧ directionNormal p u ≤ M)
    (hlower : 2 ≤ (lowerLatticeFace S (directionNormal p) m).card)
    (hshorter : (lowerLatticeFace S (directionNormal p) m).card ≤
      (lowerLatticeFace S (-directionNormal p) (-M)).card)
    (β : ℤ) (hhalf : ∀ g : Site, β + 1 ≤ directionNormal p g → x g = y g)
    (g₀ : Site) (hg₀ : directionNormal p g₀ = β) (hneq : x g₀ ≠ y g₀)
    (s : ℕ) (hspos : 0 < s) (hsbound : s ≤ (lowerLatticeFace S (directionNormal p) m).card - 1)
    (hxband : RegionalPeriod x (normalBand (directionNormal p) (β + 1) (β + (M - m))) ((s : ℤ) • p))
    (hyband : RegionalPeriod y (normalBand (directionNormal p) (β + 1) (β + (M - m))) ((s : ℤ) • p)) :
    ∃ w : Site → ℤ, w ∈ orbitClosure c ∧ ∃ l : ℕ, 0 < l ∧ IsPeriod w ((l : ℤ) • p) ∧
      ¬ FullyRegionallyPeriodic w {g | β ≤ directionNormal p g} := by
  have hbound : s ≤ 2 * ((lowerLatticeFace S (directionNormal p) m).card - 1) := by omega
  obtain ⟨l₁, hl₁, hxglobal⟩ := global_tangent_period_from_initial_band c x hc
    (languageContained_of_mem_orbitClosure c x hx) hs hdirs hpairs hann R S hgen p hprimitive m M
      hbounds hlower hshorter β s hspos hbound hxband
  obtain ⟨l₂, hl₂, hyglobal⟩ := global_tangent_period_from_initial_band c y hc
    (languageContained_of_mem_orbitClosure c y hy) hs hdirs hpairs hann R S hgen p hprimitive m M
      hbounds hlower hshorter β s hspos hbound hyband
  rcases one_member_not_fully_regionally_periodic x y p hprimitive l₁ l₂ hl₁ hl₂ hxglobal hyglobal
      β hhalf g₀ hg₀ hneq with hnotx | hnoty
  · exact ⟨x, hx, l₁, hl₁, hxglobal, hnotx⟩
  · exact ⟨y, hy, l₂, hl₂, hyglobal, hnoty⟩

end KumarNivat
