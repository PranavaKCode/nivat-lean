import KumarNivat.AnchoredPhaseLimits
import KumarNivat.PrimitiveRetention
import KumarNivat.ShiftedConfigurations

open Filter Topology

namespace KumarNivat

-- shifting along a half-plane boundary preserves the excluded full regional periodicity.
theorem halfplane_phase_not_fully_regionally_periodic {A : Type*} (w : Site → A)
    (ν : Site →+ ℤ) (β : ℤ) (a : Site) (hνa : ν a = 0) (r : ℤ)
    (hnot : ¬ FullyRegionallyPeriodic w {g | β ≤ ν g}) :
    ¬ FullyRegionallyPeriodic (shift (r • a) w) {g | β ≤ ν g} := by
  rintro ⟨p, q, hdet, hp, hq⟩
  apply hnot
  have htransfer (v : Site)
      (hv : RegionalPeriod (shift (r • a) w) {g | β ≤ ν g} v) :
      RegionalPeriod w {g | β ≤ ν g} v := by
    intro g hg hgv
    have hfirst : g - r • a ∈ {g | β ≤ ν g} := by
      simpa only [Set.mem_ofPred_eq, map_sub, map_zsmul, hνa, smul_zero, sub_zero] using hg
    have hsecond : (g - r • a) + v ∈ {g | β ≤ ν g} := by
      rw [sub_add_eq_add_sub]
      simpa only [Set.mem_ofPred_eq, map_sub, map_zsmul, hνa, smul_zero, sub_zero] using hgv
    have he := hv (g - r • a) hfirst hsecond
    simpa only [shift, sub_add_cancel, sub_add_eq_add_sub] using he
  exact ⟨p, q, hdet, htransfer p hp, htransfer q hq⟩

-- the chosen phase keeps the same global reference period.
theorem anchored_reference_phase_period {A : Type*} (w : Site → A) (a : Site)
    (l : ℕ) (hw : IsPeriod w ((l : ℤ) • a)) (r : ℤ) :
    IsPeriod (shift (r • a) w) ((l : ℤ) • a) := by
  intro g
  change w (g + (l : ℤ) • a + r • a) = w (g + r • a)
  rw [show g + (l : ℤ) • a + r • a = (g + r • a) + (l : ℤ) • a by abel, hw]

-- this packages the actual compactness choice with the paper's retained-witness nonperiodicity test.
theorem anchored_nonperiodic_orbit_limit {A ι : Type*} [TopologicalSpace A]
    [DiscreteTopology A] [Finite ι] (c w : Site → A) (hc : (Set.range c).Finite)
    (a : Site) (hprimitive : Int.gcd a.1 a.2 = 1)
    (l : ℕ) (hl : 0 < l) (hw : IsPeriod w ((l : ℤ) • a))
    (u : ℕ → Site) (k : ℕ → ℤ) (P : ℕ → Set Site) (lengths : ℕ → ι → ℕ)
    (hnest : ∀ i j, lengths i ≤ lengths j → P i ⊆ P j)
    (hagree : ∀ n, ∀ g ∈ P n, shift (u n) c g = shift (k n • a) w g)
    (E : Finset Site)
    (hfail : ∀ᶠ n in atTop, ∃ g ∈ E, shift (u n) c g ≠ shift (k n • a) w g)
    (ν : Site →+ ℤ) (β : ℤ) (hνa : ν a = 0)
    (hnot : ¬ FullyRegionallyPeriodic w {g | β ≤ ν g})
    (hE : ∀ g ∈ E, β ≤ ν g)
    (htravel : ∀ ρ : ℕ → ℕ, StrictMono ρ → Monotone (lengths ∘ ρ) →
      BackwardCofinal (⋃ n, P (ρ n)) {g | β ≤ ν g} a) :
    ∃ r : ℤ, 0 ≤ r ∧ r < (l : ℤ) ∧ ∃ θ ∈ orbitClosure c,
      ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ Monotone (lengths ∘ ρ) ∧ Monotone (P ∘ ρ) ∧
        Tendsto ((fun n => shift (u n) c) ∘ ρ) atTop (𝓝 θ) ∧
        (∀ g ∈ ⋃ n, P (ρ n), θ g = shift (r • a) w g) ∧
        (∃ g ∈ E, θ g ≠ shift (r • a) w g) ∧
        ¬ ∃ p : Site, p ≠ 0 ∧ IsPeriod θ p := by
  obtain ⟨r, hr₀, hr₁, θ, hθ, ρ, hρ, hlengths, hregions, _hphase, hlimit,
      hθagree, hθfail⟩ :=
    anchored_phase_orbit_limit c w hc a l hl hw u k P lengths hnest hagree E hfail
  refine ⟨r, hr₀, hr₁, θ, hθ, ρ, hρ, hlengths, hregions, hlimit, hθagree, hθfail, ?_⟩
  apply nonperiodic_of_primitive_retained_disagreement θ (shift (r • a) w)
    (⋃ n, P (ρ n)) {g | β ≤ ν g} a hprimitive l hl
    (anchored_reference_phase_period w a l hw r) hθagree
    (htravel ρ hρ hlengths) (halfplane_phase_not_fully_regionally_periodic w ν β a hνa r hnot)
  obtain ⟨g, hg, hne⟩ := hθfail
  exact ⟨g, hE g hg, hne⟩

end KumarNivat
