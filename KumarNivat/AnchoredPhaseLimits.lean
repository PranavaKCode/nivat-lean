import KumarNivat.AnchoredSubsequences

open Filter Topology

namespace KumarNivat

-- select a phase, nondecreasing edge data, and a limit without losing the finite boundary failure.
theorem anchored_phase_orbit_limit {A ι : Type*} [TopologicalSpace A]
    [DiscreteTopology A] [Finite ι] (c w : Site → A) (hc : (Set.range c).Finite)
    (a : Site) (l : ℕ) (hl : 0 < l) (hw : IsPeriod w ((l : ℤ) • a))
    (u : ℕ → Site) (k : ℕ → ℤ) (P : ℕ → Set Site) (lengths : ℕ → ι → ℕ)
    (hnest : ∀ i j, lengths i ≤ lengths j → P i ⊆ P j)
    (hagree : ∀ n, ∀ g ∈ P n, shift (u n) c g = shift (k n • a) w g)
    (E : Finset Site)
    (hfail : ∀ᶠ n in atTop, ∃ g ∈ E, shift (u n) c g ≠ shift (k n • a) w g) :
    ∃ r : ℤ, 0 ≤ r ∧ r < (l : ℤ) ∧ ∃ θ ∈ orbitClosure c,
      ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ Monotone (lengths ∘ ρ) ∧
        Monotone (P ∘ ρ) ∧
        (∀ n, shift (k (ρ n) • a) w = shift (r • a) w) ∧
        Tendsto ((fun n => shift (u n) c) ∘ ρ) atTop (𝓝 θ) ∧
        (∀ g ∈ ⋃ n, P (ρ n), θ g = shift (r • a) w g) ∧
        ∃ g ∈ E, θ g ≠ shift (r • a) w g := by
  obtain ⟨r, hr₀, hr₁, φ, hφ, hphase⟩ :=
    periodic_reference_constant_phase w a l hl hw k
  obtain ⟨ψ, hψ, hlengths⟩ := anchored_lengths_monotone_subsequence (lengths ∘ φ)
  obtain ⟨θ, hθ, χ, hχ, hlimit⟩ :=
    finite_range_orbit_subsequence c hc (fun n => u (φ (ψ n)))
  let ρ : ℕ → ℕ := φ ∘ ψ ∘ χ
  have hρ : StrictMono ρ := hφ.comp (hψ.comp hχ)
  have hlengthsρ : Monotone (lengths ∘ ρ) := hlengths.comp hχ.monotone
  have hregionsρ : Monotone (P ∘ ρ) := by
    intro i j hij
    exact hnest (ρ i) (ρ j) (hlengthsρ hij)
  have hphaseρ : ∀ n, shift (k (ρ n) • a) w = shift (r • a) w :=
    fun n => hphase (ψ (χ n))
  have hlimitρ : Tendsto ((fun n => shift (u n) c) ∘ ρ) atTop (𝓝 θ) := hlimit
  have hregionAgreement : ∀ g ∈ ⋃ n, P (ρ n), θ g = shift (r • a) w g := by
    apply configuration_limit_agrees_of_eventually _ θ (shift (r • a) w) _ hlimitρ
    intro g hg
    have hmembership := monotone_regions_eventually_contain (P ∘ ρ) hregionsρ g hg
    exact hmembership.mono (fun n hn => by
      change shift (u (ρ n)) c g = shift (r • a) w g
      rw [← hphaseρ n]
      exact hagree (ρ n) g hn)
  have hfailureρ : ∀ᶠ n in atTop, ∃ g ∈ E,
      shift (u (ρ n)) c g ≠ shift (r • a) w g := by
    have hfailure := hρ.tendsto_atTop.eventually hfail
    exact hfailure.mono (fun n hn => by
      change ∃ g ∈ E, shift (u (ρ n)) c g ≠ shift (k (ρ n) • a) w g at hn
      rw [hphaseρ n] at hn
      exact hn)
  refine ⟨r, hr₀, hr₁, θ, hθ, ρ, hρ, hlengthsρ, hregionsρ, hphaseρ, hlimitρ,
    hregionAgreement, ?_⟩
  exact configuration_limit_retains_finite_disagreement _ θ (shift (r • a) w)
    E hlimitρ hfailureρ

end KumarNivat
