module

public import KumarNivat.PairedStructureOrbit
public import KumarNivat.AnchoredCompactness

@[expose] public section

open Filter Topology

namespace KumarNivat

-- a finite boundary failure survives while agreement expands through the entire half-plane.
theorem oneSidedNonexpansive_of_growing_halfplane_pairs {A : Type*}
    [TopologicalSpace A] [DiscreteTopology A] (c : Site → A)
    (hc : (Set.range c).Finite) (ell : Site →+ ℝ) (hell : ell ≠ 0)
    (x y : ℕ → Site → A) (hx : ∀ n, x n ∈ orbitClosure c)
    (hy : ∀ n, y n ∈ orbitClosure c) (E : Finset Site)
    (hfail : ∀ n, ∃ g ∈ E, x n g ≠ y n g)
    (hagree : ∀ g : Site, 0 ≤ ell g → ∀ᶠ n in atTop, x n g = y n g) :
    OneSidedNonexpansive c ell := by
  have hcompact := finite_range_orbitClosure_compact c hc
  obtain ⟨⟨θ, w⟩, hmem, φ, hφ, hlimit⟩ := (hcompact.prod hcompact).tendsto_subseq
    (fun n => show (x n, y n) ∈ orbitClosure c ×ˢ orbitClosure c from ⟨hx n, hy n⟩)
  have hxlimit : Tendsto (x ∘ φ) atTop (𝓝 θ) := hlimit.fst_nhds
  have hylimit : Tendsto (y ∘ φ) atTop (𝓝 w) := hlimit.snd_nhds
  have hfail' : ∀ᶠ n in atTop, ∃ g ∈ E, (x ∘ φ) n g ≠ (y ∘ φ) n g :=
    Eventually.of_forall (fun n => hfail (φ n))
  obtain ⟨g, _hg, hne⟩ := configuration_limits_retain_finite_disagreement
    (x ∘ φ) (y ∘ φ) θ w E hxlimit hylimit hfail'
  refine ⟨hell, θ, w, hmem.1, hmem.2, fun he => hne (congrFun he g), ?_⟩
  intro u hu
  have hevent : ∀ᶠ n in atTop, (x ∘ φ) n u = (y ∘ φ) n u :=
    hφ.tendsto_atTop.eventually (hagree u hu)
  obtain ⟨n, ⟨hnx, hny⟩, hnequal⟩ :=
    (((configuration_limit_eventually_eq (x ∘ φ) θ hxlimit u).and
      (configuration_limit_eventually_eq (y ∘ φ) w hylimit u)).and hevent).exists
  exact hnx.symm.trans (hnequal.trans hny)

end KumarNivat
