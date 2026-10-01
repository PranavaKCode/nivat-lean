import KumarNivat.OrbitLanguage
import Mathlib.Topology.Sequences
import Mathlib.Topology.Compactness.Compact
import Mathlib.Order.Filter.Finite

open Filter Topology

namespace KumarNivat

-- the original finite alphabet gives compactness of the actual orbit closure.
theorem finite_range_orbitClosure_compact {A : Type*} [TopologicalSpace A]
    [DiscreteTopology A] (c : Site → A) (hc : (Set.range c).Finite) :
    IsCompact (orbitClosure c) := by
  let alphabetConfigurations : Set (Site → A) := {x | ∀ g, x g ∈ Set.range c}
  have hcompact : IsCompact alphabetConfigurations :=
    isCompact_pi_infinite (fun _ : Site => hc.isCompact)
  have hclosed : IsClosed alphabetConfigurations := by
    change IsClosed {x : Site → A | ∀ g, x g ∈ Set.range c}
    simp only [Set.ofPred_forall]
    exact isClosed_iInter (fun g => hc.isClosed.preimage (continuous_apply g))
  apply hcompact.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hclosed
  rintro x ⟨h, rfl⟩ g
  exact ⟨g + h, rfl⟩

-- an arbitrary sequence in this closure has a convergent increasing subsequence.
theorem finite_range_orbitClosure_subsequence {A : Type*} [TopologicalSpace A]
    [DiscreteTopology A] (c : Site → A) (hc : (Set.range c).Finite)
    (x : ℕ → Site → A) (hx : ∀ n, x n ∈ orbitClosure c) :
    ∃ θ ∈ orbitClosure c, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 θ) :=
  (finite_range_orbitClosure_compact c hc).tendsto_subseq hx

-- the selected limit is a point of the same orbit closure of the original array.
theorem finite_range_orbit_subsequence {A : Type*} [TopologicalSpace A]
    [DiscreteTopology A] (c : Site → A) (hc : (Set.range c).Finite) (u : ℕ → Site) :
    ∃ θ ∈ orbitClosure c, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto ((fun n => shift (u n) c) ∘ φ) atTop (𝓝 θ) := by
  apply finite_range_orbitClosure_subsequence c hc
  intro n
  exact subset_closure ⟨u n, rfl⟩

-- product convergence over discrete symbols is eventual equality at each fixed site.
theorem configuration_limit_eventually_eq {A : Type*} [TopologicalSpace A]
    [DiscreteTopology A] (x : ℕ → Site → A) (θ : Site → A)
    (hx : Tendsto x atTop (𝓝 θ)) (g : Site) :
    ∀ᶠ n in atTop, x n g = θ g := by
  have heval := (continuous_apply g).tendsto θ |>.comp hx
  rw [nhds_discrete] at heval
  exact tendsto_pure.mp heval

-- eventual agreement survives at the same site of the selected limit.
theorem configuration_limit_agrees_of_eventually {A : Type*} [TopologicalSpace A]
    [DiscreteTopology A] (x : ℕ → Site → A) (θ w : Site → A) (R : Set Site)
    (hx : Tendsto x atTop (𝓝 θ))
    (hagree : ∀ g ∈ R, ∀ᶠ n in atTop, x n g = w g) :
    ∀ g ∈ R, θ g = w g := by
  intro g hg
  obtain ⟨n, hlimit, hreference⟩ :=
    ((configuration_limit_eventually_eq x θ hx g).and (hagree g hg)).exists
  exact hlimit.symm.trans hreference

-- convergence on one fixed finite witness set prevents the boundary failure from escaping.
theorem configuration_limit_retains_finite_disagreement {A : Type*} [TopologicalSpace A]
    [DiscreteTopology A] (x : ℕ → Site → A) (θ w : Site → A) (E : Finset Site)
    (hx : Tendsto x atTop (𝓝 θ))
    (hfail : ∀ᶠ n in atTop, ∃ g ∈ E, x n g ≠ w g) :
    ∃ g ∈ E, θ g ≠ w g := by
  have hpattern : ∀ᶠ n in atTop, ∀ g ∈ E, x n g = θ g :=
    E.eventually_all.mpr (fun g _ => configuration_limit_eventually_eq x θ hx g)
  obtain ⟨n, hnfail, hnpattern⟩ := (hfail.and hpattern).exists
  obtain ⟨g, hg, hne⟩ := hnfail
  exact ⟨g, hg, fun heq => hne ((hnpattern g hg).trans heq)⟩

-- the same finite witness argument applies when both arrays are selected as limits.
theorem configuration_limits_retain_finite_disagreement {A : Type*} [TopologicalSpace A]
    [DiscreteTopology A] (x y : ℕ → Site → A) (θ w : Site → A) (E : Finset Site)
    (hx : Tendsto x atTop (𝓝 θ)) (hy : Tendsto y atTop (𝓝 w))
    (hfail : ∀ᶠ n in atTop, ∃ g ∈ E, x n g ≠ y n g) :
    ∃ g ∈ E, θ g ≠ w g := by
  have hxpattern : ∀ᶠ n in atTop, ∀ g ∈ E, x n g = θ g :=
    E.eventually_all.mpr (fun g _ => configuration_limit_eventually_eq x θ hx g)
  have hypattern : ∀ᶠ n in atTop, ∀ g ∈ E, y n g = w g :=
    E.eventually_all.mpr (fun g _ => configuration_limit_eventually_eq y w hy g)
  obtain ⟨n, ⟨hnfail, hnx⟩, hny⟩ := ((hfail.and hxpattern).and hypattern).exists
  obtain ⟨g, hg, hne⟩ := hnfail
  exact ⟨g, hg, fun heq => hne ((hnx g hg).trans (heq.trans (hny g hg).symm))⟩

-- a nested sequence eventually contains every site in its increasing union.
theorem monotone_regions_eventually_contain (P : ℕ → Set Site) (hP : Monotone P) :
    ∀ g ∈ ⋃ n, P n, ∀ᶠ n in atTop, g ∈ P n := by
  intro g hg
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hg
  exact (eventually_ge_atTop n).mono (fun m hnm => hP hnm hn)

-- the increasing union is unchanged by taking any strictly increasing subsequence.
theorem monotone_regions_subsequence_union (P : ℕ → Set Site) (hP : Monotone P)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) : (⋃ n, P (φ n)) = ⋃ n, P n := by
  apply Set.Subset.antisymm
  · intro g hg
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hg
    exact Set.mem_iUnion.mpr ⟨φ n, hn⟩
  · intro g hg
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hg
    exact Set.mem_iUnion.mpr ⟨n, hP (hφ.id_le n) hn⟩

end KumarNivat
