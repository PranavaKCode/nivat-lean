module

public import KumarNivat.PairedStructureOrbit
public import KumarNivat.AnchoredCompactness
public import Mathlib.Order.Zorn

@[expose] public section

namespace KumarNivat

-- invariant closed subsets describe subshifts without changing the ambient configuration space.
def IsShiftInvariant {A : Type*} (S : Set (Site → A)) : Prop :=
  ∀ x ∈ S, ∀ h : Site, shift h x ∈ S

-- every original orbit closure is closed under all integer translations.
theorem orbitClosure_shift_invariant {A : Type*} [TopologicalSpace A] (c : Site → A) :
    IsShiftInvariant (orbitClosure c) := fun x hx h => orbitClosure_shift_mem c x hx h

-- a point of a closed invariant set has its whole orbit closure inside that same set.
theorem orbitClosure_subset_closed_invariant {A : Type*} [TopologicalSpace A]
    (S : Set (Site → A)) (hclosed : IsClosed S) (hinvariant : IsShiftInvariant S)
    (x : Site → A) (hx : x ∈ S) : orbitClosure x ⊆ S := by
  apply closure_minimal _ hclosed
  rintro _ ⟨h, rfl⟩
  exact hinvariant x hx h

-- the zero translate puts each array into its own orbit closure.
theorem mem_own_orbitClosure {A : Type*} [TopologicalSpace A] (c : Site → A) :
    c ∈ orbitClosure c := by
  apply subset_closure
  exact ⟨0, by funext g; simp only [shift, add_zero]⟩

-- compactness and the chain intersection theorem give an actual minimal closed invariant subset.
theorem exists_minimal_closed_invariant_orbit_subset {A : Type*} [TopologicalSpace A]
    [DiscreteTopology A] (c : Site → A) (hc : (Set.range c).Finite) :
    ∃ M : Set (Site → A), M ⊆ orbitClosure c ∧ IsClosed M ∧ M.Nonempty ∧ IsShiftInvariant M ∧
      ∀ S : Set (Site → A), S ⊆ M → IsClosed S → S.Nonempty → IsShiftInvariant S → S = M := by
  classical
  let family : Set (Set (Site → A)) :=
    {S | S ⊆ orbitClosure c ∧ IsClosed S ∧ S.Nonempty ∧ IsShiftInvariant S}
  have hroot : orbitClosure c ∈ family :=
    ⟨Set.Subset.refl _, isClosed_closure, ⟨c, mem_own_orbitClosure c⟩, orbitClosure_shift_invariant c⟩
  have hchains (C : Set (Set (Site → A))) (hC : C ⊆ family)
      (hchain : IsChain (· ⊆ ·) C) (hne : C.Nonempty) :
      ∃ S ∈ family, ∀ U ∈ C, S ⊆ U := by
    obtain ⟨U₀, hU₀⟩ := hne
    let : Nonempty C := ⟨⟨U₀, hU₀⟩⟩
    have hclosed : IsClosed (⋂₀ C) := isClosed_sInter (fun U hU => (hC hU).2.1)
    have hsub : ⋂₀ C ⊆ orbitClosure c := (Set.sInter_subset_of_mem hU₀).trans (hC hU₀).1
    have hdirected : DirectedOn (· ⊇ ·) C := by
      intro U hU V hV
      rcases hchain.total hU hV with hUV | hVU
      · exact ⟨U, hU, Set.Subset.refl _, hUV⟩
      · exact ⟨V, hV, hVU, Set.Subset.refl _⟩
    have hnonempty : (⋂₀ C).Nonempty :=
      IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed
        hdirected (fun U hU => (hC hU).2.2.1)
        (fun U hU => (finite_range_orbitClosure_compact c hc).of_isClosed_subset
          (hC hU).2.1 (hC hU).1) (fun U hU => (hC hU).2.1)
    have hinvariant : IsShiftInvariant (⋂₀ C) := by
      intro x hx h
      apply Set.mem_sInter.mpr
      intro U hU
      exact (hC hU).2.2.2 x (Set.mem_sInter.mp hx U hU) h
    exact ⟨⋂₀ C, ⟨hsub, hclosed, hnonempty, hinvariant⟩,
      fun U hU => Set.sInter_subset_of_mem hU⟩
  obtain ⟨M, _hMroot, hM⟩ := zorn_superset_nonempty family hchains (orbitClosure c) hroot
  obtain ⟨hsub, hclosed, hnonempty, hinvariant⟩ := hM.prop
  refine ⟨M, hsub, hclosed, hnonempty, hinvariant, ?_⟩
  intro S hSM hSclosed hSne hSinvariant
  exact hM.eq_of_subset ⟨hSM.trans hsub, hSclosed, hSne, hSinvariant⟩ hSM

-- the selected point has exactly the same orbit closure as every point in its own closure.
theorem exists_orbit_minimal_configuration {A : Type*} [TopologicalSpace A]
    [DiscreteTopology A] (c : Site → A) (hc : (Set.range c).Finite) :
    ∃ d ∈ orbitClosure c, ∀ x ∈ orbitClosure d, orbitClosure x = orbitClosure d := by
  obtain ⟨M, hsub, hclosed, hne, hinvariant, hminimal⟩ :=
    exists_minimal_closed_invariant_orbit_subset c hc
  obtain ⟨d, hd⟩ := hne
  have hclosure (x : Site → A) (hx : x ∈ M) : orbitClosure x = M := by
    exact hminimal (orbitClosure x) (orbitClosure_subset_closed_invariant M hclosed hinvariant x hx)
      isClosed_closure ⟨x, mem_own_orbitClosure x⟩ (orbitClosure_shift_invariant x)
  have hdM := hclosure d hd
  refine ⟨d, hsub hd, ?_⟩
  intro x hx
  exact (hclosure x (hdM ▸ hx)).trans hdM.symm

end KumarNivat
