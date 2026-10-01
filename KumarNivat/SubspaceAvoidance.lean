import Mathlib.Algebra.Module.Submodule.Union

namespace KumarNivat

-- use mathlib's finite-subspace avoidance theorem for the paper's coefficient space.
theorem exists_outside_finite_subspaces {K V : Type*} [Field K] [Infinite K]
    [AddCommGroup V] [Module K V] (s : Finset (Submodule K V))
    (hproper : ∀ U ∈ s, U ≠ ⊤) : ∃ g : V, ∀ U ∈ s, g ∉ U := by
  obtain ⟨g, hg⟩ := Submodule.exists_forall_notMem_of_forall_ne_top
    (fun U : s => U.val) (fun U => hproper U.val U.property)
  exact ⟨g, fun U hU => hg ⟨U, hU⟩⟩

end KumarNivat
