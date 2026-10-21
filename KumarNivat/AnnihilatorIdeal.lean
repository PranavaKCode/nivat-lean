module

public import KumarNivat.LaurentMaps
public import KumarNivat.SubspaceAvoidance
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.Algebra.Module.Submodule.RestrictScalars

@[expose] public section

namespace KumarNivat

-- finite convolution annihilators form an actual ideal of the laurent ring.
noncomputable def annihilatorIdeal {K : Type*} [CommRing K] (c : Site → K) : Ideal (Laurent K) where
  carrier := {f | laurentAct f c = 0}
  zero_mem' := laurentAct_zero c
  add_mem' := by
    intro f g hf hg
    change laurentAct (f + g) c = 0
    rw [laurentAct_add, hf, hg, add_zero]
  smul_mem' := by
    intro f g hg
    change laurentAct (f * g) c = 0
    rw [laurentAct_mul, hg, laurentAct_config_zero]

-- ideal membership is the manuscript's annihilation identity without a change of action.
@[simp] theorem mem_annihilatorIdeal {K : Type*} [CommRing K] (c : Site → K) (f : Laurent K) :
    f ∈ annihilatorIdeal c ↔ laurentAct f c = 0 := Iff.rfl

-- divisibility by each omitted factor cuts out a proper subspace inside the annihilator ideal.
theorem exists_annihilator_avoiding_factors {K : Type*} [Field K] [Infinite K]
    (c : Site → K) (S : Finset (Laurent K))
    (hwitness : ∀ p ∈ S, ∃ f : Laurent K, laurentAct f c = 0 ∧ ¬ p ∣ f) :
    ∃ g : Laurent K, laurentAct g c = 0 ∧ ∀ p ∈ S, ¬ p ∣ g := by
  classical
  let I : Submodule K (Laurent K) := (annihilatorIdeal c).restrictScalars K
  let bad (p : S) : Submodule K I :=
    ((Ideal.span ({p.val} : Set (Laurent K))).restrictScalars K).comap I.subtype
  have hproper (p : S) : bad p ≠ ⊤ := by
    intro hp
    obtain ⟨f, hf, hnot⟩ := hwitness p.val p.property
    let fI : I := ⟨f, hf⟩
    have hmem : fI ∈ bad p := by rw [hp]; trivial
    have hdiv : p.val ∣ f := Ideal.mem_span_singleton.mp hmem
    exact hnot hdiv
  obtain ⟨g, hg⟩ := Submodule.exists_forall_notMem_of_forall_ne_top bad hproper
  refine ⟨g.val, g.property, ?_⟩
  intro p hp hdiv
  apply hg ⟨p, hp⟩
  exact Ideal.mem_span_singleton.mpr hdiv

end KumarNivat
