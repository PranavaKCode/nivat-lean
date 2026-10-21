module

public import KumarNivat.LaurentAlgebra
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Instances.Discrete
public import Mathlib.Topology.Closure

@[expose] public section

namespace KumarNivat

-- this is the actual closure in the product topology, not an extra recurrence assumption.
def orbitClosure {A : Type*} [TopologicalSpace A] (c : Site → A) : Set (Site → A) :=
  closure (Set.range (fun h : Site => shift h c))

-- finite-pattern inheritance records exactly what the closure argument must establish.
def LanguageContained {A : Type*} (x c : Site → A) : Prop :=
  ∀ D : Finset Site, ∀ g : Site, ∃ t : Site, ∀ u ∈ D, x (g + u) = c (t + u)

-- every finite cylinder around an orbit-closure point meets a translate of the original array.
theorem languageContained_of_mem_orbitClosure {A : Type*} [TopologicalSpace A] [DiscreteTopology A]
    (c x : Site → A) (hx : x ∈ orbitClosure c) : LanguageContained x c := by
  intro D g
  let cylinder : Set (Site → A) := {y | ∀ u : D, y (g + u.val) = x (g + u.val)}
  have hcylinder : IsOpen cylinder := by
    change IsOpen {y : Site → A | ∀ u : D, y (g + u.val) = x (g + u.val)}
    simp only [Set.ofPred_forall]
    apply isOpen_iInter_of_finite
    intro u
    have heval : Continuous (fun y : Site → A => y (g + u.val)) := continuous_apply _
    exact (isOpen_discrete {x (g + u.val)}).preimage heval
  have hxcylinder : x ∈ cylinder := fun _ => rfl
  obtain ⟨y, hy, t, hyt⟩ := mem_closure_iff.mp hx cylinder hcylinder hxcylinder
  subst y
  refine ⟨g + t, ?_⟩
  intro u hu
  have he := (hy ⟨u, hu⟩).symm
  simpa [shift, add_assoc, add_comm, add_left_comm] using he

-- inherited language implies inclusion of each full occurring-pattern set.
theorem patterns_subset_of_language {A : Type*} (x c : Site → A)
    (hlang : LanguageContained x c) (D : Finset Site) : patterns x D ⊆ patterns c D := by
  rintro p ⟨g, rfl⟩
  obtain ⟨t, ht⟩ := hlang D g
  refine ⟨t, ?_⟩
  funext u
  exact (ht u.val u.property).symm

-- pattern counts cannot increase when passing to a point with inherited language.
theorem complexity_le_of_language {A : Type*} (x c : Site → A)
    (hc : (Set.range c).Finite) (hlang : LanguageContained x c) (D : Finset Site) :
    complexity x D ≤ complexity c D := by
  unfold complexity
  exact Set.ncard_le_ncard (patterns_subset_of_language x c hlang D)
    (patterns_finite_of_range c hc D)

-- the selected point remains finitary over the same original symbols.
theorem finite_range_of_language {A : Type*} (x c : Site → A)
    (hc : (Set.range c).Finite) (hlang : LanguageContained x c) : (Set.range x).Finite := by
  apply hc.subset
  rintro y ⟨g, rfl⟩
  obtain ⟨t, ht⟩ := hlang {0} g
  have he := ht 0 (Finset.mem_singleton_self 0)
  simp only [add_zero] at he
  exact ⟨t, he.symm⟩

-- every finite stencil identity passes to the same selected orbit point.
theorem annihilator_inherited_of_language {K : Type*} [CommRing K]
    (x c : Site → K) (hlang : LanguageContained x c) (f : Stencil K)
    (hann : ∀ g, act f c g = 0) : ∀ g, act f x g = 0 := by
  intro g
  obtain ⟨t, ht⟩ := hlang f.support g
  calc
    act f x g = act f c t := by
      unfold act Finsupp.sum
      apply Finset.sum_congr rfl
      intro u hu
      change f u * x (g + u) = f u * c (t + u)
      rw [ht u hu]
    _ = 0 := hann t

-- this is the closure-to-configuration inheritance used in the final contradiction.
theorem orbitClosure_inheritance {K : Type*} [CommRing K] [TopologicalSpace K] [DiscreteTopology K]
    (c x : Site → K) (hc : (Set.range c).Finite) (hx : x ∈ orbitClosure c)
    (f : Stencil K) (hann : ∀ g, act f c g = 0) :
    (Set.range x).Finite ∧ (∀ D : Finset Site, complexity x D ≤ complexity c D) ∧
      (∀ g, act f x g = 0) := by
  have hlang := languageContained_of_mem_orbitClosure c x hx
  exact ⟨finite_range_of_language x c hc hlang,
    fun D => complexity_le_of_language x c hc hlang D,
    annihilator_inherited_of_language x c hlang f hann⟩

end KumarNivat
