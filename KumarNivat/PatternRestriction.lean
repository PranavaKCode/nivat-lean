import KumarNivat.AffineDependence

namespace KumarNivat

-- restriction keeps the original lattice positions of a smaller observation window.
def restrictPattern {A : Type*} (S T : Finset Site) (hTS : T ⊆ S)
    (p : S → A) (u : T) : A := p ⟨u.val, hTS u.property⟩

-- every occurring smaller pattern is the restriction of an occurring larger pattern.
theorem patterns_restriction_image {A : Type*} (c : Site → A)
    (S T : Finset Site) (hTS : T ⊆ S) :
    patterns c T = restrictPattern S T hTS '' patterns c S := by
  ext p
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨fun u => c (g + u.val), ⟨g, rfl⟩, rfl⟩
  · rintro ⟨q, ⟨g, rfl⟩, rfl⟩
    exact ⟨g, rfl⟩

-- observing fewer sites cannot increase the number of occurring patterns.
theorem complexity_mono_window {A : Type*} (c : Site → A) (hc : (Set.range c).Finite)
    (S T : Finset Site) (hTS : T ⊆ S) : complexity c T ≤ complexity c S := by
  unfold complexity
  rw [patterns_restriction_image c S T hTS]
  exact Set.ncard_image_le (patterns_finite_of_range c hc S)

-- uniqueness concerns the actual occurring translated patterns, rather than arbitrary assignments.
def ExtensionUnique {A : Type*} (c : Site → A) (T S : Finset Site) : Prop :=
  ∀ g h : Site, (∀ u ∈ T, c (g + u) = c (h + u)) → ∀ u ∈ S, c (g + u) = c (h + u)

-- equal finite counts force the surjective restriction map to be injective.
theorem extensionUnique_of_equal_complexity {A : Type*}
    (c : Site → A) (hc : (Set.range c).Finite) (S T : Finset Site) (hTS : T ⊆ S)
    (hcount : complexity c T = complexity c S) : ExtensionUnique c T S := by
  have hinj : Set.InjOn (restrictPattern (A := A) S T hTS) (patterns c S) :=
    Set.injOn_of_ncard_image_eq (by
      rw [← patterns_restriction_image c S T hTS]
      exact hcount) (patterns_finite_of_range c hc S)
  intro g h hagree u hu
  have he := hinj (show (fun v : S => c (g + v.val)) ∈ patterns c S from ⟨g, rfl⟩)
    (show (fun v : S => c (h + v.val)) ∈ patterns c S from ⟨h, rfl⟩) (by
      funext v
      exact hagree v.val v.property)
  exact congrFun he ⟨u, hu⟩

-- deleting a generated site retains enough information to determine its value.
def GeneratedSite {A : Type*} (c : Site → A) (S : Finset Site) (v : Site) : Prop :=
  ExtensionUnique c (S.erase v) S

-- an injective alphabet relabeling preserves uniqueness of every occurring extension.
theorem extensionUnique_map_injective {A B : Type*} (c : Site → A) (f : A → B)
    (hf : Function.Injective f) (T S : Finset Site) :
    ExtensionUnique (fun g => f (c g)) T S ↔ ExtensionUnique c T S := by
  constructor
  · intro hunique g h hagree u hu
    apply hf
    exact hunique g h (fun v hv => congrArg f (hagree v hv)) u hu
  · intro hunique g h hagree u hu
    exact congrArg f (hunique g h (fun v hv => hf (hagree v hv)) u hu)

-- discrepancy is integer-valued so the equality threshold remains visible under deletion.
noncomputable def discrepancy {A : Type*} (c : Site → A) (S : Finset Site) : ℤ :=
  (complexity c S : ℤ) - (S.card : ℤ)

end KumarNivat
