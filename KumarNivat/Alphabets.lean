import KumarNivat.Operators
import Mathlib.Data.Fintype.EquivFin

namespace KumarNivat

-- relabeling commutes with restriction to every translated window.
theorem patterns_map {A B : Type*} (c : Site → A) (f : A → B) (D : Finset Site) :
    patterns (fun g => f (c g)) D =
      (fun p : D → A => fun u => f (p u)) '' patterns c D := by
  ext p
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨fun u => c (g + u.val), ⟨g, rfl⟩, rfl⟩
  · rintro ⟨q, ⟨g, rfl⟩, rfl⟩
    exact ⟨g, rfl⟩

-- an injective alphabet change preserves the exact pattern count, including equality.
theorem complexity_map_injective {A B : Type*} (c : Site → A) (f : A → B)
    (hf : Function.Injective f) (D : Finset Site) :
    complexity (fun g => f (c g)) D = complexity c D := by
  unfold complexity
  rw [patterns_map]
  apply Set.ncard_image_of_injective
  intro p q hpq
  funext u
  exact hf (congrFun hpq u)

-- every individual period is preserved by the same injective labeling.
theorem isPeriod_map_injective {A B : Type*} (c : Site → A) (f : A → B)
    (hf : Function.Injective f) (h : Site) :
    IsPeriod (fun g => f (c g)) h ↔ IsPeriod c h := by
  constructor
  · intro hp g
    exact hf (hp g)
  · intro hp g
    exact congrArg f (hp g)

-- finite alphabets have integer labels in every universe.
theorem exists_integer_label (A : Type*) [Finite A] : ∃ f : A → ℤ, Function.Injective f := by
  classical
  let : Fintype A := Fintype.ofFinite A
  refine ⟨fun a => ((Fintype.equivFin A a).val : ℤ), ?_⟩
  intro a b hab
  change ((Fintype.equivFin A a).val : ℤ) = ((Fintype.equivFin A b).val : ℤ) at hab
  apply (Fintype.equivFin A).injective
  apply Fin.ext
  exact_mod_cast hab

-- section 1's integer encoding preserves all windows and all period vectors simultaneously.
theorem exists_integer_model {A : Type*} [Finite A] (c : Site → A) :
    ∃ d : Site → ℤ, (Set.range d).Finite ∧
      (∀ D : Finset Site, complexity d D = complexity c D) ∧
      (∀ h : Site, IsPeriod d h ↔ IsPeriod c h) := by
  obtain ⟨f, hf⟩ := exists_integer_label A
  refine ⟨fun g => f (c g), ?_, fun D => complexity_map_injective c f hf D,
    fun h => isPeriod_map_injective c f hf h⟩
  exact (Set.toFinite (Set.range c)).image f |>.subset (by
    rintro x ⟨g, rfl⟩
    exact ⟨c g, ⟨g, rfl⟩, rfl⟩)

end KumarNivat
