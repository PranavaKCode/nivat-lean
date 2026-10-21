module

public import Mathlib.Data.Set.Card
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Finset.Prod
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Data.Fintype.Pi

@[expose] public section

namespace KumarNivat

universe u

-- the domain is the full integer lattice.
abbrev Site := ℤ × ℤ

-- patterns use the original axis-aligned rectangle.
def rectangle (k n : ℕ) : Finset Site :=
  (Finset.Ico (0 : ℤ) (k : ℤ)).product (Finset.Ico (0 : ℤ) (n : ℤ))

-- each translation contributes a function, so repeated patterns count once.
def patterns {A : Type*} (c : Site → A) (D : Finset Site) : Set (D → A) :=
  Set.range (fun g : Site => fun u : D => c (g + u.val))

-- finite alphabets make this natural cardinality an actual pattern count.
noncomputable def complexity {A : Type*} (c : Site → A) (D : Finset Site) : ℕ :=
  (patterns c D).ncard

-- this proposition is theorem 1.1, with no recurrence or decomposition assumption.
def FullNivat : Prop :=
  ∀ (A : Type u) [Finite A] (c : Site → A),
    (∃ k n : ℕ, 0 < k ∧ 0 < n ∧ complexity c (rectangle k n) ≤ k * n) →
      ∃ h : Site, h ≠ (0, 0) ∧ ∀ g : Site, c (g + h) = c g

-- the pattern set cannot be infinite under the intended alphabet hypothesis.
theorem patterns_finite {A : Type*} [Finite A] (c : Site → A) (D : Finset Site) :
    (patterns c D).Finite := Set.toFinite _

-- expanding the statement confirms every quantifier and the counting convention.
theorem fullNivat_iff_explicit : FullNivat.{u} ↔
    ∀ (A : Type u) [Finite A] (c : (ℤ × ℤ) → A),
      (∃ k n : ℕ, 0 < k ∧ 0 < n ∧
        (Set.range (fun g : ℤ × ℤ =>
          fun u : (Finset.Ico (0 : ℤ) (k : ℤ)).product
            (Finset.Ico (0 : ℤ) (n : ℤ)) => c (g + u.val))).ncard ≤ k * n) →
          ∃ h : ℤ × ℤ, h ≠ (0, 0) ∧ ∀ g : ℤ × ℤ, c (g + h) = c g := Iff.rfl

end KumarNivat
