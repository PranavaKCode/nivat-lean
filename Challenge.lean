module

public import Mathlib.Data.Set.Card
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Finset.Prod
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Data.Fintype.Pi

public section

/-!
# full nivat conjecture

this is the independent statement surface, using only canonical mathlib notions.
the private declaration below is an intentionally unproved specification stub,
not a proof of the conjecture. the public theorem presents that specification in
the declaration form required by comparator. the solution module independently
proves the same theorem and never imports this module or its private stub.
-/

namespace PalomarNivat

universe u

-- this statement-only placeholder belongs solely to the independent challenge.
private axiom nivat_statement_stub :
    ∀ (A : Type u) [Finite A] (c : (ℤ × ℤ) → A),
      (∃ k n : ℕ, 0 < k ∧ 0 < n ∧
        (Set.range (fun g : ℤ × ℤ =>
          fun v : (Finset.Ico (0 : ℤ) (k : ℤ)).product
            (Finset.Ico (0 : ℤ) (n : ℤ)) => c (g + v.val))).ncard ≤ k * n) →
        ∃ h : ℤ × ℤ, h ≠ (0, 0) ∧ ∀ g : ℤ × ℤ, c (g + h) = c g

/-- every finite-alphabet array with at most its rectangular area in occurring patterns has a nonzero global period. -/
theorem nivat :
    ∀ (A : Type u) [Finite A] (c : (ℤ × ℤ) → A),
      (∃ k n : ℕ, 0 < k ∧ 0 < n ∧
        (Set.range (fun g : ℤ × ℤ =>
          fun v : (Finset.Ico (0 : ℤ) (k : ℤ)).product
            (Finset.Ico (0 : ℤ) (n : ℤ)) => c (g + v.val))).ncard ≤ k * n) →
        ∃ h : ℤ × ℤ, h ≠ (0, 0) ∧ ∀ g : ℤ × ℤ, c (g + h) = c g :=
  nivat_statement_stub

end PalomarNivat
