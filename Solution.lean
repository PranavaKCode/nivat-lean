module

public import KumarNivat.Nivat

public section

/-!
# full nivat conjecture proof

the statement below is identical to the independently stated challenge.
its proof uses the original manuscript formalization, without importing the
challenge module or its unproved statement-only placeholder.
-/

namespace PalomarNivat

universe u

/-- the full finite-alphabet conjecture follows from the completed manuscript formalization. -/
theorem nivat :
    ∀ (A : Type u) [Finite A] (c : (ℤ × ℤ) → A),
      (∃ k n : ℕ, 0 < k ∧ 0 < n ∧
        (Set.range (fun g : ℤ × ℤ =>
          fun v : (Finset.Ico (0 : ℤ) (k : ℤ)).product
            (Finset.Ico (0 : ℤ) (n : ℤ)) => c (g + v.val))).ncard ≤ k * n) →
        ∃ h : ℤ × ℤ, h ≠ (0, 0) ∧ ∀ g : ℤ × ℤ, c (g + h) = c g := by
  exact KumarNivat.nivat

end PalomarNivat
