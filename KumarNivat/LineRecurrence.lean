import KumarNivat.Operators
import Mathlib.Algebra.BigOperators.Fin

namespace KumarNivat

-- a line polynomial gives a reversible scalar recurrence of its primitive degree.
def LineRecurrence {K : Type*} [CommRing K] (t : ℕ) (α : Fin (t + 1) → K)
    (a : ℤ → K) : Prop :=
  ∀ n : ℤ, ∑ i : Fin (t + 1), α i * a (n + (i.val : ℤ)) = 0

-- t consecutive zeros propagate in both directions when the two endpoint coefficients are nonzero.
theorem zero_of_reversible_recurrence_block {K : Type*} [Field K]
    (t : ℕ) (α : Fin (t + 1) → K) (a : ℤ → K)
    (hfirst : α 0 ≠ 0) (hlast : α (Fin.last t) ≠ 0)
    (hrec : LineRecurrence t α a) (b : ℤ)
    (hblock : ∀ i : Fin t, a (b + (i.val : ℤ)) = 0) : ∀ n : ℤ, a n = 0 := by
  have hforward (n : ℕ) : a (b + (n : ℤ)) = 0 := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hnt : n < t
      · exact hblock ⟨n, hnt⟩
      · have htn : t ≤ n := by omega
        let base : ℤ := b + ((n - t : ℕ) : ℤ)
        have hsmall : ∑ i : Fin t, α i.castSucc * a (base + (i.castSucc.val : ℤ)) = 0 := by
          apply Finset.sum_eq_zero
          intro i hi
          have hindex : n - t + i.val < n := by have := i.isLt; omega
          have hsite : base + (i.castSucc.val : ℤ) = b + ((n - t + i.val : ℕ) : ℤ) := by
            dsimp [base]
            omega
          rw [hsite, ih (n - t + i.val) hindex, mul_zero]
        have he := hrec base
        rw [Fin.sum_univ_castSucc, hsmall, zero_add] at he
        have hsite : base + ((Fin.last t).val : ℤ) = b + (n : ℤ) := by
          dsimp [base]
          omega
        rw [hsite] at he
        exact (mul_eq_zero.mp he).resolve_left hlast
  have htail (n : ℕ) : ∀ j : ℤ, b - (n : ℤ) ≤ j → a j = 0 := by
    induction n with
    | zero =>
      intro j hj
      have hrepr : b + (((j - b).toNat : ℕ) : ℤ) = j := by omega
      rw [← hrepr]
      exact hforward (j - b).toNat
    | succ n ih =>
      let base : ℤ := b - (n : ℤ) - 1
      have hsmall : ∑ i : Fin t, α i.succ * a (base + (i.succ.val : ℤ)) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        have hbound : b - (n : ℤ) ≤ base + (i.succ.val : ℤ) := by
          dsimp [base]
          omega
        rw [ih _ hbound, mul_zero]
      have he := hrec base
      rw [Fin.sum_univ_succ, hsmall] at he
      simp only [Fin.val_zero, Nat.cast_zero, add_zero] at he
      have hbase : a base = 0 := (mul_eq_zero.mp he).resolve_left hfirst
      intro j hj
      by_cases hje : j = base
      · rw [hje]
        exact hbase
      · apply ih
        dsimp [base] at hje
        omega
  intro n
  exact htail (b - n).toNat n (by omega)

-- a nonzero recurrent line has a nonzero value in every block of the factor degree.
theorem exists_nonzero_recurrence_block {K : Type*} [Field K]
    (t : ℕ) (α : Fin (t + 1) → K) (a : ℤ → K)
    (hfirst : α 0 ≠ 0) (hlast : α (Fin.last t) ≠ 0)
    (hrec : LineRecurrence t α a) (hne : ∃ n : ℤ, a n ≠ 0) (b : ℤ) :
    ∃ i : Fin t, a (b + (i.val : ℤ)) ≠ 0 := by
  by_contra hn
  have hblock : ∀ i : Fin t, a (b + (i.val : ℤ)) = 0 := by
    intro i
    by_contra hi
    exact hn ⟨i, hi⟩
  have hall := zero_of_reversible_recurrence_block t α a hfirst hlast hrec b hblock
  obtain ⟨n, hn⟩ := hne
  exact hn (hall n)

end KumarNivat
