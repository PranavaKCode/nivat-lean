import KumarNivat

universe u

-- the requested endpoint is the full conjecture, uniformly in the alphabet universe.
example : KumarNivat.FullNivat.{u} := KumarNivat.nivat

-- the expanded acceptance statement checks all translations, the equality threshold and an original global period.
example (A : Type u) [Finite A] (c : (ℤ × ℤ) → A)
    (hlow : ∃ k n : ℕ, 0 < k ∧ 0 < n ∧
      (Set.range (fun g : ℤ × ℤ =>
        fun v : (Finset.Ico (0 : ℤ) (k : ℤ)).product
          (Finset.Ico (0 : ℤ) (n : ℤ)) => c (g + v.val))).ncard ≤ k * n) :
    ∃ h : ℤ × ℤ, h ≠ (0, 0) ∧ ∀ g : ℤ × ℤ, c (g + h) = c g :=
  KumarNivat.nivat A c hlow

#print axioms KumarNivat.nivat
