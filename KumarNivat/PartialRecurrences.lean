import KumarNivat.LineRecurrence

namespace KumarNivat

-- a facet recurrence is required only when its whole consecutive stencil fits on the facet.
def IntervalRecurrence {K : Type*} [CommRing K] (t : ℕ) (α : Fin (t + 1) → K)
    (a : ℤ → K) (b N : ℤ) : Prop :=
  ∀ n : ℤ, b ≤ n → n + (t : ℤ) ≤ N → ∑ i : Fin (t + 1), α i * a (n + (i.val : ℤ)) = 0

-- only prefix points inside the finite facet need seed values.
theorem zero_of_interval_recurrence_truncated_prefix {K : Type*} [CommRing K] [NoZeroDivisors K]
    (t : ℕ) (α : Fin (t + 1) → K) (a : ℤ → K) (b N : ℤ)
    (hlast : α (Fin.last t) ≠ 0) (hrec : IntervalRecurrence t α a b N)
    (hprefix : ∀ i : Fin t, b + (i.val : ℤ) ≤ N → a (b + (i.val : ℤ)) = 0) :
    ∀ n : ℤ, b ≤ n → n ≤ N → a n = 0 := by
  have hforward (n : ℕ) : b + (n : ℤ) ≤ N → a (b + (n : ℤ)) = 0 := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      by_cases hnt : n < t
      · exact hprefix ⟨n, hnt⟩ hn
      · have htn : t ≤ n := by omega
        let base : ℤ := b + ((n - t : ℕ) : ℤ)
        have hsmall : ∑ i : Fin t, α i.castSucc * a (base + (i.castSucc.val : ℤ)) = 0 := by
          apply Finset.sum_eq_zero
          intro i _hi
          have hindex : n - t + i.val < n := by have hi := i.isLt; omega
          have hsite : base + (i.castSucc.val : ℤ) = b + ((n - t + i.val : ℕ) : ℤ) := by
            dsimp [base]
            omega
          have hfit : b + ((n - t + i.val : ℕ) : ℤ) ≤ N := by omega
          rw [hsite, ih _ hindex hfit, mul_zero]
        have hsite : base + (t : ℤ) = b + (n : ℤ) := by dsimp [base]; omega
        have he := hrec base (by dsimp [base]; omega) (by rw [hsite]; exact hn)
        rw [Fin.sum_univ_castSucc, hsmall, zero_add] at he
        simp only [Fin.val_last, hsite] at he
        exact (mul_eq_zero.mp he).resolve_left hlast
  intro n hn hN
  have he : b + (((n - b).toNat : ℕ) : ℤ) = n := by omega
  rw [← he]
  exact hforward (n - b).toNat (by rw [he]; exact hN)

-- a full degree-length zero seed is a convenient special case of the truncated seed.
theorem zero_of_interval_recurrence_prefix {K : Type*} [CommRing K] [NoZeroDivisors K]
    (t : ℕ) (α : Fin (t + 1) → K) (a : ℤ → K) (b N : ℤ)
    (hlast : α (Fin.last t) ≠ 0) (hrec : IntervalRecurrence t α a b N)
    (hprefix : ∀ i : Fin t, a (b + (i.val : ℤ)) = 0) :
    ∀ n : ℤ, b ≤ n → n ≤ N → a n = 0 :=
  zero_of_interval_recurrence_truncated_prefix t α a b N hlast hrec (fun i _hi => hprefix i)

-- a ray admits every forward recurrence whose first input is on the ray.
def RayRecurrence {K : Type*} [CommRing K] (t : ℕ) (α : Fin (t + 1) → K)
    (a : ℤ → K) (b : ℤ) : Prop :=
  ∀ n : ℤ, b ≤ n → ∑ i : Fin (t + 1), α i * a (n + (i.val : ℤ)) = 0

-- the first nonzero coefficient propagates a zero tail backwards through the entire ray.
theorem zero_of_ray_recurrence_tail {K : Type*} [CommRing K] [NoZeroDivisors K]
    (t : ℕ) (α : Fin (t + 1) → K) (a : ℤ → K) (b B : ℤ)
    (hfirst : α 0 ≠ 0) (hrec : RayRecurrence t α a b)
    (htail : ∀ n : ℤ, B ≤ n → a n = 0) : ∀ n : ℤ, b ≤ n → a n = 0 := by
  by_cases hBb : B ≤ b
  · exact fun n hn => htail n (hBb.trans hn)
  have hbB : b ≤ B := by omega
  let N := (B - b).toNat
  have hN : B - (N : ℤ) = b := by dsimp [N]; omega
  have hback (k : ℕ) : k ≤ N → ∀ n : ℤ, B - (k : ℤ) ≤ n → a n = 0 := by
    induction k with
    | zero => intro _hk; simpa only [Nat.cast_zero, sub_zero] using htail
    | succ k ih =>
      intro hk
      let base : ℤ := B - (k : ℤ) - 1
      have hkN : k ≤ N := by omega
      have hbase : b ≤ base := by dsimp [base]; omega
      have hsmall : ∑ i : Fin t, α i.succ * a (base + (i.succ.val : ℤ)) = 0 := by
        apply Finset.sum_eq_zero
        intro i _hi
        have hbound : B - (k : ℤ) ≤ base + (i.succ.val : ℤ) := by dsimp [base]; omega
        rw [ih hkN _ hbound, mul_zero]
      have he := hrec base hbase
      rw [Fin.sum_univ_succ, hsmall] at he
      simp only [Fin.val_zero, Nat.cast_zero, add_zero] at he
      have hz : a base = 0 := (mul_eq_zero.mp he).resolve_left hfirst
      intro n hn
      by_cases hne : n = base
      · rw [hne]
        exact hz
      · apply ih hkN
        dsimp [base] at hne
        omega
  intro n hn
  exact hback N le_rfl n (by rw [hN]; exact hn)

end KumarNivat
