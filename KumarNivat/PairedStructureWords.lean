import KumarNivat.WordComplexity

namespace KumarNivat

-- predecessor uniqueness on a finite bilateral word language would force a global period.
theorem nonperiodic_word_has_predecessor_branch {A : Type*} (a : ℤ → A)
    (ha : (Set.range a).Finite)
    (hnoper : ¬ ∃ p : ℕ, 0 < p ∧ Function.Periodic a (p : ℤ))
    (r : ℕ) (hr : 0 < r) :
    ∃ i j : ℤ, sequenceWord a r i = sequenceWord a r j ∧ a (i - 1) ≠ a (j - 1) := by
  classical
  by_contra! hnone
  have hprev (i j : ℤ) (he : sequenceWord a r i = sequenceWord a r j) :
      sequenceWord a r (i - 1) = sequenceWord a r (j - 1) := by
    funext k
    by_cases hk : k.val = 0
    · simpa only [sequenceWord, hk, Nat.cast_zero, add_zero] using hnone i j he
    · let t : Fin r := ⟨k.val - 1, by have := k.isLt; omega⟩
      have hletter := congrFun he t
      have hi : i - 1 + (k.val : ℤ) = i + (t.val : ℤ) := by dsimp [t]; omega
      have hj : j - 1 + (k.val : ℤ) = j + (t.val : ℤ) := by dsimp [t]; omega
      simpa only [sequenceWord, hi, hj] using hletter
  let state : ℤ → (Fin r → A) := fun n => sequenceWord a r (-n)
  have hfinite : (Set.range state).Finite := by
    apply (sequenceWord_range_finite a ha r).subset
    rintro _ ⟨n, rfl⟩
    exact ⟨-n, rfl⟩
  have hnext (i j : ℤ) (he : state i = state j) : state (i + 1) = state (j + 1) := by
    have hstep := hprev (-i) (-j) he
    simpa only [state, neg_add, sub_eq_add_neg] using hstep
  obtain ⟨p, hp, _hbound, hperiod⟩ := bounded_period_of_bilateral_determinism state hfinite hnext
  have hback (n : ℤ) : a (n - (p : ℤ)) = a n := by
    have he := congrFun (hperiod (-n)) (⟨0, hr⟩ : Fin r)
    simpa [state, sequenceWord, neg_add, sub_eq_add_neg, add_comm] using he
  apply hnoper
  refine ⟨p, hp, ?_⟩
  intro n
  simpa only [add_sub_cancel_right] using (hback (n + (p : ℤ))).symm

-- successor uniqueness gives the same obstruction in the opposite orientation.
theorem nonperiodic_word_has_successor_branch {A : Type*} (a : ℤ → A)
    (ha : (Set.range a).Finite)
    (hnoper : ¬ ∃ p : ℕ, 0 < p ∧ Function.Periodic a (p : ℤ))
    (r : ℕ) (hr : 0 < r) :
    ∃ i j : ℤ, sequenceWord a r i = sequenceWord a r j ∧ a (i + (r : ℤ)) ≠ a (j + (r : ℤ)) := by
  classical
  by_contra! hnone
  have hnext (i j : ℤ) (he : sequenceWord a r i = sequenceWord a r j) :
      sequenceWord a r (i + 1) = sequenceWord a r (j + 1) := by
    funext k
    by_cases hk : k.val + 1 < r
    · have hletter := congrFun he (⟨k.val + 1, hk⟩ : Fin r)
      simpa [sequenceWord, add_assoc, add_comm, add_left_comm] using hletter
    · have hk' : k.val + 1 = r := by have := k.isLt; omega
      have hi : i + 1 + (k.val : ℤ) = i + (r : ℤ) := by omega
      have hj : j + 1 + (k.val : ℤ) = j + (r : ℤ) := by omega
      simpa only [sequenceWord, hi, hj] using hnone i j he
  obtain ⟨p, hp, _hbound, hperiod⟩ := bounded_period_of_bilateral_determinism
    (sequenceWord a r) (sequenceWord_range_finite a ha r) hnext
  apply hnoper
  refine ⟨p, hp, ?_⟩
  intro n
  have he := congrFun (hperiod n) (⟨0, hr⟩ : Fin r)
  simpa only [sequenceWord, Fin.val_mk, Nat.cast_zero, add_zero] using he

end KumarNivat
