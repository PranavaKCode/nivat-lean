module

public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Set.Card
public import Lean.Elab.Tactic.Omega

@[expose] public section

namespace KumarNivat

-- reduction modulo a positive period lists every letter in the initial period block.
theorem periodic_integer_word_range_eq_initial_block {A : Type*} (a : ℤ → A)
    (p : ℕ) (hp : 0 < p) (hper : Function.Periodic a (p : ℤ)) :
    Set.range a = (fun j : Fin p => a (j.val : ℤ)) '' Set.univ := by
  apply Set.Subset.antisymm
  · rintro _ ⟨n, rfl⟩
    let i : ℤ := n % (p : ℤ)
    have hi₀ : 0 ≤ i := Int.emod_nonneg _ (by omega : (p : ℤ) ≠ 0)
    have hip : i < (p : ℤ) := Int.emod_lt_of_pos _ (by omega)
    let j : Fin p := ⟨i.toNat, by omega⟩
    have hj : (j.val : ℤ) = i := by dsimp [j]; omega
    have hn : n = (j.val : ℤ) + (n / (p : ℤ)) * (p : ℤ) := by
      have he := Int.emod_add_ediv_mul n (p : ℤ)
      change i + (n / (p : ℤ)) * (p : ℤ) = n at he
      omega
    refine ⟨j, Set.mem_univ _, ?_⟩
    rw [hn]
    exact (hper.int_mul (n / (p : ℤ)) (j.val : ℤ)).symm
  · rintro _ ⟨j, _hj, rfl⟩
    exact ⟨(j.val : ℤ), rfl⟩

-- a periodic integer word has at most one period's worth of distinct letters.
theorem periodic_integer_word_range_finite_card_le {A : Type*} (a : ℤ → A)
    (p : ℕ) (hp : 0 < p) (hper : Function.Periodic a (p : ℤ)) :
    (Set.range a).Finite ∧ (Set.range a).ncard ≤ p := by
  rw [periodic_integer_word_range_eq_initial_block a p hp hper]
  refine ⟨(Set.finite_univ : (Set.univ : Set (Fin p)).Finite).image _, ?_⟩
  have hcard := Set.ncard_image_le (f := fun j : Fin p => a (j.val : ℤ))
    (Set.finite_univ : (Set.univ : Set (Fin p)).Finite)
  simpa only [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] using hcard

-- one full period's worth of equal letters makes a displacement a global word period.
theorem period_of_equal_block_in_short_periodic_word {A : Type*} (a : ℤ → A)
    (p r : ℕ) (hp : 0 < p) (hpr : p ≤ r) (hper : Function.Periodic a (p : ℤ))
    (b q : ℤ) (hblock : ∀ j : Fin r, a (b + (j.val : ℤ) + q) = a (b + (j.val : ℤ))) :
    Function.Periodic a q := by
  intro n
  let P : ℤ := (p : ℤ)
  let i : ℤ := (n - b) % P
  let d : ℤ := (n - b) / P
  have hP : 0 < P := by dsimp [P]; exact_mod_cast hp
  have hi₀ : 0 ≤ i := Int.emod_nonneg _ (by omega : P ≠ 0)
  have hiP : i < P := Int.emod_lt_of_pos _ hP
  let j : Fin r := ⟨i.toNat, by dsimp [P] at hiP; omega⟩
  have hj : (j.val : ℤ) = i := by dsimp [j]; omega
  have hrep : n = b + i + d * P := by
    have h := Int.emod_add_mul_ediv (n - b) P
    change i + P * d = n - b at h
    rw [mul_comm P d] at h
    omega
  have hn : a n = a (b + i) := by
    rw [hrep]
    exact hper.int_mul d (b + i)
  have hnq : a (n + q) = a (b + i + q) := by
    have hrepq : n + q = (b + i + q) + d * P := by rw [hrep]; omega
    rw [hrepq]
    exact hper.int_mul d (b + i + q)
  have hseed : a (b + i + q) = a (b + i) := by
    simpa only [hj] using hblock j
  exact hnq.trans (hseed.trans hn.symm)

end KumarNivat
