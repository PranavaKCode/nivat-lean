module

public import KumarNivat.RecurrenceEquality
public import KumarNivat.PeriodLattice
public import Mathlib.Data.Nat.Factorial.Basic

@[expose] public section

namespace KumarNivat

-- two equal recurrence states force a global period equal to their displacement.
theorem recurrence_period_of_equal_blocks {K : Type*} [Field K]
    (t : ℕ) (α : Fin (t + 1) → K) (a : ℤ → K)
    (hfirst : α 0 ≠ 0) (hlast : α (Fin.last t) ≠ 0)
    (hrec : LineRecurrence t α a) (i j : ℤ)
    (he : ∀ l : Fin t, a (i + (l.val : ℤ)) = a (j + (l.val : ℤ))) :
    ∀ n : ℤ, a (n + (j - i)) = a n := by
  have hall := recurrence_equal_of_block t α (fun n => a (n + j)) (fun n => a (n + i))
    hfirst hlast (hrec.translate j) (hrec.translate i) 0 (by
      intro l
      simpa [add_comm] using (he l).symm)
  intro n
  simpa only [show n - i + j = n + (j - i) by omega,
    show n - i + i = n by omega] using hall (n - i)

-- finite recurrence states give a positive period bounded by the number of possible states.
theorem bounded_period_of_finite_recurrence {K : Type*} [Field K]
    (t : ℕ) (α : Fin (t + 1) → K) (a : ℤ → K)
    (hfirst : α 0 ≠ 0) (hlast : α (Fin.last t) ≠ 0) (hrec : LineRecurrence t α a)
    (S : Set K) (hS : S.Finite) (hmem : ∀ n, a n ∈ S) :
    ∃ q : ℕ, 0 < q ∧ q ≤ S.ncard ^ t ∧ ∀ n : ℤ, a (n + (q : ℤ)) = a n := by
  classical
  let : Fintype S := hS.fintype
  let M := Fintype.card (Fin t → S)
  let state (m : Fin (M + 1)) : Fin t → S :=
    fun l => ⟨a ((m.val : ℤ) + (l.val : ℤ)), hmem _⟩
  obtain ⟨i, j, hij, he⟩ := Fintype.exists_ne_map_eq_of_card_lt state (by simp [M])
  have hex : ∃ i j : Fin (M + 1), i.val < j.val ∧ state i = state j := by
    by_cases hlt : i.val < j.val
    · exact ⟨i, j, hlt, he⟩
    · have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
      exact ⟨j, i, by omega, he.symm⟩
  obtain ⟨i, j, hij, he⟩ := hex
  have hblocks (l : Fin t) : a ((i.val : ℤ) + (l.val : ℤ)) =
      a ((j.val : ℤ) + (l.val : ℤ)) := congrArg Subtype.val (congrFun he l)
  have hp := recurrence_period_of_equal_blocks t α a hfirst hlast hrec i.val j.val hblocks
  have hcard : M = S.ncard ^ t := by
    simp only [M, Fintype.card_fun, Fintype.card_fin, Set.fintypeCard_eq_ncard]
  refine ⟨j.val - i.val, by omega, ?_, ?_⟩
  · rw [← hcard]
    have hj := j.isLt
    omega
  · intro n
    simpa only [Nat.cast_sub (by omega : i.val ≤ j.val)] using hp n

-- multiples of a scalar sequence period preserve every value.
theorem sequence_period_nat_multiple {A : Type*} (a : ℤ → A) (q : ℤ)
    (hp : ∀ n : ℤ, a (n + q) = a n) (r : ℕ) :
    ∀ n : ℤ, a (n + (r : ℤ) * q) = a n := by
  induction r with
  | zero => intro n; simp
  | succ r ih =>
    intro n
    rw [show n + ((r + 1 : ℕ) : ℤ) * q = (n + (r : ℤ) * q) + q by push_cast; ring,
      hp, ih]

-- the factorial of the common state bound is one period on all parallel lines at once.
theorem finite_range_recurrence_period {K : Type*} [Field K]
    (c : Site → K) (hc : (Set.range c).Finite) (p : Site)
    (t : ℕ) (α : Fin (t + 1) → K) (hfirst : α 0 ≠ 0) (hlast : α (Fin.last t) ≠ 0)
    (hrec : ∀ k, LineRecurrence t α (fun n : ℤ => c (k + n • p))) :
    IsPeriod c ((((Set.range c).ncard ^ t).factorial : ℤ) • p) := by
  intro g
  obtain ⟨q, hq, hbound, hp⟩ := bounded_period_of_finite_recurrence t α
    (fun n : ℤ => c (g + n • p)) hfirst hlast (hrec g) (Set.range c) hc
    (fun n => ⟨g + n • p, rfl⟩)
  obtain ⟨r, hr⟩ := Nat.dvd_factorial hq hbound
  have he := sequence_period_nat_multiple (fun n : ℤ => c (g + n • p)) q hp r 0
  have hmul : (r : ℤ) * (q : ℤ) = (((Set.range c).ncard ^ t).factorial : ℤ) := by
    rw [hr]
    push_cast
    ring
  simpa only [zero_add, hmul, zero_smul, add_zero] using he

end KumarNivat
