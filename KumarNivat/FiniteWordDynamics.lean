module

public import KumarNivat.Statement
public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Logic.Function.Basic
public import Mathlib.Data.Fintype.Pigeonhole
public import Lean.Elab.Tactic.Omega

@[expose] public section

namespace KumarNivat

-- one more sample than the actual state count gives a repeat at a bounded positive gap.
theorem finite_state_short_collision {A : Type*} (s : ℕ → A)
    (S : Set A) (hS : S.Finite) (hmem : ∀ n, s n ∈ S) :
    ∃ i j : ℕ, i < j ∧ j ≤ S.ncard ∧ s i = s j := by
  classical
  let : Fintype S := hS.fintype
  let M := S.ncard
  let sample : Fin (M + 1) → S := fun n => ⟨s n.val, hmem n.val⟩
  have hcard : Fintype.card S < Fintype.card (Fin (M + 1)) := by
    simp only [Set.fintypeCard_eq_ncard, Fintype.card_fin]
    dsimp [M]
    omega
  obtain ⟨i, j, hne, he⟩ := Fintype.exists_ne_map_eq_of_card_lt sample hcard
  have hij : i.val ≠ j.val := fun heq => hne (Fin.ext heq)
  have he' : s i.val = s j.val := congrArg Subtype.val he
  have hi := i.isLt
  have hj := j.isLt
  by_cases hlt : i.val < j.val
  · exact ⟨i.val, j.val, hlt, by dsimp [M] at hj; omega, he'⟩
  · exact ⟨j.val, i.val, by omega, by dsimp [M] at hi; omega, he'.symm⟩

-- a finite bilateral successor relation is reversible on its occurring states.
theorem finite_bilateral_predecessor_determined {A : Type*} (s : ℤ → A)
    (hs : (Set.range s).Finite)
    (hnext : ∀ i j : ℤ, s i = s j → s (i + 1) = s (j + 1)) :
    ∀ i j : ℤ, s i = s j → s (i - 1) = s (j - 1) := by
  classical
  let : Nonempty A := ⟨s 0⟩
  let : Fintype (Set.range s) := hs.fintype
  have hfactor : (fun n : ℤ => s (n + 1)).FactorsThrough s := fun _i _j he => hnext _ _ he
  obtain ⟨F, hF⟩ := Function.factorsThrough_iff _ |>.mp hfactor
  have hF' (n : ℤ) : F (s n) = s (n + 1) := (congrFun hF n).symm
  have hmaps (x : Set.range s) : F x.val ∈ Set.range s := by
    obtain ⟨n, hn⟩ := x.property
    exact ⟨n + 1, by rw [← hn, hF']⟩
  let step : Set.range s → Set.range s := fun x => ⟨F x.val, hmaps x⟩
  let state : ℤ → Set.range s := fun n => ⟨s n, ⟨n, rfl⟩⟩
  have hstep (n : ℤ) : step (state n) = state (n + 1) := Subtype.ext (hF' n)
  have hsurj : Function.Surjective step := by
    rintro ⟨x, n, rfl⟩
    refine ⟨state (n - 1), ?_⟩
    simpa only [sub_add_cancel] using hstep (n - 1)
  have hinj : Function.Injective step := Finite.injective_iff_surjective.mpr hsurj
  intro i j he
  have he' : step (state (i - 1)) = step (state (j - 1)) := by
    rw [hstep, hstep, sub_add_cancel, sub_add_cancel]
    exact Subtype.ext he
  exact congrArg Subtype.val (hinj he')

-- one repeated state forces a global positive period because equality propagates both ways.
theorem bounded_period_of_bilateral_determinism {A : Type*} (s : ℤ → A)
    (hs : (Set.range s).Finite)
    (hnext : ∀ i j : ℤ, s i = s j → s (i + 1) = s (j + 1)) :
    ∃ p : ℕ, 0 < p ∧ p ≤ (Set.range s).ncard ∧ Function.Periodic s (p : ℤ) := by
  obtain ⟨i, j, hij, hj, he⟩ := finite_state_short_collision (fun n : ℕ => s (n : ℤ))
    (Set.range s) hs (fun n => ⟨(n : ℤ), rfl⟩)
  have hprev := finite_bilateral_predecessor_determined s hs hnext
  have hcollision (r : ℤ) : s ((i : ℤ) + r) = s ((j : ℤ) + r) := by
    induction r using Int.induction_on with
    | zero => simpa only [add_zero] using he
    | succ r ih => simpa only [add_assoc] using hnext _ _ ih
    | pred r ih => simpa only [sub_eq_add_neg, add_assoc] using hprev _ _ ih
  refine ⟨j - i, by omega, by omega, ?_⟩
  intro n
  have hsite₁ : (i : ℤ) + (n - (i : ℤ)) = n := by omega
  have hsite₂ : (j : ℤ) + (n - (i : ℤ)) = n + ((j - i : ℕ) : ℤ) := by omega
  simpa only [hsite₁, hsite₂] using (hcollision (n - (i : ℤ))).symm

-- on a one-sided sequence the same repeat gives an eventual period with bounded start and gap.
theorem bounded_eventual_period_of_determinism {A : Type*} (s : ℕ → A)
    (hs : (Set.range s).Finite)
    (hnext : ∀ i j : ℕ, s i = s j → s (i + 1) = s (j + 1)) :
    ∃ b p : ℕ, b < (Set.range s).ncard ∧ 0 < p ∧ p ≤ (Set.range s).ncard ∧
      ∀ n : ℕ, b ≤ n → s (n + p) = s n := by
  obtain ⟨i, j, hij, hj, he⟩ := finite_state_short_collision s (Set.range s) hs
    (fun n => ⟨n, rfl⟩)
  have hcollision (r : ℕ) : s (i + r) = s (j + r) := by
    induction r with
    | zero => simpa only [add_zero] using he
    | succ r ih => simpa only [Nat.add_assoc] using hnext _ _ ih
  refine ⟨i, j - i, by omega, by omega, by omega, ?_⟩
  intro n hn
  have hsite₁ : i + (n - i) = n := by omega
  have hsite₂ : j + (n - i) = n + (j - i) := by omega
  simpa only [hsite₁, hsite₂] using (hcollision (n - i)).symm

end KumarNivat
