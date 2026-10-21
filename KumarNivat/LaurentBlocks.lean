module

public import KumarNivat.LaurentFactorization
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

namespace KumarNivat

-- a finite consecutive exponent block records the coefficients of one directional eliminant.
noncomputable def laurentBlock {K : Type*} [CommRing K] (m : ℤ) (t : ℕ)
    (α : Fin (t + 1) → K) : LaurentPolynomial K :=
  ∑ i : Fin (t + 1), AddMonoidAlgebra.single (m + (i.val : ℤ)) (α i)

-- the block recovers each of its coefficients without collisions between integer exponents.
theorem laurentBlock_coeff {K : Type*} [CommRing K] (m : ℤ) (t : ℕ)
    (α : Fin (t + 1) → K) (i : Fin (t + 1)) :
    (laurentBlock m t α).coeff (m + (i.val : ℤ)) = α i := by
  classical
  have hinj : Function.Injective (fun j : Fin (t + 1) => m + (j.val : ℤ)) := by
    intro j l he
    apply Fin.ext
    exact_mod_cast (add_left_cancel he)
  simp only [laurentBlock, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    AddMonoidAlgebra.coeff_single, Finsupp.single_apply, hinj.eq_iff]
  simp

-- no other exponent contributes to the block.
theorem laurentBlock_coeff_outside {K : Type*} [CommRing K] (m : ℤ) (t : ℕ)
    (α : Fin (t + 1) → K) (n : ℤ) (hout : ∀ i : Fin (t + 1), m + (i.val : ℤ) ≠ n) :
    (laurentBlock m t α).coeff n = 0 := by
  classical
  simp only [laurentBlock, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  apply Finset.sum_eq_zero
  intro i hi
  rw [ite_eq_right (hout i)]

-- trim exactly to the first and last nonzero coefficients to obtain a reversible recurrence.
theorem exists_reversible_laurent_block {K : Type*} [CommRing K]
    (d : LaurentPolynomial K) (hd : d ≠ 0) :
    ∃ m : ℤ, ∃ t : ℕ, ∃ α : Fin (t + 1) → K,
      α 0 ≠ 0 ∧ α (Fin.last t) ≠ 0 ∧ d = laurentBlock m t α := by
  classical
  have hsupport : d.coeff.support.Nonempty := Finsupp.support_nonempty_iff.mpr
    (fun hz => hd (AddMonoidAlgebra.coeff_injective hz))
  let m := d.coeff.support.min' hsupport
  let M := d.coeff.support.max' hsupport
  have hm : m ∈ d.coeff.support := Finset.min'_mem _ _
  have hM : M ∈ d.coeff.support := Finset.max'_mem _ _
  have hlo (n : ℤ) (hn : n ∈ d.coeff.support) : m ≤ n := Finset.min'_le _ n hn
  have hhi (n : ℤ) (hn : n ∈ d.coeff.support) : n ≤ M := Finset.le_max' _ n hn
  have hmM : m ≤ M := hlo M hM
  let t := (M - m).toNat
  have ht : m + (t : ℤ) = M := by dsimp [t]; omega
  let α (i : Fin (t + 1)) := d.coeff (m + (i.val : ℤ))
  refine ⟨m, t, α, ?_, ?_, ?_⟩
  · simpa only [α, Fin.val_zero, Nat.cast_zero, add_zero] using Finsupp.mem_support_iff.mp hm
  · simpa only [α, Fin.val_last, ht] using Finsupp.mem_support_iff.mp hM
  · apply AddMonoidAlgebra.coeff_injective
    ext n
    by_cases hn : m ≤ n ∧ n ≤ M
    · let i : Fin (t + 1) := ⟨(n - m).toNat, by omega⟩
      have hni : m + (i.val : ℤ) = n := by dsimp [i]; omega
      rw [← hni, laurentBlock_coeff]
    · have hdn : d.coeff n = 0 := Finsupp.notMem_support_iff.mp
        (fun hs => hn ⟨hlo n hs, hhi n hs⟩)
      rw [hdn, laurentBlock_coeff_outside m t α n]
      intro i he
      have hi := i.isLt
      exact hn (by constructor <;> omega)

end KumarNivat
