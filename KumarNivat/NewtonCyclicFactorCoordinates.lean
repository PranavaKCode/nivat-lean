module

public import KumarNivat.NewtonCyclicFactorWalk
public import KumarNivat.NewtonProductZonotope
public import Mathlib.Algebra.Group.Pointwise.Set.BigOperators
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

namespace KumarNivat

open scoped Pointwise

-- the real lattice embedding commutes with actual finite sums.
theorem latticeEmbedding_finset_sum {I : Type*} (s : Finset I) (h : I → Site) :
    latticeEmbedding (∑ i ∈ s, h i) = ∑ i ∈ s, latticeEmbedding (h i) := by
  classical
  induction s using Finset.induction_on with
  | empty => ext <;> simp [latticeEmbedding]
  | @insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, latticeEmbedding_add, ih]

-- prefix vertices are precisely the corresponding endpoint choices in the segment sum.
theorem factorVertexPrefix_embedding {q : ℕ} (h : Fin q → Site) (t : ℕ) :
    latticeEmbedding (factorVertexPrefix h t) =
      ∑ i : Fin q, if i.val < t then latticeEmbedding (h i) else 0 := by
  classical
  rw [factorVertexPrefix, latticeEmbedding_finset_sum, Finset.sum_filter]

-- the opposite walk vertices choose the complementary segment endpoints.
theorem factorVertexComplement_embedding {q : ℕ} (h : Fin q → Site) (t : ℕ) :
    latticeEmbedding (factorVertexPrefix h q - factorVertexPrefix h t) =
      ∑ i : Fin q, if i.val < t then 0 else latticeEmbedding (h i) := by
  classical
  rw [latticeEmbedding_sub, factorVertexPrefix_embedding, factorVertexPrefix_embedding, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  simp only [i.isLt, ite_true]
  split_ifs <;> simp

-- the original recursive segment sum is also its ordinary finite sum over factor indices.
theorem factorZonotope_eq_finset_sum {q : ℕ} (h : Fin q → Site) :
    differenceZonotope (List.ofFn h) = ∑ i : Fin q, lineInterval 0 (latticeEmbedding (h i)) 0 1 := by
  have hlist (hs : List Site) : differenceZonotope hs =
      (hs.map (fun p => lineInterval 0 (latticeEmbedding p) 0 1)).sum := by
    induction hs with
    | nil => rfl
    | cons p hs ih => simp only [differenceZonotope, List.map_cons, List.sum_cons, ih]
  simpa only [List.map_ofFn, List.sum_ofFn, Function.comp_apply] using hlist (List.ofFn h)

-- segment coordinates describe every actual point of the zonotope, with no subset-sum assumption.
theorem factorZonotope_mem_coordinates {q : ℕ} (h : Fin q → Site) (z : RealPlane) :
    z ∈ differenceZonotope (List.ofFn h) ↔
      ∃ t : Fin q → ℝ, (∀ i, 0 ≤ t i ∧ t i ≤ 1) ∧
        ∑ i : Fin q, t i • latticeEmbedding (h i) = z := by
  classical
  rw [factorZonotope_eq_finset_sum]
  constructor
  · intro hz
    obtain ⟨u, hu, hsum⟩ := (Set.mem_fintype_sum _ z).mp hz
    have hparameter (i : Fin q) : ∃ t : ℝ, (0 ≤ t ∧ t ≤ 1) ∧ t • latticeEmbedding (h i) = u i := by
      obtain ⟨t, ht, he⟩ := hu i
      refine ⟨t, ht, ?_⟩
      simpa only [zero_add] using he
    choose t ht he using hparameter
    refine ⟨t, ht, ?_⟩
    calc
      (∑ i : Fin q, t i • latticeEmbedding (h i)) = ∑ i : Fin q, u i :=
        Finset.sum_congr rfl (fun i _hi => he i)
      _ = z := hsum
  · rintro ⟨t, ht, hsum⟩
    apply (Set.mem_fintype_sum _ z).mpr
    refine ⟨fun i => t i • latticeEmbedding (h i), ?_, hsum⟩
    intro i
    exact ⟨t i, ht i, by simp only [zero_add]⟩

-- each segment contributes its actual smaller normal endpoint to a lower support bound.
theorem factorZonotope_normal_lower_bound {q : ℕ} (h : Fin q → Site) (ν : Site →+ ℤ)
    (z : RealPlane) (hz : z ∈ differenceZonotope (List.ofFn h)) :
    (∑ i : Fin q, min 0 (ν (h i) : ℝ)) ≤ latticeNormal ν z := by
  classical
  obtain ⟨t, ht, he⟩ := (factorZonotope_mem_coordinates h z).mp hz
  rw [← he, map_sum]
  simp only [map_smul, smul_eq_mul]
  apply Finset.sum_le_sum
  intro i _hi
  rw [latticeNormal_embedding]
  by_cases hd : (ν (h i) : ℝ) ≤ 0
  · rw [min_eq_right hd]
    simpa only [one_mul] using mul_le_mul_of_nonpos_right (ht i).2 hd
  · rw [min_eq_left (le_of_lt (lt_of_not_ge hd))]
    exact mul_nonneg (ht i).1 (le_of_lt (lt_of_not_ge hd))

-- the first half of the walk consists of actual segment-endpoint choices.
theorem factorVertexPrefix_mem_zonotope {q : ℕ} (h : Fin q → Site) (t : ℕ) :
    latticeEmbedding (factorVertexPrefix h t) ∈ differenceZonotope (List.ofFn h) := by
  classical
  apply (factorZonotope_mem_coordinates h _).mpr
  refine ⟨fun i => if i.val < t then 1 else 0, ?_, ?_⟩
  · intro i
    change 0 ≤ (if i.val < t then (1 : ℝ) else 0) ∧ (if i.val < t then (1 : ℝ) else 0) ≤ 1
    by_cases hi : i.val < t <;> simp [hi]
  · rw [factorVertexPrefix_embedding]
    apply Finset.sum_congr rfl
    intro i _hi
    change (if i.val < t then (1 : ℝ) else 0) • latticeEmbedding (h i) =
      if i.val < t then latticeEmbedding (h i) else 0
    by_cases hi : i.val < t <;> simp [hi]

-- the return half chooses the complementary actual segment endpoints.
theorem factorVertexComplement_mem_zonotope {q : ℕ} (h : Fin q → Site) (t : ℕ) :
    latticeEmbedding (factorVertexPrefix h q - factorVertexPrefix h t) ∈
      differenceZonotope (List.ofFn h) := by
  classical
  apply (factorZonotope_mem_coordinates h _).mpr
  refine ⟨fun i => if i.val < t then 0 else 1, ?_, ?_⟩
  · intro i
    change 0 ≤ (if i.val < t then (0 : ℝ) else 1) ∧ (if i.val < t then (0 : ℝ) else 1) ≤ 1
    by_cases hi : i.val < t <;> simp [hi]
  · rw [factorVertexComplement_embedding]
    apply Finset.sum_congr rfl
    intro i _hi
    change (if i.val < t then (0 : ℝ) else 1) • latticeEmbedding (h i) =
      if i.val < t then 0 else latticeEmbedding (h i)
    by_cases hi : i.val < t <;> simp [hi]

end KumarNivat
