module

public import KumarNivat.NewtonProductGeometry
public import Mathlib.Data.ZMod.Basic

@[expose] public section

namespace KumarNivat

-- rotating an oriented convex edge list crosses each normal's positive half-plane only once.
structure CyclicEdgeOrder {n : ℕ} [NeZero n] (e : ZMod n → Site) : Prop where
  adjacent_pos : ∀ i, 0 < determinant (e (i - 1)) (e i)
  normal_turn : ∀ i, ∃ k : ℕ, k ≤ n ∧
    (∀ j : ℕ, j < k → 0 ≤ determinant (e i) (e (i + (j : ZMod n)))) ∧
    (∀ j : ℕ, k ≤ j → j < n → determinant (e i) (e (i + (j : ZMod n))) ≤ 0)

-- these are actual integer vertices and edge lengths of the named lattice hull.
structure OrderedCyclicLatticePolygon {n : ℕ} [NeZero n] (e : ZMod n → Site)
    (F : Finset Site) where
  vertex : ZMod n → Site
  edgeLength : ZMod n → ℤ
  length_pos : ∀ i, 0 < edgeLength i
  edge_eq : ∀ i, vertex (i + 1) = vertex i + edgeLength i • e i
  vertex_mem : ∀ i, vertex i ∈ F
  hull_eq : latticeHull F = convexHull ℝ (Set.range (fun i => latticeEmbedding (vertex i)))

-- increasing then decreasing around a closed scalar walk puts its start at a minimum.
theorem closed_scalar_walk_minimum (w : ℕ → ℤ) (n k : ℕ) (hkn : k ≤ n)
    (hclosed : w n = w 0) (hup : ∀ j < k, w j ≤ w (j + 1))
    (hdown : ∀ j, k ≤ j → j < n → w (j + 1) ≤ w j) :
    ∀ j ≤ n, w 0 ≤ w j := by
  have hlower : ∀ j, j ≤ k → w 0 ≤ w j := by
    intro j
    induction j with
    | zero => intro _h; exact le_rfl
    | succ j ih =>
      intro hj
      exact (ih (by omega)).trans (hup j (by omega))
  have hupper : ∀ d, d ≤ n - k → w n ≤ w (n - d) := by
    intro d
    induction d with
    | zero => intro _h; simp
    | succ d ih =>
      intro hd
      have hstep := hdown (n - (d + 1)) (by omega) (by omega)
      have he : n - (d + 1) + 1 = n - d := by omega
      rw [he] at hstep
      exact (ih (by omega)).trans hstep
  intro j hj
  by_cases hjk : j ≤ k
  · exact hlower j hjk
  · have he : n - (n - j) = j := by omega
    have h := hupper (n - j) (by omega)
    rwa [he, hclosed] at h

-- nonnegative cyclic edge lengths give the actual supporting inequality for each oriented edge.
theorem ordered_cyclic_walk_normal_minimum {n : ℕ} [NeZero n]
    (e : ZMod n → Site) (horder : CyclicEdgeOrder e) (v : ZMod n → Site)
    (r : ZMod n → ℤ) (hr : ∀ i, 0 ≤ r i)
    (hedge : ∀ i, v (i + 1) = v i + r i • e i) :
    ∀ i j, directionNormal (e i) (v i) ≤ directionNormal (e i) (v j) := by
  intro i j
  obtain ⟨k, hkn, hpositive, hnegative⟩ := horder.normal_turn i
  let w : ℕ → ℤ := fun t => directionNormal (e i) (v (i + (t : ZMod n)))
  have hclosed : w n = w 0 := by simp only [w, ZMod.natCast_self, Nat.cast_zero, add_zero]
  have hstep (t : ℕ) : w (t + 1) = w t + r (i + (t : ZMod n)) *
      determinant (e i) (e (i + (t : ZMod n))) := by
    dsimp [w]
    rw [Nat.cast_add, Nat.cast_one, ← add_assoc, hedge, map_add, map_zsmul, smul_eq_mul]
    rfl
  have hup : ∀ t < k, w t ≤ w (t + 1) := by
    intro t ht
    rw [hstep]
    exact le_add_of_nonneg_right (mul_nonneg (hr _) (hpositive t ht))
  have hdown : ∀ t, k ≤ t → t < n → w (t + 1) ≤ w t := by
    intro t hkt htn
    rw [hstep]
    exact add_le_of_nonpos_right (mul_nonpos_of_nonneg_of_nonpos (hr _) (hnegative t hkt htn))
  have hj : i + (((j - i).val : ℕ) : ZMod n) = j := by
    rw [ZMod.natCast_zmod_val]
    ring
  have hm := closed_scalar_walk_minimum w n k hkn hclosed hup hdown
    (j - i).val (le_of_lt (ZMod.val_lt (j - i)))
  simpa only [w, Nat.cast_zero, add_zero, hj] using hm

end KumarNivat
