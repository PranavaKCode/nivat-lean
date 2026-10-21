module

public import KumarNivat.NewtonCyclicNormals

@[expose] public section

namespace KumarNivat

-- the same closed scalar walk argument applies to real support levels.
theorem closed_real_scalar_walk_minimum (w : ℕ → ℝ) (n k : ℕ) (hkn : k ≤ n)
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

-- nonnegative real edge lengths retain the original integer fan's supporting normals.
theorem ordered_real_cyclic_walk_normal_minimum {n : ℕ} [NeZero n]
    (e : ZMod n → Site) (horder : CyclicEdgeOrder e) (v : ZMod n → RealPlane)
    (r : ZMod n → ℝ) (hr : ∀ i, 0 ≤ r i)
    (hedge : ∀ i, v (i + 1) = v i + r i • latticeEmbedding (e i)) :
    ∀ i j, latticeNormal (directionNormal (e i)) (v i) ≤
      latticeNormal (directionNormal (e i)) (v j) := by
  intro i j
  obtain ⟨k, hkn, hpositive, hnegative⟩ := horder.normal_turn i
  let w : ℕ → ℝ := fun t => latticeNormal (directionNormal (e i)) (v (i + (t : ZMod n)))
  have hclosed : w n = w 0 := by simp only [w, ZMod.natCast_self, Nat.cast_zero, add_zero]
  have hstep (t : ℕ) : w (t + 1) = w t + r (i + (t : ZMod n)) *
      (determinant (e i) (e (i + (t : ZMod n))) : ℝ) := by
    dsimp [w]
    rw [Nat.cast_add, Nat.cast_one, ← add_assoc, hedge, map_add, map_smul,
      latticeNormal_embedding, smul_eq_mul]
    rfl
  have hup : ∀ t < k, w t ≤ w (t + 1) := by
    intro t ht
    rw [hstep]
    exact le_add_of_nonneg_right (mul_nonneg (hr _) (by exact_mod_cast hpositive t ht))
  have hdown : ∀ t, k ≤ t → t < n → w (t + 1) ≤ w t := by
    intro t hkt htn
    rw [hstep]
    exact add_le_of_nonpos_right (mul_nonpos_of_nonneg_of_nonpos (hr _) (by exact_mod_cast hnegative t hkt htn))
  have hj : i + (((j - i).val : ℕ) : ZMod n) = j := by
    rw [ZMod.natCast_zmod_val]
    ring
  have hm := closed_real_scalar_walk_minimum w n k hkn hclosed hup hdown
    (j - i).val (le_of_lt (ZMod.val_lt (j - i)))
  simpa only [w, Nat.cast_zero, add_zero, hj] using hm

-- a real maximizing vertex has the same adjacent edge signs as the lattice walk.
theorem real_cyclic_maximum_adjacent_signs {n : ℕ} [NeZero n]
    (e : ZMod n → Site) (v : ZMod n → RealPlane) (r : ZMod n → ℝ) (hr : ∀ i, 0 < r i)
    (hedge : ∀ i, v (i + 1) = v i + r i • latticeEmbedding (e i))
    (L : RealPlane →ₗ[ℝ] ℝ) (i : ZMod n) (hmax : ∀ j, L (v j) ≤ L (v i)) :
    0 ≤ L (latticeEmbedding (e (i - 1))) ∧ L (latticeEmbedding (e i)) ≤ 0 := by
  have hnext := hmax (i + 1)
  rw [hedge, map_add, map_smul, smul_eq_mul] at hnext
  have hprev := hedge (i - 1)
  simp only [sub_add_cancel] at hprev
  have he := congrArg L hprev
  simp only [map_add, map_smul, smul_eq_mul] at he
  have hleft := hmax (i - 1)
  have hri := hr i
  have hrprev := hr (i - 1)
  constructor <;> nlinarith

-- a nonnegative real residual walk shares a maximizing vertex with the original positive walk.
theorem ordered_real_cyclic_common_linear_maximum {n : ℕ} [NeZero n]
    (e : ZMod n → Site) (horder : CyclicEdgeOrder e)
    (v w : ZMod n → RealPlane) (r d : ZMod n → ℝ)
    (hr : ∀ i, 0 < r i) (hd : ∀ i, 0 ≤ d i)
    (hv : ∀ i, v (i + 1) = v i + r i • latticeEmbedding (e i))
    (hw : ∀ i, w (i + 1) = w i + d i • latticeEmbedding (e i))
    (L : RealPlane →ₗ[ℝ] ℝ) :
    ∃ i, (∀ j, L (v j) ≤ L (v i)) ∧ (∀ j, L (w j) ≤ L (w i)) := by
  classical
  obtain ⟨i, _hi, hmax⟩ := Finset.univ.exists_max_image (fun j => L (v j))
    (Finset.univ_nonempty : (Finset.univ : Finset (ZMod n)).Nonempty)
  have hmax' : ∀ j, L (v j) ≤ L (v i) := fun j => hmax j (Finset.mem_univ j)
  obtain ⟨hprevsign, hnextsign⟩ := real_cyclic_maximum_adjacent_signs e v r hr hv L i hmax'
  have hmin := ordered_real_cyclic_walk_normal_minimum e horder w d hd hw
  refine ⟨i, hmax', ?_⟩
  intro j
  have hi := hmin i j
  have hp := hmin (i - 1) j
  have hprevious := congrArg (latticeNormal (directionNormal (e (i - 1)))) (hw (i - 1))
  simp only [sub_add_cancel, map_add, map_smul, latticeNormal_embedding, directionNormal_self,
    Int.cast_zero, smul_zero, add_zero] at hprevious
  rw [← hprevious] at hp
  have hpx : 0 ≤ latticeNormal (directionNormal (e (i - 1))) (w j - w i) := by
    rw [map_sub]
    exact sub_nonneg.mpr hp
  have hqx : 0 ≤ latticeNormal (directionNormal (e i)) (w j - w i) := by
    rw [map_sub]
    exact sub_nonneg.mpr hi
  have hcontrol := adjacent_edge_normals_linear_control (e (i - 1)) (e i)
    (horder.adjacent_pos i) L hprevsign hnextsign _ hpx hqx
  rw [map_sub] at hcontrol
  exact sub_nonpos.mp hcontrol

end KumarNivat
