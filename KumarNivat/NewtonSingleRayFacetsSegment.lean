import KumarNivat.PairedStructureRayChainRealOrder
import KumarNivat.LineFaceGeometry

namespace KumarNivat

-- a selected factor and its opposite trace a single lattice segment.
def singleFactorSegmentUnitVertices (q j : ℕ) (e : ZMod (2 * q) → Site) : ZMod (2 * q) → Site :=
  fun i => if j < i.val ∧ i.val ≤ q + j then e (j : ZMod (2 * q)) else 0

-- only the two selected opposite edges have a nonzero unit length.
def singleFactorSegmentUnitLengths (q j : ℕ) : ZMod (2 * q) → ℤ :=
  fun i => if i.val = j ∨ i.val = q + j then 1 else 0

-- the unit segment walk closes in the actual antipodal fan.
theorem singleFactorSegmentUnitVertices_next {q : ℕ} [NeZero q]
    (e : ZMod (2 * q) → Site) (hanti : ∀ i, e (i + (q : ZMod (2 * q))) = -e i)
    (j : ℕ) (hjq : j < q) (i : ZMod (2 * q)) :
    singleFactorSegmentUnitVertices q j e (i + 1) =
      singleFactorSegmentUnitVertices q j e i + singleFactorSegmentUnitLengths q j i • e i := by
  have hq : 0 < q := NeZero.pos q
  have hi := ZMod.val_lt i
  have hone : (1 : ZMod (2 * q)).val = 1 := by
    simpa only [Nat.cast_one] using (ZMod.val_natCast_of_lt (n := 2 * q) (a := 1) (by omega))
  have hcast : (i.val : ZMod (2 * q)) = i := ZMod.natCast_zmod_val i
  have hpos (hv : i.val = j) : e i = e (j : ZMod (2 * q)) := by rw [← hcast, hv]
  have hneg (hv : i.val = q + j) : e i = -e (j : ZMod (2 * q)) := by
    calc
      e i = e ((j : ZMod (2 * q)) + (q : ZMod (2 * q))) := by
        rw [← Nat.cast_add, show j + q = i.val by omega, hcast]
      _ = _ := hanti _
  by_cases hstay : i.val + 1 < 2 * q
  · have hv : (i + 1).val = i.val + 1 := by
      rw [ZMod.val_add, hone, Nat.mod_eq_of_lt hstay]
    simp only [singleFactorSegmentUnitVertices, hv]
    by_cases hj : i.val = j
    · simp [singleFactorSegmentUnitLengths, hj, hpos hj,
        show j + 1 ≤ q + j by omega]
    · by_cases hqj : i.val = q + j
      · simp [singleFactorSegmentUnitLengths, hqj, hneg hqj, show j < q + j by omega]
      · have he : (j < i.val + 1 ∧ i.val + 1 ≤ q + j) ↔ (j < i.val ∧ i.val ≤ q + j) := by omega
        simp only [he, singleFactorSegmentUnitLengths, hj, hqj, or_self, ite_false,
          zero_smul, add_zero]
  · have hv : (i + 1).val = 0 := by
      rw [ZMod.val_add_of_le (by rw [hone]; omega), hone]
      omega
    have hj : i.val ≠ j := by omega
    simp only [singleFactorSegmentUnitVertices, hv]
    by_cases hqj : i.val = q + j
    · simp [singleFactorSegmentUnitLengths, hqj, hneg hqj, show j < q + j by omega]
    · have hmask : ¬(j < i.val ∧ i.val ≤ q + j) := by omega
      simp [singleFactorSegmentUnitLengths, hj, hqj, hmask]

-- real scaling allows the exact rational or real width of a relaxed facet.
def singleFactorSegmentVertices (q j : ℕ) (e : ZMod (2 * q) → Site) (t : ℝ) :
    ZMod (2 * q) → RealPlane :=
  fun i => t • latticeEmbedding (singleFactorSegmentUnitVertices q j e i)

-- the two selected real lengths share the same nonnegative segment width.
def singleFactorSegmentLengths (q j : ℕ) (t : ℝ) : ZMod (2 * q) → ℝ :=
  fun i => t * (singleFactorSegmentUnitLengths q j i : ℝ)

-- the real segment vertices have the requested explicit endpoint formula.
theorem singleFactorSegmentVertices_apply (q j : ℕ) (e : ZMod (2 * q) → Site) (t : ℝ)
    (i : ZMod (2 * q)) :
    singleFactorSegmentVertices q j e t i =
      if j < i.val ∧ i.val ≤ q + j then t • latticeEmbedding (e (j : ZMod (2 * q))) else 0 := by
  unfold singleFactorSegmentVertices singleFactorSegmentUnitVertices
  split_ifs
  · rfl
  · have hzero : latticeEmbedding (0 : Site) = (0 : RealPlane) := by ext <;> simp [latticeEmbedding]
    rw [hzero, smul_zero]

-- the real residual lengths are supported at exactly the selected opposite edges.
theorem singleFactorSegmentLengths_apply (q j : ℕ) (t : ℝ) (i : ZMod (2 * q)) :
    singleFactorSegmentLengths q j t i = if i.val = j ∨ i.val = q + j then t else 0 := by
  unfold singleFactorSegmentLengths singleFactorSegmentUnitLengths
  split_ifs <;> simp

-- nonnegative segment width gives nonnegative residual lengths.
theorem singleFactorSegmentLengths_nonnegative (q j : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (i : ZMod (2 * q)) : 0 ≤ singleFactorSegmentLengths q j t i := by
  rw [singleFactorSegmentLengths_apply]
  split_ifs <;> positivity

-- real scaling transports the checked closed unit walk into the same actual fan.
theorem singleFactorSegmentVertices_next {q : ℕ} [NeZero q]
    (e : ZMod (2 * q) → Site) (hanti : ∀ i, e (i + (q : ZMod (2 * q))) = -e i)
    (j : ℕ) (hjq : j < q) (t : ℝ) (i : ZMod (2 * q)) :
    singleFactorSegmentVertices q j e t (i + 1) = singleFactorSegmentVertices q j e t i +
      singleFactorSegmentLengths q j t i • latticeEmbedding (e i) := by
  unfold singleFactorSegmentVertices singleFactorSegmentLengths
  rw [singleFactorSegmentUnitVertices_next e hanti j hjq, latticeEmbedding_add,
    latticeEmbedding_zsmul, smul_add, smul_smul]

-- both endpoints occur in the actual residual walk, including at zero width.
theorem singleFactorSegmentVertices_range {q : ℕ} [NeZero q]
    (e : ZMod (2 * q) → Site) (j : ℕ) (hjq : j < q) (t : ℝ) :
    Set.range (singleFactorSegmentVertices q j e t) =
      {0, t • latticeEmbedding (e (j : ZMod (2 * q)))} := by
  have hq : 0 < q := NeZero.pos q
  have hzero : singleFactorSegmentVertices q j e t 0 = 0 := by
    rw [singleFactorSegmentVertices_apply]
    simp
  have hnext : singleFactorSegmentVertices q j e t ((j + 1 : ℕ) : ZMod (2 * q)) =
      t • latticeEmbedding (e (j : ZMod (2 * q))) := by
    have hv : ((j + 1 : ℕ) : ZMod (2 * q)).val = j + 1 := ZMod.val_natCast_of_lt (by omega)
    rw [singleFactorSegmentVertices_apply, hv]
    simp [show j + 1 ≤ q + j by omega]
  apply Set.Subset.antisymm
  · rintro _ ⟨i, rfl⟩
    rw [singleFactorSegmentVertices_apply]
    split_ifs <;> simp
  · intro x hx
    rcases hx with rfl | hx
    · exact ⟨0, hzero⟩
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact ⟨((j + 1 : ℕ) : ZMod (2 * q)), hnext⟩

-- the residual hull is the complete real segment with its original lattice direction.
theorem singleFactorSegmentVertices_hull {q : ℕ} [NeZero q]
    (e : ZMod (2 * q) → Site) (j : ℕ) (hjq : j < q) (t : ℝ) (ht : 0 ≤ t) :
    convexHull ℝ (Set.range (singleFactorSegmentVertices q j e t)) =
      lineInterval 0 (latticeEmbedding (e (j : ZMod (2 * q)))) 0 t := by
  rw [singleFactorSegmentVertices_range e j hjq t, convexHull_pair,
    lineInterval_eq_segment _ _ _ _ ht]
  simp only [zero_smul, zero_add]

-- every cyclic normal attains the smaller of the segment's two endpoint levels.
theorem singleFactorSegmentVertices_normal_minimum {q : ℕ} [NeZero q]
    (e : ZMod (2 * q) → Site) (horder : CyclicEdgeOrder e)
    (hanti : ∀ i, e (i + (q : ZMod (2 * q))) = -e i)
    (j : ℕ) (hjq : j < q) (t : ℝ) (ht : 0 ≤ t) (i : ZMod (2 * q)) :
    latticeNormal (directionNormal (e i)) (singleFactorSegmentVertices q j e t i) =
      t * min 0 (directionNormal (e i) (e (j : ZMod (2 * q))) : ℝ) := by
  let ν := latticeNormal (directionNormal (e i))
  let w := singleFactorSegmentVertices q j e t
  have hm := ordered_real_cyclic_walk_normal_minimum e horder w (singleFactorSegmentLengths q j t)
    (singleFactorSegmentLengths_nonnegative q j t ht) (singleFactorSegmentVertices_next e hanti j hjq t)
  have hrange := singleFactorSegmentVertices_range e j hjq t
  have hzero : ∃ k, w k = 0 := by
    have hz : (0 : RealPlane) ∈ Set.range w := by rw [hrange]; simp
    exact hz
  have hother : ∃ k, w k = t • latticeEmbedding (e (j : ZMod (2 * q))) := by
    have hz : t • latticeEmbedding (e (j : ZMod (2 * q))) ∈ Set.range w := by rw [hrange]; simp
    exact hz
  obtain ⟨k₀, hk₀⟩ := hzero
  obtain ⟨k₁, hk₁⟩ := hother
  have ha := hm i k₀
  have hb := hm i k₁
  change ν (w i) ≤ ν (w k₀) at ha
  change ν (w i) ≤ ν (w k₁) at hb
  rw [hk₀, map_zero] at ha
  rw [hk₁, map_smul, smul_eq_mul] at hb
  change ν (w i) ≤ t * latticeNormal (directionNormal (e i)) (latticeEmbedding (e (j : ZMod (2 * q)))) at hb
  rw [latticeNormal_embedding] at hb
  change ν (w i) ≤ t * (directionNormal (e i) (e (j : ZMod (2 * q))) : ℝ) at hb
  rw [mul_min_of_nonneg _ _ ht, mul_zero]
  apply le_antisymm (le_min ha hb)
  have hwi : w i ∈ ({0, t • latticeEmbedding (e (j : ZMod (2 * q)))} : Set RealPlane) := by
    rw [← hrange]
    exact ⟨i, rfl⟩
  rcases hwi with hw | hw
  · rw [hw, map_zero]
    exact min_le_left _ _
  · rw [Set.mem_singleton_iff] at hw
    rw [hw, map_smul, smul_eq_mul]
    change min (0 : ℝ) (t * (directionNormal (e i) (e (j : ZMod (2 * q))) : ℝ)) ≤
      t * latticeNormal (directionNormal (e i)) (latticeEmbedding (e (j : ZMod (2 * q))))
    rw [latticeNormal_embedding]
    exact min_le_right _ _

end KumarNivat
