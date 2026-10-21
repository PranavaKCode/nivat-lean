module

public import KumarNivat.NewtonSingleRayFacetsSegment
public import KumarNivat.AnchoredCyclicRotation

@[expose] public section

namespace KumarNivat

-- rotating the zero-edge segment places its residual at any actual cyclic factor.
def cyclicFactorSegmentVertices (q : ℕ) (e : ZMod (2 * q) → Site)
    (j : ZMod (2 * q)) (t : ℝ) : ZMod (2 * q) → RealPlane :=
  fun i => singleFactorSegmentVertices q 0 (fun k => e (k + j)) t (i - j)

-- pulling back the two opposite residual lengths uses the same rotation.
def cyclicFactorSegmentLengths (q : ℕ) (j : ZMod (2 * q)) (t : ℝ) : ZMod (2 * q) → ℝ :=
  fun i => singleFactorSegmentLengths q 0 t (i - j)

-- every cyclic factor, including the opposite of the first factor, has a closed real segment walk.
theorem cyclicFactorSegmentVertices_next {q : ℕ} [NeZero q]
    (e : ZMod (2 * q) → Site) (hanti : ∀ i, e (i + (q : ZMod (2 * q))) = -e i)
    (j : ZMod (2 * q)) (t : ℝ) (i : ZMod (2 * q)) :
    cyclicFactorSegmentVertices q e j t (i + 1) = cyclicFactorSegmentVertices q e j t i +
      cyclicFactorSegmentLengths q j t i • latticeEmbedding (e i) := by
  have hrot : ∀ k : ZMod (2 * q), e ((k + (q : ZMod (2 * q))) + j) = -e (k + j) := by
    intro k
    simpa only [add_assoc, add_comm, add_left_comm] using hanti (k + j)
  have hh := singleFactorSegmentVertices_next (fun k => e (k + j)) hrot 0 (NeZero.pos q) t (i - j)
  simpa only [cyclicFactorSegmentVertices, cyclicFactorSegmentLengths,
    sub_add_cancel, sub_add_eq_add_sub, add_sub_assoc] using hh

-- all rotated segment residuals retain nonnegative real lengths.
theorem cyclicFactorSegmentLengths_nonnegative (q : ℕ) (j : ZMod (2 * q))
    (t : ℝ) (ht : 0 ≤ t) (i : ZMod (2 * q)) : 0 ≤ cyclicFactorSegmentLengths q j t i :=
  singleFactorSegmentLengths_nonnegative q 0 t ht (i - j)

-- cyclic reindexing preserves both actual segment endpoints.
theorem cyclicFactorSegmentVertices_range {q : ℕ} [NeZero q]
    (e : ZMod (2 * q) → Site) (j : ZMod (2 * q)) (t : ℝ) :
    Set.range (cyclicFactorSegmentVertices q e j t) = {0, t • latticeEmbedding (e j)} := by
  have hrange : Set.range (cyclicFactorSegmentVertices q e j t) =
      Set.range (singleFactorSegmentVertices q 0 (fun k => e (k + j)) t) := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i - j, rfl⟩
    · rintro ⟨i, rfl⟩
      refine ⟨i + j, ?_⟩
      simp only [cyclicFactorSegmentVertices, add_sub_cancel_right]
  rw [hrange, singleFactorSegmentVertices_range _ 0 (NeZero.pos q) t]
  simp only [Nat.cast_zero, zero_add]

-- the segment residual hull keeps its prescribed cyclic factor direction after rotation.
theorem cyclicFactorSegmentVertices_hull {q : ℕ} [NeZero q]
    (e : ZMod (2 * q) → Site) (j : ZMod (2 * q)) (t : ℝ) (ht : 0 ≤ t) :
    convexHull ℝ (Set.range (cyclicFactorSegmentVertices q e j t)) =
      lineInterval 0 (latticeEmbedding (e j)) 0 t := by
  rw [cyclicFactorSegmentVertices_range, convexHull_pair, lineInterval_eq_segment _ _ _ _ ht]
  simp only [zero_smul, zero_add]

-- the same actual normal minimum formula holds for every cyclic segment direction.
theorem cyclicFactorSegmentVertices_normal_minimum {q : ℕ} [NeZero q]
    (e : ZMod (2 * q) → Site) (horder : CyclicEdgeOrder e)
    (hanti : ∀ i, e (i + (q : ZMod (2 * q))) = -e i)
    (j : ZMod (2 * q)) (t : ℝ) (ht : 0 ≤ t) (i : ZMod (2 * q)) :
    latticeNormal (directionNormal (e i)) (cyclicFactorSegmentVertices q e j t i) =
      t * min 0 (directionNormal (e i) (e j) : ℝ) := by
  have hrot : ∀ k : ZMod (2 * q), e ((k + (q : ZMod (2 * q))) + j) = -e (k + j) := by
    intro k
    simpa only [add_assoc, add_comm, add_left_comm] using hanti (k + j)
  have hh := singleFactorSegmentVertices_normal_minimum (fun k => e (k + j))
    (horder.rotation j) hrot 0 (NeZero.pos q) t ht (i - j)
  simpa only [cyclicFactorSegmentVertices, Nat.cast_zero, zero_add, sub_add_cancel] using hh

end KumarNivat
