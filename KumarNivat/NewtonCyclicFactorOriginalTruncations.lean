import KumarNivat.NewtonCyclicFactorWalk
import KumarNivat.NewtonCyclicMinkowski
import KumarNivat.NewtonCyclicFacets
import KumarNivat.LineFaceGeometry

namespace KumarNivat

open scoped Pointwise

-- two selected positive factors generate the finite ray truncation.
def sparseTruncationFactors {q : ℕ} (a b : Site) (j N : ℕ) : Fin q → Site :=
  fun i => (if i.val = 0 then (N : ℤ) • a else 0) +
    (if i.val = j then (N : ℤ) • b else 0)

-- these four constant stretches trace the actual rectangle boundary.
def sparseTruncationVertices (q : ℕ) (a b : Site) (j N : ℕ) : ZMod (2 * q) → Site :=
  fun i => (if 0 < i.val ∧ i.val ≤ q then (N : ℤ) • a else 0) +
    (if j < i.val ∧ i.val ≤ q + j then (N : ℤ) • b else 0)

-- each selected ray and its opposite receive the same nonnegative length.
def sparseTruncationLengths (q j N : ℕ) : ZMod (2 * q) → ℤ :=
  fun i => if i.val = 0 ∨ i.val = j ∨ i.val = q ∨ i.val = q + j then (N : ℤ) else 0

-- summing the two sparse factors gives their explicit prefix endpoints.
theorem sparseTruncationFactors_prefix {q : ℕ} (hq : 0 < q)
    (a b : Site) (j N t : ℕ) (hj : j < q) :
    factorVertexPrefix (sparseTruncationFactors (q := q) a b j N) t =
      (if 0 < t then (N : ℤ) • a else 0) +
      (if j < t then (N : ℤ) • b else 0) := by
  classical
  unfold factorVertexPrefix sparseTruncationFactors
  rw [Finset.sum_add_distrib]
  congr 1
  · calc
      _ = ∑ i ∈ Finset.univ.filter (fun i : Fin q => i.val < t),
          if i = (⟨0, hq⟩ : Fin q) then (N : ℤ) • a else 0 := by
        apply Finset.sum_congr rfl
        intro i _hi
        simp only [Fin.ext_iff]
      _ = _ := by simp
  · calc
      _ = ∑ i ∈ Finset.univ.filter (fun i : Fin q => i.val < t),
          if i = (⟨j, hj⟩ : Fin q) then (N : ℤ) • b else 0 := by
        apply Finset.sum_congr rfl
        intro i _hi
        simp only [Fin.ext_iff]
      _ = _ := by simp

-- the explicit rectangle vertices agree with the closed prefix construction.
theorem sparseTruncationVertices_eq_doubled {q : ℕ} [NeZero q]
    (a b : Site) (j N : ℕ) (hj0 : 0 < j) (hjq : j < q) :
    sparseTruncationVertices q a b j N =
      doubledFactorVertices q (sparseTruncationFactors a b j N) := by
  funext i
  have hq : 0 < q := NeZero.pos q
  have hi := ZMod.val_lt i
  by_cases hfirst : i.val < q
  · simp only [doubledFactorVertices, hfirst, ite_true]
    rw [sparseTruncationFactors_prefix hq a b j N i.val hjq]
    have h₁ : (0 < i.val ∧ i.val ≤ q) ↔ 0 < i.val := by omega
    have h₂ : (j < i.val ∧ i.val ≤ q + j) ↔ j < i.val := by omega
    simp only [sparseTruncationVertices, h₁, h₂]
  · simp only [doubledFactorVertices, hfirst, ite_false]
    rw [sparseTruncationFactors_prefix hq a b j N q hjq,
      sparseTruncationFactors_prefix hq a b j N (i.val - q) hjq]
    simp only [hq, hjq, ite_true]
    unfold sparseTruncationVertices
    split_ifs <;> (try omega) <;> abel

-- the sparse doubled factors follow the given antipodal fan with these actual lengths.
theorem sparseTruncationFactors_directions {q : ℕ} [NeZero q]
    (e : ZMod (2 * q) → Site) (hanti : ∀ i, e (i + (q : ZMod (2 * q))) = -e i)
    (j N : ℕ) (hj0 : 0 < j) (hjq : j < q) (i : ZMod (2 * q)) :
    doubledFactorDirections q (sparseTruncationFactors (e 0) (e (j : ZMod (2 * q))) j N) i =
      sparseTruncationLengths q j N i • e i := by
  have hi := ZMod.val_lt i
  have hcast : (i.val : ZMod (2 * q)) = i := ZMod.natCast_zmod_val i
  by_cases hfirst : i.val < q
  · have hneqQ : i.val ≠ q := by omega
    have hneqQj : i.val ≠ q + j := by omega
    simp only [doubledFactorDirections, hfirst, dite_true, sparseTruncationFactors]
    by_cases hz : i.val = 0
    · have he : e i = e 0 := by rw [← hcast, hz, Nat.cast_zero]
      simp [sparseTruncationLengths, hz, he, show 0 ≠ j by omega]
    · by_cases hj : i.val = j
      · have he : e i = e (j : ZMod (2 * q)) := by rw [← hcast, hj]
        simp [sparseTruncationLengths, hj, he, show j ≠ 0 by omega]
      · simp [sparseTruncationLengths, hz, hj, hneqQ, hneqQj]
  · have hneq0 : i.val ≠ 0 := by have hq := NeZero.pos q; omega
    have hneqj : i.val ≠ j := by omega
    have hindex : ((i.val - q : ℕ) : ZMod (2 * q)) + (q : ZMod (2 * q)) = i := by
      rw [← Nat.cast_add, show i.val - q + q = i.val by omega, hcast]
    have he : e i = -e ((i.val - q : ℕ) : ZMod (2 * q)) := by
      calc
        e i = e (((i.val - q : ℕ) : ZMod (2 * q)) + (q : ZMod (2 * q))) :=
          congrArg e hindex.symm
        _ = _ := hanti _
    simp only [doubledFactorDirections, hfirst, dite_false, sparseTruncationFactors]
    by_cases hz : i.val - q = 0
    · have hvq : i.val = q := by omega
      simp [sparseTruncationLengths, hvq, he, smul_neg, show 0 ≠ j by omega]
    · by_cases hj : i.val - q = j
      · have hvqj : i.val = q + j := by omega
        simp [sparseTruncationLengths, hvqj, he, smul_neg, show j ≠ 0 by omega]
      · have hneqQ : i.val ≠ q := by omega
        have hneqQj : i.val ≠ q + j := by omega
        simp [sparseTruncationLengths, hz, hj, hneq0, hneqj, hneqQ, hneqQj]

-- the rectangle therefore has a closed cyclic walk in the original fan.
theorem sparseTruncationVertices_next {q : ℕ} [NeZero q]
    (e : ZMod (2 * q) → Site) (hanti : ∀ i, e (i + (q : ZMod (2 * q))) = -e i)
    (j N : ℕ) (hj0 : 0 < j) (hjq : j < q) (i : ZMod (2 * q)) :
    sparseTruncationVertices q (e 0) (e (j : ZMod (2 * q))) j N (i + 1) =
      sparseTruncationVertices q (e 0) (e (j : ZMod (2 * q))) j N i +
        sparseTruncationLengths q j N i • e i := by
  rw [sparseTruncationVertices_eq_doubled (e 0) (e (j : ZMod (2 * q))) j N hj0 hjq,
    doubledFactorVertices_next, sparseTruncationFactors_directions e hanti j N hj0 hjq]

-- the actual sparse edge lengths remain nonnegative even for the zero truncation.
theorem sparseTruncationLengths_nonnegative (q j N : ℕ) (i : ZMod (2 * q)) :
    0 ≤ sparseTruncationLengths q j N i := by
  unfold sparseTruncationLengths
  split_ifs <;> simp

-- all four rectangle corners occur at explicit positions of the sparse walk.
theorem sparseTruncationVertices_range {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    (a b : Site) (j N : ℕ) (hj0 : 0 < j) (hjq : j < q) :
    Set.range (sparseTruncationVertices q a b j N) =
      ({0, (N : ℤ) • a} : Set Site) + {0, (N : ℤ) • b} := by
  have hzero : sparseTruncationVertices q a b j N 0 = 0 := by
    simp [sparseTruncationVertices]
  have hone : sparseTruncationVertices q a b j N 1 = (N : ℤ) • a := by
    have hv : (1 : ZMod (2 * q)).val = 1 := by
      simpa only [Nat.cast_one] using (ZMod.val_natCast_of_lt (n := 2 * q) (a := 1) (by omega))
    simp [sparseTruncationVertices, hv, show ¬j < 1 by omega, show 1 ≤ q by omega]
  have hboth : sparseTruncationVertices q a b j N ((j + 1 : ℕ) : ZMod (2 * q)) =
      (N : ℤ) • a + (N : ℤ) • b := by
    have hv : ((j + 1 : ℕ) : ZMod (2 * q)).val = j + 1 := ZMod.val_natCast_of_lt (by omega)
    simp only [sparseTruncationVertices, hv]
    simp [show j + 1 ≤ q by omega,
      show j + 1 ≤ q + j by omega]
  have hsecond : sparseTruncationVertices q a b j N ((q + 1 : ℕ) : ZMod (2 * q)) =
      (N : ℤ) • b := by
    have hv : ((q + 1 : ℕ) : ZMod (2 * q)).val = q + 1 := ZMod.val_natCast_of_lt (by omega)
    simp only [sparseTruncationVertices, hv]
    simp [show j < q + 1 by omega,
      show q + 1 ≤ q + j by omega]
  apply Set.Subset.antisymm
  · rintro _ ⟨i, rfl⟩
    unfold sparseTruncationVertices
    apply Set.add_mem_add <;> split_ifs <;> simp
  · rintro _ ⟨x, hx, y, hy, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact ⟨0, by simpa using hzero⟩
    · exact ⟨((q + 1 : ℕ) : ZMod (2 * q)), by simpa using hsecond⟩
    · exact ⟨1, by simpa using hone⟩
    · exact ⟨((j + 1 : ℕ) : ZMod (2 * q)), hboth⟩

-- the sparse walk's real hull is exactly the sum of the two finite ray segments.
theorem sparseTruncationVertices_hull {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    (a b : Site) (j N : ℕ) (hj0 : 0 < j) (hjq : j < q) :
    convexHull ℝ (Set.range (fun i => latticeEmbedding (sparseTruncationVertices q a b j N i))) =
      lineInterval 0 (latticeEmbedding a) 0 (N : ℝ) +
        lineInterval 0 (latticeEmbedding b) 0 (N : ℝ) := by
  let emb : Site →+ RealPlane :=
    { toFun := latticeEmbedding
      map_zero' := by ext <;> simp [latticeEmbedding]
      map_add' := latticeEmbedding_add }
  have hgen : Set.range (fun i => latticeEmbedding (sparseTruncationVertices q a b j N i)) =
      ({0, latticeEmbedding ((N : ℤ) • a)} : Set RealPlane) +
        {0, latticeEmbedding ((N : ℤ) • b)} := by
    calc
      _ = emb '' Set.range (sparseTruncationVertices q a b j N) := Set.range_comp' _ _
      _ = emb '' (({0, (N : ℤ) • a} : Set Site) + {0, (N : ℤ) • b}) := by
        rw [sparseTruncationVertices_range hq a b j N hj0 hjq]
      _ = _ := by
        rw [Set.image_add]
        simp only [Set.image_insert_eq, Set.image_singleton, map_zero]
        rfl
  rw [hgen, convexHull_add, convexHull_pair, convexHull_pair,
    lineInterval_eq_segment 0 (latticeEmbedding a) 0 N (Nat.cast_nonneg N),
    lineInterval_eq_segment 0 (latticeEmbedding b) 0 N (Nat.cast_nonneg N)]
  simp only [latticeEmbedding_zsmul, Int.cast_natCast, zero_smul, zero_add]

-- each cyclic normal attains the exact sum of its two endpoint minima.
theorem sparseTruncationVertices_normal_minimum {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    (e : ZMod (2 * q) → Site) (horder : CyclicEdgeOrder e)
    (hanti : ∀ i, e (i + (q : ZMod (2 * q))) = -e i)
    (j N : ℕ) (hj0 : 0 < j) (hjq : j < q) (i : ZMod (2 * q)) :
    directionNormal (e i) (sparseTruncationVertices q (e 0) (e (j : ZMod (2 * q))) j N i) =
      (N : ℤ) * (min 0 (directionNormal (e i) (e 0)) +
        min 0 (directionNormal (e i) (e (j : ZMod (2 * q))))) := by
  let ν := directionNormal (e i)
  let a := e 0
  let b := e (j : ZMod (2 * q))
  let w := sparseTruncationVertices q a b j N
  have hrange := sparseTruncationVertices_range hq a b j N hj0 hjq
  have hbound (c x : Site) (hx : x ∈ ({0, (N : ℤ) • c} : Set Site)) :
      (N : ℤ) * min 0 (ν c) ≤ ν x := by
    rw [mul_min_of_nonneg _ _ (Int.natCast_nonneg N), mul_zero]
    rcases hx with rfl | hx
    · simpa only [map_zero] using (min_le_left (0 : ℤ) ((N : ℤ) * ν c))
    · rw [Set.mem_singleton_iff] at hx
      rw [hx, map_zsmul, smul_eq_mul]
      exact min_le_right _ _
  have hattains (c : Site) : ∃ x ∈ ({0, (N : ℤ) • c} : Set Site),
      ν x = (N : ℤ) * min 0 (ν c) := by
    rcases le_total (ν c) 0 with hc | hc
    · refine ⟨(N : ℤ) • c, by simp, ?_⟩
      rw [map_zsmul, smul_eq_mul, min_eq_right hc]
    · refine ⟨0, by simp, ?_⟩
      rw [map_zero, min_eq_left hc, mul_zero]
  have hlower : (N : ℤ) * (min 0 (ν a) + min 0 (ν b)) ≤ ν (w i) := by
    have hwi : w i ∈ ({0, (N : ℤ) • a} : Set Site) + {0, (N : ℤ) • b} := by
      rw [← hrange]
      exact ⟨i, rfl⟩
    obtain ⟨x, hx, y, hy, he⟩ := hwi
    rw [← he, map_add, mul_add]
    exact add_le_add (hbound a x hx) (hbound b y hy)
  obtain ⟨x, hx, hxl⟩ := hattains a
  obtain ⟨y, hy, hyl⟩ := hattains b
  have hxy : x + y ∈ Set.range w := by
    rw [hrange]
    exact Set.add_mem_add hx hy
  obtain ⟨k, hk⟩ := hxy
  have hm := ordered_cyclic_walk_normal_minimum e horder w (sparseTruncationLengths q j N)
    (sparseTruncationLengths_nonnegative q j N)
    (sparseTruncationVertices_next e hanti j N hj0 hjq) i k
  change ν (w i) ≤ ν (w k) at hm
  rw [hk, map_add, hxl, hyl, ← mul_add] at hm
  exact le_antisymm hm hlower

-- adding the sparse walk yields the complete finite truncation facet presentation.
theorem finite_factor_ray_truncation_facets {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    (e : ZMod (2 * q) → Site) (horder : CyclicEdgeOrder e)
    (hanti : ∀ i, e (i + (q : ZMod (2 * q))) = -e i)
    (T : Finset Site) (P : OrderedCyclicLatticePolygon e T)
    (j N : ℕ) (hj0 : 0 < j) (hjq : j < q) :
    latticeHull T + lineInterval 0 (latticeEmbedding (e 0)) 0 (N : ℝ) +
        lineInterval 0 (latticeEmbedding (e (j : ZMod (2 * q)))) 0 (N : ℝ) =
      {x : RealPlane | ∀ i,
        ((directionNormal (e i) (P.vertex i) : ℝ) + (N : ℝ) *
          (min 0 (directionNormal (e i) (e 0) : ℝ) +
            min 0 (directionNormal (e i) (e (j : ZMod (2 * q))) : ℝ))) ≤
          latticeNormal (directionNormal (e i)) x} := by
  let w := sparseTruncationVertices q (e 0) (e (j : ZMod (2 * q))) j N
  let d := sparseTruncationLengths q j N
  have hd : ∀ i, 0 ≤ d i := sparseTruncationLengths_nonnegative q j N
  have hw : ∀ i, w (i + 1) = w i + d i • e i := sparseTruncationVertices_next e hanti j N hj0 hjq
  have hs := ordered_cyclic_walk_minkowski e horder P.vertex w P.edgeLength d P.length_pos hd P.edge_eq hw
  rw [← P.hull_eq, sparseTruncationVertices_hull hq (e 0) (e (j : ZMod (2 * q))) j N hj0 hjq,
    ← add_assoc] at hs
  have hpos : ∀ i, 0 < P.edgeLength i + d i := fun i => add_pos_of_pos_of_nonneg (P.length_pos i) (hd i)
  have hedge : ∀ i, P.vertex (i + 1) + w (i + 1) =
      P.vertex i + w i + (P.edgeLength i + d i) • e i := by
    intro i
    rw [P.edge_eq, hw, add_smul]
    abel
  have hf := ordered_cyclic_walk_facet_presentation e horder (fun i => P.vertex i + w i)
    (fun i => P.edgeLength i + d i) hpos hedge
  have hlevel (i : ZMod (2 * q)) :
      (directionNormal (e i) (P.vertex i + w i) : ℝ) =
        (directionNormal (e i) (P.vertex i) : ℝ) + (N : ℝ) *
          (min 0 (directionNormal (e i) (e 0) : ℝ) +
            min 0 (directionNormal (e i) (e (j : ZMod (2 * q))) : ℝ)) := by
    rw [map_add]
    change ((directionNormal (e i) (P.vertex i) +
      directionNormal (e i) (sparseTruncationVertices q (e 0) (e (j : ZMod (2 * q))) j N i) : ℤ) : ℝ) = _
    rw [sparseTruncationVertices_normal_minimum hq e horder hanti j N hj0 hjq]
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_min, Int.cast_zero]
  rw [hs] at hf
  simpa only [hlevel] using hf

end KumarNivat
