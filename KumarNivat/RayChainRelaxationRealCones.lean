module

public import KumarNivat.PairedStructureRayChainRealMinkowski
public import KumarNivat.PairedStructureRayChainFacets

@[expose] public section

open Filter Topology

namespace KumarNivat

open scoped Pointwise

-- real support levels also retain exactly the facets nonnegative on both actual rays.
theorem real_ray_truncation_facet_union {I : Type*} (J : Finset I)
    (μ : I → Site →+ ℤ) (z : I → ℝ) (a b : Site) :
    (⋃ N : ℕ, {x : RealPlane | ∀ i ∈ J, z i + (N : ℝ) *
      ((min 0 (μ i a) + min 0 (μ i b) : ℤ) : ℝ) ≤ latticeNormal (μ i) x}) =
        {x : RealPlane | ∀ i ∈ J.filter (fun i => 0 ≤ μ i a ∧ 0 ≤ μ i b),
          z i ≤ latticeNormal (μ i) x} := by
  classical
  let K := J.filter (fun i => 0 ≤ μ i a ∧ 0 ≤ μ i b)
  let d : I → ℤ := fun i => min 0 (μ i a) + min 0 (μ i b)
  have hzero : ∀ i ∈ K, d i = 0 := by
    intro i hi
    obtain ⟨_hi, ha, hb⟩ := Finset.mem_filter.mp hi
    simp only [d, min_eq_left ha, min_eq_left hb, add_zero]
  ext x
  constructor
  · intro hx i hi
    obtain ⟨N, hN⟩ := Set.mem_iUnion.mp hx
    have h := hN i (Finset.filter_subset _ _ hi)
    change z i + (N : ℝ) * (d i : ℝ) ≤ latticeNormal (μ i) x at h
    simpa only [hzero i hi, Int.cast_zero, mul_zero, add_zero] using h
  · intro hx
    have hevent : ∀ i ∈ J, ∀ᶠ N : ℕ in atTop,
        z i + (N : ℝ) * (d i : ℝ) ≤ latticeNormal (μ i) x := by
      intro i hi
      by_cases hk : i ∈ K
      · exact Eventually.of_forall (fun N => by simpa only [hzero i hk, Int.cast_zero, mul_zero, add_zero] using hx i hk)
      · have hbad : ¬ (0 ≤ μ i a ∧ 0 ≤ μ i b) := fun h => hk (Finset.mem_filter.mpr ⟨hi, h⟩)
        have hd : d i < 0 := by
          have ha := min_le_left (0 : ℤ) (μ i a)
          have hb := min_le_left (0 : ℤ) (μ i b)
          have ha' := min_le_right (0 : ℤ) (μ i a)
          have hb' := min_le_right (0 : ℤ) (μ i b)
          dsimp [d]
          omega
        have hdR : (d i : ℝ) ≤ -1 := by exact_mod_cast (by omega : d i ≤ -1)
        obtain ⟨M, hM⟩ := exists_nat_ge (z i - latticeNormal (μ i) x)
        filter_upwards [eventually_ge_atTop M] with N hN
        have hNM : (M : ℝ) ≤ N := by exact_mod_cast hN
        have hN₀ : (0 : ℝ) ≤ N := Nat.cast_nonneg N
        nlinarith
    obtain ⟨N, hN⟩ := (J.eventually_all.mpr hevent).exists
    exact Set.mem_iUnion.mpr ⟨N, hN⟩

-- adding the original ordered rectangle walk truncates the two rays of any positive real cyclic walk.
theorem ordered_real_cyclic_ray_truncation_facets {q : ℕ} [NeZero q]
    (hq : 2 ≤ q) (e : ZMod (2 * q) → Site) (hfan : AnchoredChainFanOrder e)
    (v : ZMod (2 * q) → RealPlane) (r : ZMod (2 * q) → ℝ) (hr : ∀ i, 0 < r i)
    (hv : ∀ i, v (i + 1) = v i + r i • latticeEmbedding (e i))
    (k N : ℕ) (hk₀ : 0 < k) (hkq : k < q) :
    convexHull ℝ (Set.range v) +
      (lineInterval 0 (latticeEmbedding (e 0)) 0 N + lineInterval 0 (latticeEmbedding (e (k : ZMod (2 * q)))) 0 N) =
        {x : RealPlane | ∀ i, latticeNormal (directionNormal (e i)) (v i) + (N : ℝ) *
          (min 0 (directionNormal (e i) (e 0) : ℝ) +
            min 0 (directionNormal (e i) (e (k : ZMod (2 * q))) : ℝ)) ≤ latticeNormal (directionNormal (e i)) x} := by
  let w := sparseTruncationVertices q (e 0) (e (k : ZMod (2 * q))) k N
  let d := sparseTruncationLengths q k N
  have hd : ∀ i, 0 ≤ (d i : ℝ) := fun i => by exact_mod_cast sparseTruncationLengths_nonnegative q k N i
  have hw : ∀ i, latticeEmbedding (w (i + 1)) = latticeEmbedding (w i) + (d i : ℝ) • latticeEmbedding (e i) := by
    intro i
    dsimp [w, d]
    rw [sparseTruncationVertices_next e hfan.opposite k N hk₀ hkq, latticeEmbedding_add, latticeEmbedding_zsmul]
  have hsum := ordered_real_cyclic_walk_minkowski e hfan.order v (fun i => latticeEmbedding (w i)) r
    (fun i => (d i : ℝ)) hr hd hv hw
  have hhull := sparseTruncationVertices_hull hq (e 0) (e (k : ZMod (2 * q))) k N hk₀ hkq
  rw [hhull] at hsum
  have hpos : ∀ i, 0 < r i + (d i : ℝ) := fun i => add_pos_of_pos_of_nonneg (hr i) (hd i)
  have hedge : ∀ i, v (i + 1) + latticeEmbedding (w (i + 1)) =
      v i + latticeEmbedding (w i) + (r i + (d i : ℝ)) • latticeEmbedding (e i) := by
    intro i
    rw [hv, hw, add_smul]
    abel
  have hf := ordered_real_cyclic_walk_facet_presentation e hfan.order
    (fun i => v i + latticeEmbedding (w i)) (fun i => r i + (d i : ℝ)) hpos hedge
  have hlevel (i : ZMod (2 * q)) : latticeNormal (directionNormal (e i)) (v i + latticeEmbedding (w i)) =
      latticeNormal (directionNormal (e i)) (v i) + (N : ℝ) *
        (min 0 (directionNormal (e i) (e 0) : ℝ) + min 0 (directionNormal (e i) (e (k : ZMod (2 * q))) : ℝ)) := by
    rw [map_add, latticeNormal_embedding]
    rw [sparseTruncationVertices_normal_minimum hq e hfan.order hfan.opposite k N hk₀ hkq]
    simp only [Int.cast_mul, Int.cast_add, Int.cast_natCast, Int.cast_min, Int.cast_zero]
  rw [hsum] at hf
  simpa only [hlevel] using hf

-- the same actual truncations derive the complete surviving facet presentation for real residual polygons.
theorem ordered_real_cyclic_two_ray_facets {q : ℕ} [NeZero q]
    (hq : 2 ≤ q) (e : ZMod (2 * q) → Site) (hfan : AnchoredChainFanOrder e)
    (v : ZMod (2 * q) → RealPlane) (r : ZMod (2 * q) → ℝ) (hr : ∀ i, 0 < r i)
    (hv : ∀ i, v (i + 1) = v i + r i • latticeEmbedding (e i))
    (k : ℕ) (hk₀ : 0 < k) (hkq : k < q) :
    convexHull ℝ (Set.range v) + forwardTwoRayCone (e 0) (e (k : ZMod (2 * q))) =
      {x : RealPlane | ∀ i : ℕ, i < 2 * q →
        0 ≤ directionNormal (e (i : ZMod (2 * q))) (e 0) →
          0 ≤ directionNormal (e (i : ZMod (2 * q))) (e (k : ZMod (2 * q))) →
            latticeNormal (directionNormal (e (i : ZMod (2 * q)))) (v (i : ZMod (2 * q))) ≤
              latticeNormal (directionNormal (e (i : ZMod (2 * q)))) x} := by
  classical
  let μ : ℕ → Site →+ ℤ := fun i => directionNormal (e (i : ZMod (2 * q)))
  let z : ℕ → ℝ := fun i => latticeNormal (μ i) (v (i : ZMod (2 * q)))
  have hunion : (⋃ N : ℕ, convexHull ℝ (Set.range v) +
      (lineInterval 0 (latticeEmbedding (e 0)) 0 N + lineInterval 0 (latticeEmbedding (e (k : ZMod (2 * q)))) 0 N)) =
        convexHull ℝ (Set.range v) + forwardTwoRayCone (e 0) (e (k : ZMod (2 * q))) := by
    rw [← line_interval_truncations_exhaust_two_ray_cone]
    ext x
    constructor
    · intro hx
      obtain ⟨N, u, hu, w, hw, rfl⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_add.mpr ⟨u, hu, w, Set.mem_iUnion.mpr ⟨N, hw⟩, rfl⟩
    · rintro ⟨u, hu, w, hw, rfl⟩
      obtain ⟨N, hN⟩ := Set.mem_iUnion.mp hw
      exact Set.mem_iUnion.mpr ⟨N, Set.mem_add.mpr ⟨u, hu, w, hN, rfl⟩⟩
  have htrunc (N : ℕ) : convexHull ℝ (Set.range v) +
      (lineInterval 0 (latticeEmbedding (e 0)) 0 N + lineInterval 0 (latticeEmbedding (e (k : ZMod (2 * q)))) 0 N) =
      {x : RealPlane | ∀ i ∈ Finset.range (2 * q), z i + (N : ℝ) *
        ((min 0 (μ i (e 0)) + min 0 (μ i (e (k : ZMod (2 * q)))) : ℤ) : ℝ) ≤ latticeNormal (μ i) x} := by
    rw [ordered_real_cyclic_ray_truncation_facets hq e hfan v r hr hv k N hk₀ hkq]
    ext x
    constructor
    · intro hx i _hi
      simpa only [z, μ, Int.cast_add, Int.cast_min, Int.cast_zero] using hx (i : ZMod (2 * q))
    · intro hx i
      have h := hx i.val (Finset.mem_range.mpr (ZMod.val_lt i))
      simpa only [z, μ, ZMod.natCast_zmod_val, Int.cast_add, Int.cast_min, Int.cast_zero] using h
  rw [← hunion]
  simp_rw [htrunc]
  rw [real_ray_truncation_facet_union]
  ext x
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h i hi ha hb => h i ⟨hi, ha, hb⟩, fun h i hi => h i hi.1 hi.2.1 hi.2.2⟩

end KumarNivat
