import KumarNivat.NewtonSingleRayFacetsSegment
import KumarNivat.PairedStructureRayChainRealMinkowski
import KumarNivat.PolyhedralLimits

open Filter Topology

namespace KumarNivat

open scoped Pointwise

-- a segment in any first-half factor direction changes each actual polygon support by its endpoint minimum.
theorem finite_single_factor_segment_facets {q : ℕ} [NeZero q]
    (e : ZMod (2 * q) → Site) (horder : CyclicEdgeOrder e)
    (hanti : ∀ i, e (i + (q : ZMod (2 * q))) = -e i)
    (F : Finset Site) (P : OrderedCyclicLatticePolygon e F)
    (j : ℕ) (hjq : j < q) (t : ℝ) (ht : 0 ≤ t) :
    latticeHull F + lineInterval 0 (latticeEmbedding (e (j : ZMod (2 * q)))) 0 t =
      {x : RealPlane | ∀ i,
        (directionNormal (e i) (P.vertex i) : ℝ) +
          t * min 0 (directionNormal (e i) (e (j : ZMod (2 * q))) : ℝ) ≤
          latticeNormal (directionNormal (e i)) x} := by
  let v := fun i => latticeEmbedding (P.vertex i)
  let r := fun i => (P.edgeLength i : ℝ)
  let w := singleFactorSegmentVertices q j e t
  let d := singleFactorSegmentLengths q j t
  have hr : ∀ i, 0 < r i := fun i => by
    change 0 < (P.edgeLength i : ℝ)
    exact_mod_cast P.length_pos i
  have hd : ∀ i, 0 ≤ d i := singleFactorSegmentLengths_nonnegative q j t ht
  have hv : ∀ i, v (i + 1) = v i + r i • latticeEmbedding (e i) := by
    intro i
    dsimp [v, r]
    rw [P.edge_eq, latticeEmbedding_add, latticeEmbedding_zsmul]
  have hw : ∀ i, w (i + 1) = w i + d i • latticeEmbedding (e i) :=
    singleFactorSegmentVertices_next e hanti j hjq t
  have hs := ordered_real_cyclic_walk_minkowski e horder v w r d hr hd hv hw
  change convexHull ℝ (Set.range (fun i => v i + w i)) =
    convexHull ℝ (Set.range (fun i => latticeEmbedding (P.vertex i))) +
      convexHull ℝ (Set.range (singleFactorSegmentVertices q j e t)) at hs
  rw [← P.hull_eq, singleFactorSegmentVertices_hull e j hjq t ht] at hs
  have hpos : ∀ i, 0 < r i + d i := fun i => add_pos_of_pos_of_nonneg (hr i) (hd i)
  have hedge : ∀ i, v (i + 1) + w (i + 1) =
      v i + w i + (r i + d i) • latticeEmbedding (e i) := by
    intro i
    rw [hv, hw, add_smul]
    abel
  have hf := ordered_real_cyclic_walk_facet_presentation e horder (fun i => v i + w i)
    (fun i => r i + d i) hpos hedge
  have hlevel (i : ZMod (2 * q)) :
      latticeNormal (directionNormal (e i)) (v i + w i) =
        (directionNormal (e i) (P.vertex i) : ℝ) +
          t * min 0 (directionNormal (e i) (e (j : ZMod (2 * q))) : ℝ) := by
    rw [map_add]
    change latticeNormal (directionNormal (e i)) (latticeEmbedding (P.vertex i)) +
      latticeNormal (directionNormal (e i)) (singleFactorSegmentVertices q j e t i) = _
    rw [latticeNormal_embedding, singleFactorSegmentVertices_normal_minimum e horder hanti j hjq t ht]
  rw [hs] at hf
  simpa only [hlevel] using hf

-- natural truncations of a forward ray have integer support levels for every actual cyclic facet.
theorem finite_single_factor_ray_truncation_facets {q : ℕ} [NeZero q]
    (e : ZMod (2 * q) → Site) (horder : CyclicEdgeOrder e)
    (hanti : ∀ i, e (i + (q : ZMod (2 * q))) = -e i)
    (F : Finset Site) (P : OrderedCyclicLatticePolygon e F) (N : ℕ) :
    latticeHull F + lineInterval 0 (latticeEmbedding (e 0)) 0 (N : ℝ) =
      finiteInwardRegion Finset.univ (fun i => directionNormal (e i))
        (fun i => directionNormal (e i) (P.vertex i) +
          (N : ℤ) * min 0 (directionNormal (e i) (e 0))) := by
  have hq : 0 < q := NeZero.pos q
  have hf := finite_single_factor_segment_facets e horder hanti F P 0 hq N (Nat.cast_nonneg N)
  simp only [Nat.cast_zero] at hf
  rw [hf]
  ext x
  simp only [finiteInwardRegion, Set.mem_ofPred_eq, Finset.mem_univ,
    forall_const, Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_min, Int.cast_zero]

-- the increasing integer segment bounds exhaust the actual forward ray.
theorem single_ray_segment_truncations_union (a : Site) :
    (⋃ N : ℕ, lineInterval 0 (latticeEmbedding a) 0 (N : ℝ)) =
      lineRay 0 (latticeEmbedding a) 0 := by
  ext x
  constructor
  · intro hx
    obtain ⟨N, s, hs, rfl⟩ := Set.mem_iUnion.mp hx
    exact ⟨s, hs.1, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨N, hN⟩ := exists_nat_ge s
    exact Set.mem_iUnion.mpr ⟨N, s, ⟨hs, hN⟩, rfl⟩

-- an arbitrary real base set commutes with this same ray exhaustion.
theorem base_single_ray_truncations_union (A : Set RealPlane) (a : Site) :
    (⋃ N : ℕ, A + lineInterval 0 (latticeEmbedding a) 0 (N : ℝ)) =
      A + lineRay 0 (latticeEmbedding a) 0 := by
  rw [← single_ray_segment_truncations_union a]
  ext x
  constructor
  · intro hx
    obtain ⟨N, u, hu, v, hv, rfl⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_add.mpr ⟨u, hu, v, Set.mem_iUnion.mpr ⟨N, hv⟩, rfl⟩
  · rintro ⟨u, hu, v, hv, rfl⟩
    obtain ⟨N, hN⟩ := Set.mem_iUnion.mp hv
    exact Set.mem_iUnion.mpr ⟨N, Set.mem_add.mpr ⟨u, hu, v, hN, rfl⟩⟩

-- supports with negative slope escape while the nonnegative ray slopes keep their original attained levels.
theorem single_ray_truncation_facet_union {I : Type*} (J : Finset I)
    (μ : I → Site →+ ℤ) (z : I → ℤ) (a : Site) :
    (⋃ N : ℕ, finiteInwardRegion J μ (fun i => z i + (N : ℤ) * min 0 (μ i a))) =
      finiteInwardRegion (J.filter (fun i => 0 ≤ μ i a)) μ z := by
  classical
  let K := J.filter (fun i => 0 ≤ μ i a)
  let d := fun i => min 0 (μ i a)
  have hzero : ∀ i ∈ K, d i = 0 := by
    intro i hi
    exact min_eq_left (Finset.mem_filter.mp hi).2
  apply finite_inward_region_union J K (Finset.filter_subset _ _) μ
    (fun N i => z i + (N : ℤ) * d i) z
  · intro N i hi
    simp only [hzero i hi, mul_zero, add_zero, le_refl]
  · intro i hi
    exact Eventually.of_forall (fun N => by simp only [hzero i hi, mul_zero, add_zero])
  · intro i hi hnot
    have hnegative : μ i a < 0 := by
      have hn : ¬ 0 ≤ μ i a := fun h => hnot (Finset.mem_filter.mpr ⟨hi, h⟩)
      omega
    have hd : (d i : ℝ) ≤ -1 := by
      dsimp [d]
      rw [min_eq_right (le_of_lt hnegative)]
      exact_mod_cast (by omega : μ i a ≤ -1)
    apply tendsto_atBot.mpr
    intro t
    obtain ⟨N, hN⟩ := exists_nat_gt ((z i : ℝ) - t)
    filter_upwards [eventually_ge_atTop N] with n hn
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast]
    have hnR : (N : ℝ) ≤ n := by exact_mod_cast hn
    have hn₀ : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith

-- the exact forward-ray hull presentation applies to any polygon in the actual fan.
theorem single_factor_ray_facet_presentation {q : ℕ} [NeZero q]
    (e : ZMod (2 * q) → Site) (horder : CyclicEdgeOrder e)
    (hanti : ∀ i, e (i + (q : ZMod (2 * q))) = -e i)
    (F : Finset Site) (P : OrderedCyclicLatticePolygon e F) :
    latticeHull F + lineRay 0 (latticeEmbedding (e 0)) 0 =
      {x : RealPlane | ∀ i, 0 ≤ directionNormal (e i) (e 0) →
        (directionNormal (e i) (P.vertex i) : ℝ) ≤ latticeNormal (directionNormal (e i)) x} := by
  classical
  calc
    _ = ⋃ N : ℕ, latticeHull F + lineInterval 0 (latticeEmbedding (e 0)) 0 (N : ℝ) :=
      (base_single_ray_truncations_union (latticeHull F) (e 0)).symm
    _ = ⋃ N : ℕ, finiteInwardRegion Finset.univ (fun i => directionNormal (e i))
        (fun i => directionNormal (e i) (P.vertex i) +
          (N : ℤ) * min 0 (directionNormal (e i) (e 0))) := by
      congr 1
      funext N
      exact finite_single_factor_ray_truncation_facets e horder hanti F P N
    _ = finiteInwardRegion (Finset.univ.filter (fun i => 0 ≤ directionNormal (e i) (e 0)))
        (fun i => directionNormal (e i)) (fun i => directionNormal (e i) (P.vertex i)) :=
      single_ray_truncation_facet_union _ _ _ _
    _ = _ := by
      ext x
      simp only [finiteInwardRegion, Set.mem_ofPred_eq, Finset.mem_filter, Finset.mem_univ,
        true_and]

end KumarNivat
