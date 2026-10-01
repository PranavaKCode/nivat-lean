import KumarNivat.PairedStructureRayChainNormals
import KumarNivat.PolyhedralLimits

open Filter Topology

namespace KumarNivat

-- bounded ray truncations remove exactly the actual facets whose normal decreases on one of the named rays.
theorem finite_ray_truncation_facet_union {I : Type*} (J : Finset I)
    (μ : I → Site →+ ℤ) (z : I → ℤ) (a b : Site) :
    (⋃ N : ℕ, finiteInwardRegion J μ
      (fun i => z i + (N : ℤ) * (min 0 (μ i a) + min 0 (μ i b)))) =
        finiteInwardRegion (J.filter (fun i => 0 ≤ μ i a ∧ 0 ≤ μ i b)) μ z := by
  classical
  let K := J.filter (fun i => 0 ≤ μ i a ∧ 0 ≤ μ i b)
  let d : I → ℤ := fun i => min 0 (μ i a) + min 0 (μ i b)
  have hzero : ∀ i ∈ K, d i = 0 := by
    intro i hi
    obtain ⟨_hi, ha, hb⟩ := Finset.mem_filter.mp hi
    simp only [d, min_eq_left ha, min_eq_left hb, add_zero]
  apply finite_inward_region_union J K (Finset.filter_subset _ _) μ
    (fun N i => z i + (N : ℤ) * d i) z
  · intro N i hi
    simp only [hzero i hi, mul_zero, add_zero, le_refl]
  · intro i hi
    exact Eventually.of_forall (fun N => by simp only [hzero i hi, mul_zero, add_zero])
  · intro i hi hnot
    have hbad : ¬ (0 ≤ μ i a ∧ 0 ≤ μ i b) := fun h => hnot (Finset.mem_filter.mpr ⟨hi, h⟩)
    have hd : d i < 0 := by
      have ha := min_le_left (0 : ℤ) (μ i a)
      have hb := min_le_left (0 : ℤ) (μ i b)
      have ha' := min_le_right (0 : ℤ) (μ i a)
      have hb' := min_le_right (0 : ℤ) (μ i b)
      dsimp [d]
      omega
    have hdR : (d i : ℝ) ≤ -1 := by exact_mod_cast (by omega : d i ≤ -1)
    apply tendsto_atBot.mpr
    intro t
    obtain ⟨N, hN⟩ := exists_nat_gt ((z i : ℝ) - t)
    filter_upwards [eventually_ge_atTop N] with n hn
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast]
    have hnR : (N : ℝ) ≤ n := by exact_mod_cast hn
    have hn₀ : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith

-- the surviving actual fan facets are the fixed old-ray half-plane and the later opposite-factor inequalities.
theorem forward_factor_surviving_facets_eq_inward_region {q : ℕ} [NeZero (2 * q)]
    (e : ZMod (2 * q) → Site) (hfan : AnchoredChainFanOrder e)
    (k : ℕ) (hk₀ : 0 < k) (hkq : k < q) (z : ℕ → ℤ) :
    finiteInwardRegion ((Finset.range (2 * q)).filter (fun i : ℕ =>
      0 ≤ directionNormal (e (i : ZMod (2 * q))) (e 0) ∧
        0 ≤ directionNormal (e (i : ZMod (2 * q))) (e (k : ZMod (2 * q)))))
      (fun i : ℕ => directionNormal (e (i : ZMod (2 * q)))) z =
        inwardLayerRegion (directionNormal (e 0)) (z 0) (Finset.Icc k (q - 1))
          (fun i => -directionNormal (e (i : ZMod (2 * q)))) (fun i => z (q + i)) := by
  classical
  have hnormal (a : Site) : directionNormal (-a) = -directionNormal a := by
    ext g
    simp [directionNormal, determinant]
    ring
  have hindex (i : ℕ) : e ((q + i : ℕ) : ZMod (2 * q)) = -e (i : ZMod (2 * q)) := by
    rw [Nat.cast_add, add_comm, hfan.opposite]
  ext x
  constructor
  · intro hx
    have hzero : 0 ∈ (Finset.range (2 * q)).filter (fun i : ℕ =>
        0 ≤ directionNormal (e (i : ZMod (2 * q))) (e 0) ∧
          0 ≤ directionNormal (e (i : ZMod (2 * q))) (e (k : ZMod (2 * q)))) := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr (by omega), ?_⟩
      exact (forward_factor_normal_survives_iff e hfan k hk₀ hkq 0 (by omega)).mpr (Or.inl rfl)
    refine ⟨by simpa only [Nat.cast_zero] using hx 0 hzero, ?_⟩
    intro i hi
    obtain ⟨hki, hiq⟩ := Finset.mem_Icc.mp hi
    have hm : q + i ∈ (Finset.range (2 * q)).filter (fun j : ℕ =>
        0 ≤ directionNormal (e (j : ZMod (2 * q))) (e 0) ∧
          0 ≤ directionNormal (e (j : ZMod (2 * q))) (e (k : ZMod (2 * q)))) := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
        (forward_factor_normal_survives_iff e hfan k hk₀ hkq (q + i) (by omega)).mpr (Or.inr (by omega))⟩
    simpa only [hindex, hnormal] using hx (q + i) hm
  · intro hx i hi
    obtain ⟨hiq, hsign⟩ := Finset.mem_filter.mp hi
    have hiq' := Finset.mem_range.mp hiq
    rcases (forward_factor_normal_survives_iff e hfan k hk₀ hkq i hiq').mp hsign with hi₀ | hki
    · subst i
      simpa only [Nat.cast_zero] using hx.1
    · have hj : i - q ∈ Finset.Icc k (q - 1) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      have he : q + (i - q) = i := by omega
      have h := hx.2 (i - q) hj
      change (z i : ℝ) ≤ latticeNormal (directionNormal (e (i : ZMod (2 * q)))) x
      rw [← he, hindex, hnormal]
      exact h

end KumarNivat
