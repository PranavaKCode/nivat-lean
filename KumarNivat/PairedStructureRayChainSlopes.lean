import KumarNivat.PairedStructureRayChainFan

namespace KumarNivat

-- every retained later factor facet is strictly inward on both actual rays of the current stage.
theorem forward_factor_ray_chain_slopes {q : ℕ} [NeZero (2 * q)]
    (e : ZMod (2 * q) → Site) (hfan : AnchoredChainFanOrder e)
    (k : ℕ) (hk₀ : 0 < k) (hkq : k < q) :
    0 < determinant (e 0) (e (k : ZMod (2 * q))) ∧
      0 < (-directionNormal (e (k : ZMod (2 * q)))) (e 0) ∧
      (-directionNormal (e (k : ZMod (2 * q)))) (e (k : ZMod (2 * q))) = 0 ∧
      ∀ i : ℕ, k < i → i < q →
        0 < (-directionNormal (e (i : ZMod (2 * q)))) (e 0) ∧
        0 < (-directionNormal (e (i : ZMod (2 * q)))) (e (k : ZMod (2 * q))) := by
  have hcross (p r : Site) : (-directionNormal r) p = determinant p r := by
    simp [directionNormal, determinant]
    ring
  have hk : 0 < determinant (e 0) (e (k : ZMod (2 * q))) := by
    simpa only [Nat.cast_zero] using anchored_chain_first_half_pair_positive e hfan 0 k hk₀ hkq
  refine ⟨hk, by rwa [hcross], by simp [directionNormal_self], ?_⟩
  intro i hki hiq
  rw [hcross, hcross]
  refine ⟨?_, anchored_chain_first_half_pair_positive e hfan k i hki hiq⟩
  simpa only [Nat.cast_zero] using anchored_chain_first_half_pair_positive e hfan 0 i (by omega) hiq

-- the actual no-intermediate-factor condition forces the initial moving ray to be the immediate successor.
theorem initial_factor_ray_is_adjacent {q : ℕ} [NeZero (2 * q)]
    (hs : List Site) (hdirs : ∀ g ∈ hs, g ≠ 0)
    (e : ZMod (2 * q) → Site) (hfan : AnchoredChainFanOrder e)
    (hprimitive : ∀ i, Int.gcd (e i).1 (e i).2 = 1)
    (hsource : ∀ i, ∃ g ∈ hs, determinant (e i) g = 0)
    (j : ℕ) (hj₀ : 0 < j) (hjq : j < q)
    (μ : Site →+ ℤ) (hμb : μ (e (j : ZMod (2 * q))) = 0) (hμa : 0 < μ (e 0))
    (hbetween : ∀ g ∈ hs,
      (¬ ((-directionNormal (e 0)) g < 0 ∧ 0 < μ g)) ∧
      (¬ ((-directionNormal (e 0)) (-g) < 0 ∧ 0 < μ (-g)))) : j = 1 := by
  by_contra hj
  have h1j : 1 < j := by omega
  let r := e (1 : ZMod (2 * q))
  have hD : 0 < determinant (e 0) (e (j : ZMod (2 * q))) :=
    (forward_factor_ray_chain_slopes e hfan j hj₀ hjq).1
  have har : 0 < determinant (e 0) r := by
    simpa only [r, Nat.cast_zero, Nat.cast_one] using anchored_chain_first_half_pair_positive e hfan 0 1 (by omega) (by omega)
  have hrb : 0 < determinant r (e (j : ZMod (2 * q))) :=
    by simpa only [r, Nat.cast_one] using anchored_chain_first_half_pair_positive e hfan 1 j h1j hjq
  have hμr : 0 < μ r := by
    have he := normal_cramer_identity μ (e 0) (e (j : ZMod (2 * q))) r
    rw [hμb, mul_zero, add_zero] at he
    have hright := mul_pos hrb hμa
    by_contra hnot
    have hleft := mul_nonpos_of_nonneg_of_nonpos hD.le (le_of_not_gt hnot)
    rw [he] at hleft
    exact not_lt_of_ge hleft hright
  obtain ⟨g, hg, hparallel⟩ := hsource (1 : ZMod (2 * q))
  obtain ⟨τ, _hτ, hline⟩ := primitive_direction_coordinate r (hprimitive _)
  have hrep : g = τ g • r := hline g hparallel
  have hm : τ g ≠ 0 := by
    intro hm
    exact hdirs g hg (by rw [hrep, hm, zero_smul])
  rcases lt_or_gt_of_ne hm with hm | hm
  · apply (hbetween g hg).2
    rw [hrep, ← neg_smul, map_zsmul, map_zsmul]
    have hνr : (-directionNormal (e 0)) r = -determinant (e 0) r := rfl
    simp only [smul_eq_mul, hνr]
    exact ⟨mul_neg_of_pos_of_neg (neg_pos.mpr hm) (neg_neg_of_pos har),
      mul_pos (neg_pos.mpr hm) hμr⟩
  · apply (hbetween g hg).1
    rw [hrep, map_zsmul, map_zsmul]
    have hνr : (-directionNormal (e 0)) r = -determinant (e 0) r := rfl
    simp only [smul_eq_mul, hνr]
    exact ⟨mul_neg_of_pos_of_neg hm (neg_neg_of_pos har), mul_pos hm hμr⟩

end KumarNivat
