import KumarNivat.PairedStructureRayChainCones
import KumarNivat.PairedStructureRayChainSlopes

namespace KumarNivat

-- the negative first-half factor normals survive exactly at and after the current moving facet.
theorem forward_negative_factor_normal_survives_iff {q : ℕ} [NeZero (2 * q)]
    (e : ZMod (2 * q) → Site) (hfan : AnchoredChainFanOrder e)
    (k : ℕ) (hk₀ : 0 < k) (hkq : k < q) (j : ℕ) (hjq : j < q) :
    (0 ≤ (-directionNormal (e (j : ZMod (2 * q)))) (e 0) ∧
      0 ≤ (-directionNormal (e (j : ZMod (2 * q)))) (e (k : ZMod (2 * q)))) ↔ k ≤ j := by
  have hcross (a b : Site) : (-directionNormal b) a = determinant a b := by simp [directionNormal, determinant]; ring
  rw [hcross, hcross]
  constructor
  · intro h
    by_contra hj
    have hturn := anchored_chain_first_half_pair_positive e hfan j k (by omega) hkq
    have hrev : determinant (e (k : ZMod (2 * q))) (e (j : ZMod (2 * q))) =
        -determinant (e (j : ZMod (2 * q))) (e (k : ZMod (2 * q))) := by simp [determinant]; ring
    rw [hrev] at h
    omega
  · intro hkj
    have hfirst : 0 < determinant (e 0) (e (j : ZMod (2 * q))) := by
      simpa only [Nat.cast_zero] using anchored_chain_first_half_pair_positive e hfan 0 j (by omega) hjq
    refine ⟨hfirst.le, ?_⟩
    by_cases he : j = k
    · subst j
      simp [determinant, mul_comm]
    · exact (anchored_chain_first_half_pair_positive e hfan k j (by omega) hjq).le

-- the actual full fan loses precisely its first half and the earlier opposite factor facets.
theorem forward_factor_normal_survives_iff {q : ℕ} [NeZero (2 * q)]
    (e : ZMod (2 * q) → Site) (hfan : AnchoredChainFanOrder e)
    (k : ℕ) (hk₀ : 0 < k) (hkq : k < q) (i : ℕ) (hiq : i < 2 * q) :
    (0 ≤ directionNormal (e (i : ZMod (2 * q))) (e 0) ∧
      0 ≤ directionNormal (e (i : ZMod (2 * q))) (e (k : ZMod (2 * q)))) ↔
        i = 0 ∨ q + k ≤ i := by
  by_cases hi₀ : i = 0
  · subst i
    have hk := (forward_factor_ray_chain_slopes e hfan k hk₀ hkq).1
    simp only [Nat.cast_zero, directionNormal_self, le_refl, true_and, true_or]
    exact ⟨fun _ => trivial, fun _ => hk.le⟩
  · by_cases hiq' : i < q
    · have hturn : 0 < determinant (e 0) (e (i : ZMod (2 * q))) := by
        simpa only [Nat.cast_zero] using anchored_chain_first_half_pair_positive e hfan 0 i (by omega) hiq'
      have hrev : directionNormal (e (i : ZMod (2 * q))) (e 0) =
          -determinant (e 0) (e (i : ZMod (2 * q))) := by simp [directionNormal, determinant]; ring
      rw [hrev]
      constructor
      · intro h
        omega
      · intro h
        rcases h with h | h <;> omega
    · have hindex : e (i : ZMod (2 * q)) = -e ((i - q : ℕ) : ZMod (2 * q)) := by
        have he : ((i - q : ℕ) : ZMod (2 * q)) + (q : ZMod (2 * q)) =
            (i : ZMod (2 * q)) := by rw [← Nat.cast_add, Nat.sub_add_cancel (by omega : q ≤ i)]
        rw [← he, hfan.opposite]
      have hnormal (a : Site) : directionNormal (-a) = -directionNormal a := by
        ext g
        simp [directionNormal, determinant]
        ring
      rw [hindex, hnormal]
      rw [forward_negative_factor_normal_survives_iff e hfan k hk₀ hkq (i - q) (by omega)]
      omega

-- all actual surviving later normals give the same pointed cone as its two endpoint normals.
theorem forward_factor_cone_surviving_normals {q : ℕ} [NeZero (2 * q)]
    (e : ZMod (2 * q) → Site) (hfan : AnchoredChainFanOrder e)
    (k : ℕ) (hk₀ : 0 < k) (hkq : k < q) :
    forwardFactorRayCone e k = {x | 0 ≤ latticeNormal (directionNormal (e 0)) x ∧
      ∀ j ∈ Finset.Icc k (q - 1), 0 ≤ latticeNormal (-directionNormal (e (j : ZMod (2 * q)))) x} := by
  have hkdet := (forward_factor_ray_chain_slopes e hfan k hk₀ hkq).1
  simp only [forwardFactorRayCone, hkq, ite_true]
  ext x
  constructor
  · intro hx
    have hends := (forward_two_ray_cone_normals _ _ hkdet) ▸ hx
    refine ⟨hends.1, ?_⟩
    intro j hj
    obtain ⟨hkj, hjq⟩ := Finset.mem_Icc.mp hj
    have hsurvive := (forward_negative_factor_normal_survives_iff e hfan k hk₀ hkq j (by omega)).mpr hkj
    rcases hx with ⟨_, ⟨α, hα, rfl⟩, _, ⟨β, hβ, rfl⟩, rfl⟩
    simp only [zero_add, map_add, map_smul, latticeNormal_embedding, smul_eq_mul]
    exact add_nonneg (mul_nonneg hα (by exact_mod_cast hsurvive.1))
      (mul_nonneg hβ (by exact_mod_cast hsurvive.2))
  · intro hx
    rw [forward_two_ray_cone_normals _ _ hkdet]
    exact ⟨hx.1, hx.2 k (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)⟩

end KumarNivat
