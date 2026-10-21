module

public import KumarNivat.PairedStructureRayChainFan
public import KumarNivat.PairedStructureWideStripGeometry
public import KumarNivat.NewtonCyclicNormals

@[expose] public section

namespace KumarNivat

open scoped Pointwise

-- reversing an integer normal reverses its real linear extension.
theorem lattice_normal_neg_normal (ν : Site →+ ℤ) : latticeNormal (-ν) = -latticeNormal ν := by
  apply LinearMap.ext
  intro x
  simp [latticeNormal]
  ring

-- the two named rays are the actual closed pointed recession cone.
def forwardTwoRayCone (a b : Site) : Set RealPlane :=
  lineRay 0 (latticeEmbedding a) 0 + lineRay 0 (latticeEmbedding b) 0

-- the endpoint normals give an exact presentation of the pointed cone.
theorem forward_two_ray_cone_normals (a b : Site) (hab : 0 < determinant a b) :
    forwardTwoRayCone a b = {x | 0 ≤ latticeNormal (directionNormal a) x ∧
      0 ≤ latticeNormal (-directionNormal b) x} := by
  ext x
  have hD : (0 : ℝ) < (determinant a b : ℝ) := by exact_mod_cast hab
  constructor
  · rintro ⟨_, ⟨α, hα, rfl⟩, _, ⟨β, hβ, rfl⟩, rfl⟩
    change 0 ≤ latticeNormal (directionNormal a) ((0 + α • latticeEmbedding a) + (0 + β • latticeEmbedding b)) ∧
      0 ≤ latticeNormal (-directionNormal b) ((0 + α • latticeEmbedding a) + (0 + β • latticeEmbedding b))
    simp only [zero_add, map_add, map_smul, latticeNormal_embedding, smul_eq_mul]
    have hselfa : directionNormal a a = 0 := directionNormal_self a
    have hselfb : (-directionNormal b) b = 0 := by simp [directionNormal_self]
    have hcross : (-directionNormal b) a = determinant a b := by simp [directionNormal, determinant]; ring
    simp only [hselfa, hselfb, hcross, Int.cast_zero, mul_zero, zero_add, add_zero]
    exact ⟨mul_nonneg hβ hD.le, mul_nonneg hα hD.le⟩
  · intro hx
    change 0 ≤ latticeNormal (directionNormal a) x ∧ 0 ≤ latticeNormal (-directionNormal b) x at hx
    let D : ℝ := determinant a b
    let α : ℝ := -latticeNormal (directionNormal b) x / D
    let β : ℝ := latticeNormal (directionNormal a) x / D
    have hα : 0 ≤ α := div_nonneg (by simpa only [lattice_normal_neg_normal, LinearMap.neg_apply] using hx.2) hD.le
    have hβ : 0 ≤ β := div_nonneg hx.1 hD.le
    have he : x = α • latticeEmbedding a + β • latticeEmbedding b := by
      have hid := real_plane_edge_cramer_identity a b x
      calc
        x = D⁻¹ • (D • x) := by rw [smul_smul, inv_mul_cancel₀ (ne_of_gt hD), one_smul]
        _ = _ := by rw [hid]; simp only [α, β, div_eq_inv_mul, smul_add, smul_smul]
    exact Set.mem_add.mpr ⟨α • latticeEmbedding a, ⟨α, hα, by simp⟩,
      β • latticeEmbedding b, ⟨β, hβ, by simp⟩, he.symm⟩

-- rotating the second actual ray forward enlarges the cone without rotating its first ray.
theorem forward_two_ray_cone_subset (a b d : Site)
    (hab : 0 < determinant a b) (had : 0 < determinant a d) (hbd : 0 ≤ determinant b d) :
    forwardTwoRayCone a b ⊆ forwardTwoRayCone a d := by
  rw [forward_two_ray_cone_normals a d had]
  rintro x ⟨_, ⟨α, hα, rfl⟩, _, ⟨β, hβ, rfl⟩, rfl⟩
  change 0 ≤ latticeNormal (directionNormal a) ((0 + α • latticeEmbedding a) + (0 + β • latticeEmbedding b)) ∧
    0 ≤ latticeNormal (-directionNormal d) ((0 + α • latticeEmbedding a) + (0 + β • latticeEmbedding b))
  simp only [zero_add, map_add, map_smul, latticeNormal_embedding, smul_eq_mul]
  have hcross₁ : (-directionNormal d) a = determinant a d := by simp [directionNormal, determinant]; ring
  have hcross₂ : (-directionNormal d) b = determinant b d := by simp [directionNormal, determinant]; ring
  have habR : (0 : ℝ) ≤ (determinant a b : ℝ) := by exact_mod_cast hab.le
  have hadR : (0 : ℝ) ≤ (determinant a d : ℝ) := by exact_mod_cast had.le
  have hbdR : (0 : ℝ) ≤ (determinant b d : ℝ) := by exact_mod_cast hbd
  simp only [directionNormal_self, hcross₁, hcross₂, Int.cast_zero, mul_zero, zero_add]
  exact ⟨mul_nonneg hβ habR, add_nonneg (mul_nonneg hα hadR) (mul_nonneg hβ hbdR)⟩

-- adding the opposite first ray at the last stage gives the complete tangent half-plane.
theorem forward_cone_with_opposite_ray (a b : Site) (hab : 0 < determinant a b) :
    forwardTwoRayCone a b + lineRay 0 (latticeEmbedding (-a)) 0 =
      {x | 0 ≤ latticeNormal (directionNormal a) x} := by
  have hD : (0 : ℝ) < (determinant a b : ℝ) := by exact_mod_cast hab
  have hneg : latticeEmbedding (-a) = -latticeEmbedding a := by ext <;> simp [latticeEmbedding]
  ext x
  constructor
  · rintro ⟨u, hu, _, ⟨γ, hγ, rfl⟩, rfl⟩
    have hn := ((forward_two_ray_cone_normals a b hab) ▸ hu).1
    change 0 ≤ latticeNormal (directionNormal a) (u + (0 + γ • latticeEmbedding (-a)))
    simp only [zero_add, map_add, map_smul, latticeNormal_embedding, smul_eq_mul]
    have hflat : directionNormal a (-a) = 0 := by rw [map_neg, directionNormal_self, neg_zero]
    simpa only [hflat, Int.cast_zero, mul_zero, add_zero] using hn
  · intro hx
    change 0 ≤ latticeNormal (directionNormal a) x at hx
    let D : ℝ := determinant a b
    let α : ℝ := -latticeNormal (directionNormal b) x / D
    let β : ℝ := latticeNormal (directionNormal a) x / D
    have hβ : 0 ≤ β := div_nonneg hx hD.le
    have he : x = α • latticeEmbedding a + β • latticeEmbedding b := by
      have hid := real_plane_edge_cramer_identity a b x
      calc
        x = D⁻¹ • (D • x) := by rw [smul_smul, inv_mul_cancel₀ (ne_of_gt hD), one_smul]
        _ = _ := by rw [hid]; simp only [α, β, div_eq_inv_mul, smul_add, smul_smul]
    by_cases hα : 0 ≤ α
    · refine Set.mem_add.mpr ⟨α • latticeEmbedding a + β • latticeEmbedding b,
        Set.mem_add.mpr ⟨α • latticeEmbedding a, ⟨α, hα, by simp⟩,
          β • latticeEmbedding b, ⟨β, hβ, by simp⟩, rfl⟩, 0, ⟨0, by simp, by simp⟩, ?_⟩
      simpa only [add_zero] using he.symm
    · refine Set.mem_add.mpr ⟨β • latticeEmbedding b,
        Set.mem_add.mpr ⟨0, ⟨0, by simp, by simp⟩,
          β • latticeEmbedding b, ⟨β, hβ, by simp⟩, by simp⟩,
        (-α) • latticeEmbedding (-a), ⟨-α, by change 0 ≤ -α; linarith, by simp⟩, ?_⟩
      rw [hneg, smul_neg, neg_smul, neg_neg]
      rw [he]
      exact add_comm _ _

-- the sorted fan determines every stage, including the final added antipodal ray.
def forwardFactorRayCone {q : ℕ} [NeZero (2 * q)] (e : ZMod (2 * q) → Site) (k : ℕ) : Set RealPlane :=
  if k < q then forwardTwoRayCone (e 0) (e (k : ZMod (2 * q)))
  else forwardTwoRayCone (e 0) (e ((q - 1 : ℕ) : ZMod (2 * q))) +
    lineRay 0 (latticeEmbedding (-e 0)) 0

-- the actual finite forward stages are nested, and the last stage is the full homogeneous half-plane.
theorem forward_factor_ray_cones_chain {q : ℕ} [NeZero (2 * q)]
    (e : ZMod (2 * q) → Site) (hfan : AnchoredChainFanOrder e) (hq : 2 ≤ q) :
    (∀ i j : ℕ, 0 < i → i ≤ j → j ≤ q → forwardFactorRayCone e i ⊆ forwardFactorRayCone e j) ∧
      forwardFactorRayCone e q = {x | 0 ≤ latticeNormal (directionNormal (e 0)) x} := by
  have hlast : 0 < determinant (e 0) (e ((q - 1 : ℕ) : ZMod (2 * q))) := by
    simpa only [Nat.cast_zero] using anchored_chain_first_half_pair_positive e hfan 0 (q - 1) (by omega) (by omega)
  have hfinal : forwardFactorRayCone e q = {x | 0 ≤ latticeNormal (directionNormal (e 0)) x} := by
    simp only [forwardFactorRayCone, lt_self_iff_false, ite_false]
    exact forward_cone_with_opposite_ray _ _ hlast
  refine ⟨?_, hfinal⟩
  intro i j hi hij hjq
  by_cases hj : j < q
  · by_cases he : i = j
    · rw [he]
    · have hab : 0 < determinant (e 0) (e (i : ZMod (2 * q))) := by
        simpa only [Nat.cast_zero] using anchored_chain_first_half_pair_positive e hfan 0 i hi (by omega)
      have had : 0 < determinant (e 0) (e (j : ZMod (2 * q))) := by
        simpa only [Nat.cast_zero] using anchored_chain_first_half_pair_positive e hfan 0 j (by omega) hj
      have hbd := anchored_chain_first_half_pair_positive e hfan i j (by omega) hj
      simp only [forwardFactorRayCone, show i < q by omega, hj, ite_true]
      exact forward_two_ray_cone_subset _ _ _ hab had hbd.le
  · have hj' : j = q := by omega
    rw [hj', hfinal]
    by_cases hiq : i < q
    · have hab : 0 < determinant (e 0) (e (i : ZMod (2 * q))) := by
        simpa only [Nat.cast_zero] using anchored_chain_first_half_pair_positive e hfan 0 i hi hiq
      simp only [forwardFactorRayCone, hiq, ite_true]
      rw [forward_two_ray_cone_normals _ _ hab]
      exact fun _ hx => hx.1
    · have hi' : i = q := by omega
      rw [hi', hfinal]

end KumarNivat
