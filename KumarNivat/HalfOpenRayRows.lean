module

public import KumarNivat.LocalParallelograms
public import KumarNivat.PrimitiveRealLines

@[expose] public section

namespace KumarNivat

-- deleting the supporting line leaves this semi-open strip along the transverse ray.
def halfOpenRayStrip (q₀ a b : Site) (r : ℕ) : Set RealPlane :=
  {z | ∃ α β : ℝ, 0 < α ∧ α ≤ (r : ℝ) ∧ 0 ≤ β ∧
    z = latticeEmbedding q₀ + α • latticeEmbedding a + β • latticeEmbedding b}

-- a primitive row has r consecutive lattice sites in the semi-open strip, regardless of the determinant size.
theorem half_open_ray_strip_row_run (q₀ a b : Site) (hprimitive : Int.gcd a.1 a.2 = 1)
    (hdet : 0 < determinant a b) (r : ℕ) (j : ℤ)
    (hj : directionNormal a q₀ ≤ j) :
    ∃ E : Site, directionNormal a E = j ∧ ∀ i : Fin r,
      latticeEmbedding (E + (i.val : ℤ) • a) ∈ halfOpenRayStrip q₀ a b r := by
  obtain ⟨τ, hτ, _hker⟩ := primitive_direction_coordinate a hprimitive
  obtain ⟨v, hav⟩ := primitive_basis_of_line_coordinate a τ hτ
  have ha : directionNormal a a = 0 := by simp [directionNormal, determinant, mul_comm]
  have hv : directionNormal a v = 1 := hav
  let G := q₀ + (j - directionNormal a q₀) • v
  have hG : directionNormal a G = j := by
    dsimp [G]
    rw [map_add, map_zsmul, hv, smul_eq_mul, mul_one]
    omega
  let β : ℝ := ((j - directionNormal a q₀ : ℤ) : ℝ) / (determinant a b : ℝ)
  have hD : (0 : ℝ) < (determinant a b : ℝ) := by exact_mod_cast hdet
  have hβ : 0 ≤ β := div_nonneg (by exact_mod_cast (sub_nonneg.mpr hj)) (le_of_lt hD)
  have hβD : β * (determinant a b : ℝ) = ((j - directionNormal a q₀ : ℤ) : ℝ) :=
    div_mul_cancel₀ _ (ne_of_gt hD)
  let W := latticeEmbedding q₀ + β • latticeEmbedding b
  have hW : latticeNormal (directionNormal a) W = (j : ℝ) := by
    dsimp [W]
    rw [map_add, map_smul, latticeNormal_embedding, latticeNormal_embedding, smul_eq_mul]
    change (directionNormal a q₀ : ℝ) + β * (determinant a b : ℝ) = (j : ℝ)
    rw [hβD, Int.cast_sub]
    ring
  obtain ⟨s, hs⟩ := real_points_on_same_primitive_normal a hprimitive W (latticeEmbedding G)
    (by rw [latticeNormal_embedding, hG, hW])
  let d : ℤ := ⌊-s⌋ + 1
  let E := G + d • a
  have hd₀ : (⌊-s⌋ : ℝ) ≤ -s := Int.floor_le (-s)
  have hd₁ : -s < (⌊-s⌋ : ℝ) + 1 := Int.lt_floor_add_one (-s)
  have hα : 0 < s + (d : ℝ) ∧ s + (d : ℝ) ≤ 1 := by
    dsimp [d]
    push_cast
    constructor <;> linarith
  refine ⟨E, ?_, ?_⟩
  · dsimp [E]
    rw [map_add, map_zsmul, ha, smul_zero, add_zero, hG]
  · intro i
    refine ⟨s + (d : ℝ) + (i.val : ℝ), β, ?_, ?_, hβ, ?_⟩
    · have hi := Nat.cast_nonneg (α := ℝ) i.val
      linarith [hα.1]
    · have hi : (i.val : ℝ) + 1 ≤ (r : ℝ) := by exact_mod_cast Nat.succ_le_of_lt i.isLt
      linarith [hα.2]
    · dsimp [E, W] at hs ⊢
      rw [latticeEmbedding_add, latticeEmbedding_add, latticeEmbedding_zsmul, latticeEmbedding_zsmul,
        Int.cast_natCast, hs]
      simp only [add_smul]
      abel

end KumarNivat
