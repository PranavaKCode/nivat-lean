import KumarNivat.NewtonEnvelopeSaturation
import KumarNivat.PrimitiveRealLines

namespace KumarNivat

open scoped Pointwise

-- integer translations and dilations preserve the exact real hull of their finite lattice generators.
theorem latticeHull_integer_affinity (T : Finset Site) (n : ℤ) (E : Site) :
    latticeHull (T.image (fun u => E + n • u)) =
      (fun z : RealPlane => latticeEmbedding E + (n : ℝ) • z) '' latticeHull T := by
  classical
  let A : RealPlane →ᵃ[ℝ] RealPlane :=
    { toFun := fun z => latticeEmbedding E + (n : ℝ) • z
      linear := (n : ℝ) • LinearMap.id
      map_vadd' := by
        intro z w
        change latticeEmbedding E + (n : ℝ) • (w + z) =
          (n : ℝ) • w + (latticeEmbedding E + (n : ℝ) • z)
        rw [smul_add]
        abel }
  have hA (u : Site) : latticeEmbedding (E + n • u) = A (latticeEmbedding u) := by
    rw [latticeEmbedding_add, latticeEmbedding_zsmul]
    rfl
  have hgen : latticeEmbedding '' ((T.image (fun u => E + n • u)) : Set Site) =
      A '' (latticeEmbedding '' (T : Set Site)) := by
    ext z
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
      exact ⟨latticeEmbedding v, ⟨v, hv, rfl⟩, (hA v).symm⟩
    · rintro ⟨_w, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨E + n • u, Finset.mem_image.mpr ⟨u, hu, rfl⟩, hA u⟩
  unfold latticeHull
  rw [hgen, ← A.image_convexHull]
  rfl

-- centering opposite tangent endpoints retains both unit primitive boundary directions.
theorem convex_primitive_symmetric_segment (P : Set RealPlane) (hP : Convex ℝ P)
    (a : Site) (hprimitive : Int.gcd a.1 a.2 = 1) (p : Site) (hp : p ≠ 0)
    (hparallel : directionNormal a p = 0)
    (hplus : latticeEmbedding p ∈ P) (hminus : -latticeEmbedding p ∈ P) :
    (0 : RealPlane) ∈ P ∧ latticeEmbedding a ∈ P ∧ -latticeEmbedding a ∈ P := by
  obtain ⟨τ, _hτ, hker⟩ := primitive_direction_coordinate a hprimitive
  have hrep := hker p hparallel
  have hk : τ p ≠ 0 := by intro he; apply hp; rw [hrep, he, zero_smul]
  have hrZ : (1 : ℤ) ≤ |τ p| := Int.one_le_abs hk
  have hr : (1 : ℝ) ≤ (|τ p| : ℤ) := by exact_mod_cast hrZ
  have hrne : ((|τ p| : ℤ) : ℝ) ≠ 0 := by linarith
  have h0 : (0 : RealPlane) ∈ P := by
    have hm : (1 / 2 : ℝ) • latticeEmbedding p + (1 / 2 : ℝ) • (-latticeEmbedding p) ∈ P :=
      hP hplus hminus (by norm_num) (by norm_num) (by norm_num)
    simpa only [smul_neg, add_neg_cancel] using hm
  have htwo : ((|τ p| : ℤ) : ℝ) • latticeEmbedding a ∈ P ∧
      ((|τ p| : ℤ) : ℝ) • (-latticeEmbedding a) ∈ P := by
    by_cases hnonneg : 0 ≤ τ p
    · rw [abs_of_nonneg hnonneg]
      have he := congrArg latticeEmbedding hrep
      rw [latticeEmbedding_zsmul] at he
      constructor
      · rwa [← he]
      · rw [smul_neg, ← he]
        exact hminus
    · have hnonpos : τ p ≤ 0 := le_of_lt (lt_of_not_ge hnonneg)
      rw [abs_of_nonpos hnonpos, Int.cast_neg]
      have he := congrArg latticeEmbedding hrep
      rw [latticeEmbedding_zsmul] at he
      constructor
      · rw [neg_smul, ← he]
        exact hminus
      · rw [smul_neg, neg_smul, neg_neg, ← he]
        exact hplus
  have hi : (((|τ p| : ℤ) : ℝ)⁻¹) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨inv_nonneg.mpr (by linarith), inv_le_one_of_one_le₀ hr⟩
  refine ⟨h0, ?_, ?_⟩
  · simpa only [smul_smul, inv_mul_cancel₀ hrne, one_smul] using
      hP.smul_mem_of_zero_mem h0 htwo.1 hi
  · simpa only [smul_smul, inv_mul_cancel₀ hrne, one_smul] using
      hP.smul_mem_of_zero_mem h0 htwo.2 hi

end KumarNivat
