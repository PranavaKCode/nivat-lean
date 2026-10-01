import KumarNivat.InitialWedgeFromHalfStrip
import KumarNivat.PrimitiveRealLines

namespace KumarNivat

open scoped Pointwise

-- the same newton two-ray region is stable under every nonnegative motion along its first ray.
theorem newton_two_ray_region_first_motion (S : Finset Site) (E a b : Site) :
    ∀ z ∈ latticeHull S +
      (lineRay (latticeEmbedding E) (latticeEmbedding a) 0 + lineRay 0 (latticeEmbedding b) 0),
      ∀ r : ℝ, 0 ≤ r → z + r • latticeEmbedding a ∈ latticeHull S +
        (lineRay (latticeEmbedding E) (latticeEmbedding a) 0 + lineRay 0 (latticeEmbedding b) 0) := by
  intro z hz r hr
  obtain ⟨u, hu, v, hv, rfl⟩ := Set.mem_add.mp hz
  obtain ⟨x, ⟨s, hs, rfl⟩, y, hy, rfl⟩ := Set.mem_add.mp hv
  refine Set.mem_add.mpr ⟨u, hu, (latticeEmbedding E + (s + r) • latticeEmbedding a) + y,
    Set.add_mem_add ⟨s + r, add_nonneg hs hr, rfl⟩ hy, ?_⟩
  change u + ((latticeEmbedding E + (s + r) • latticeEmbedding a) + y) =
    (u + ((latticeEmbedding E + s • latticeEmbedding a) + y)) + r • latticeEmbedding a
  rw [add_smul]
  abel

-- forward first-ray translates exhaust an actual half-plane inside the unchanged newton two-ray region.
theorem newton_two_ray_region_first_ray_halfplane_cofinal (S : Finset Site)
    (u₀ : Site) (hu₀ : u₀ ∈ S) (E a b : Site) (hprimitive : Int.gcd a.1 a.2 = 1)
    (hdet : 0 < determinant a b) (q : ℕ) (hq : 0 < q) :
    ∀ g : Site, directionNormal a (E + u₀) ≤ directionNormal a g →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → latticeEmbedding (g + (n : ℤ) • ((q : ℤ) • a)) ∈
        latticeHull S + (lineRay (latticeEmbedding E) (latticeEmbedding a) 0 +
          lineRay 0 (latticeEmbedding b) 0) := by
  intro g hg
  let F := E + u₀
  let D : ℝ := determinant a b
  let s : ℝ := ((directionNormal a g - directionNormal a F : ℤ) : ℝ) / D
  have hD : 0 < D := by dsimp [D]; exact_mod_cast hdet
  have hs : 0 ≤ s := div_nonneg (by exact_mod_cast sub_nonneg.mpr hg) (le_of_lt hD)
  have hsD : s * D = ((directionNormal a g - directionNormal a F : ℤ) : ℝ) :=
    div_mul_cancel₀ _ (ne_of_gt hD)
  let W := latticeEmbedding F + s • latticeEmbedding b
  have hW : latticeNormal (directionNormal a) W = (directionNormal a g : ℝ) := by
    dsimp [W]
    rw [map_add, map_smul, latticeNormal_embedding, latticeNormal_embedding, smul_eq_mul]
    change (directionNormal a F : ℝ) + s * D = (directionNormal a g : ℝ)
    rw [hsD, Int.cast_sub]
    ring
  obtain ⟨r, hr⟩ := real_points_on_same_primitive_normal a hprimitive W (latticeEmbedding g)
    (by rw [latticeNormal_embedding, hW])
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  obtain ⟨N, hN⟩ := exists_nat_ge (-r / (q : ℝ))
  refine ⟨N, ?_⟩
  intro n hn
  have hN' := (div_le_iff₀ hqR).mp hN
  have hnR : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hα : 0 ≤ r + (n : ℝ) * (q : ℝ) := by
    have he := mul_le_mul_of_nonneg_right hnR (le_of_lt hqR)
    linarith
  have hemb : latticeEmbedding (g + (n : ℤ) • ((q : ℤ) • a)) =
      W + r • latticeEmbedding a + ((n : ℝ) * (q : ℝ)) • latticeEmbedding a := by
    rw [latticeEmbedding_add, latticeEmbedding_zsmul, latticeEmbedding_zsmul, hr]
    simp only [Int.cast_natCast, smul_smul]
  refine Set.mem_add.mpr ⟨latticeEmbedding u₀, subset_convexHull ℝ _ ⟨u₀, hu₀, rfl⟩,
    (latticeEmbedding E + (r + (n : ℝ) * (q : ℝ)) • latticeEmbedding a) +
      (0 + s • latticeEmbedding b),
    Set.add_mem_add ⟨r + (n : ℝ) * (q : ℝ), hα, rfl⟩ ⟨s, hs, rfl⟩, ?_⟩
  rw [hemb]
  dsimp [W, F]
  rw [latticeEmbedding_add, add_smul]
  simp only [zero_add]
  abel

end KumarNivat
