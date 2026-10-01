import KumarNivat.RowFrames
import KumarNivat.StableRegions
import KumarNivat.PolyhedralRays

namespace KumarNivat

-- a finite primitive frame can be placed above any prescribed level inside the actual inward-inequality region.
theorem exists_row_frame_in_inward_region {I : Type*} (a b : Site)
    (hprimitive : Int.gcd a.1 a.2 = 1) (hdet : 0 < determinant a b)
    (cut : ℤ) (J : Finset I) (μ : I → Site →+ ℤ) (c : I → ℤ)
    (hμ : ∀ i ∈ J, μ i ≠ 0) (hμa : ∀ i ∈ J, 0 ≤ μ i a) (hμb : ∀ i ∈ J, 0 ≤ μ i b)
    (p d : ℕ) (j₀ : ℤ) :
    ∃ v E : Site, determinant a v = 1 ∧ j₀ ≤ directionNormal a E ∧
      ∀ u ∈ rowFrame E a v p d, latticeEmbedding u ∈ inwardLayerRegion (directionNormal a) cut J μ c := by
  obtain ⟨τ, hτ, _hker⟩ := primitive_direction_coordinate a hprimitive
  obtain ⟨v, hav⟩ := primitive_basis_of_line_coordinate a τ hτ
  have hnormalA : directionNormal a a = 0 := by simp [directionNormal, determinant, mul_comm]
  have hv : directionNormal a v = 1 := hav
  let t := a + b
  have ht : 0 < directionNormal a t := by
    dsimp [t]
    rw [map_add, hnormalA, zero_add]
    exact hdet
  have hslopes : ∀ i ∈ J, 0 < μ i t := fun i hi =>
    nonzero_normal_positive_on_independent_sum (μ i) (hμ i hi) a b (ne_of_gt hdet) (hμa i hi) (hμb i hi)
  obtain ⟨N₀, _hN₀, hfixed⟩ := eventually_translated_window_in_fixed_halfplanes J μ c
    (rowFrame 0 a v p d) 0 t hslopes
  obtain ⟨N₁, hheight⟩ := halfplane_forward_cofinal (directionNormal a) (max cut j₀) t ht 0
  let N := max N₀.toNat N₁
  let E := (N : ℤ) • t
  have hN₀ : N₀ ≤ (N : ℤ) := by dsimp [N]; omega
  have hN₁ : N₁ ≤ N := le_max_right _ _
  have hE : max cut j₀ ≤ directionNormal a E := by
    have he := hheight N hN₁
    change max cut j₀ ≤ directionNormal a (0 + (N : ℤ) • t) at he
    simpa only [zero_add, E] using he
  refine ⟨v, E, hav, (le_max_right cut j₀).trans hE, ?_⟩
  intro u hu
  obtain ⟨⟨i, j⟩, _hz, rfl⟩ := Finset.mem_image.mp hu
  apply (mem_inwardLayerRegion_lattice (directionNormal a) cut J μ c _).mpr
  refine ⟨?_, ?_⟩
  · change cut ≤ directionNormal a (E + (i.val : ℤ) • a + (j.val : ℤ) • v)
    have hlevel : directionNormal a (E + (i.val : ℤ) • a + (j.val : ℤ) • v) =
        directionNormal a E + (j.val : ℤ) := by
      simp only [map_add, map_zsmul, hnormalA, hv, smul_eq_mul, mul_zero, add_zero, mul_one]
    rw [hlevel]
    exact ((le_max_left cut j₀).trans hE).trans (le_add_of_nonneg_right (Int.natCast_nonneg j.val))
  · intro z hz
    have hsite : E + (i.val : ℤ) • a + (j.val : ℤ) • v =
        0 + (N : ℤ) • t + (0 + (i.val : ℤ) • a + (j.val : ℤ) • v) := by
      dsimp [E]
      abel
    rw [hsite]
    exact hfixed (N : ℤ) hN₀ _ (rowFrame_mem 0 a v p d i j) z hz

end KumarNivat
