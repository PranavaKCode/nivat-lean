import KumarNivat.FiniteBandPlacement
import KumarNivat.RepeatedRowBands
import KumarNivat.MinkowskiStencilFit
import KumarNivat.LineFaceGeometry

namespace KumarNivat

-- the actual inward inequalities supply the finite frame, its stable translates, and one fixed gap for all high bands.
theorem inward_region_fixed_gap_periodic_bands {A I : Type*} (c x : Site → A)
    (hc : (Set.range c).Finite) (hx : LanguageContained x c) (a b : Site)
    (hprimitive : Int.gcd a.1 a.2 = 1) (hdet : 0 < determinant a b)
    (cut : ℤ) (J : Finset I) (μ : I → Site →+ ℤ) (z : I → ℤ)
    (hμ : ∀ i ∈ J, μ i ≠ 0) (hμa : ∀ i ∈ J, 0 ≤ μ i a) (hμb : ∀ i ∈ J, 0 ≤ μ i b)
    (p : ℕ) (hp : 0 < p)
    (hperiod : RegionalPeriod x {g | latticeEmbedding g ∈ inwardLayerRegion (directionNormal a) cut J μ z}
      ((p : ℤ) • a)) (l : ℕ) (hl : 0 < l) (d : ℕ) (j₀ : ℤ) :
    ∃ v E : Site, ∃ D : ℕ, determinant a v = 1 ∧ j₀ ≤ directionNormal a E ∧
      0 < D ∧ D ≤ complexity c (rowFrame E a v p d) ∧
      ∀ L : ℤ, ∃ q : ℕ, L ≤ directionNormal a (E + (q : ℤ) • ((l : ℤ) • b)) ∧
        ∀ g : Site, latticeEmbedding g ∈ inwardLayerRegion (directionNormal a) cut J μ z →
          directionNormal a (E + (q : ℤ) • ((l : ℤ) • b)) ≤ directionNormal a g →
          directionNormal a g ≤ directionNormal a (E + (q : ℤ) • ((l : ℤ) • b)) + (d : ℤ) →
            x (g + (D : ℤ) • ((l : ℤ) • b)) = x g := by
  obtain ⟨v, E, hav, hE, hframe⟩ := exists_row_frame_in_inward_region a b hprimitive hdet cut J μ z hμ hμa hμb p d j₀
  have hnormalA : directionNormal a a = 0 := by simp [directionNormal, determinant, mul_comm]
  have hforwardA := inwardLayerRegion_forward_stable (directionNormal a) cut J μ z a hnormalA hμa
  have hforwardB := inwardLayerRegion_nonnegative_motion (directionNormal a) cut J μ z b (le_of_lt hdet) hμb
  have hstableA : ∀ g ∈ {g | latticeEmbedding g ∈ inwardLayerRegion (directionNormal a) cut J μ z},
      g + (p : ℤ) • a ∈ {g | latticeEmbedding g ∈ inwardLayerRegion (directionNormal a) cut J μ z} := by
    intro g hg
    change latticeEmbedding (g + (p : ℤ) • a) ∈ inwardLayerRegion (directionNormal a) cut J μ z
    rw [latticeEmbedding_add, latticeEmbedding_zsmul, Int.cast_natCast]
    exact hforwardA _ hg (p : ℝ) (Nat.cast_nonneg p)
  have hstableB : ∀ g ∈ {g | latticeEmbedding g ∈ inwardLayerRegion (directionNormal a) cut J μ z},
      g + (l : ℤ) • b ∈ {g | latticeEmbedding g ∈ inwardLayerRegion (directionNormal a) cut J μ z} := by
    intro g hg
    change latticeEmbedding (g + (l : ℤ) • b) ∈ inwardLayerRegion (directionNormal a) cut J μ z
    rw [latticeEmbedding_add, latticeEmbedding_zsmul, Int.cast_natCast]
    exact hforwardB _ hg (l : ℝ) (Nat.cast_nonneg l)
  have hheight : 0 < directionNormal a ((l : ℤ) • b) := by
    rw [map_zsmul, smul_eq_mul]
    exact mul_pos (by exact_mod_cast hl) hdet
  obtain ⟨D, hD, hbound, hbands⟩ := fixed_gap_regional_row_bands c x hc hx
    {g | latticeEmbedding g ∈ inwardLayerRegion (directionNormal a) cut J μ z} a hprimitive p hp
      hstableA hperiod ((l : ℤ) • b) hheight hstableB v E hav d hframe
  exact ⟨v, E, D, hav, hE, hD, hbound, hbands⟩

end KumarNivat
