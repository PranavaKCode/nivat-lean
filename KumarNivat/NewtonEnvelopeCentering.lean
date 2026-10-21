module

public import KumarNivat.NewtonEnvelopeAffine

@[expose] public section

namespace KumarNivat

-- doubling around an integer boundary midpoint supplies the centered triangle used to exhaust a half-plane.
theorem centered_doubled_lattice_hull (T : Finset Site) (a : Site)
    (hprimitive : Int.gcd a.1 a.2 = 1) (p : Site) (hp : p ≠ 0)
    (hparallel : directionNormal a p = 0) (u₀ : Site) (hu₀ : u₀ ∈ T) (hu₀p : u₀ + p ∈ T)
    (hmin : ∀ u ∈ T, directionNormal a u₀ ≤ directionNormal a u)
    (u₁ : Site) (hu₁ : u₁ ∈ T) (hheight : directionNormal a u₀ < directionNormal a u₁) :
    ∃ D : Finset Site,
      latticeHull D = (fun z : RealPlane =>
        latticeEmbedding (-((2 : ℤ) • u₀ + p)) + (2 : ℝ) • z) '' latticeHull T ∧
      (∀ u ∈ D, 0 ≤ directionNormal a u) ∧
      (0 : RealPlane) ∈ latticeHull D ∧ latticeEmbedding a ∈ latticeHull D ∧
      -latticeEmbedding a ∈ latticeHull D ∧
      ∃ v ∈ D, 0 < directionNormal a v := by
  classical
  let c := (2 : ℤ) • u₀ + p
  let D := T.image (fun u => -c + (2 : ℤ) • u)
  have heq : latticeHull D = (fun z : RealPlane =>
      latticeEmbedding (-c) + (2 : ℝ) • z) '' latticeHull T :=
    latticeHull_integer_affinity T 2 (-c)
  have hlow (u : Site) (hu : u ∈ D) : 0 ≤ directionNormal a u := by
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
    have hb := hmin v hv
    change 0 ≤ directionNormal a (-((2 : ℤ) • u₀ + p) + (2 : ℤ) • v)
    simp only [map_add, map_neg, map_zsmul, smul_eq_mul, hparallel, add_zero]
    omega
  have hminus : -p ∈ D := by
    apply Finset.mem_image.mpr
    refine ⟨u₀, hu₀, ?_⟩
    dsimp [c]
    simp only [two_smul]
    abel
  have hplus : p ∈ D := by
    apply Finset.mem_image.mpr
    refine ⟨u₀ + p, hu₀p, ?_⟩
    dsimp [c]
    simp only [two_smul]
    abel
  have hneg : latticeEmbedding (-p) = -latticeEmbedding p := by
    ext <;> simp [latticeEmbedding]
  have hPminus : -latticeEmbedding p ∈ latticeHull D := by
    rw [← hneg]
    exact subset_convexHull ℝ _ ⟨-p, hminus, rfl⟩
  obtain ⟨h0, ha, hna⟩ := convex_primitive_symmetric_segment (latticeHull D)
    (convex_convexHull ℝ _) a hprimitive p hp hparallel
    (subset_convexHull ℝ _ ⟨p, hplus, rfl⟩) hPminus
  let v := -c + (2 : ℤ) • u₁
  have hv : v ∈ D := Finset.mem_image.mpr ⟨u₁, hu₁, rfl⟩
  have hvheight : 0 < directionNormal a v := by
    change 0 < directionNormal a (-((2 : ℤ) • u₀ + p) + (2 : ℤ) • u₁)
    simp only [map_add, map_neg, map_zsmul, smul_eq_mul, hparallel, add_zero]
    omega
  exact ⟨D, heq, hlow, h0, ha, hna, v, hv, hvheight⟩

end KumarNivat
