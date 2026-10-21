module

public import KumarNivat.FiniteBandPlacement
public import KumarNivat.RegionalBackground
public import KumarNivat.TangentNormals
public import KumarNivat.LineFaceGeometry

@[expose] public section

namespace KumarNivat

-- the two actual ray normals define a translated rational wedge inside every nonnegative inward constraint.
theorem ray_normal_wedge_subset_inward_region {I : Type*} (a b E : Site) (hdet : 0 < determinant a b)
    (cut : ℤ) (J : Finset I) (μ : I → Site →+ ℤ) (z : I → ℤ)
    (hμa : ∀ i ∈ J, 0 ≤ μ i a) (hμb : ∀ i ∈ J, 0 ≤ μ i b)
    (hE : latticeEmbedding E ∈ inwardLayerRegion (directionNormal a) cut J μ z) :
    ∀ g : Site, directionNormal a E ≤ directionNormal a g →
      (-directionNormal b) E ≤ (-directionNormal b) g →
        latticeEmbedding g ∈ inwardLayerRegion (directionNormal a) cut J μ z := by
  have hEm := (mem_inwardLayerRegion_lattice (directionNormal a) cut J μ z E).mp hE
  intro g hg₁ hg₂
  have hδ₁ : 0 ≤ directionNormal a (g - E) := by rw [map_sub]; omega
  have hδ₂ : 0 ≤ (-directionNormal b) (g - E) := by rw [map_sub]; omega
  have hswap : determinant (g - E) b = (-directionNormal b) (g - E) := by
    change (g - E).1 * b.2 - (g - E).2 * b.1 = -(b.1 * (g - E).2 - b.2 * (g - E).1)
    ring
  apply (mem_inwardLayerRegion_lattice (directionNormal a) cut J μ z g).mpr
  refine ⟨hEm.1.trans hg₁, ?_⟩
  intro i hi
  have hcramer := normal_cramer_identity (μ i) a b (g - E)
  have hproduct : 0 ≤ determinant a b * μ i (g - E) := by
    rw [hcramer]
    exact add_nonneg (mul_nonneg (by rwa [hswap]) (hμa i hi)) (mul_nonneg hδ₁ (hμb i hi))
  have hδμ : 0 ≤ μ i (g - E) := by
    by_contra hnot
    have hnegative : μ i (g - E) < 0 := by omega
    have hpnegative := mul_neg_of_pos_of_neg hdet hnegative
    omega
  rw [map_sub] at hδμ
  have hbase := hEm.2 i hi
  omega

-- the two oriented regional ray periods give a fully periodic background on a genuine rational wedge of the same array.
theorem background_on_wedge_of_inward_ray_periods {A I : Type*} (x : Site → A) (a b : Site)
    (hprimitive : Int.gcd a.1 a.2 = 1) (hdet : 0 < determinant a b)
    (cut : ℤ) (J : Finset I) (μ : I → Site →+ ℤ) (z : I → ℤ)
    (hμa : ∀ i ∈ J, 0 < μ i a) (hμb : ∀ i ∈ J, 0 ≤ μ i b)
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hperiodA : RegionalPeriod x {g | latticeEmbedding g ∈ inwardLayerRegion (directionNormal a) cut J μ z} ((p : ℤ) • a))
    (hperiodB : RegionalPeriod x {g | latticeEmbedding g ∈ inwardLayerRegion (directionNormal a) cut J μ z} ((q : ℤ) • b)) :
    Function.Injective ((directionNormal a).prod (-directionNormal b)) ∧
      ∃ E : Site, ∃ B : Site → A, FullyPeriodic B ∧
        AgreesOnWedge (directionNormal a) (-directionNormal b) (directionNormal a E) ((-directionNormal b) E) x B ∧
        Set.range B ⊆ Set.range x := by
  have hane : a ≠ 0 := by rintro rfl; simp at hprimitive
  have hbne : b ≠ 0 := by intro hz; rw [hz] at hdet; simp [determinant] at hdet
  have hnormalA : directionNormal a a = 0 := by simp [directionNormal, determinant, mul_comm]
  have hnormalB : (-directionNormal b) b = 0 := by change -determinant b b = 0; simp [determinant, mul_comm]
  have hnormalBA : (-directionNormal b) a = determinant a b := by
    change -(b.1 * a.2 - b.2 * a.1) = a.1 * b.2 - a.2 * b.1
    ring
  have hinj := independent_tangent_normals (directionNormal a) (-directionNormal b) a b
    (directionNormal_ne_zero a hane) (neg_ne_zero.mpr (directionNormal_ne_zero b hbne))
      (ne_of_gt hdet) hnormalA hnormalB
  have hμne : ∀ i ∈ J, μ i ≠ 0 := by
    intro i hi hz
    have hh := hμa i hi
    rw [hz] at hh
    simp at hh
  obtain ⟨v, E, _hav, _hheight, hframe⟩ := exists_row_frame_in_inward_region a b hprimitive hdet
    cut J μ z hμne (fun i hi => le_of_lt (hμa i hi)) hμb 1 0 cut
  have hEmem : E ∈ rowFrame E a v 1 0 := by
    simpa only [Fin.val_zero, Nat.cast_zero, zero_smul, add_zero] using rowFrame_mem E a v 1 0 0 0
  have hsub := ray_normal_wedge_subset_inward_region a b E hdet cut J μ z
    (fun i hi => le_of_lt (hμa i hi)) hμb (hframe E hEmem)
  let W : Set Site := {g | directionNormal a E ≤ directionNormal a g ∧ (-directionNormal b) E ≤ (-directionNormal b) g}
  have hperiodAW : RegionalPeriod x W ((p : ℤ) • a) := by
    intro g hg hfit
    exact hperiodA g (hsub g hg.1 hg.2) (hsub _ hfit.1 hfit.2)
  have hperiodBW : RegionalPeriod x W ((q : ℤ) • b) := by
    intro g hg hfit
    exact hperiodB g (hsub g hg.1 hg.2) (hsub _ hfit.1 hfit.2)
  have hpZ : (0 : ℤ) < p := by exact_mod_cast hp
  have hqZ : (0 : ℤ) < q := by exact_mod_cast hq
  have hνpa : directionNormal a ((p : ℤ) • a) = 0 := by rw [map_zsmul, hnormalA, smul_zero]
  have hνqb : directionNormal a ((q : ℤ) • b) = (q : ℤ) * determinant a b := by rw [map_zsmul, smul_eq_mul]; rfl
  have hηpa : (-directionNormal b) ((p : ℤ) • a) = (p : ℤ) * determinant a b := by
    rw [map_zsmul, hnormalBA, smul_eq_mul]
  have hηqb : (-directionNormal b) ((q : ℤ) • b) = 0 := by rw [map_zsmul, hnormalB, smul_zero]
  have hdetperiod : determinant ((p : ℤ) • a) ((q : ℤ) • b) ≠ 0 := by
    rw [determinant_zsmul]
    exact ne_of_gt (mul_pos (mul_pos hpZ hqZ) hdet)
  obtain ⟨B, hB, hagree, hrange⟩ := exists_background_on_wedge x (directionNormal a) (-directionNormal b)
    (directionNormal a E) ((-directionNormal b) E) ((p : ℤ) • a) ((q : ℤ) • b) hdetperiod
      (by rw [hνpa]) (by rw [hνqb]; exact le_of_lt (mul_pos hqZ hdet))
      (by rw [hηpa]; exact le_of_lt (mul_pos hpZ hdet)) (by rw [hηqb])
      (by rw [map_add, hνpa, hνqb, zero_add]; exact mul_pos hqZ hdet)
      (by rw [map_add, hηpa, hηqb, add_zero]; exact mul_pos hpZ hdet) hperiodAW hperiodBW
  exact ⟨hinj, E, B, hB, hagree, hrange⟩

end KumarNivat
