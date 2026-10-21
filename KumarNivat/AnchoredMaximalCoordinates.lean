module

public import KumarNivat.PolygonHalfStrips
public import KumarNivat.PrimitiveRealLines

@[expose] public section

namespace KumarNivat

-- a unimodular tangent frame evaluates every facet normal in integer coordinates.
theorem tangent_frame_normal_expression (a v g : Site) (hav : determinant a v = 1)
    (μ : Site →+ ℤ) :
    μ g = (-directionNormal v) g * μ a + directionNormal a g * μ v := by
  have he := normal_cramer_identity μ a v g
  rw [hav, one_mul] at he
  have hreverse : (-directionNormal v) g = determinant g v := by
    change -determinant v g = determinant g v
    simp only [determinant]
    ring
  rw [hreverse]
  exact he

-- the longitudinal frame coordinate increases by one along the primitive tangent.
theorem tangent_frame_coordinate_at_tangent (a v : Site) (hav : determinant a v = 1) :
    (-directionNormal v) a = 1 := by
  change -determinant v a = 1
  have hreverse : determinant v a = -determinant a v := by simp only [determinant]; ring
  rw [hreverse, hav]
  norm_num

-- the transverse and longitudinal coordinates distinguish all original lattice sites.
theorem tangent_frame_coordinates_injective (a v : Site) (hav : determinant a v = 1) :
    Function.Injective ((directionNormal a).prod (-directionNormal v)) := by
  apply normal_line_coordinate_injective a (-directionNormal v)
  intro g hg
  change determinant a g = 0 at hg
  have he := determinant_smul_identity a v g
  rw [hav, one_smul, hg, zero_smul, add_zero] at he
  have hreverse : determinant g v = (-directionNormal v) g := by
    change determinant g v = -determinant v g
    simp only [determinant]
    ring
  rwa [hreverse] at he

-- one finite sum bounds both primitive coordinates of the initial polygon.
noncomputable def polygonCoordinateBound (F : Finset Site) (ν τ : Site →+ ℤ) : ℤ :=
  (∑ g ∈ F, (|ν g| + |τ g|)) + 1

-- the coordinate bound is nonnegative and bounds every actual base site.
theorem polygon_coordinate_bound_data (F : Finset Site) (ν τ : Site →+ ℤ) :
    0 ≤ polygonCoordinateBound F ν τ ∧
      ∀ g ∈ F, |ν g| ≤ polygonCoordinateBound F ν τ ∧
        |τ g| ≤ polygonCoordinateBound F ν τ := by
  classical
  have hsum : 0 ≤ ∑ g ∈ F, (|ν g| + |τ g|) :=
    Finset.sum_nonneg (fun _ _ => add_nonneg (abs_nonneg _) (abs_nonneg _))
  refine ⟨by dsimp [polygonCoordinateBound]; omega, ?_⟩
  intro g hg
  have hterm : |ν g| + |τ g| ≤ ∑ u ∈ F, (|ν u| + |τ u|) :=
    Finset.single_le_sum (f := fun u => |ν u| + |τ u|)
      (fun _ _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) hg
  have hν : 0 ≤ |ν g| := abs_nonneg _
  have hτ : 0 ≤ |τ g| := abs_nonneg _
  dsimp [polygonCoordinateBound]
  constructor <;> omega

-- the forward half-strip fixes the transverse width and has a fixed lower longitudinal bound.
theorem polygon_half_strip_coordinate_bounds (F : Finset Site) (a : Site)
    (ν τ : Site →+ ℤ) (hνa : ν a = 0) (hτa : τ a = 1)
    (g : Site) (hg : g ∈ polygonHalfStrip F a) :
    |ν g| ≤ polygonCoordinateBound F ν τ ∧
      -polygonCoordinateBound F ν τ ≤ τ g := by
  obtain ⟨⟨u, n⟩, he⟩ := hg
  change u.val + (0 + (n : ℤ)) • a = g at he
  have hbase := (polygon_coordinate_bound_data F ν τ).2 u.val u.property
  have hνg : ν g = ν u.val := by
    rw [← he, map_add, map_zsmul, hνa, smul_zero, add_zero]
  have hτg : τ g = τ u.val + (n : ℤ) := by
    rw [← he, map_add, map_zsmul, hτa, smul_eq_mul, mul_one, zero_add]
  refine ⟨by rw [hνg]; exact hbase.1, ?_⟩
  have hlow : -polygonCoordinateBound F ν τ ≤ τ u.val :=
    (neg_le_neg hbase.2).trans (neg_abs_le (τ u.val))
  rw [hτg]
  have hn : (0 : ℤ) ≤ n := Int.natCast_nonneg n
  omega

-- one right-facing facet separating the retained failure bounds every longitudinal coordinate.
theorem separating_right_facet_coordinate_bound (a v g q : Site)
    (hav : determinant a v = 1) (μ : Site →+ ℤ) (W : ℤ) (hW : 0 ≤ W)
    (hwidth : |directionNormal a g| ≤ W) (hright : μ a < 0) (hseparate : μ q < μ g) :
    (-directionNormal v) g ≤ |μ q| + W * |μ v| := by
  let τ := -directionNormal v
  by_cases hτ : 0 ≤ τ g
  · have hslope : μ a ≤ -1 := by omega
    have hproduct : τ g * μ a ≤ -τ g := by
      simpa only [mul_neg, mul_one] using mul_le_mul_of_nonneg_left hslope hτ
    have htrans : directionNormal a g * μ v ≤ W * |μ v| := by
      calc
        directionNormal a g * μ v ≤ |directionNormal a g * μ v| := le_abs_self _
        _ = |directionNormal a g| * |μ v| := abs_mul _ _
        _ ≤ W * |μ v| := mul_le_mul_of_nonneg_right hwidth (abs_nonneg _)
    have hexpression := tangent_frame_normal_expression a v g hav μ
    have hlow : -|μ q| ≤ μ q := neg_abs_le _
    change μ g = τ g * μ a + directionNormal a g * μ v at hexpression
    change τ g ≤ |μ q| + W * |μ v|
    omega
  · have hnegative : τ g < 0 := by omega
    have hnonnegative : 0 ≤ |μ q| + W * |μ v| :=
      add_nonneg (abs_nonneg _) (mul_nonneg hW (abs_nonneg _))
    change τ g ≤ |μ q| + W * |μ v|
    omega

end KumarNivat
