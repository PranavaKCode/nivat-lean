import KumarNivat.PrimitiveRealLines
import Mathlib.Data.Int.Basic

namespace KumarNivat

-- these are the actual two coefficients of each integer facet normal.
def normalCoefficientDeterminant (μ ν : Site →+ ℤ) : ℤ :=
  μ (1, 0) * ν (0, 1) - μ (0, 1) * ν (1, 0)

-- evaluating a lattice normal uses the original integer coordinates.
theorem integer_normal_site_coordinates (ν : Site →+ ℤ) (g : Site) :
    ν g = g.1 * ν (1, 0) + g.2 * ν (0, 1) := by
  simpa [determinant] using normal_cramer_identity ν (1, 0) (0, 1) g

-- clearing the coefficient determinant gives a genuine lattice displacement of the intersection.
theorem integer_facet_intersection_displacement (μ ν : Site →+ ℤ) (j : ℤ)
    (hdiv : normalCoefficientDeterminant μ ν ∣ j) :
    ∃ d : Site, μ d = 0 ∧ ν d = -j := by
  obtain ⟨r, hr⟩ := hdiv
  let d : Site := (r * μ (0, 1), -r * μ (1, 0))
  refine ⟨d, ?_, ?_⟩
  · rw [integer_normal_site_coordinates μ d]
    dsimp [d]
    ring
  · rw [integer_normal_site_coordinates ν d, hr]
    dsimp [d, normalCoefficientDeterminant]
    ring

-- an old lattice endpoint moves to the relaxed supporting level without leaving the neighboring line.
theorem integer_facet_endpoint_relaxation (μ ν : Site →+ ℤ) (α β j : ℤ)
    (hdiv : normalCoefficientDeterminant μ ν ∣ j) (v : Site)
    (hμv : μ v = α) (hνv : ν v = β) :
    ∃ v' : Site, μ v' = α ∧ ν v' = β - j := by
  obtain ⟨d, hμd, hνd⟩ := integer_facet_intersection_displacement μ ν j hdiv
  exact ⟨v + d, by rw [map_add, hμv, hμd, add_zero],
    by rw [map_add, hνv, hνd, sub_eq_add_neg]⟩

-- independent integer normal coefficients distinguish actual real facet intersections.
theorem independent_facet_normals_real_injective (μ ν : Site →+ ℤ)
    (hne : normalCoefficientDeterminant μ ν ≠ 0) :
    Function.Injective (fun z : RealPlane => (latticeNormal μ z, latticeNormal ν z)) := by
  intro x y hxy
  have hμ : latticeNormal μ x = latticeNormal μ y := congrArg Prod.fst hxy
  have hν : latticeNormal ν x = latticeNormal ν y := congrArg Prod.snd hxy
  have hD : (normalCoefficientDeterminant μ ν : ℝ) ≠ 0 := by exact_mod_cast hne
  have hx : (normalCoefficientDeterminant μ ν : ℝ) * (x.1 - y.1) = 0 := by
    calc
      (normalCoefficientDeterminant μ ν : ℝ) * (x.1 - y.1) =
          (latticeNormal μ x - latticeNormal μ y) * (ν (0, 1) : ℝ) -
          (latticeNormal ν x - latticeNormal ν y) * (μ (0, 1) : ℝ) := by
        simp only [normalCoefficientDeterminant, latticeNormal, LinearMap.coe_mk,
          AddHom.coe_mk, Int.cast_sub, Int.cast_mul]
        ring
      _ = 0 := by rw [hμ, hν]; ring
  have hy : (normalCoefficientDeterminant μ ν : ℝ) * (x.2 - y.2) = 0 := by
    calc
      (normalCoefficientDeterminant μ ν : ℝ) * (x.2 - y.2) =
          (latticeNormal ν x - latticeNormal ν y) * (μ (1, 0) : ℝ) -
          (latticeNormal μ x - latticeNormal μ y) * (ν (1, 0) : ℝ) := by
        simp only [normalCoefficientDeterminant, latticeNormal, LinearMap.coe_mk,
          AddHom.coe_mk, Int.cast_sub, Int.cast_mul]
        ring
      _ = 0 := by rw [hμ, hν]; ring
  exact Prod.ext (sub_eq_zero.mp ((mul_eq_zero.mp hx).resolve_left hD))
    (sub_eq_zero.mp ((mul_eq_zero.mp hy).resolve_left hD))

-- uniqueness identifies the relaxed real endpoint with the constructed integer endpoint.
theorem real_facet_intersection_is_lattice (μ ν : Site →+ ℤ)
    (hne : normalCoefficientDeterminant μ ν ≠ 0) (α β j : ℤ)
    (hdiv : normalCoefficientDeterminant μ ν ∣ j) (v : Site)
    (hμv : μ v = α) (hνv : ν v = β) (z : RealPlane)
    (hμz : latticeNormal μ z = (α : ℝ))
    (hνz : latticeNormal ν z = ((β - j : ℤ) : ℝ)) :
    ∃ v' : Site, latticeEmbedding v' = z ∧ μ v' = α ∧ ν v' = β - j := by
  obtain ⟨v', hv'μ, hv'ν⟩ := integer_facet_endpoint_relaxation μ ν α β j hdiv v hμv hνv
  refine ⟨v', ?_, hv'μ, hv'ν⟩
  apply independent_facet_normals_real_injective μ ν hne
  apply Prod.ext
  · change latticeNormal μ (latticeEmbedding v') = latticeNormal μ z
    rw [latticeNormal_embedding, hv'μ, hμz]
  · change latticeNormal ν (latticeEmbedding v') = latticeNormal ν z
    rw [latticeNormal_embedding, hv'ν, hνz]

-- one positive outward relaxation clears both fixed neighboring coefficient determinants.
theorem common_positive_facet_relaxation (μLeft μRight ν : Site →+ ℤ)
    (hleft : normalCoefficientDeterminant μLeft ν ≠ 0)
    (hright : normalCoefficientDeterminant μRight ν ≠ 0) :
    ∃ M : ℕ, 0 < M ∧ normalCoefficientDeterminant μLeft ν ∣ (M : ℤ) ∧
      normalCoefficientDeterminant μRight ν ∣ (M : ℤ) := by
  let DLeft := normalCoefficientDeterminant μLeft ν
  let DRight := normalCoefficientDeterminant μRight ν
  refine ⟨DLeft.natAbs * DRight.natAbs,
    Nat.mul_pos (Int.natAbs_pos.mpr hleft) (Int.natAbs_pos.mpr hright), ?_, ?_⟩
  · exact Int.dvd_natCast.mpr (dvd_mul_right _ _)
  · exact Int.dvd_natCast.mpr (dvd_mul_left _ _)

end KumarNivat
