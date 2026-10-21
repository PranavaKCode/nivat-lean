module

public import KumarNivat.OrientedNormals
public import KumarNivat.LatticeConvexity

@[expose] public section

namespace KumarNivat

-- a unimodular integer basis gives the same exact coordinate decomposition over the reals.
theorem real_unimodular_decomposition (p q : Site) (hpq : determinant p q = 1) (z : RealPlane) :
    z = (-latticeNormal (directionNormal q) z) • latticeEmbedding p +
      (latticeNormal (directionNormal p) z) • latticeEmbedding q := by
  have hdet : (p.1 : ℝ) * (q.2 : ℝ) - (p.2 : ℝ) * (q.1 : ℝ) = 1 := by
    exact_mod_cast hpq
  have hx : ((p.1 : ℝ) * (q.2 : ℝ) - (p.2 : ℝ) * (q.1 : ℝ)) * z.1 = z.1 := by
    rw [hdet, one_mul]
  have hy : ((p.1 : ℝ) * (q.2 : ℝ) - (p.2 : ℝ) * (q.1 : ℝ)) * z.2 = z.2 := by
    rw [hdet, one_mul]
  apply Prod.ext <;> simp [latticeNormal, latticeEmbedding, directionNormal, determinant, smul_eq_mul] <;>
    nlinarith [hx, hy]

-- two real points on the same primitive normal level differ along its actual tangent.
theorem real_points_on_same_primitive_normal (p : Site) (hprimitive : Int.gcd p.1 p.2 = 1)
    (w z : RealPlane)
    (hlevel : latticeNormal (directionNormal p) z = latticeNormal (directionNormal p) w) :
    ∃ s : ℝ, z = w + s • latticeEmbedding p := by
  obtain ⟨τ, hτ, _hker⟩ := primitive_direction_coordinate p hprimitive
  obtain ⟨q, hpq⟩ := primitive_basis_of_line_coordinate p τ hτ
  let A := -latticeNormal (directionNormal q) z
  let B := -latticeNormal (directionNormal q) w
  refine ⟨A - B, ?_⟩
  calc
    z = A • latticeEmbedding p + (latticeNormal (directionNormal p) z) • latticeEmbedding q :=
      real_unimodular_decomposition p q hpq z
    _ = (B • latticeEmbedding p +
        (latticeNormal (directionNormal p) w) • latticeEmbedding q) +
        (A - B) • latticeEmbedding p := by
      rw [hlevel, sub_smul]
      abel
    _ = w + (A - B) • latticeEmbedding p := by
      rw [← real_unimodular_decomposition p q hpq w]

-- the integer-level version uses the same real-line proof without changing lattice coordinates.
theorem real_point_on_primitive_lattice_line (p : Site) (hprimitive : Int.gcd p.1 p.2 = 1)
    (g : Site) (z : RealPlane)
    (hlevel : latticeNormal (directionNormal p) z = (directionNormal p g : ℝ)) :
    ∃ s : ℝ, z = latticeEmbedding g + s • latticeEmbedding p :=
  real_points_on_same_primitive_normal p hprimitive (latticeEmbedding g) z
    (by simpa only [latticeNormal_embedding] using hlevel)

end KumarNivat
