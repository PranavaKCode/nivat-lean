import KumarNivat.SupportingFaceGeometry
import KumarNivat.LineFaceGeometry
import KumarNivat.PairedDirections

namespace KumarNivat

-- a supporting normal face is an actual extreme set of the original real set.
theorem normalFace_isExtreme (P : Set RealPlane) (ell : RealPlane →ₗ[ℝ] ℝ) (m : ℝ)
    (hmin : ∀ x ∈ P, m ≤ ell x) : IsExtreme ℝ P (normalFace P ell m) := by
  refine ⟨fun _x hx => hx.1, ?_⟩
  intro x hx y hy z hz hopen
  obtain ⟨a, b, ha, hb, hab, he⟩ := hopen
  have hval : a * ell x + b * ell y = m := by
    simpa only [map_add, map_smul, smul_eq_mul, hz.2] using congrArg ell he
  have hbase : a * m + b * m = m := by rw [← add_mul, hab, one_mul]
  have hx₀ : 0 ≤ a * (ell x - m) := mul_nonneg ha.le (sub_nonneg.mpr (hmin x hx))
  have hy₀ : 0 ≤ b * (ell y - m) := mul_nonneg hb.le (sub_nonneg.mpr (hmin y hy))
  have hzero : a * (ell x - m) + b * (ell y - m) = 0 := by
    rw [mul_sub, mul_sub]
    linarith
  have hax : a * (ell x - m) = 0 := le_antisymm (by linarith) hx₀
  exact ⟨hx, sub_eq_zero.mp ((mul_eq_zero.mp hax).resolve_left (ne_of_gt ha))⟩

-- a unique point at a supporting level is an extreme point by the supporting-face criterion.
theorem unique_normal_minimum_is_extremePoint (P : Set RealPlane) (ell : RealPlane →ₗ[ℝ] ℝ)
    (v : RealPlane) (hv : v ∈ P) (hmin : ∀ x ∈ P, ell v ≤ ell x)
    (hunique : ∀ x ∈ P, ell x = ell v → x = v) : v ∈ P.extremePoints ℝ := by
  have hface : normalFace P ell (ell v) = {v} := by
    ext x
    constructor
    · rintro ⟨hx, he⟩
      exact Set.mem_singleton_iff.mpr (hunique x hx he)
    · rintro rfl
      exact ⟨hv, rfl⟩
  have hext := normalFace_isExtreme P ell (ell v) hmin
  rw [hface] at hext
  exact isExtreme_singleton.mp hext

-- the primitive coordinate distinguishes both endpoints of the actual real line interval.
theorem primitive_lineInterval_endpoints_extreme (A : RealPlane) (p : Site)
    (hprimitive : Int.gcd p.1 p.2 = 1) (t : ℝ) (ht : 0 ≤ t) :
    A ∈ (lineInterval A (latticeEmbedding p) 0 t).extremePoints ℝ ∧
      A + t • latticeEmbedding p ∈ (lineInterval A (latticeEmbedding p) 0 t).extremePoints ℝ := by
  obtain ⟨τ, hτ, _hker⟩ := primitive_direction_coordinate p hprimitive
  let L := latticeNormal τ
  have hv : L (latticeEmbedding p) = 1 := by rw [latticeNormal_embedding, hτ]; norm_num
  have heval (s : ℝ) : L (A + s • latticeEmbedding p) = L A + s := by
    rw [map_add, map_smul, hv]
    simp only [smul_eq_mul, mul_one]
  have hleft : A ∈ lineInterval A (latticeEmbedding p) 0 t :=
    ⟨0, ⟨le_rfl, ht⟩, by simp only [zero_smul, add_zero]⟩
  have hright : A + t • latticeEmbedding p ∈ lineInterval A (latticeEmbedding p) 0 t :=
    ⟨t, ⟨ht, le_rfl⟩, rfl⟩
  constructor
  · apply unique_normal_minimum_is_extremePoint _ L A hleft
    · rintro x ⟨s, hs, rfl⟩
      rw [heval]
      linarith [hs.1]
    · rintro x ⟨s, _hs, rfl⟩ he
      rw [heval] at he
      have hs : s = 0 := by linarith
      simp only [hs, zero_smul, add_zero]
  · apply unique_normal_minimum_is_extremePoint _ (-L) (A + t • latticeEmbedding p) hright
    · rintro x ⟨s, hs, rfl⟩
      change -L (A + t • latticeEmbedding p) ≤ -L (A + s • latticeEmbedding p)
      rw [heval, heval]
      linarith [hs.2]
    · rintro x ⟨s, _hs, rfl⟩ he
      change -L (A + s • latticeEmbedding p) = -L (A + t • latticeEmbedding p) at he
      rw [heval, heval] at he
      have hs : s = t := by linarith
      rw [hs]

-- endpoints of an actual supporting hull segment are actual vertices of the polygon.
theorem supporting_line_face_endpoints_lattice_vertices (S : Finset Site) (ν : Site →+ ℤ) (m : ℤ)
    (hmin : ∀ u ∈ S, m ≤ ν u) (q₀ p : Site) (hprimitive : Int.gcd p.1 p.2 = 1) (t : ℕ)
    (hface : normalFace (latticeHull S) (latticeNormal ν) (m : ℝ) =
      lineInterval (latticeEmbedding q₀) (latticeEmbedding p) 0 (t : ℝ)) :
    IsLatticeVertex S q₀ ∧ IsLatticeVertex S (q₀ + (t : ℤ) • p) := by
  have hfaceext := normalFace_isExtreme (latticeHull S) (latticeNormal ν) (m : ℝ)
    (lower_face_hull_bound S ν m hmin)
  rw [hface] at hfaceext
  have hend := primitive_lineInterval_endpoints_extreme (latticeEmbedding q₀) p hprimitive
    (t : ℝ) (Nat.cast_nonneg t)
  refine ⟨hfaceext.extremePoints_subset_extremePoints hend.1, ?_⟩
  have he := hfaceext.extremePoints_subset_extremePoints hend.2
  simpa only [IsLatticeVertex, latticeEmbedding_add, latticeEmbedding_zsmul, Int.cast_natCast] using he

end KumarNivat
