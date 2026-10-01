import KumarNivat.PolyhedralRays
import KumarNivat.LineFaceGeometry

namespace KumarNivat

open scoped Pointwise

-- moving a finite newton hull sufficiently far inward fits its whole two-ray minkowski region in the zero wedge.
theorem newton_two_ray_region_inside_wedge (S : Finset Site) (ν μ : Site →+ ℤ)
    (a b : Site) (haν : ν a = 0) (hbν : ν b < 0) (haμ : 0 < μ a) (hbμ : μ b = 0)
    (top A : ℤ) :
    ∃ E : Site, ∀ z ∈ latticeHull S +
      (lineRay (latticeEmbedding E) (latticeEmbedding a) 0 + lineRay 0 (latticeEmbedding b) 0),
      latticeNormal ν z ≤ (top : ℝ) ∧ (A : ℝ) ≤ latticeNormal μ z := by
  classical
  let t := a + b
  let κ : Fin 2 → Site →+ ℤ := fun i => if i = 0 then -ν else μ
  let cut : Fin 2 → ℤ := fun i => if i = 0 then -top else A
  have hslopes : ∀ i ∈ (Finset.univ : Finset (Fin 2)), 0 < κ i t := by
    intro i _hi
    dsimp [κ, t]
    split_ifs
    · change 0 < -ν (a + b)
      rw [map_add, haν, zero_add]
      omega
    · rw [map_add, hbμ, add_zero]
      exact haμ
  obtain ⟨N, _hN, hplaced⟩ := eventually_translated_window_in_fixed_halfplanes
    Finset.univ κ cut S 0 t hslopes
  let E := N • t
  have hbounds (u : Site) (hu : u ∈ S) : ν (E + u) ≤ top ∧ A ≤ μ (E + u) := by
    have hν := hplaced N le_rfl u hu 0 (Finset.mem_univ _)
    have hμ := hplaced N le_rfl u hu 1 (Finset.mem_univ _)
    change (if (0 : Fin 2) = 0 then -top else A) ≤
      (if (0 : Fin 2) = 0 then -ν else μ) (0 + N • t + u) at hν
    change (if (1 : Fin 2) = 0 then -top else A) ≤
      (if (1 : Fin 2) = 0 then -ν else μ) (0 + N • t + u) at hμ
    simp only [ite_true, zero_add, AddMonoidHom.neg_apply] at hν
    simp only [show (1 : Fin 2) ≠ 0 by decide, ite_false, zero_add] at hμ
    exact ⟨by change ν (N • t + u) ≤ top; omega, hμ⟩
  have hsub : latticeEmbedding '' (S : Set Site) ⊆
      {z : RealPlane | latticeNormal ν z ≤ (top - ν E : ℤ) ∧
        (A - μ E : ℤ) ≤ latticeNormal μ z} := by
    rintro _ ⟨u, hu, rfl⟩
    have hb := hbounds u hu
    simp only [map_add] at hb
    change latticeNormal ν (latticeEmbedding u) ≤ ((top - ν E : ℤ) : ℝ) ∧
      ((A - μ E : ℤ) : ℝ) ≤ latticeNormal μ (latticeEmbedding u)
    rw [latticeNormal_embedding, latticeNormal_embedding]
    exact ⟨by exact_mod_cast (by omega : ν u ≤ top - ν E),
      by exact_mod_cast (by omega : A - μ E ≤ μ u)⟩
  have hhull : ∀ z ∈ latticeHull S, latticeNormal ν z ≤ ((top - ν E : ℤ) : ℝ) ∧
      ((A - μ E : ℤ) : ℝ) ≤ latticeNormal μ z := convexHull_min hsub
        (((convex_Iic ((top - ν E : ℤ) : ℝ)).linear_preimage (latticeNormal ν)).inter
          ((convex_Ici ((A - μ E : ℤ) : ℝ)).linear_preimage (latticeNormal μ)))
  refine ⟨E, ?_⟩
  intro z hz
  obtain ⟨u, hu, v, hv, rfl⟩ := Set.mem_add.mp hz
  obtain ⟨x, ⟨r, hr, rfl⟩, y, ⟨s, hs, rfl⟩, rfl⟩ := Set.mem_add.mp hv
  change latticeNormal ν (u + ((latticeEmbedding E + r • latticeEmbedding a) +
    (0 + s • latticeEmbedding b))) ≤ (top : ℝ) ∧
    (A : ℝ) ≤ latticeNormal μ (u + ((latticeEmbedding E + r • latticeEmbedding a) +
      (0 + s • latticeEmbedding b)))
  have hb := hhull u hu
  have hbνR : (ν b : ℝ) ≤ 0 := by exact_mod_cast le_of_lt hbν
  have haμR : (0 : ℝ) ≤ (μ a : ℝ) := by exact_mod_cast le_of_lt haμ
  have hdec := mul_nonpos_of_nonneg_of_nonpos hs hbνR
  have hinc := mul_nonneg hr haμR
  simp only [map_add, map_smul, latticeNormal_embedding, haν, hbμ, Int.cast_zero,
    zero_add, smul_eq_mul]
  push_cast at hb
  constructor <;> linarith

end KumarNivat
