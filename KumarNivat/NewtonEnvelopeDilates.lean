import KumarNivat.NewtonEnvelopeSaturation
import KumarNivat.PrimitiveRealLines

namespace KumarNivat

open scoped Pointwise

-- finitely many real size requirements fit within one positive integer dilation.
theorem finite_positive_integer_bound (S : Finset Site) (r : Site → ℝ) :
    ∃ N : ℕ, 0 < N ∧ ∀ g ∈ S, r g ≤ (N : ℝ) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert g S hg ih =>
    obtain ⟨N, hN, hbound⟩ := ih
    obtain ⟨M, hM⟩ := exists_nat_gt (r g)
    refine ⟨max N M, lt_of_lt_of_le hN (le_max_left _ _), ?_⟩
    intro u hu
    rcases Finset.mem_insert.mp hu with rfl | hu
    · exact le_trans (le_of_lt hM) (by exact_mod_cast le_max_right N M)
    · exact le_trans (hbound u hu) (by exact_mod_cast le_max_left N M)

-- a centered boundary segment and one inward point generate every half-plane point after dilation.
theorem convex_triangle_mem_dilate (P : Set RealPlane) (hP : Convex ℝ P)
    (a v : RealPlane) (h0 : (0 : RealPlane) ∈ P) (ha : a ∈ P) (hna : -a ∈ P)
    (hv : v ∈ P) (β γ n : ℝ) (hβ : 0 ≤ β) (hsize : β + |γ| ≤ n) :
    β • v + γ • a ∈ n • P := by
  have hβv : β • v ∈ β • P := Set.smul_mem_smul_set hv
  have hγa : γ • a ∈ |γ| • P := by
    by_cases hγ : 0 ≤ γ
    · rw [abs_of_nonneg hγ]
      exact Set.smul_mem_smul_set ha
    · have hneg : γ ≤ 0 := le_of_lt (lt_of_not_ge hγ)
      rw [abs_of_nonpos hneg]
      convert Set.smul_mem_smul_set (a := -γ) hna using 1
      simp only [smul_neg, neg_smul, neg_neg]
  have hsum : β • v + γ • a ∈ (β + |γ|) • P := by
    rw [hP.add_smul hβ (abs_nonneg γ)]
    exact Set.add_mem_add hβv hγa
  have hpadding : 0 ≤ n - (β + |γ|) := sub_nonneg.mpr hsize
  have hn : n = (β + |γ|) + (n - (β + |γ|)) := by ring
  rw [hn, hP.add_smul (add_nonneg hβ (abs_nonneg γ)) hpadding]
  have hz : (0 : RealPlane) ∈ (n - (β + |γ|)) • P := by
    simpa only [smul_zero] using Set.smul_mem_smul_set (a := n - (β + |γ|)) h0
  simpa only [add_zero] using Set.add_mem_add hsum hz

-- the same centered triangle covers any prescribed finite set in the primitive inward half-plane.
theorem finite_primitive_halfplane_cover_by_dilates (P : Set RealPlane) (hP : Convex ℝ P)
    (a : Site) (hprimitive : Int.gcd a.1 a.2 = 1)
    (h0 : (0 : RealPlane) ∈ P) (ha : latticeEmbedding a ∈ P) (hna : -latticeEmbedding a ∈ P)
    (v : Site) (hv : latticeEmbedding v ∈ P) (hheight : 0 < directionNormal a v)
    (cut : ℤ) (S : Finset Site) (hS : ∀ g ∈ S, cut ≤ directionNormal a g) :
    ∃ N : ℕ, ∃ E : Site, 0 < N ∧ directionNormal a E = cut ∧
      ∀ g ∈ S, latticeEmbedding g ∈ latticeEmbedding E +ᵥ ((N : ℝ) • P) := by
  obtain ⟨τ, hτ, _hker⟩ := primitive_direction_coordinate a hprimitive
  obtain ⟨q, haq⟩ := primitive_basis_of_line_coordinate a τ hτ
  let ν := directionNormal a
  let E := cut • q
  have hE : ν E = cut := by
    change ν (cut • q) = cut
    rw [map_zsmul]
    change cut * determinant a q = cut
    rw [haq, mul_one]
  let β : Site → ℝ := fun g => (ν (g - E) : ℝ) / (ν v : ℝ)
  have hden : (0 : ℝ) < (ν v : ℝ) := by exact_mod_cast hheight
  have hdecomp (g : Site) : ∃ γ : ℝ,
      latticeEmbedding (g - E) = β g • latticeEmbedding v + γ • latticeEmbedding a := by
    have hn : latticeNormal ν (latticeEmbedding (g - E) - β g • latticeEmbedding v) =
        latticeNormal ν (0 : RealPlane) := by
      rw [map_sub, map_smul, latticeNormal_embedding, latticeNormal_embedding, map_zero]
      dsimp [β]
      field_simp
      ring
    obtain ⟨γ, he⟩ := real_points_on_same_primitive_normal a hprimitive 0
      (latticeEmbedding (g - E) - β g • latticeEmbedding v) hn
    refine ⟨γ, ?_⟩
    simp only [zero_add] at he
    rw [sub_eq_iff_eq_add] at he
    simpa only [add_comm] using he
  choose γ hrep using hdecomp
  obtain ⟨N, hN, hbound⟩ := finite_positive_integer_bound S (fun g => β g + |γ g|)
  refine ⟨N, E, hN, hE, ?_⟩
  intro g hg
  have hβ : 0 ≤ β g := by
    apply div_nonneg ?_ (le_of_lt hden)
    have hi : 0 ≤ ν (g - E) := by rw [map_sub, hE]; exact sub_nonneg.mpr (hS g hg)
    exact_mod_cast hi
  have hpoint := convex_triangle_mem_dilate P hP (latticeEmbedding a) (latticeEmbedding v)
    h0 ha hna hv (β g) (γ g) (N : ℝ) hβ (hbound g hg)
  rw [← hrep g] at hpoint
  refine ⟨latticeEmbedding (g - E), hpoint, ?_⟩
  change latticeEmbedding E + latticeEmbedding (g - E) = latticeEmbedding g
  rw [latticeEmbedding_sub]
  abel

end KumarNivat
