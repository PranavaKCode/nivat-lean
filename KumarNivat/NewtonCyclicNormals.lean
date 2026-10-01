import KumarNivat.NewtonCyclicOrder
import KumarNivat.LineFaceGeometry

namespace KumarNivat

-- cramer's identity also resolves real points against the two integer edge normals.
theorem real_plane_edge_cramer_identity (p q : Site) (x : RealPlane) :
    (determinant p q : ℝ) • x =
      (-latticeNormal (directionNormal q) x) • latticeEmbedding p +
        (latticeNormal (directionNormal p) x) • latticeEmbedding q := by
  ext <;> simp [latticeNormal, directionNormal, determinant, latticeEmbedding, smul_eq_mul] <;> ring

-- adjacent inward normal inequalities control every functional maximized at their shared vertex.
theorem adjacent_edge_normals_linear_control (p q : Site) (hdet : 0 < determinant p q)
    (L : RealPlane →ₗ[ℝ] ℝ) (hp : 0 ≤ L (latticeEmbedding p)) (hq : L (latticeEmbedding q) ≤ 0)
    (x : RealPlane) (hpx : 0 ≤ latticeNormal (directionNormal p) x)
    (hqx : 0 ≤ latticeNormal (directionNormal q) x) : L x ≤ 0 := by
  have he := congrArg L (real_plane_edge_cramer_identity p q x)
  simp only [map_smul, map_add, smul_eq_mul] at he
  have hfirst := mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hqx) hp
  have hsecond := mul_nonpos_of_nonneg_of_nonpos hpx hq
  have hprod : (determinant p q : ℝ) * L x ≤ 0 := by rw [he]; exact add_nonpos hfirst hsecond
  have hDr : (0 : ℝ) < (determinant p q : ℝ) := by exact_mod_cast hdet
  by_contra hn
  exact not_lt_of_ge hprod (mul_pos hDr (lt_of_not_ge hn))

-- a genuine positive-edge walk turns a maximizing vertex into the required adjacent functional signs.
theorem cyclic_maximum_adjacent_signs {n : ℕ} [NeZero n]
    (e v : ZMod n → Site) (r : ZMod n → ℤ) (hr : ∀ i, 0 < r i)
    (hedge : ∀ i, v (i + 1) = v i + r i • e i)
    (L : RealPlane →ₗ[ℝ] ℝ) (i : ZMod n)
    (hmax : ∀ j, L (latticeEmbedding (v j)) ≤ L (latticeEmbedding (v i))) :
    0 ≤ L (latticeEmbedding (e (i - 1))) ∧ L (latticeEmbedding (e i)) ≤ 0 := by
  have hnext := hmax (i + 1)
  rw [hedge, latticeEmbedding_add, latticeEmbedding_zsmul, map_add, map_smul, smul_eq_mul] at hnext
  have hri : (0 : ℝ) < (r i : ℝ) := by exact_mod_cast hr i
  have hprev := hedge (i - 1)
  simp only [sub_add_cancel] at hprev
  have he := congrArg (fun u : Site => L (latticeEmbedding u)) hprev
  simp only [latticeEmbedding_add, latticeEmbedding_zsmul, map_add, map_smul, smul_eq_mul] at he
  have hleft := hmax (i - 1)
  have hrprev : (0 : ℝ) < (r (i - 1) : ℝ) := by exact_mod_cast hr (i - 1)
  constructor <;> nlinarith

-- ordered nonnegative residual edges share the original positive walk's maximizing vertex.
theorem ordered_cyclic_common_linear_maximum {n : ℕ} [NeZero n]
    (e : ZMod n → Site) (horder : CyclicEdgeOrder e)
    (v w : ZMod n → Site) (r d : ZMod n → ℤ)
    (hr : ∀ i, 0 < r i) (hd : ∀ i, 0 ≤ d i)
    (hv : ∀ i, v (i + 1) = v i + r i • e i)
    (hw : ∀ i, w (i + 1) = w i + d i • e i)
    (L : RealPlane →ₗ[ℝ] ℝ) :
    ∃ i : ZMod n,
      (∀ j, L (latticeEmbedding (v j)) ≤ L (latticeEmbedding (v i))) ∧
      (∀ j, L (latticeEmbedding (w j)) ≤ L (latticeEmbedding (w i))) := by
  classical
  obtain ⟨i, _hi, hmax⟩ := Finset.univ.exists_max_image (fun j => L (latticeEmbedding (v j)))
    (Finset.univ_nonempty : (Finset.univ : Finset (ZMod n)).Nonempty)
  have hmax' : ∀ j, L (latticeEmbedding (v j)) ≤ L (latticeEmbedding (v i)) :=
    fun j => hmax j (Finset.mem_univ j)
  obtain ⟨hprevsign, hnextsign⟩ := cyclic_maximum_adjacent_signs e v r hr hv L i hmax'
  have hmin := ordered_cyclic_walk_normal_minimum e horder w d hd hw
  refine ⟨i, hmax', ?_⟩
  intro j
  have hi := hmin i j
  have hp := hmin (i - 1) j
  have hprevious := congrArg (directionNormal (e (i - 1))) (hw (i - 1))
  simp only [sub_add_cancel, map_add, map_zsmul, directionNormal_self, smul_zero, add_zero] at hprevious
  rw [← hprevious] at hp
  have hpx : 0 ≤ latticeNormal (directionNormal (e (i - 1)))
      (latticeEmbedding (w j) - latticeEmbedding (w i)) := by
    rw [map_sub, latticeNormal_embedding, latticeNormal_embedding]
    exact_mod_cast (sub_nonneg.mpr hp)
  have hqx : 0 ≤ latticeNormal (directionNormal (e i))
      (latticeEmbedding (w j) - latticeEmbedding (w i)) := by
    rw [map_sub, latticeNormal_embedding, latticeNormal_embedding]
    exact_mod_cast (sub_nonneg.mpr hi)
  have hcontrol := adjacent_edge_normals_linear_control (e (i - 1)) (e i)
    (horder.adjacent_pos i) L hprevsign hnextsign _ hpx hqx
  rw [map_sub] at hcontrol
  exact sub_nonpos.mp hcontrol

end KumarNivat
