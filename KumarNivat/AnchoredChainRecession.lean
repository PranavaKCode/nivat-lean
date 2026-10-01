import KumarNivat.AnchoredChainUnion

namespace KumarNivat

-- recession means that every point stays in the actual region under every forward real multiple.
def RealForwardRecession (R : Set RealPlane) (v : RealPlane) : Prop :=
  ∀ x ∈ R, ∀ t : ℝ, 0 ≤ t → x + t • v ∈ R

-- a nonempty finite inward polyhedron has exactly its homogeneous normal inequalities as recession directions.
theorem finite_inward_recession_iff {I : Type*} (J : Finset I)
    (μ : I → Site →+ ℤ) (fixed : I → ℤ)
    (hnonempty : (finiteInwardRegion J μ fixed).Nonempty) (v : RealPlane) :
    RealForwardRecession (finiteInwardRegion J μ fixed) v ↔
      ∀ i ∈ J, 0 ≤ latticeNormal (μ i) v := by
  constructor
  · intro hrec i hi
    obtain ⟨x, hx⟩ := hnonempty
    by_contra hnot
    have hneg : latticeNormal (μ i) v < 0 := lt_of_not_ge hnot
    let t : ℝ := (latticeNormal (μ i) x - (fixed i : ℝ) + 1) / (-latticeNormal (μ i) v)
    have hden : 0 < -latticeNormal (μ i) v := neg_pos.mpr hneg
    have ht : 0 ≤ t := div_nonneg (by have h := hx i hi; linarith) hden.le
    have hlevel := hrec x hx t ht i hi
    rw [map_add, map_smul, smul_eq_mul] at hlevel
    have hmul : t * latticeNormal (μ i) v = -(latticeNormal (μ i) x - (fixed i : ℝ) + 1) := by
      calc
        t * latticeNormal (μ i) v = -(t * (-latticeNormal (μ i) v)) := by ring
        _ = -(latticeNormal (μ i) x - (fixed i : ℝ) + 1) := by
          dsimp [t]
          rw [div_mul_cancel₀ _ (ne_of_gt hden)]
    rw [hmul] at hlevel
    linarith
  · intro hnorm x hx t ht i hi
    rw [map_add, map_smul, smul_eq_mul]
    exact (hx i hi).trans (le_add_of_nonneg_right (mul_nonneg ht (hnorm i hi)))

-- the two actual endpoint normals force every homogeneous chain direction to be a nonnegative sum of its two rays.
theorem anchored_chain_homogeneous_two_rays {q : ℕ} [NeZero (2 * q)]
    (e : ZMod (2 * q) → Site) (hfan : AnchoredChainFanOrder e)
    (b : ℕ) (hb₀ : 0 < b) (hbq : b < q) (v : RealPlane) :
    (∀ i ∈ Finset.range (b + 1),
      0 ≤ latticeNormal (directionNormal (e (i : ZMod (2 * q)))) v) ↔
      ∃ α β : ℝ, 0 ≤ α ∧ 0 ≤ β ∧
        v = α • latticeEmbedding (-e 0) + β • latticeEmbedding (e (b : ZMod (2 * q))) := by
  have hD : 0 < determinant (e 0) (e (b : ZMod (2 * q))) := by
    simpa only [Nat.cast_zero] using anchored_chain_first_half_pair_positive e hfan 0 b hb₀ hbq
  have hDR : (0 : ℝ) < (determinant (e 0) (e (b : ZMod (2 * q))) : ℝ) := by exact_mod_cast hD
  constructor
  · intro hnorm
    have ha : 0 ≤ latticeNormal (directionNormal (e 0)) v := by
      simpa only [Nat.cast_zero] using hnorm 0 (Finset.mem_range.mpr (by omega))
    have hb := hnorm b (Finset.mem_range.mpr (by omega))
    let D : ℝ := determinant (e 0) (e (b : ZMod (2 * q)))
    refine ⟨latticeNormal (directionNormal (e (b : ZMod (2 * q)))) v / D,
      latticeNormal (directionNormal (e 0)) v / D,
      div_nonneg hb hDR.le, div_nonneg ha hDR.le, ?_⟩
    have he := real_plane_edge_cramer_identity (e 0) (e (b : ZMod (2 * q))) v
    have hneg : latticeEmbedding (-e 0) = -latticeEmbedding (e 0) := by
      ext <;> simp [latticeEmbedding]
    calc
      v = D⁻¹ • (D • v) := by rw [smul_smul, inv_mul_cancel₀ (ne_of_gt hDR), one_smul]
      _ = D⁻¹ • ((-latticeNormal (directionNormal (e (b : ZMod (2 * q)))) v) • latticeEmbedding (e 0) +
          (latticeNormal (directionNormal (e 0)) v) • latticeEmbedding (e (b : ZMod (2 * q)))) := by rw [he]
      _ = _ := by simp only [hneg, div_eq_inv_mul, smul_add, smul_smul, neg_smul, smul_neg]
  · rintro ⟨α, β, hα, hβ, he⟩ i hi
    have hib : i ≤ b := by have h := Finset.mem_range.mp hi; omega
    obtain ⟨ha, hb, _hstrict⟩ := anchored_chain_surviving_normal_signs e hfan b hb₀ hbq i hib
    have haR : (0 : ℝ) ≤ (directionNormal (e (i : ZMod (2 * q))) (-e 0) : ℝ) := by exact_mod_cast ha
    have hbR : (0 : ℝ) ≤ (directionNormal (e (i : ZMod (2 * q))) (e (b : ZMod (2 * q))) : ℝ) := by
      exact_mod_cast hb
    rw [he, map_add, map_smul, map_smul, latticeNormal_embedding, latticeNormal_embedding, smul_eq_mul, smul_eq_mul]
    exact add_nonneg (mul_nonneg hα haR) (mul_nonneg hβ hbR)

-- the actual nonempty finite chain has precisely the paper's backwards tangent and first unbounded factor rays.
theorem anchored_chain_recession_two_rays {q : ℕ} [NeZero (2 * q)]
    (e : ZMod (2 * q) → Site) (hfan : AnchoredChainFanOrder e)
    (b : ℕ) (hb₀ : 0 < b) (hbq : b < q) (fixed : ℕ → ℤ)
    (hnonempty : (finiteInwardRegion (Finset.range (b + 1))
      (fun i => directionNormal (e (i : ZMod (2 * q)))) fixed).Nonempty) (v : RealPlane) :
    RealForwardRecession (finiteInwardRegion (Finset.range (b + 1))
      (fun i => directionNormal (e (i : ZMod (2 * q)))) fixed) v ↔
      ∃ α β : ℝ, 0 ≤ α ∧ 0 ≤ β ∧
        v = α • latticeEmbedding (-e 0) + β • latticeEmbedding (e (b : ZMod (2 * q))) := by
  rw [finite_inward_recession_iff _ _ _ hnonempty]
  exact anchored_chain_homogeneous_two_rays e hfan b hb₀ hbq v

end KumarNivat
