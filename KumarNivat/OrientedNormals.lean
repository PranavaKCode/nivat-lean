module

public import KumarNivat.SupportingFaces

@[expose] public section

namespace KumarNivat

noncomputable section

-- an integer coordinate taking value one supplies the bezout witness for primitivity.
theorem primitive_gcd_of_line_coordinate (p : Site) (τ : Site →+ ℤ) (hτ : τ p = 1) :
    Int.gcd p.1 p.2 = 1 := by
  apply Nat.dvd_one.mp
  apply Int.gcd_dvd_iff.mpr
  refine ⟨τ (1, 0), τ (0, 1), ?_⟩
  simpa [determinant, hτ] using normal_cramer_identity τ (1, 0) (0, 1) p

-- the same coordinate completes the primitive vector to a unimodular integer basis.
theorem primitive_basis_of_line_coordinate (p : Site) (τ : Site →+ ℤ) (hτ : τ p = 1) :
    ∃ q : Site, determinant p q = 1 := by
  let A := τ (1, 0)
  let B := τ (0, 1)
  have he : 1 = p.1 * A + p.2 * B := by
    simpa [determinant, hτ, A, B] using normal_cramer_identity τ (1, 0) (0, 1) p
  refine ⟨(-B, A), ?_⟩
  simp only [determinant]
  nlinarith [he]

-- orient the primitive tangent so its integer normal has the same inward sign as the real one.
theorem oneSidedNonexpansive_oriented_primitive_normal {A : Type*}
    [TopologicalSpace A] [DiscreteTopology A] (c : Site → A) (R S : Finset Site)
    (hgen : GeneratingPolygon c R S) (ell : Site →+ ℝ) (hNE : OneSidedNonexpansive c ell) :
    ∃ p : Site, p ≠ 0 ∧ Int.gcd p.1 p.2 = 1 ∧ ∃ κ : ℝ, 0 < κ ∧
      ∀ g : Site, ell g = κ * (directionNormal p g : ℝ) := by
  obtain ⟨p, hp, τ, hτ, hker⟩ := oneSidedNonexpansive_primitive_direction c R S hgen ell hNE
  have hpell : ell p = 0 := (hker p).mpr (by rw [hτ, one_smul])
  obtain ⟨q, hpq⟩ := primitive_basis_of_line_coordinate p τ hτ
  have hrep (g : Site) : ell g = ell q * (directionNormal p g : ℝ) := by
    have he := congrArg ell (determinant_smul_identity p q g)
    rw [hpq, one_smul, map_add, map_zsmul, map_zsmul, hpell, smul_zero, zero_add] at he
    change ell g = ell q * (determinant p g : ℝ)
    simpa only [zsmul_eq_mul, mul_comm] using he
  have hq : ell q ≠ 0 := by
    intro hz
    apply hNE.1
    ext g
    rw [hrep g, hz, zero_mul]
    rfl
  rcases lt_or_gt_of_ne hq with hneg | hpos
  · have hτneg : (-τ) (-p) = 1 := by simp [hτ]
    refine ⟨-p, neg_ne_zero.mpr hp, primitive_gcd_of_line_coordinate (-p) (-τ) hτneg,
      -ell q, neg_pos.mpr hneg, ?_⟩
    intro g
    have hnormal : directionNormal (-p) g = -directionNormal p g := by
      simp [directionNormal, determinant]
      ring
    rw [hnormal, Int.cast_neg, neg_mul_neg]
    exact hrep g
  · exact ⟨p, hp, primitive_gcd_of_line_coordinate p τ hτ, ell q, hpos, hrep⟩

-- integer normal values are viewed as real numbers only at the interface to expansiveness.
def integerNormalAsReal (ν : Site →+ ℤ) : Site →+ ℝ :=
  (Int.castRingHom ℝ).toAddMonoidHom.comp ν

-- the chosen integer normal defines exactly the same closed inward half-plane.
theorem oneSidedNonexpansive_integer_normal {A : Type*} [TopologicalSpace A] [DiscreteTopology A]
    (c : Site → A) (R S : Finset Site) (hgen : GeneratingPolygon c R S)
    (ell : Site →+ ℝ) (hNE : OneSidedNonexpansive c ell) :
    ∃ p : Site, p ≠ 0 ∧ Int.gcd p.1 p.2 = 1 ∧
      OneSidedNonexpansive c (integerNormalAsReal (directionNormal p)) := by
  obtain ⟨p, hp, hprimitive, κ, hκ, hrep⟩ :=
    oneSidedNonexpansive_oriented_primitive_normal c R S hgen ell hNE
  have hnormal : integerNormalAsReal (directionNormal p) ≠ 0 := by
    intro hz
    apply directionNormal_ne_zero p hp
    ext g
    have he := congrArg (fun f : Site →+ ℝ => f g) hz
    change (directionNormal p g : ℝ) = 0 at he
    exact Int.cast_eq_zero.mp he
  obtain ⟨_hell, x, y, hx, hy, hxy, hagree⟩ := hNE
  refine ⟨p, hp, hprimitive, hnormal, x, y, hx, hy, hxy, ?_⟩
  intro g hg
  have hgn : (0 : ℝ) ≤ (directionNormal p g : ℝ) := hg
  apply hagree
  rw [hrep]
  exact mul_nonneg (le_of_lt hκ) hgn

end

end KumarNivat
