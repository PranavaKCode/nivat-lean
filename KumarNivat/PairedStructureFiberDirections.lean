import KumarNivat.PairedStructureFiberElimination
import KumarNivat.OrientedDifferenceProducts

namespace KumarNivat

-- reversing every actual factor preserves both annihilation and directional independence.
theorem negative_difference_product_data {K : Type*} [CommRing K]
    (c : Site → K) (hs : List Site)
    (hpairs : hs.Pairwise (fun p q => determinant p q ≠ 0))
    (hann : laurentAct (differenceProduct hs) c = 0) :
    (hs.map (fun p => -p)).Pairwise (fun p q => determinant p q ≠ 0) ∧
      laurentAct (differenceProduct (hs.map (fun p => -p))) c = 0 := by
  constructor
  · simpa only [List.pairwise_map, determinant, Prod.fst_neg, Prod.snd_neg, neg_mul_neg] using hpairs
  · have hzero : orientNormalDirection (0 : Site →+ ℤ) = (fun p : Site => -p) := by
      funext p
      change (if (0 : ℤ) < 0 then p else -p) = -p
      simp only [lt_self_iff_false, ite_false]
    have h := oriented_difference_product_annihilates c hs (0 : Site →+ ℤ) hann
    rw [hzero] at h
    exact h

-- an actual tangent factor supplies an oriented primitive basis with a positive real normal scale.
theorem oriented_binomial_factor_basis_of_real_normal {K : Type*} [CommRing K]
    (c : Site → K) (hs : List Site)
    (hpairs : hs.Pairwise (fun p q => determinant p q ≠ 0))
    (hann : laurentAct (differenceProduct hs) c = 0)
    (ell : Site →+ ℝ) (hell : ell ≠ 0) (p : Site) (hpmem : p ∈ hs)
    (hp : p ≠ 0) (hellp : ell p = 0) :
    ∃ ts : List Site, ∃ a v : Site, ∃ L : ℕ, ∃ κ : ℝ,
      0 < κ ∧ 0 < L ∧ determinant a v = 1 ∧ (L : ℤ) • a ∈ ts ∧
      ts.Pairwise (fun p q => determinant p q ≠ 0) ∧
      laurentAct (differenceProduct ts) c = 0 ∧
      ∀ g : Site, ell g = κ * integerNormalAsReal (directionNormal a) g := by
  obtain ⟨a, L, hL, hrep, _ha, τ, hτ, _hker⟩ := exists_primitive_direction_coordinate p hp
  obtain ⟨v, hav⟩ := primitive_basis_of_line_coordinate a τ hτ
  have he := congrArg ell hrep
  rw [hellp, map_zsmul, zsmul_eq_mul] at he
  have hEa : ell a = 0 := (mul_eq_zero.mp he.symm).resolve_left
    (by exact_mod_cast Nat.ne_of_gt hL)
  have hnormal (g : Site) : ell g = ell v * integerNormalAsReal (directionNormal a) g := by
    have hg := congrArg ell (determinant_smul_identity a v g)
    rw [hav, one_smul, map_add, map_zsmul, map_zsmul, hEa, smul_zero, zero_add] at hg
    change ell g = ell v * (determinant a g : ℝ)
    simpa only [zsmul_eq_mul, mul_comm] using hg
  have hκ : ell v ≠ 0 := by
    intro hz
    apply hell
    ext g
    rw [hnormal g, hz, zero_mul]
    rfl
  rcases lt_or_gt_of_ne hκ with hnegative | hpositive
  · obtain ⟨hpairsneg, hannneg⟩ := negative_difference_product_data c hs hpairs hann
    have havneg : determinant (-a) (-v) = 1 := by
      simpa only [determinant, Prod.fst_neg, Prod.snd_neg, neg_mul_neg] using hav
    have hmem : (L : ℤ) • (-a) ∈ hs.map (fun p => -p) := by
      have hm : -p ∈ hs.map (fun p => -p) := List.mem_map.mpr ⟨p, hpmem, rfl⟩
      simpa only [hrep, smul_neg] using hm
    refine ⟨hs.map (fun p => -p), -a, -v, L, -ell v, neg_pos.mpr hnegative,
      hL, havneg, hmem, hpairsneg, hannneg, ?_⟩
    intro g
    rw [integerNormalAsReal_direction_neg]
    change ell g = (-ell v) * (-integerNormalAsReal (directionNormal a) g)
    rw [neg_mul_neg]
    exact hnormal g
  · refine ⟨hs, a, v, L, ell v, hpositive, hL, hav, ?_, hpairs, hann, hnormal⟩
    rwa [← hrep]

end KumarNivat
