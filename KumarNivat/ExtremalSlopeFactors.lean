import KumarNivat.OrientedNormals
import Mathlib.Algebra.Order.Field.Rat

namespace KumarNivat

-- clear the extremal rational slope denominator to keep the wedge normal integral.
def slopingNormal (ν τ : Site →+ ℤ) (p : Site) : Site →+ ℤ where
  toFun g := ν p * τ g - τ p * ν g
  map_zero' := by simp
  map_add' g h := by simp only [map_add]; ring

-- the minimum actual factor slope supplies a nonnegative normal on every transverse factor.
theorem exists_extremal_slope_factor (hs : List Site) (hne : hs ≠ [])
    (ν τ : Site →+ ℤ) (hν : ∀ h ∈ hs, 0 < ν h) :
    ∃ p ∈ hs, ∀ h ∈ hs, 0 ≤ slopingNormal ν τ p h := by
  classical
  have hS : hs.toFinset.Nonempty := by
    obtain ⟨h, tail, he⟩ := List.exists_cons_of_ne_nil hne
    refine ⟨h, ?_⟩
    rw [he]
    simp
  let slope : Site → ℚ := fun h => (τ h : ℚ) / (ν h : ℚ)
  obtain ⟨p, hp, hmin⟩ := hs.toFinset.exists_min_image slope hS
  have hpmem : p ∈ hs := List.mem_toFinset.mp hp
  refine ⟨p, hpmem, ?_⟩
  intro h hh
  have hσ := hmin h (List.mem_toFinset.mpr hh)
  have hpν : (0 : ℚ) < (ν p : ℚ) := by exact_mod_cast hν p hpmem
  have hhν : (0 : ℚ) < (ν h : ℚ) := by exact_mod_cast hν h hh
  have hcross : (τ p : ℚ) * (ν h : ℚ) ≤ (τ h : ℚ) * (ν p : ℚ) :=
    (div_le_div_iff₀ hpν hhν).mp hσ
  have hcrossZ : τ p * ν h ≤ τ h * ν p := by exact_mod_cast hcross
  change 0 ≤ ν p * τ h - τ p * ν h
  nlinarith

-- the extremal vector gives a primitive forward boundary ray and retains its actual factor-line provenance.
theorem exists_extremal_primitive_boundary (hs : List Site) (hne : hs ≠ [])
    (ν τ : Site →+ ℤ) (hν : ∀ h ∈ hs, 0 < ν h)
    (a : Site) (hτa : τ a = 1) (hνa : ν a = 0) :
    ∃ p ∈ hs, ∃ b : Site, ∃ k : ℕ, 0 < k ∧ p = (k : ℤ) • (-b) ∧
      Int.gcd b.1 b.2 = 1 ∧ ν b < 0 ∧
      slopingNormal ν τ p b = 0 ∧ 0 < slopingNormal ν τ p a ∧
      ∀ h ∈ hs, 0 ≤ slopingNormal ν τ p h := by
  obtain ⟨p, hpmem, hslopes⟩ := exists_extremal_slope_factor hs hne ν τ hν
  have hpν := hν p hpmem
  have hpne : p ≠ 0 := by intro hz; rw [hz, map_zero] at hpν; omega
  obtain ⟨q, k, hk, hrep, _hqne, τq, hτq, _hkerq⟩ := exists_primitive_direction_coordinate p hpne
  have hkZ : (0 : ℤ) < k := by exact_mod_cast hk
  have hqν : 0 < ν q := by
    rw [hrep, map_zsmul, smul_eq_mul] at hpν
    by_contra hnot
    have hqnonpos : ν q ≤ 0 := by omega
    have hprod := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hkZ) hqnonpos
    omega
  have hpp : slopingNormal ν τ p p = 0 := by change ν p * τ p - τ p * ν p = 0; ring
  have hqμ : slopingNormal ν τ p q = 0 := by
    have hscaled : slopingNormal ν τ p ((k : ℤ) • q) = 0 :=
      (congrArg (slopingNormal ν τ p) hrep.symm).trans hpp
    rw [map_zsmul, smul_eq_mul] at hscaled
    exact (mul_eq_zero.mp hscaled).resolve_left (ne_of_gt hkZ)
  have hτneg : (-τq) (-q) = 1 := by simp [hτq]
  refine ⟨p, hpmem, -q, k, hk, ?_, primitive_gcd_of_line_coordinate (-q) (-τq) hτneg, ?_, ?_, ?_, hslopes⟩
  · simpa only [neg_neg] using hrep
  · rw [map_neg]
    omega
  · rw [map_neg, hqμ, neg_zero]
  · change 0 < ν p * τ a - τ p * ν a
    rw [hτa, hνa, mul_one, mul_zero, sub_zero]
    exact hν p hpmem

end KumarNivat
