module

public import KumarNivat.NewtonCyclicOrder
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Order.WithBot

@[expose] public section

namespace KumarNivat

-- the upper semicircle includes its positive horizontal endpoint exactly once.
def InUpperFactorHalf (h : Site) : Prop := 0 < h.2 ∨ h.2 = 0 ∧ 0 < h.1

-- the semicircle test uses ordinary integer comparisons.
instance (h : Site) : Decidable (InUpperFactorHalf h) := by
  unfold InUpperFactorHalf
  infer_instance

-- choose the original factor or its opposite on that semicircle.
def upperFactorDirection (h : Site) : Site := if InUpperFactorHalf h then h else -h

-- the horizontal edge precedes finite decreasing rational slopes.
def upperFactorSlope (h : Site) : WithTop ℚ :=
  if h.2 = 0 then ⊤ else ((h.1 : ℚ) / (h.2 : ℚ) : ℚ)

-- reversing a direction retains the actual factor line.
theorem upperFactorDirection_choice (h : Site) : upperFactorDirection h = h ∨ upperFactorDirection h = -h := by
  unfold upperFactorDirection
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

-- every nonzero factor has exactly the selected upper-half representative.
theorem upperFactorDirection_in_upper (h : Site) (hh : h ≠ 0) : InUpperFactorHalf (upperFactorDirection h) := by
  unfold upperFactorDirection
  split_ifs with hu
  · exact hu
  · have hx : h.1 ≠ 0 ∨ h.2 ≠ 0 := by
      by_contra hn
      have hzero : h = 0 := by apply Prod.ext <;> simp_all
      exact hh hzero
    change 0 < -h.2 ∨ -h.2 = 0 ∧ 0 < -h.1
    unfold InUpperFactorHalf at hu
    by_cases hy : h.2 = 0
    · right
      constructor
      · omega
      · have hxn : h.1 ≠ 0 := hx.resolve_right (by simp [hy])
        omega
    · left
      omega

-- the rational order is the genuine counterclockwise determinant order on the upper semicircle.
theorem upperFactorSlope_det_nonnegative (p q : Site)
    (hp : InUpperFactorHalf p) (hq : InUpperFactorHalf q)
    (hslope : upperFactorSlope q ≤ upperFactorSlope p) : 0 ≤ determinant p q := by
  rcases hp with hpY | ⟨hpY, hpX⟩
  · rcases hq with hqY | ⟨hqY, hqX⟩
    · have hpne : p.2 ≠ 0 := ne_of_gt hpY
      have hqne : q.2 ≠ 0 := ne_of_gt hqY
      simp only [upperFactorSlope, ite_eq_right hpne, ite_eq_right hqne, WithTop.coe_le_coe] at hslope
      have hpYr : (0 : ℚ) < (p.2 : ℚ) := by exact_mod_cast hpY
      have hqYr : (0 : ℚ) < (q.2 : ℚ) := by exact_mod_cast hqY
      have hcross := (div_le_div_iff₀ hqYr hpYr).mp hslope
      have hcrossZ : q.1 * p.2 ≤ p.1 * q.2 := by exact_mod_cast hcross
      change 0 ≤ p.1 * q.2 - p.2 * q.1
      nlinarith
    · have hpne : p.2 ≠ 0 := ne_of_gt hpY
      simp only [upperFactorSlope, ite_eq_right hpne, ite_eq_left hqY, WithTop.not_top_le_coe] at hslope
  · have hqy : 0 ≤ q.2 := by rcases hq with hy | ⟨hy, _hx⟩ <;> omega
    change 0 ≤ p.1 * q.2 - p.2 * q.1
    rw [hpY, zero_mul, sub_zero]
    exact mul_nonneg (le_of_lt hpX) hqy

end KumarNivat
