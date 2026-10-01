import KumarNivat.Operators

namespace KumarNivat

-- agreement on an integer half-plane is the output of the directional saturation step.
def AgreesAbove {A : Type*} (ν : Site →+ ℤ) (β : ℤ) (x y : Site → A) : Prop :=
  ∀ g, β ≤ ν g → x g = y g

-- a transverse difference vanishes beyond the manuscript's explicit half-plane inset.
theorem difference_zero_above {K : Type*} [AddGroup K]
    (A B : Site → K) (ν : Site →+ ℤ) (β : ℤ) (w : Site)
    (hagree : AgreesAbove ν β A B) (hB : IsPeriod B w) :
    ∀ g, β + max 0 (-ν w) ≤ ν g → difference w A g = 0 := by
  intro g hg
  have hmax₀ : (0 : ℤ) ≤ max 0 (-ν w) := le_max_left _ _
  have hmaxw : -ν w ≤ max 0 (-ν w) := le_max_right _ _
  have hfirst : β ≤ ν g := by omega
  have hsecond : β ≤ ν (g + w) := by rw [map_add]; omega
  unfold difference
  rw [hagree (g + w) hsecond, hagree g hfirst, hB g, sub_self]

-- nonzero defect sites therefore lie in the opposite closed lattice half-plane.
theorem difference_support_bound {K : Type*} [AddGroup K]
    (A B : Site → K) (ν : Site →+ ℤ) (β : ℤ) (w : Site)
    (hagree : AgreesAbove ν β A B) (hB : IsPeriod B w) :
    ∀ g, difference w A g ≠ 0 → ν g ≤ β + max 0 (-ν w) - 1 := by
  intro g hne
  by_contra hbound
  have hg : β + max 0 (-ν w) ≤ ν g := by omega
  exact hne (difference_zero_above A B ν β w hagree hB g hg)

-- shifts of arrays commute with taking a directional difference.
theorem difference_shift {K : Type*} [Sub K] (w u : Site) (A : Site → K) :
    difference w (shift u A) = shift u (difference w A) := by
  funext g
  change A (g + w + u) - A (g + u) = A (g + u + w) - A (g + u)
  rw [show g + w + u = g + u + w by abel]

-- section 3's product of placed defects obeys both shifted half-plane bounds.
theorem shifted_defect_product_support {K : Type*} [Ring K]
    (A₁ A₂ B₁ B₂ : Site → K) (ν₁ ν₂ : Site →+ ℤ) (β₁ β₂ : ℤ)
    (v w u₁ u₂ : Site)
    (hagree₁ : AgreesAbove ν₁ β₁ A₁ B₁) (hagree₂ : AgreesAbove ν₂ β₂ A₂ B₂)
    (hB₁ : IsPeriod B₁ w) (hB₂ : IsPeriod B₂ v) :
    ∀ g, difference w (shift u₁ A₁) g * difference v (shift u₂ A₂) g ≠ 0 →
      ν₁ u₁ - β₁ - max 0 (-ν₁ w) + 1 ≤ -ν₁ g ∧
        ν₂ u₂ - β₂ - max 0 (-ν₂ v) + 1 ≤ -ν₂ g := by
  intro g hne
  have hne₁ := left_ne_zero_of_mul hne
  have hne₂ := right_ne_zero_of_mul hne
  simp only [difference_shift, shift] at hne₁ hne₂
  have h₁ := difference_support_bound A₁ B₁ ν₁ β₁ w hagree₁ hB₁ (g + u₁) hne₁
  have h₂ := difference_support_bound A₂ B₂ ν₂ β₂ v hagree₂ hB₂ (g + u₂) hne₂
  rw [map_add] at h₁ h₂
  constructor <;> omega

end KumarNivat
