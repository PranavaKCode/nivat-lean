import KumarNivat.ShiftedConfigurations
import KumarNivat.RegionalBackground
import KumarNivat.HalfplaneRecurrence

namespace KumarNivat

-- forward stability alone retains every nonnegative integer translate inside the region.
theorem forward_stable_nat_multiples (R : Set Site) (h : Site) (hstable : ∀ g ∈ R, g + h ∈ R) :
    ∀ n : ℕ, ∀ g ∈ R, g + (n : ℤ) • h ∈ R := by
  intro n
  induction n with
  | zero => intro g hg; simpa only [Nat.cast_zero, zero_smul, add_zero] using hg
  | succ n ih =>
    intro g hg
    have he := hstable _ (ih g hg)
    simpa only [Nat.cast_add, Nat.cast_one, add_smul, one_smul, add_assoc] using he

-- a regional period survives a shift that carries the working region into itself.
theorem regional_period_shift_of_forward_stability {A : Type*} (x : Site → A) (R : Set Site)
    (h p : Site) (hstable : ∀ g ∈ R, g + h ∈ R) (hperiod : RegionalPeriod x R p) :
    RegionalPeriod (shift h x) R p := by
  have hp := regional_period_shift x R h p hperiod
  intro g hg hfit
  exact hp g (hstable g hg) (hstable (g + p) hfit)

-- two independent recession directions give strictly positive interior slope for every nonzero inward normal.
theorem nonzero_normal_positive_on_independent_sum (μ : Site →+ ℤ) (hμ : μ ≠ 0)
    (a b : Site) (hdet : determinant a b ≠ 0) (ha : 0 ≤ μ a) (hb : 0 ≤ μ b) :
    0 < μ (a + b) := by
  rw [map_add]
  by_contra hnot
  have ha₀ : μ a = 0 := by omega
  have hb₀ : μ b = 0 := by omega
  exact hdet (nonzero_normal_kernel_parallel μ hμ a b ha₀ hb₀)

end KumarNivat
