module

public import KumarNivat.PartialRecurrences
public import KumarNivat.LineOperators

@[expose] public section

namespace KumarNivat

-- removing the zero nonface inputs leaves the actual exposed line recurrence at each fitting base.
theorem exposed_line_recurrence_at {K : Type*} [CommRing K]
    (δ : Site → K) (f r : Laurent K) (q₀ p E : Site) (t : ℕ) (α : Fin (t + 1) → K)
    (hdecomp : f = lineOperator q₀ p t α + r) (hann : laurentAct f δ = 0)
    (n : ℤ) (hinterior : ∀ u ∈ r.coeff.support, δ ((E + n • p - q₀) + u) = 0) :
    (∑ i : Fin (t + 1), α i * δ (E + (n + (i.val : ℤ)) • p)) = 0 := by
  classical
  have hr : laurentAct r δ (E + n • p - q₀) = 0 := by
    unfold laurentAct act Finsupp.sum
    apply Finset.sum_eq_zero
    intro u hu
    change r.coeff u * δ ((E + n • p - q₀) + u) = 0
    rw [hinterior u hu, mul_zero]
  have he := congrFun hann (E + n • p - q₀)
  rw [hdecomp] at he
  change laurentActAt δ (E + n • p - q₀) (lineOperator q₀ p t α + r) = 0 at he
  rw [map_add] at he
  change laurentAct (lineOperator q₀ p t α) δ (E + n • p - q₀) +
    laurentAct r δ (E + n • p - q₀) = 0 at he
  rw [hr, add_zero, laurentAct_lineOperator] at he
  have hsite (i : Fin (t + 1)) :
      (E + n • p - q₀) + q₀ + (i.val : ℤ) • p = E + (n + (i.val : ℤ)) • p := by
    rw [add_smul]
    abel
  simpa only [hsite] using he

-- the finite-facet conclusion uses only the recurrences at sites where the stencil actually fits.
theorem finite_facet_zero_from_exposed_stencil {K : Type*} [CommRing K] [NoZeroDivisors K]
    (δ : Site → K) (f r : Laurent K) (q₀ p E : Site) (t : ℕ) (α : Fin (t + 1) → K)
    (hdecomp : f = lineOperator q₀ p t α + r) (hann : laurentAct f δ = 0)
    (b N : ℤ) (hlast : α (Fin.last t) ≠ 0)
    (hinterior : ∀ n : ℤ, b ≤ n → n + (t : ℤ) ≤ N →
      ∀ u ∈ r.coeff.support, δ ((E + n • p - q₀) + u) = 0)
    (hseed : ∀ i : Fin t, δ (E + (b + (i.val : ℤ)) • p) = 0) :
    ∀ n : ℤ, b ≤ n → n ≤ N → δ (E + n • p) = 0 := by
  apply zero_of_interval_recurrence_prefix t α (fun n => δ (E + n • p)) b N hlast _ hseed
  intro n hn hN
  exact exposed_line_recurrence_at δ f r q₀ p E t α hdecomp hann n (hinterior n hn hN)

-- the ray conclusion solves backwards from a tail using only recurrences based on that ray.
theorem ray_facet_zero_from_exposed_stencil {K : Type*} [CommRing K] [NoZeroDivisors K]
    (δ : Site → K) (f r : Laurent K) (q₀ p E : Site) (t : ℕ) (α : Fin (t + 1) → K)
    (hdecomp : f = lineOperator q₀ p t α + r) (hann : laurentAct f δ = 0)
    (b B : ℤ) (hfirst : α 0 ≠ 0)
    (hinterior : ∀ n : ℤ, b ≤ n → ∀ u ∈ r.coeff.support, δ ((E + n • p - q₀) + u) = 0)
    (htail : ∀ n : ℤ, B ≤ n → δ (E + n • p) = 0) :
    ∀ n : ℤ, b ≤ n → δ (E + n • p) = 0 := by
  apply zero_of_ray_recurrence_tail t α (fun n => δ (E + n • p)) b B hfirst _ htail
  intro n hn
  exact exposed_line_recurrence_at δ f r q₀ p E t α hdecomp hann n (hinterior n hn)

end KumarNivat
