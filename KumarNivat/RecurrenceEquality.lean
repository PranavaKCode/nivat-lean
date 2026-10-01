import KumarNivat.LineRecurrence

namespace KumarNivat

-- translating a scalar recurrence leaves its coefficients unchanged.
theorem LineRecurrence.translate {K : Type*} [CommRing K]
    {t : ℕ} {α : Fin (t + 1) → K} {a : ℤ → K}
    (ha : LineRecurrence t α a) (m : ℤ) :
    LineRecurrence t α (fun n => a (n + m)) := by
  intro n
  simpa only [show ∀ i : Fin (t + 1), n + (i.val : ℤ) + m =
    n + m + (i.val : ℤ) by intro i; omega] using ha (n + m)

-- subtracting two solutions gives another solution of the same linear recurrence.
theorem LineRecurrence.sub {K : Type*} [CommRing K]
    {t : ℕ} {α : Fin (t + 1) → K} {a b : ℤ → K}
    (ha : LineRecurrence t α a) (hb : LineRecurrence t α b) :
    LineRecurrence t α (fun n => a n - b n) := by
  intro n
  simp only [mul_sub, Finset.sum_sub_distrib, ha n, hb n, sub_self]

-- one full recurrence block determines the solution in both time directions.
theorem recurrence_equal_of_block {K : Type*} [Field K]
    (t : ℕ) (α : Fin (t + 1) → K) (a b : ℤ → K)
    (hfirst : α 0 ≠ 0) (hlast : α (Fin.last t) ≠ 0)
    (ha : LineRecurrence t α a) (hb : LineRecurrence t α b) (m : ℤ)
    (he : ∀ i : Fin t, a (m + (i.val : ℤ)) = b (m + (i.val : ℤ))) :
    ∀ n : ℤ, a n = b n := by
  have hz := zero_of_reversible_recurrence_block t α (fun n => a n - b n)
    hfirst hlast (ha.sub hb) m (fun i => sub_eq_zero.mpr (he i))
  intro n
  exact sub_eq_zero.mp (hz n)

end KumarNivat
