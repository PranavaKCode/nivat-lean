import KumarNivat.KariSzabados

namespace KumarNivat

-- zero or one actual difference factor would already give a global period of the original array.
theorem nonperiodic_difference_product_has_two_factors {K : Type*} [CommRing K]
    (c : Site → K) (hnot : ¬ ∃ p : Site, p ≠ 0 ∧ IsPeriod c p)
    (hs : List Site) (hdirs : ∀ p ∈ hs, p ≠ 0) (hann : laurentAct (differenceProduct hs) c = 0) :
    2 ≤ hs.length := by
  cases hs with
  | nil =>
    have hz : c = 0 := by simpa only [differenceProduct_nil, laurentAct_one] using hann
    exact False.elim (hnot ⟨(1, 0), by decide, by intro g; rw [hz]; rfl⟩)
  | cons p hs =>
    cases hs with
    | nil =>
      rw [differenceProduct_cons, differenceProduct_nil, mul_one, laurentAct_binomial] at hann
      have hp : IsPeriod c p := by
        intro g
        have he := congrFun hann g
        change c (g + p) - c g = 0 at he
        exact sub_eq_zero.mp he
      exact False.elim (hnot ⟨p, hdirs p List.mem_cons_self, hp⟩)
    | cons r hs => simp

-- the original integer complexity bound therefore supplies the required nondegenerate factor polygon data.
theorem nonperiodic_low_complexity_product_data (c : Site → ℤ) (hc : (Set.range c).Finite)
    (hnot : ¬ ∃ p : Site, p ≠ 0 ∧ IsPeriod c p) (D : Finset Site)
    (hlow : complexity c D ≤ D.card) :
    ∃ hs : List Site, 2 ≤ hs.length ∧
      hs.Pairwise (fun p q => determinant p q ≠ 0) ∧ (∀ h ∈ hs, h ≠ 0) ∧
      laurentAct (differenceProduct hs) c = 0 := by
  obtain ⟨hs, _hnil, hpairs, hdirs, hann⟩ := low_complexity_distinct_difference_product c hc D hlow
  exact ⟨hs, nonperiodic_difference_product_has_two_factors c hnot hs hdirs hann, hpairs, hdirs, hann⟩

end KumarNivat
