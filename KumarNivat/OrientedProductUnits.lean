import KumarNivat.OrientedDifferenceProducts
import KumarNivat.LaurentNormalization

namespace KumarNivat

-- simultaneous factor reversal changes the actual polynomial by one nonzero monomial, rather than merely preserving its divisor.
theorem oriented_difference_product_monomial {K : Type*} [CommRing K] [Nontrivial K]
    (hs : List Site) (ν : Site →+ ℤ) :
    ∃ v : Site, ∃ ε : K, ε ≠ 0 ∧
      differenceProduct (hs.map (orientNormalDirection ν)) =
        AddMonoidAlgebra.single v ε * differenceProduct hs := by
  induction hs with
  | nil =>
    refine ⟨0, 1, one_ne_zero, ?_⟩
    simp only [List.map_nil, differenceProduct_nil, mul_one]
    rfl
  | cons h hs ih =>
    obtain ⟨v, ε, hε, he⟩ := ih
    by_cases hpos : 0 < ν h
    · refine ⟨v, ε, hε, ?_⟩
      simp only [List.map_cons, differenceProduct_cons, orientNormalDirection, ite_eq_left hpos, he]
      ring
    · refine ⟨-h + v, -ε, neg_ne_zero.mpr hε, ?_⟩
      simp only [List.map_cons, differenceProduct_cons, orientNormalDirection, ite_eq_right hpos, he,
        binomial_negative]
      have hsingle : (-AddMonoidAlgebra.single (-h) (1 : K)) * AddMonoidAlgebra.single v ε =
          AddMonoidAlgebra.single (-h + v) (-ε) := by
        rw [neg_mul, AddMonoidAlgebra.single_mul_single, one_mul, AddMonoidAlgebra.single_neg]
      rw [← hsingle]
      ring

-- a nonzero monomial coefficient shifts the support exactly, including all canceled interior terms.
theorem nonzero_monomial_translate_mem_support {K : Type*} [CommRing K] [NoZeroDivisors K]
    (v : Site) (ε : K) (hε : ε ≠ 0) (f : Laurent K) (u : Site) :
    u ∈ (AddMonoidAlgebra.single v ε * f).coeff.support ↔ u - v ∈ f.coeff.support := by
  classical
  simp only [Finsupp.mem_support_iff, AddMonoidAlgebra.coeff_single_mul_apply,
    mul_ne_zero_iff, sub_eq_add_neg, add_comm]
  exact ⟨fun h => h.2, fun h => ⟨hε, h⟩⟩

end KumarNivat
