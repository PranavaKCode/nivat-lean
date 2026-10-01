import KumarNivat.NormalMinima

namespace KumarNivat

-- reverse only those actual factor vectors whose normal slope is negative.
def orientNormalDirection (ν : Site →+ ℤ) (h : Site) : Site := if 0 < ν h then h else -h

-- every transverse direction acquires a strictly positive integer normal value.
theorem oriented_difference_directions_positive (hs : List Site) (ν : Site →+ ℤ)
    (htransverse : ∀ h ∈ hs, ν h ≠ 0) :
    ∀ h ∈ hs.map (orientNormalDirection ν), 0 < ν h := by
  intro h hh
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hh
  by_cases hpos : 0 < ν q
  · simpa only [orientNormalDirection, ite_eq_left hpos] using hpos
  · have hne := htransverse q hq
    simp only [orientNormalDirection, ite_eq_right hpos, map_neg]
    omega

-- reversing factors preserves divisibility of the original difference product.
theorem differenceProduct_dvd_oriented {K : Type*} [CommRing K] (hs : List Site) (ν : Site →+ ℤ) :
    differenceProduct (K := K) hs ∣ differenceProduct (hs.map (orientNormalDirection ν)) := by
  induction hs with
  | nil => simp
  | cons h hs ih =>
    have hfactor : (binomial h : Laurent K) ∣ binomial (orientNormalDirection ν h) := by
      by_cases hpos : 0 < ν h
      · simp only [orientNormalDirection, ite_eq_left hpos]
        exact dvd_refl _
      · simp only [orientNormalDirection, ite_eq_right hpos]
        simpa only [neg_one_zsmul] using binomial_dvd_integer_multiple (K := K) h (-1)
    simpa only [List.map_cons, differenceProduct_cons] using mul_dvd_mul hfactor ih

-- the actual reoriented product remains an annihilator of the same array.
theorem oriented_difference_product_annihilates {K : Type*} [CommRing K] (δ : Site → K)
    (hs : List Site) (ν : Site →+ ℤ) (hann : laurentAct (differenceProduct hs) δ = 0) :
    laurentAct (differenceProduct (hs.map (orientNormalDirection ν))) δ = 0 := by
  obtain ⟨U, hU⟩ := differenceProduct_dvd_oriented (K := K) hs ν
  rw [hU, mul_comm, laurentAct_mul, hann, laurentAct_config_zero]

-- the orientation retains the same original factor line for every resulting vector.
theorem oriented_difference_direction_mem (hs : List Site) (ν : Site →+ ℤ) (h : Site)
    (hh : h ∈ hs.map (orientNormalDirection ν)) : ∃ q ∈ hs, h = q ∨ h = -q := by
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hh
  refine ⟨q, hq, ?_⟩
  by_cases hpos : 0 < ν q
  · exact Or.inl (by simp only [orientNormalDirection, ite_eq_left hpos])
  · exact Or.inr (by simp only [orientNormalDirection, ite_eq_right hpos])

end KumarNivat
