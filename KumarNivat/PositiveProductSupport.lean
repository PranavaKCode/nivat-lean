module

public import KumarNivat.NormalMinima
public import KumarNivat.OrientedNormals

@[expose] public section

namespace KumarNivat

-- subset-sum bounds hold on the actual product support even when interior coefficients cancel.
theorem positive_difference_product_support_bounds {K : Type*} [CommRing K]
    (hs : List Site) (ν μ : Site →+ ℤ) (hν : ∀ h ∈ hs, 0 < ν h) (hμ : ∀ h ∈ hs, 0 ≤ μ h) :
    ∀ u ∈ (differenceProduct (K := K) hs).coeff.support,
      0 ≤ ν u ∧ ν u ≤ (hs.map ν).sum ∧ 0 ≤ μ u := by
  induction hs with
  | nil =>
    intro u hu
    have hu₀ : u = 0 := by
      simp only [differenceProduct_nil, AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single] at hu
      exact Finset.mem_singleton.mp (Finsupp.support_single_subset hu)
    subst u
    simp
  | cons h hs ih =>
    intro u hu
    rw [differenceProduct_cons] at hu
    obtain ⟨x, hx, y, hy, he⟩ := Finset.mem_add.mp
      (AddMonoidAlgebra.support_coeff_mul_subset (binomial h) (differenceProduct hs) hu)
    have hydata := ih (fun q hq => hν q (List.mem_cons_of_mem h hq))
      (fun q hq => hμ q (List.mem_cons_of_mem h hq)) y hy
    have hνh := hν h List.mem_cons_self
    have hμh := hμ h List.mem_cons_self
    rcases Finset.mem_union.mp (binomial_support_subset h hx) with hxh | hx₀
    · have hx' : x = h := Finset.mem_singleton.mp hxh
      rw [← he, hx', map_add, map_add]
      simp only [List.map_cons, List.sum_cons]
      exact ⟨by omega, by omega, by omega⟩
    · have hx' : x = 0 := Finset.mem_singleton.mp hx₀
      rw [← he, hx', zero_add]
      simp only [List.map_cons, List.sum_cons]
      exact ⟨hydata.1, by omega, hydata.2.2⟩

-- the first coefficient of each positively oriented factor is the actual unique normal minimum.
theorem positive_binomial_minimum_at_zero {K : Type*} [CommRing K] [Nontrivial K]
    (h : Site) (ν : Site →+ ℤ) (hν : 0 < ν h) :
    UniqueNormalMinimum (binomial h : Laurent K) (integerNormalAsReal ν) 0 := by
  have hne : h ≠ 0 := by intro hz; rw [hz, map_zero] at hν; omega
  obtain ⟨v, hv⟩ := binomial_has_unique_normal_minimum (K := K) h (integerNormalAsReal ν)
    (by change (ν h : ℝ) ≠ 0; exact_mod_cast ne_of_gt hν)
  have hzero : 0 ∈ (binomial h : Laurent K).coeff.support := by
    simp [binomial, AddMonoidAlgebra.one_def, hne]
  have hle := hv.le 0 hzero
  change (ν v : ℝ) ≤ (ν 0 : ℝ) at hle
  rw [map_zero, Int.cast_zero] at hle
  have hνv : ν v ≤ 0 := by exact_mod_cast hle
  have hv₀ : v = 0 := by
    rcases Finset.mem_union.mp (binomial_support_subset h hv.1) with hvh | hvzero
    · rw [Finset.mem_singleton.mp hvh] at hνv
      omega
    · exact Finset.mem_singleton.mp hvzero
  simpa only [hv₀] using hv

-- the other endpoint is the actual unique maximum for the same positive factor.
theorem positive_binomial_minimum_at_vector {K : Type*} [CommRing K] [Nontrivial K]
    (h : Site) (ν : Site →+ ℤ) (hν : 0 < ν h) :
    UniqueNormalMinimum (binomial h : Laurent K) (integerNormalAsReal (-ν)) h := by
  have hne : h ≠ 0 := by intro hz; rw [hz, map_zero] at hν; omega
  obtain ⟨v, hv⟩ := binomial_has_unique_normal_minimum (K := K) h (integerNormalAsReal (-ν))
    (by
      have hn : (-ν) h ≠ 0 := by change -ν h ≠ 0; exact neg_ne_zero.mpr (ne_of_gt hν)
      change ((-ν) h : ℝ) ≠ 0
      exact_mod_cast hn)
  have hmem : h ∈ (binomial h : Laurent K).coeff.support := by
    simp [binomial, AddMonoidAlgebra.one_def, hne]
  have hle := hv.le h hmem
  change ((-ν) v : ℝ) ≤ ((-ν) h : ℝ) at hle
  have hνv : (-ν) v ≤ (-ν) h := by exact_mod_cast hle
  change -ν v ≤ -ν h at hνv
  have hvh : v = h := by
    rcases Finset.mem_union.mp (binomial_support_subset h hv.1) with hvh | hvzero
    · exact Finset.mem_singleton.mp hvh
    · rw [Finset.mem_singleton.mp hvzero, map_zero] at hνv
      omega
  simpa only [hvh] using hv

-- the actual positive product has both nonzero extreme coefficients at zero and at the sum of its vectors.
theorem positive_difference_product_endpoint_data {K : Type*} [CommRing K] [Nontrivial K] [NoZeroDivisors K]
    (hs : List Site) (ν : Site →+ ℤ) (hν : ∀ h ∈ hs, 0 < ν h) :
    UniqueNormalMinimum (differenceProduct (K := K) hs) (integerNormalAsReal ν) 0 ∧
      UniqueNormalMinimum (differenceProduct (K := K) hs) (integerNormalAsReal (-ν)) hs.sum := by
  induction hs with
  | nil =>
    have hbase (η : Site →+ ℤ) : UniqueNormalMinimum (1 : Laurent K) (integerNormalAsReal η) 0 := by
      refine ⟨by simp [AddMonoidAlgebra.one_def], ?_⟩
      intro u hu hune
      have hu₀ : u = 0 := by simpa [AddMonoidAlgebra.one_def] using hu
      exact (hune hu₀).elim
    exact ⟨hbase ν, hbase (-ν)⟩
  | cons h hs ih =>
    have hνh := hν h List.mem_cons_self
    have htail := ih (fun q hq => hν q (List.mem_cons_of_mem h hq))
    refine ⟨?_, ?_⟩
    · simpa only [differenceProduct_cons, zero_add] using (positive_binomial_minimum_at_zero h ν hνh).mul htail.1
    · simpa only [differenceProduct_cons, List.sum_cons] using (positive_binomial_minimum_at_vector h ν hνh).mul htail.2

end KumarNivat
