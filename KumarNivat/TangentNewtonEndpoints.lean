import KumarNivat.PositiveProductSupport

namespace KumarNivat

open scoped Pointwise

-- both tangent-binomial endpoints survive multiplication at a unique transverse extreme.
theorem tangent_binomial_extreme_endpoint {K : Type*} [CommRing K] [NoZeroDivisors K]
    (p : Site) (ν : Site →+ ℤ) (hp : ν p = 0) (f : Laurent K) (v e : Site)
    (hmin : UniqueNormalMinimum f (integerNormalAsReal ν) v)
    (he : e ∈ (binomial p : Laurent K).coeff.support) :
    e + v ∈ (binomial p * f).coeff.support := by
  classical
  have hflat (x : Site) (hx : x ∈ (binomial p : Laurent K).coeff.support) : ν x = 0 := by
    rcases Finset.mem_union.mp (binomial_support_subset p hx) with hxp | hx0
    · simpa only [Finset.mem_singleton.mp hxp] using hp
    · rw [Finset.mem_singleton.mp hx0, map_zero]
  have huniq : UniqueAdd (binomial p : Laurent K).coeff.support f.coeff.support e v := by
    intro x y hx hy hxy
    have hlevel : ν y = ν v := by
      have hn := congrArg ν hxy
      simpa only [map_add, hflat x hx, hflat e he, zero_add] using hn
    have hyv : y = v := by
      by_contra hne
      have hstrict := hmin.2 y hy hne
      change (ν v : ℝ) < (ν y : ℝ) at hstrict
      rw [hlevel] at hstrict
      exact (lt_irrefl _ hstrict)
    exact ⟨by rw [hyv] at hxy; exact add_right_cancel hxy, hyv⟩
  apply Finsupp.mem_support_iff.mpr
  rw [AddMonoidAlgebra.coeff_mul_add_of_uniqueAdd huniq]
  exact mul_ne_zero (Finsupp.mem_support_iff.mp he) (Finsupp.mem_support_iff.mp hmin.1)

-- cancellation leaves the four actual endpoints of the two opposite tangent newton faces present.
theorem tangent_product_normal_endpoints {K : Type*} [CommRing K] [Nontrivial K] [NoZeroDivisors K]
    (p : Site) (hp : p ≠ 0) (hs : List Site) (ν : Site →+ ℤ) (hflat : ν p = 0)
    (hpos : ∀ h ∈ hs, 0 < ν h) :
    let f := (binomial p : Laurent K) * differenceProduct hs
    0 ∈ f.coeff.support ∧ p ∈ f.coeff.support ∧ hs.sum ∈ f.coeff.support ∧
      p + hs.sum ∈ f.coeff.support ∧
      ∀ u ∈ f.coeff.support, 0 ≤ ν u ∧ ν u ≤ (hs.map ν).sum := by
  have he0 : 0 ∈ (binomial p : Laurent K).coeff.support := by
    apply Finsupp.mem_support_iff.mpr
    simp [binomial, AddMonoidAlgebra.one_def, hp]
  have hep : p ∈ (binomial p : Laurent K).coeff.support := by
    apply Finsupp.mem_support_iff.mpr
    simp [binomial, AddMonoidAlgebra.one_def, hp]
  have hext := positive_difference_product_endpoint_data (K := K) hs ν hpos
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [add_zero] using tangent_binomial_extreme_endpoint p ν hflat
      (differenceProduct hs) 0 0 hext.1 he0
  · simpa only [add_zero] using tangent_binomial_extreme_endpoint p ν hflat
      (differenceProduct hs) 0 p hext.1 hep
  · simpa only [zero_add] using tangent_binomial_extreme_endpoint p (-ν) (by simp only [AddMonoidHom.neg_apply, hflat, neg_zero])
      (differenceProduct hs) hs.sum 0 hext.2 he0
  · exact tangent_binomial_extreme_endpoint p (-ν) (by simp only [AddMonoidHom.neg_apply, hflat, neg_zero])
      (differenceProduct hs) hs.sum p hext.2 hep
  · intro u hu
    obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp (AddMonoidAlgebra.support_coeff_mul_subset
      (binomial p : Laurent K) (differenceProduct hs) hu)
    have hbounds := positive_difference_product_support_bounds (K := K) hs ν 0 hpos
      (fun _h _hh => by simp) y hy
    have hx0 : ν x = 0 := by
      rcases Finset.mem_union.mp (binomial_support_subset p hx) with hxp | hx0
      · rwa [Finset.mem_singleton.mp hxp]
      · rw [Finset.mem_singleton.mp hx0, map_zero]
    rw [map_add, hx0, zero_add]
    exact ⟨hbounds.1, hbounds.2.1⟩

end KumarNivat
