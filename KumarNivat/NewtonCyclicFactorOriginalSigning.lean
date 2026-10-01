import KumarNivat.NewtonCyclicFactorSort
import KumarNivat.MonomialNewtonTranslation

namespace KumarNivat

-- a finite integer tilt realizes the selected upper-half signs without a horizontal tie.
def upperFactorTiltNormal (M : ℤ) : Site →+ ℤ where
  toFun h := h.1 + M * h.2
  map_zero' := by simp
  map_add' h g := by simp; ring

-- finitely many actual factors allow that same tilt to match every chosen sign.
theorem exists_upper_factor_tilt_normal (hs : List Site) (hdirs : ∀ h ∈ hs, h ≠ 0) :
    ∃ ν : Site →+ ℤ, ∀ h ∈ hs, upperFactorDirection h = orientNormalDirection ν h := by
  classical
  let B : ℤ := ∑ h ∈ hs.toFinset, |h.1|
  let M := B + 1
  let ν := upperFactorTiltNormal M
  have hB : 0 ≤ B := Finset.sum_nonneg (fun h _hh => abs_nonneg h.1)
  have hM : 0 < M := by dsimp [M]; omega
  have hpositive (h : Site) (hh : h ∈ hs) : 0 < ν (upperFactorDirection h) := by
    let g := upperFactorDirection h
    have hg : InUpperFactorHalf g := upperFactorDirection_in_upper h (hdirs h hh)
    have hb : |h.1| ≤ B := Finset.single_le_sum
      (fun r _hr => abs_nonneg r.1) (List.mem_toFinset.mpr hh)
    have he : |g.1| = |h.1| := by
      rcases upperFactorDirection_choice h with he | he
      · rw [show g = h from he]
      · rw [show g = -h from he]
        simp
    have hgb : -B ≤ g.1 := (abs_le.mp (he ▸ hb)).1
    rcases hg with hy | ⟨hy, hx⟩
    · have hyle : (1 : ℤ) ≤ g.2 := by omega
      have hmul : M ≤ M * g.2 := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hyle (le_of_lt hM)
      have hlevel : B + 1 ≤ M * g.2 := hmul
      change 0 < g.1 + M * g.2
      omega
    · change 0 < g.1 + M * g.2
      rw [hy, mul_zero, add_zero]
      exact hx
  refine ⟨ν, ?_⟩
  intro h hh
  have hp := hpositive h hh
  by_cases hu : InUpperFactorHalf h
  · have he : upperFactorDirection h = h := by simp only [upperFactorDirection, ite_eq_left hu]
    rw [he] at hp
    simp only [upperFactorDirection, ite_eq_left hu, orientNormalDirection, ite_eq_left hp]
  · have he : upperFactorDirection h = -h := by simp only [upperFactorDirection, ite_eq_right hu]
    rw [he, map_neg] at hp
    have hn : ¬ 0 < ν h := by omega
    simp only [upperFactorDirection, ite_eq_right hu, orientNormalDirection, ite_eq_right hn]

-- the existing signed-factor unit identity and actual permutation give the original product's exact monomial translation.
theorem upper_sorted_difference_product_monomial {K : Type*} [CommRing K] [Nontrivial K]
    (hs : List Site) (hdirs : ∀ h ∈ hs, h ≠ 0) :
    ∃ v : Site, ∃ ε : K, ε ≠ 0 ∧ differenceProduct (K := K) (upperSortedFactors hs) =
      AddMonoidAlgebra.single v ε * differenceProduct hs := by
  obtain ⟨ν, hν⟩ := exists_upper_factor_tilt_normal hs hdirs
  have hmap : hs.map upperFactorDirection = hs.map (orientNormalDirection ν) := by
    apply List.map_congr_left
    intro h hh
    exact hν h hh
  obtain ⟨v, ε, hε, he⟩ := oriented_difference_product_monomial (K := K) hs ν
  rw [← hmap] at he
  have hperm : differenceProduct (K := K) (upperSortedFactors hs) =
      differenceProduct (hs.map upperFactorDirection) := by
    unfold differenceProduct
    exact ((upperSortedFactors_perm hs).map (fun h => (binomial h : Laurent K))).prod_eq
  exact ⟨v, ε, hε, hperm.trans he⟩

end KumarNivat
