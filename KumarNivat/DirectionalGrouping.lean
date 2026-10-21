module

public import KumarNivat.DivisorPeriods
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

namespace KumarNivat

-- decomposition in the ufd collects each divisor's factors into its corresponding period binomial.
theorem exists_directional_divisor_family {K : Type*} [Field K]
    (hs : List Site) (φ : Laurent K) (hdiv : φ ∣ differenceProduct hs) :
    ∃ u : Laurent K, IsUnit u ∧ ∃ ψ : Fin hs.length → Laurent K,
      φ = u * ∏ i, ψ i ∧ ∀ i, ψ i ∣ binomial (hs.get i) := by
  classical
  induction hs generalizing φ with
  | nil =>
    refine ⟨φ, isUnit_of_dvd_one hdiv, fun i => Fin.elim0 i, by simp, ?_⟩
    intro i
    exact Fin.elim0 i
  | cons h hs ih =>
    rw [differenceProduct_cons] at hdiv
    obtain ⟨a, b, ha, hb, hφ⟩ := exists_dvd_and_dvd_of_dvd_mul hdiv
    obtain ⟨u, hu, ψ, he, hψ⟩ := ih b hb
    refine ⟨u, hu, Fin.cons a ψ, ?_, ?_⟩
    · change φ = u * ∏ i : Fin (hs.length + 1), Fin.cons a ψ i
      rw [hφ, he, Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      ring
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa only [Fin.cons_zero, List.get_cons_zero] using ha
      · change ψ j ∣ binomial (hs.get j)
        exact hψ j

-- the original pairwise condition gives independence for every two different factor indices.
theorem indexed_directions_independent (hs : List Site)
    (hpairs : hs.Pairwise (fun p q => determinant p q ≠ 0))
    (i j : Fin hs.length) (hij : i ≠ j) : determinant (hs.get i) (hs.get j) ≠ 0 := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact hpairs.rel_get_of_lt hlt
  · have he := hpairs.rel_get_of_lt hgt
    have hswap : determinant (hs.get i) (hs.get j) = -determinant (hs.get j) (hs.get i) := by
      simp [determinant]
      ring
    rw [hswap]
    exact neg_ne_zero.mpr he

-- if only one group were nonunit, the common divisor would divide that single direction's binomial.
theorem exists_two_nonunit_factor_indices {K : Type*} [Field K]
    (hs : List Site) (φ u : Laurent K) (hu : IsUnit u) (ψ : Fin hs.length → Laurent K)
    (hprod : φ = u * ∏ i, ψ i) (hdiv : ∀ i, ψ i ∣ binomial (hs.get i))
    (hunit : ¬ IsUnit φ) (hsingle : ∀ i, ¬ φ ∣ binomial (hs.get i)) :
    ∃ i j : Fin hs.length, i ≠ j ∧ ¬ IsUnit (ψ i) ∧ ¬ IsUnit (ψ j) := by
  classical
  have hex : ∃ i, ¬ IsUnit (ψ i) := by
    by_contra hn
    have hall : ∀ i, IsUnit (ψ i) := by
      intro i
      by_contra hi
      exact hn ⟨i, hi⟩
    apply hunit
    rw [hprod]
    exact hu.mul (IsUnit.prod_univ_iff.mpr hall)
  obtain ⟨i, hi⟩ := hex
  have hsecond : ∃ j, j ≠ i ∧ ¬ IsUnit (ψ j) := by
    by_contra hn
    let O := ∏ j ∈ (Finset.univ.erase i), ψ j
    have hO : IsUnit O := by
      apply IsUnit.prod_iff.mpr
      intro j hj
      have hji := (Finset.mem_erase.mp hj).1
      by_contra hjunit
      exact hn ⟨j, hji, hjunit⟩
    have hφ : φ = (u * O) * ψ i := by
      rw [hprod, ← Finset.prod_erase_mul Finset.univ ψ (Finset.mem_univ i)]
      ring
    apply hsingle i
    rw [hφ]
    simpa only [one_mul] using mul_dvd_mul ((hu.mul hO).dvd : u * O ∣ 1) (hdiv i)
  obtain ⟨j, hji, hj⟩ := hsecond
  exact ⟨i, j, Ne.symm hji, hi, hj⟩

-- nonperiodicity forces two proper groups in the actual common-divisor factorization.
theorem exists_two_proper_directional_groups {K : Type*} [Field K] [CharZero K]
    (c : Site → K) (hc : (Set.range c).Finite) (hs : List Site)
    (hdirs : ∀ h ∈ hs, h ≠ 0) (hpairs : hs.Pairwise (fun p q => determinant p q ≠ 0))
    (φ : Laurent K) (hdiv : φ ∣ differenceProduct hs)
    (hρ : FullyPeriodic (laurentAct φ c)) (hnot : ¬ ∃ v : Site, v ≠ 0 ∧ IsPeriod c v) :
    ∃ u : Laurent K, IsUnit u ∧ ∃ ψ : Fin hs.length → Laurent K,
      φ = u * ∏ i, ψ i ∧ (∀ i, ψ i ∣ binomial (hs.get i)) ∧
      ∃ i j : Fin hs.length, i ≠ j ∧ ¬ IsUnit (ψ i) ∧ ¬ IsUnit (ψ j) ∧
        determinant (hs.get i) (hs.get j) ≠ 0 := by
  obtain ⟨u, hu, ψ, he, hψ⟩ := exists_directional_divisor_family hs φ hdiv
  have hob := nonperiodic_divisor_obstructions c hc φ hρ hnot
  obtain ⟨i, j, hij, hi, hj⟩ := exists_two_nonunit_factor_indices hs φ u hu ψ he hψ hob.1
    (fun i => hob.2 (hs.get i) (hdirs (hs.get i) (List.get_mem _ _)))
  exact ⟨u, hu, ψ, he, hψ, i, j, hij, hi, hj, indexed_directions_independent hs hpairs i j hij⟩

end KumarNivat
