module

public import KumarNivat.ExposedOperators

@[expose] public section

namespace KumarNivat

-- a line block has no nonzero coefficient outside its finite consecutive exponent segment.
theorem lineOperator_support_subset_range {K : Type*} [CommRing K]
    (E p : Site) (t : ℕ) (α : Fin (t + 1) → K) :
    (lineOperator E p t α).coeff.support ⊆
      Finset.univ.image (fun i : Fin (t + 1) => E + (i.val : ℤ) • p) := by
  classical
  intro u hu
  by_contra hout
  have hz : (lineOperator E p t α).coeff u = 0 := by
    simp only [lineOperator, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
      AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    apply Finset.sum_eq_zero
    intro i _hi
    have he : E + (i.val : ℤ) • p ≠ u := by
      intro heq
      exact hout (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, heq⟩)
    rw [ite_eq_right he]
  exact Finsupp.mem_support_iff.mp hu hz

-- the exposed block's endpoints and degree are derived from the actual supporting coefficients.
theorem exists_actual_exposed_face_data {K : Type*} [CommRing K]
    (f : Laurent K) (ν : Site →+ ℤ) (hν : ν ≠ 0) (m : ℤ)
    (hmin : ∀ u ∈ f.coeff.support, m ≤ ν u) (E p : Site) (hp : p ≠ 0)
    (hprimitive : Int.gcd p.1 p.2 = 1) (htangent : ν p = 0)
    (hE : E ∈ f.coeff.support) (hlevel : ν E = m) :
    ∃ q₀ : Site, ∃ t : ℕ, ∃ α : Fin (t + 1) → K,
      α 0 ≠ 0 ∧ α (Fin.last t) ≠ 0 ∧ ν q₀ = m ∧
        q₀ ∈ f.coeff.support ∧ q₀ + (t : ℤ) • p ∈ f.coeff.support ∧
        exposedOperator f ν m = lineOperator q₀ p t α ∧
        (∀ u ∈ f.coeff.support, ν u = m →
          ∃ i : Fin (t + 1), u = q₀ + (i.val : ℤ) • p) ∧
        f = lineOperator q₀ p t α + (f - exposedOperator f ν m) ∧
        ∀ u ∈ (f - exposedOperator f ν m).coeff.support, m + 1 ≤ ν u := by
  classical
  obtain ⟨q₀, t, α, hfirst, hlast, hq₀, hdecomp, hstrict⟩ :=
    exposed_line_decomposition_of_supporting_level f ν hν m hmin E p hp hprimitive htangent hE hlevel
  have hfaceeq : exposedOperator f ν m = lineOperator q₀ p t α := by
    have he : exposedOperator f ν m + (f - exposedOperator f ν m) = f := by abel
    exact add_right_cancel (he.trans hdecomp)
  have hend := lineOperator_endpoints_mem q₀ p hp t α hfirst hlast
  have hsupport : ∀ u ∈ (lineOperator q₀ p t α).coeff.support, u ∈ f.coeff.support := by
    intro u hu
    rw [← hfaceeq, exposedOperator_support] at hu
    exact (Finset.mem_filter.mp hu).1
  refine ⟨q₀, t, α, hfirst, hlast, hq₀, hsupport q₀ hend.1,
    hsupport _ hend.2, hfaceeq, ?_, hdecomp, hstrict⟩
  intro u hu hnormal
  have huf : u ∈ (exposedOperator f ν m).coeff.support := by
    rw [exposedOperator_support]
    exact Finset.mem_filter.mpr ⟨hu, hnormal⟩
  rw [hfaceeq] at huf
  obtain ⟨i, _hi, he⟩ := Finset.mem_image.mp (lineOperator_support_subset_range q₀ p t α huf)
  exact ⟨i, he.symm⟩

end KumarNivat
