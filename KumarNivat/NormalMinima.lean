module

public import KumarNivat.GeneratedHalfplanes
public import KumarNivat.SupportExtrema
public import KumarNivat.DistinctDirectionProducts

@[expose] public section

namespace KumarNivat

open scoped Pointwise

-- the unique normal minimum records a genuine nonzero extreme coefficient.
def UniqueNormalMinimum {K : Type*} [CommRing K]
    (f : Laurent K) (ell : Site →+ ℝ) (v : Site) : Prop :=
  v ∈ f.coeff.support ∧ ∀ u ∈ f.coeff.support, u ≠ v → ell v < ell u

-- every support term is on the inward side of the unique minimum.
theorem UniqueNormalMinimum.le {K : Type*} [CommRing K]
    {f : Laurent K} {ell : Site →+ ℝ} {v : Site} (hf : UniqueNormalMinimum f ell v)
    (u : Site) (hu : u ∈ f.coeff.support) : ell v ≤ ell u := by
  by_cases he : u = v
  · rw [he]
  · exact le_of_lt (hf.2 u hu he)

-- independent extreme inputs give a surviving unique extreme term of their product.
theorem UniqueNormalMinimum.mul {K : Type*} [CommRing K] [NoZeroDivisors K]
    {f g : Laurent K} {ell : Site →+ ℝ} {u v : Site}
    (hf : UniqueNormalMinimum f ell u) (hg : UniqueNormalMinimum g ell v) :
    UniqueNormalMinimum (f * g) ell (u + v) := by
  classical
  have huniq : UniqueAdd f.coeff.support g.coeff.support u v := by
    intro a b ha hb he
    have haMin := hf.le a ha
    have hbMin := hg.le b hb
    have heNormal : ell a + ell b = ell u + ell v := by rw [← map_add, he, map_add]
    have hau : a = u := by
      by_contra hn
      have hstrict := hf.2 a ha hn
      linarith
    have hbv : b = v := by
      by_contra hn
      have hstrict := hg.2 b hb hn
      linarith
    exact ⟨hau, hbv⟩
  refine ⟨?_, ?_⟩
  · apply Finsupp.mem_support_iff.mpr
    rw [AddMonoidAlgebra.coeff_mul_add_of_uniqueAdd huniq]
    exact mul_ne_zero (Finsupp.mem_support_iff.mp hf.1) (Finsupp.mem_support_iff.mp hg.1)
  · intro w hw hne
    obtain ⟨a, ha, b, hb, he⟩ := Finset.mem_add.mp (AddMonoidAlgebra.support_coeff_mul_subset f g hw)
    rw [← he, map_add, map_add]
    by_cases hau : a = u
    · have hbv : b ≠ v := by intro hz; exact hne (by rw [← he, hau, hz])
      have hstrict := hg.2 b hb hbv
      rw [hau]
      linarith
    · have hstrict := hf.2 a ha hau
      have hbMin := hg.le b hb
      linarith

-- subtraction introduces no support outside the two monomials of a difference binomial.
theorem binomial_support_subset {K : Type*} [CommRing K] (h : Site) :
    (binomial h : Laurent K).coeff.support ⊆ {h} ∪ {0} := by
  classical
  have hsub : (Finsupp.single h (1 : K) - Finsupp.single 0 1).support ⊆ {h} ∪ {0} := by
    grw [Finsupp.support_sub]
    exact Finset.union_subset_union Finsupp.support_single_subset Finsupp.support_single_subset
  simpa only [binomial, AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_sub,
    AddMonoidAlgebra.coeff_single] using hsub

-- a binomial transverse to the boundary normal has exactly one minimizing endpoint.
theorem binomial_has_unique_normal_minimum {K : Type*} [CommRing K] [Nontrivial K]
    (h : Site) (ell : Site →+ ℝ) (hell : ell h ≠ 0) :
    ∃ v : Site, UniqueNormalMinimum (binomial h : Laurent K) ell v := by
  classical
  have hh : h ≠ 0 := fun hz => hell (by rw [hz, map_zero])
  rcases lt_or_gt_of_ne hell with hneg | hpos
  · refine ⟨h, ?_, ?_⟩
    · apply Finsupp.mem_support_iff.mpr
      simp [binomial, AddMonoidAlgebra.one_def, hh]
    · intro u hu hne
      have htwo := Finset.mem_union.mp (binomial_support_subset h hu)
      rcases htwo with hhu | hzero
      · exact (hne (Finset.mem_singleton.mp hhu)).elim
      · rw [Finset.mem_singleton.mp hzero, map_zero]
        exact hneg
  · refine ⟨0, ?_, ?_⟩
    · apply Finsupp.mem_support_iff.mpr
      simp [binomial, AddMonoidAlgebra.one_def, hh]
    · intro u hu hne
      have htwo := Finset.mem_union.mp (binomial_support_subset h hu)
      rcases htwo with hhu | hzero
      · rw [Finset.mem_singleton.mp hhu, map_zero]
        exact hpos
      · exact (hne (Finset.mem_singleton.mp hzero)).elim

-- a product transverse in every factor has one surviving minimizing vertex, despite interior cancellation.
theorem differenceProduct_has_unique_normal_minimum {K : Type*} [CommRing K]
    [Nontrivial K] [NoZeroDivisors K] (hs : List Site) (ell : Site →+ ℝ)
    (htransverse : ∀ h ∈ hs, ell h ≠ 0) :
    ∃ v : Site, UniqueNormalMinimum (differenceProduct hs : Laurent K) ell v := by
  induction hs with
  | nil =>
    refine ⟨0, ?_, ?_⟩
    · simp [differenceProduct_nil, AddMonoidAlgebra.one_def]
    · intro u hu hne
      have he : u = 0 := by simpa [differenceProduct_nil, AddMonoidAlgebra.one_def] using hu
      exact (hne he).elim
  | cons h hs ih =>
    obtain ⟨u, hu⟩ := binomial_has_unique_normal_minimum (K := K) h ell
      (htransverse h List.mem_cons_self)
    obtain ⟨v, hv⟩ := ih (fun g hg => htransverse g (List.mem_cons_of_mem h hg))
    exact ⟨u + v, by rw [differenceProduct_cons]; exact hu.mul hv⟩

end KumarNivat
