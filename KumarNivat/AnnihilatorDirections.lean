import KumarNivat.NormalMinima

namespace KumarNivat

-- a nonzero annihilator coefficient determines that site from the rest of its finite stencil.
theorem annihilator_generates_support_site {K : Type*} [CommRing K] [NoZeroDivisors K]
    (c : Site → K) (f : Stencil K) (hann : ∀ g : Site, act f c g = 0)
    (v : Site) (hv : v ∈ f.support) : GeneratedSite c f.support v := by
  classical
  intro g h hagree u hu
  by_cases huv : u = v
  · subst u
    have hsum : (∑ w ∈ f.support, f w * (c (g + w) - c (h + w))) = 0 := by
      simp only [mul_sub, Finset.sum_sub_distrib]
      exact sub_eq_zero.mpr ((hann g).trans (hann h).symm)
    have heval : (∑ w ∈ f.support, f w * (c (g + w) - c (h + w))) =
        f v * (c (g + v) - c (h + v)) := by
      apply Finset.sum_eq_single v
      · intro w hw hwv
        rw [hagree w (Finset.mem_erase.mpr ⟨hwv, hw⟩), sub_self, mul_zero]
      · intro hn
        exact (hn hv).elim
    rw [heval] at hsum
    exact sub_eq_zero.mp ((mul_eq_zero.mp hsum).resolve_left (Finsupp.mem_support_iff.mp hv))
  · exact hagree u (Finset.mem_erase.mpr ⟨huv, hu⟩)

-- a unique minimizing annihilator coefficient makes the corresponding half-plane expansive.
theorem not_oneSidedNonexpansive_of_unique_annihilator_minimum {K : Type*}
    [CommRing K] [NoZeroDivisors K] [TopologicalSpace K] [DiscreteTopology K]
    (c : Site → K) (f : Laurent K) (hann : laurentAct f c = 0)
    (ell : Site →+ ℝ) (v : Site) (hmin : UniqueNormalMinimum f ell v) :
    ¬ OneSidedNonexpansive c ell := by
  exact not_oneSidedNonexpansive_of_generated_unique_minimum c f.coeff.support v hmin.1
    (annihilator_generates_support_site c f.coeff (congrFun hann) v hmin.1) ell hmin.2

-- every one-sided nonexpansive direction is parallel to a factor of the actual product annihilator.
theorem oneSidedNonexpansive_difference_product_direction {K : Type*}
    [CommRing K] [Nontrivial K] [NoZeroDivisors K] [TopologicalSpace K] [DiscreteTopology K]
    (c : Site → K) (hs : List Site) (hann : laurentAct (differenceProduct hs) c = 0)
    (ell : Site →+ ℝ) (hNE : OneSidedNonexpansive c ell) :
    ∃ h ∈ hs, ell h = 0 := by
  by_contra hn
  have htransverse : ∀ h ∈ hs, ell h ≠ 0 := by
    intro h hh hz
    exact hn ⟨h, hh, hz⟩
  obtain ⟨v, hv⟩ := differenceProduct_has_unique_normal_minimum (K := K) hs ell htransverse
  exact not_oneSidedNonexpansive_of_unique_annihilator_minimum c (differenceProduct hs) hann ell v hv hNE

end KumarNivat
