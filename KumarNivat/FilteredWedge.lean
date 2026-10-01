import KumarNivat.WedgeSaturation

namespace KumarNivat

-- a finite stencil only moves the two wedge thresholds farther into the agreement region.
theorem finite_filter_wedge_agreement {K : Type*} [CommRing K] (c B : Site → K)
    (ell μ : Site →+ ℤ) (a b : ℤ) (hwedge : AgreesOnWedge ell μ a b c B)
    (f : Stencil K) : ∃ a' b' : ℤ, AgreesOnWedge ell μ a' b' (act f c) (act f B) := by
  classical
  let cost₁ : ℤ := ∑ u ∈ f.support, |ell u|
  let cost₂ : ℤ := ∑ u ∈ f.support, |μ u|
  refine ⟨a + cost₁, b + cost₂, ?_⟩
  intro g hg₁ hg₂
  unfold act Finsupp.sum
  apply Finset.sum_congr rfl
  intro u hu
  have hbound₁ : |ell u| ≤ cost₁ := by
    dsimp [cost₁]
    exact Finset.single_le_sum (fun v _ => abs_nonneg (ell v)) hu
  have hbound₂ : |μ u| ≤ cost₂ := by
    dsimp [cost₂]
    exact Finset.single_le_sum (fun v _ => abs_nonneg (μ v)) hu
  have hlow₁ : -|ell u| ≤ ell u := neg_abs_le _
  have hlow₂ : -|μ u| ≤ μ u := neg_abs_le _
  have hfirst : a ≤ ell (g + u) := by rw [map_add]; omega
  have hsecond : b ≤ μ (g + u) := by rw [map_add]; omega
  change f u * c (g + u) = f u * B (g + u)
  rw [hwedge (g + u) hfirst hsecond]

-- the filtered background and array share a genuine inset tangent half-plane.
theorem filtered_halfplane_agreement {K : Type*} [CommRing K] (c B : Site → K)
    (ell μ : Site →+ ℤ) (a b : ℤ) (hinj : Function.Injective (ell.prod μ))
    (hwedge : AgreesOnWedge ell μ a b c B) (hfull : FullyPeriodic B)
    (f : Laurent K) (v : Site) (hv : v ≠ 0)
    (hcperiod : IsPeriod (laurentAct f c) v) (hBperiod : IsPeriod B v)
    (hnot : ¬ FullyPeriodic (laurentAct f c)) :
    ∃ ν : Site →+ ℤ, ν ≠ 0 ∧ ν v = 0 ∧ ∃ β : ℤ,
      AgreesAbove ν β (laurentAct f c) (laurentAct f B) := by
  obtain ⟨a', b', hwedge'⟩ := finite_filter_wedge_agreement c B ell μ a b hwedge f.coeff
  exact exists_halfplane_agreement_of_common_period _ _ ell μ a' b' v hv hinj
    hcperiod (hBperiod.filtered f.coeff) hwedge' hnot (hfull.filtered f)

end KumarNivat
