import KumarNivat.DirectionalGrouping
import KumarNivat.LaurentNormalization
import KumarNivat.WedgeFactorAssembly

namespace KumarNivat

-- theorem 1.2 follows from the actual product annihilator and wedge agreement in the paper.
theorem periodic_wedge_bound {K : Type*} [Field K] [CharZero K] [Infinite K]
    (c B : Site → K) (hc : (Set.range c).Finite)
    (hnot : ¬ ∃ v : Site, v ≠ 0 ∧ IsPeriod c v) (hB : FullyPeriodic B)
    (ell μ : Site →+ ℤ) (a b : ℤ) (hinj : Function.Injective (ell.prod μ))
    (hwedge : AgreesOnWedge ell μ a b c B)
    (hs : List Site) (hdirs : ∀ h ∈ hs, h ≠ 0)
    (hpairs : hs.Pairwise (fun p q => determinant p q ≠ 0))
    (hann : laurentAct (differenceProduct hs) c = 0) (k n : ℕ) :
    k * n + 1 ≤ complexity c (rectangle k n) := by
  classical
  obtain ⟨φ, hφ, hφQ, hρ, hdiv⟩ := exists_periodic_remainder_of_difference_product
    c hc hs hdirs hpairs hann
  obtain ⟨u, _hu, ψ, he, hψ, i, j, _hij, hi, hj, hdirDet⟩ :=
    exists_two_proper_directional_groups c hc hs hdirs hpairs φ hφQ hρ hnot
  have hψφ (l : Fin hs.length) : ψ l ∣ φ := by
    rw [he]
    exact (Finset.dvd_prod_of_mem ψ (Finset.mem_univ l)).trans (dvd_mul_left _ u)
  obtain ⟨vφ, r, s, hextφ, hboxφ⟩ := exists_normalized_laurent_box φ hφ
  let Φ := AddMonoidAlgebra.single vφ (1 : K) * φ
  have hΦ : Φ ≠ 0 := mul_ne_zero (by simp) hφ
  have hunitφ : IsUnit (AddMonoidAlgebra.single vφ (1 : K)) := single_isUnit vφ 1 one_ne_zero
  have hdivΦ (f : Laurent K) (hf : ∃ κ : K, laurentAct f c = fun _ => κ) : Φ ∣ f :=
    hunitφ.mul_left_dvd.mpr (hdiv f hf)
  have hρΦ : FullyPeriodic (laurentAct Φ c) := by
    rw [laurentAct_mul]
    exact hρ.filtered (AddMonoidAlgebra.single vφ 1)
  obtain ⟨p, A, _hA, heA, _hp, v₁, E₁, t₁, r₁, s₁, ht₁, α₁,
      hfirst₁, hlast₁, hnorm₁, hext₁, hE₁, hend₁⟩ :=
    exists_normalized_proper_line_factor (hs.get i)
      (hdirs (hs.get i) (List.get_mem _ _)) (ψ i) (hψ i) hi
  obtain ⟨q, D, _hD, heD, _hq, v₂, E₂, t₂, r₂, s₂, ht₂, α₂,
      hfirst₂, hlast₂, hnorm₂, hext₂, hE₂, hend₂⟩ :=
    exists_normalized_proper_line_factor (hs.get j)
      (hdirs (hs.get j) (List.get_mem _ _)) (ψ j) (hψ j) hj
  have hdet : determinant p q ≠ 0 := by
    intro hz
    apply hdirDet
    rw [heA, heD, determinant_zsmul, hz, mul_zero]
  have hunit₁ : IsUnit (AddMonoidAlgebra.single v₁ (1 : K)) := single_isUnit v₁ 1 one_ne_zero
  have hunit₂ : IsUnit (AddMonoidAlgebra.single v₂ (1 : K)) := single_isUnit v₂ 1 one_ne_zero
  have hdvd₁ : lineOperator E₁ p t₁ α₁ ∣ binomial (hs.get i) := by
    rw [hnorm₁]
    exact hunit₁.mul_left_dvd.mpr (hψ i)
  have hdvd₂ : lineOperator E₂ q t₂ α₂ ∣ binomial (hs.get j) := by
    rw [hnorm₂]
    exact hunit₂.mul_left_dvd.mpr (hψ j)
  have hfactor₁ : lineOperator E₁ p t₁ α₁ ∣ Φ := by
    rw [hnorm₁]
    exact hunit₁.mul_left_dvd.mpr ((hψφ i).trans (dvd_mul_left φ _))
  have hfactor₂ : lineOperator E₂ q t₂ α₂ ∣ Φ := by
    rw [hnorm₂]
    exact hunit₂.mul_left_dvd.mpr ((hψφ j).trans (dvd_mul_left φ _))
  obtain ⟨f₁, hf₁⟩ := hfactor₁
  obtain ⟨f₂, hf₂⟩ := hfactor₂
  exact rectangle_bound_of_structural_wedge_data c B hc hB ell μ a b hinj hwedge
    Φ hΦ r s k n hextφ hboxφ hdivΦ hρΦ f₁ f₂ p q E₁ E₂ t₁ t₂ r₁ s₁ r₂ s₂
    α₁ α₂ hdet hfirst₁ hlast₁ hfirst₂ hlast₂ hf₁ hf₂ hext₁ hext₂
    hE₁ hend₁ hE₂ hend₂ ht₁ ht₂ (hs.get i) (hs.get j) hdirDet hdvd₁ hdvd₂
    (differenceProduct hs) (differenceProduct_ne_zero hs hdirs) hann

end KumarNivat
