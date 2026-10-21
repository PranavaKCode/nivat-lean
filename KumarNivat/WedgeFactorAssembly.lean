module

public import KumarNivat.WedgeCount
public import KumarNivat.PeriodBinomials
public import KumarNivat.FactorBoxes
public import KumarNivat.DivisorPeriods
public import KumarNivat.LaurentUnits

@[expose] public section

namespace KumarNivat

-- the count needs only the common-divisor and directional-factor structure from section 2.
theorem rectangle_bound_of_structural_wedge_data {K : Type*} [Field K] [CharZero K]
    (c B : Site → K) (hc : (Set.range c).Finite) (hB : FullyPeriodic B)
    (ell μ : Site →+ ℤ) (a b : ℤ) (hinj : Function.Injective (ell.prod μ))
    (hwedge : AgreesOnWedge ell μ a b c B)
    (φ : Laurent K) (hφ : φ ≠ 0) (r s k n : ℕ) (hext : BoxExtrema φ r s)
    (hφbox : φ.coeff.support ⊆ rectangle (r + 1) (s + 1))
    (hdiv : ∀ f : Laurent K, (∃ κ : K, laurentAct f c = fun _ => κ) → φ ∣ f)
    (hρ : FullyPeriodic (laurentAct φ c))
    (f₁ f₂ : Laurent K) (p q E₁ E₂ : Site) (t₁ t₂ r₁ s₁ r₂ s₂ : ℕ)
    (α₁ : Fin (t₁ + 1) → K) (α₂ : Fin (t₂ + 1) → K)
    (hdet : determinant p q ≠ 0)
    (hfirst₁ : α₁ 0 ≠ 0) (hlast₁ : α₁ (Fin.last t₁) ≠ 0)
    (hfirst₂ : α₂ 0 ≠ 0) (hlast₂ : α₂ (Fin.last t₂) ≠ 0)
    (hφ₁ : φ = lineOperator E₁ p t₁ α₁ * f₁)
    (hφ₂ : φ = lineOperator E₂ q t₂ α₂ * f₂)
    (hext₁ : BoxExtrema (lineOperator E₁ p t₁ α₁) r₁ s₁)
    (hext₂ : BoxExtrema (lineOperator E₂ q t₂ α₂) r₂ s₂)
    (hE₁ : E₁ ∈ rectangle (r₁ + 1) (s₁ + 1))
    (hend₁ : E₁ + (t₁ : ℤ) • p ∈ rectangle (r₁ + 1) (s₁ + 1))
    (hE₂ : E₂ ∈ rectangle (r₂ + 1) (s₂ + 1))
    (hend₂ : E₂ + (t₂ : ℤ) • q ∈ rectangle (r₂ + 1) (s₂ + 1))
    (ht₁ : 0 < t₁) (ht₂ : 0 < t₂)
    (v₀ w₀ : Site) (hperioddet : determinant v₀ w₀ ≠ 0)
    (hdvd₁ : lineOperator E₁ p t₁ α₁ ∣ binomial v₀)
    (hdvd₂ : lineOperator E₂ q t₂ α₂ ∣ binomial w₀)
    (Q₀ : Laurent K) (hQ₀ : Q₀ ≠ 0) (hann : laurentAct Q₀ c = 0) :
    k * n + 1 ≤ complexity c (rectangle k n) := by
  have hdirs := determinant_ne_zero_directions p q hdet
  have hcommon (f : Laurent K) (hf : laurentAct f c = 0) : φ ∣ f := hdiv f ⟨0, hf⟩
  have hnot₁ := complementary_filter_not_fullyPeriodic c φ (lineOperator E₁ p t₁ α₁) f₁
    hφ hφ₁ (lineOperator_not_isUnit E₁ p hdirs.1 t₁ ht₁ α₁ hfirst₁ hlast₁) hcommon
  have hnot₂ := complementary_filter_not_fullyPeriodic c φ (lineOperator E₂ q t₂ α₂) f₂
    hφ hφ₂ (lineOperator_not_isUnit E₂ q hdirs.2 t₂ ht₂ α₂ hfirst₂ hlast₂) hcommon
  obtain ⟨hr₁, hs₁, hsupp₁⟩ := complementary_factor_box φ (lineOperator E₁ p t₁ α₁) f₁
    hφ hφ₁ r s r₁ s₁ hφbox hext₁
  obtain ⟨hr₂, hs₂, hsupp₂⟩ := complementary_factor_box φ (lineOperator E₂ q t₂ α₂) f₂
    hφ hφ₂ r s r₂ s₂ hφbox hext₂
  obtain ⟨M, hM, hBv, hρv⟩ := common_period_multiple_pair B (laurentAct φ c) hB hρ v₀
  obtain ⟨N, hN, hBw, hρw⟩ := common_period_multiple_pair B (laurentAct φ c) hB hρ w₀
  let v := (M : ℤ) • v₀
  let w := (N : ℤ) • w₀
  have hMZ : (M : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
  have hNZ : (N : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hdet' : determinant v w ≠ 0 := by
    rw [determinant_zsmul]
    exact mul_ne_zero (mul_ne_zero hMZ hNZ) hperioddet
  obtain ⟨a₁, ha₁⟩ := hdvd₁.trans (binomial_dvd_positive_multiple v₀ M)
  obtain ⟨a₂, ha₂⟩ := hdvd₂.trans (binomial_dvd_positive_multiple w₀ N)
  have hp₁ := filtered_period_of_periodic_remainder c hc φ
    (lineOperator E₁ p t₁ α₁) f₁ a₁ v hφ₁ ha₁ hρv
  have hp₂ := filtered_period_of_periodic_remainder c hc φ
    (lineOperator E₂ q t₂ α₂) f₂ a₂ w hφ₂ ha₂ hρw
  exact rectangle_bound_of_wedge_factor_data c B hc hB ell μ a b hinj hwedge
    φ hφ r s k n hext hdiv f₁ f₂ p q E₁ E₂ t₁ t₂ r₁ s₁ r₂ s₂ α₁ α₂ hdet
    hfirst₁ hlast₁ hfirst₂ hlast₂ hφ₁ hφ₂ hr₁ hs₁ hr₂ hs₂ hE₁ hend₁ hE₂ hend₂
    hsupp₁ hsupp₂ v w hdet' hp₁ hp₂ hnot₁ hnot₂ hBv hBw hρv hρw Q₀ hQ₀ hann

end KumarNivat
