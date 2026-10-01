import KumarNivat.RectangleQuotient

namespace KumarNivat

-- a normalized factor subtracts its coordinate widths from the product's support box.
theorem complementary_factor_box {K : Type*} [Field K]
    (φ ψ f : Laurent K) (hφ : φ ≠ 0) (hprod : φ = ψ * f)
    (r s r₁ s₁ : ℕ) (hφbox : φ.coeff.support ⊆ rectangle (r + 1) (s + 1))
    (hext : BoxExtrema ψ r₁ s₁) :
    r₁ ≤ r ∧ s₁ ≤ s ∧
      f.coeff.support ⊆ rectangle (r - r₁ + 1) (s - s₁ + 1) := by
  have hψ : ψ ≠ 0 := by
    intro hz
    apply hφ
    rw [hprod, hz, zero_mul]
  have hf : f ≠ 0 := by
    intro hz
    apply hφ
    rw [hprod, hz, mul_zero]
  have hfit : (ψ * f).coeff.support ⊆ rectangle (r + 1) (s + 1) := by
    rw [← hprod]
    exact hφbox
  have hq := quotient_support_rectangle ψ f hψ r₁ s₁ (r + 1) (s + 1) hext hfit
  have hnonempty : f.coeff.support.Nonempty := Finsupp.support_nonempty_iff.mpr
    (fun hz => hf (AddMonoidAlgebra.coeff_injective hz))
  obtain ⟨u, hu⟩ := hnonempty
  have hub := (mem_rectangle_iff u ((r + 1) - r₁) ((s + 1) - s₁)).mp (hq hu)
  have hr : r₁ ≤ r := by omega
  have hs : s₁ ≤ s := by omega
  refine ⟨hr, hs, ?_⟩
  simpa only [show r + 1 - r₁ = r - r₁ + 1 by omega,
    show s + 1 - s₁ = s - s₁ + 1 by omega] using hq

end KumarNivat
