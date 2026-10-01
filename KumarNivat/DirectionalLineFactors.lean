import KumarNivat.PrimitiveDirections
import KumarNivat.AffineLineOperators
import KumarNivat.LaurentUnits

namespace KumarNivat

-- a divisor of a period binomial occupies one affine copy of its primitive line.
theorem divisor_support_primitive_line {K : Type*} [Field K]
    (h : Site) (hh : h ≠ 0) (ψ : Laurent K) (hdiv : ψ ∣ binomial h)
    (p : Site) (a : ℕ) (he : h = (a : ℤ) • p) (τ : Site →+ ℤ)
    (hker : ∀ g : Site, directionNormal p g = 0 → g = τ g • p) :
    ∃ E : Site, E ∈ ψ.coeff.support ∧
      ∀ u ∈ ψ.coeff.support, u = E + τ (u - E) • p := by
  classical
  obtain ⟨f, hf⟩ := hdiv
  have hψf : ψ * f ≠ 0 := by rw [← hf]; exact binomial_ne_zero h hh
  have hψ : ψ ≠ 0 := left_ne_zero_of_mul hψf
  have hn : directionNormal p h = 0 := by
    rw [he, map_zsmul, directionNormal_self, smul_zero]
  obtain ⟨β, hβ⟩ := factor_support_normal_fiber ψ f hψ (right_ne_zero_of_mul hψf)
    (directionNormal p) τ (normal_line_coordinate_injective p τ hker) (by
      rw [← hf]
      exact binomial_support_normal_zero h (directionNormal p) hn)
  have hsupport : ψ.coeff.support.Nonempty := Finsupp.support_nonempty_iff.mpr
    (fun hz => hψ (AddMonoidAlgebra.coeff_injective hz))
  obtain ⟨E, hE⟩ := hsupport
  refine ⟨E, hE, ?_⟩
  intro u hu
  have hline := hker (u - E) (by rw [map_sub, hβ u hu, hβ E hE, sub_self])
  simpa only [add_sub_cancel] using congrArg (fun v => E + v) hline

-- the binomial divisor's affine support supplies the common trimmed line block.
theorem exists_binomial_divisor_line_block {K : Type*} [Field K]
    (h : Site) (hh : h ≠ 0) (ψ : Laurent K) (hdiv : ψ ∣ binomial h) :
    ∃ p : Site, ∃ a : ℕ, 0 < a ∧ h = (a : ℤ) • p ∧ p ≠ 0 ∧
      ∃ E : Site, ∃ t : ℕ, ∃ α : Fin (t + 1) → K,
        α 0 ≠ 0 ∧ α (Fin.last t) ≠ 0 ∧ ψ = lineOperator E p t α := by
  classical
  obtain ⟨p, a, ha, he, hp, τ, _ht, hker⟩ := exists_primitive_direction_coordinate h hh
  obtain ⟨E, _hE, hline⟩ := divisor_support_primitive_line h hh ψ hdiv p a he τ hker
  have hψ : ψ ≠ 0 := by
    obtain ⟨f, hf⟩ := hdiv
    exact left_ne_zero_of_mul (show ψ * f ≠ 0 by rw [← hf]; exact binomial_ne_zero h hh)
  have hsupp : (ψ.coeff.support : Set Site) ⊆ Set.range (fun n : ℤ => E + n • p) := by
    intro u hu
    exact ⟨τ (u - E), (hline u hu).symm⟩
  obtain ⟨m, t, α, hfirst, hlast, hblock⟩ := exists_affine_support_line_block ψ hψ E p hp hsupp
  exact ⟨p, a, ha, he, hp, E + m • p, t, α, hfirst, hlast, hblock⟩

-- a proper directional group has positive degree because a degree-zero block is a unit monomial.
theorem exists_proper_binomial_divisor_line_block {K : Type*} [Field K]
    (h : Site) (hh : h ≠ 0) (ψ : Laurent K) (hdiv : ψ ∣ binomial h)
    (hproper : ¬ IsUnit ψ) :
    ∃ p : Site, ∃ a : ℕ, 0 < a ∧ h = (a : ℤ) • p ∧ p ≠ 0 ∧
      ∃ E : Site, ∃ t : ℕ, 0 < t ∧ ∃ α : Fin (t + 1) → K,
        α 0 ≠ 0 ∧ α (Fin.last t) ≠ 0 ∧ ψ = lineOperator E p t α := by
  obtain ⟨p, a, ha, he, hp, E, t, α, hfirst, hlast, hψ⟩ :=
    exists_binomial_divisor_line_block h hh ψ hdiv
  have ht : 0 < t := by
    by_contra hn
    have hz : t = 0 := by omega
    subst t
    apply hproper
    rw [hψ]
    change IsUnit (∑ i : Fin 1, AddMonoidAlgebra.single (E + (i.val : ℤ) • p) (α i))
    rw [Fin.sum_univ_one]
    simpa only [Fin.val_zero, Nat.cast_zero, zero_smul, add_zero]
      using single_isUnit E (α 0) hfirst
  exact ⟨p, a, ha, he, hp, E, t, ht, α, hfirst, hlast, hψ⟩

end KumarNivat
