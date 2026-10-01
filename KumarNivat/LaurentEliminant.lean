import KumarNivat.CoefficientLocalization
import KumarNivat.LocalizationCoprime
import KumarNivat.LaurentBezout

namespace KumarNivat

-- coefficient localization and denominator clearing produce a nonzero coefficient-ring eliminant.
theorem laurent_relPrime_eliminant {R : Type*} [CommRing R] [Nontrivial R]
    [UniqueFactorizationMonoid R] (f g : LaurentPolynomial R)
    (hf : f ≠ 0) (hcop : IsRelPrime f g) :
    ∃ d : R, d ≠ 0 ∧ ∃ a b : LaurentPolynomial R,
      a * f + b * g = LaurentPolynomial.C d := by
  classical
  let S := FractionRing R
  let ρ : R →+* S := algebraMap R S
  have hinj : Function.Injective ρ := IsFractionRing.injective R S
  let loc := coefficientLocalizationMap (nonZeroDivisors R) hinj
  have hlocal : IsRelPrime (coefficientMap ρ f) (coefficientMap ρ g) :=
    localization_preserves_relPrime loc (coefficientMap_injective ρ hinj) f g hf hcop
  obtain ⟨u, v, hbez⟩ := laurent_field_relPrime_isCoprime _ _ hlocal
  obtain ⟨s, A, hA⟩ := exists_coefficient_denominator (nonZeroDivisors R) u
  obtain ⟨t, B, hB⟩ := exists_coefficient_denominator (nonZeroDivisors R) v
  let d : R := (s : R) * (t : R)
  refine ⟨d, ?_, A * LaurentPolynomial.C (t : R), B * LaurentPolynomial.C (s : R), ?_⟩
  · exact mul_ne_zero (nonZeroDivisors.ne_zero s.property) (nonZeroDivisors.ne_zero t.property)
  · apply coefficientMap_injective ρ hinj
    dsimp only [d]
    simp only [map_add, map_mul, coefficientMap_C]
    rw [← hA, ← hB]
    calc
      _ = (u * coefficientMap ρ f + v * coefficientMap ρ g) *
          LaurentPolynomial.C (ρ (s : R)) * LaurentPolynomial.C (ρ (t : R)) := by ring
      _ = LaurentPolynomial.C (ρ (s : R)) * LaurentPolynomial.C (ρ (t : R)) := by
        rw [hbez, one_mul]

end KumarNivat
