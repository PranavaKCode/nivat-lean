import KumarNivat.LaurentFactorization
import Mathlib.RingTheory.Localization.FractionRing

namespace KumarNivat

-- map only the coefficients of a one-variable laurent polynomial.
noncomputable def coefficientMap {R S : Type*} [CommRing R] [CommRing S] (ρ : R →+* S) :
    LaurentPolynomial R →+* LaurentPolynomial S := AddMonoidAlgebra.mapRingHom ℤ ρ

-- constants follow the original coefficient-ring map.
@[simp] theorem coefficientMap_C {R S : Type*} [CommRing R] [CommRing S]
    (ρ : R →+* S) (a : R) : coefficientMap ρ (LaurentPolynomial.C a) =
      LaurentPolynomial.C (ρ a) := by
  change AddMonoidAlgebra.mapRingHom ℤ ρ (AddMonoidAlgebra.single 0 a) =
    AddMonoidAlgebra.single 0 (ρ a)
  exact AddMonoidAlgebra.mapRingHom_single ρ 0 a

-- an injective coefficient map remains injective on the finite laurent sums.
theorem coefficientMap_injective {R S : Type*} [CommRing R] [CommRing S]
    (ρ : R →+* S) (hinj : Function.Injective ρ) : Function.Injective (coefficientMap ρ) := by
  intro f g he
  apply AddMonoidAlgebra.coeff_injective
  ext n
  apply hinj
  have hc := congrArg (fun p : LaurentPolynomial S => p.coeff n) he
  simpa only [coefficientMap, AddMonoidAlgebra.coeff_mapRingHom] using hc

-- one coefficient denominator clears an entire finite laurent polynomial.
theorem exists_coefficient_denominator {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (M : Submonoid R) [IsLocalization M S] (p : LaurentPolynomial S) :
    ∃ s : M, ∃ q : LaurentPolynomial R,
      p * LaurentPolynomial.C (algebraMap R S s) = coefficientMap (algebraMap R S) q := by
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => exact ⟨1, 0, by simp⟩
  | add p q hp hq =>
    obtain ⟨s, P, hP⟩ := hp
    obtain ⟨t, Q, hQ⟩ := hq
    refine ⟨s * t, P * LaurentPolynomial.C (t : R) + Q * LaurentPolynomial.C (s : R), ?_⟩
    calc
      (p + q) * LaurentPolynomial.C (algebraMap R S (s * t : M)) =
          (p * LaurentPolynomial.C (algebraMap R S s)) * LaurentPolynomial.C (algebraMap R S t) +
          (q * LaurentPolynomial.C (algebraMap R S t)) * LaurentPolynomial.C (algebraMap R S s) := by
        rw [Submonoid.coe_mul, map_mul, map_mul]
        ring
      _ = _ := by rw [hP, hQ, map_add, map_mul, map_mul, coefficientMap_C, coefficientMap_C]
  | single n a =>
    obtain ⟨⟨r, s⟩, hs⟩ := IsLocalization.surj M a
    refine ⟨s, AddMonoidAlgebra.single n r, ?_⟩
    change AddMonoidAlgebra.single n a * AddMonoidAlgebra.single 0 (algebraMap R S s) =
      AddMonoidAlgebra.mapRingHom ℤ (algebraMap R S) (AddMonoidAlgebra.single n r)
    rw [AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.mapRingHom_single, add_zero]
    exact congrArg (AddMonoidAlgebra.single n) hs

-- localizing the coefficients localizes the laurent ring at the corresponding constants.
noncomputable def coefficientLocalizationMap {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (M : Submonoid R) [IsLocalization M S]
    (hinj : Function.Injective (algebraMap R S)) :
    (M.map (LaurentPolynomial.C : R →+* LaurentPolynomial R)).LocalizationMap
      (LaurentPolynomial S) where
  toFun := coefficientMap (algebraMap R S)
  map_mul' := map_mul (coefficientMap (algebraMap R S))
  isLocalizationMap := {
    map_units := by
      intro x
      obtain ⟨s, hs, he⟩ := Submonoid.mem_map.mp x.property
      change IsUnit (coefficientMap (algebraMap R S) x.val)
      rw [← he, coefficientMap_C]
      exact (IsLocalization.map_units S ⟨s, hs⟩).map LaurentPolynomial.C
    surj := by
      intro p
      obtain ⟨s, q, he⟩ := exists_coefficient_denominator M p
      refine ⟨⟨q, ⟨LaurentPolynomial.C (s : R), Submonoid.mem_map.mpr ⟨s, s.property, rfl⟩⟩⟩, ?_⟩
      change p * coefficientMap (algebraMap R S) (LaurentPolynomial.C (s : R)) =
        coefficientMap (algebraMap R S) q
      rw [coefficientMap_C]
      exact he
    exists_of_eq := by
      intro x y he
      refine ⟨1, ?_⟩
      simp only [Submonoid.coe_one, one_mul]
      exact coefficientMap_injective (algebraMap R S) hinj he
  }

end KumarNivat
