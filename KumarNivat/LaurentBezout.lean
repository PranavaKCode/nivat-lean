module

public import KumarNivat.LaurentFactorization
public import Mathlib.Algebra.Polynomial.FieldDivision

@[expose] public section

namespace KumarNivat

-- clearing the two negative exponent tails lets polynomial bezout apply over a field.
theorem laurent_field_relPrime_isCoprime {K : Type*} [Field K]
    (f g : LaurentPolynomial K) (hcop : IsRelPrime f g) : IsCoprime f g := by
  classical
  obtain ⟨n, F, hF⟩ := LaurentPolynomial.exists_T_pow f
  obtain ⟨m, G, hG⟩ := LaurentPolynomial.exists_T_pow g
  let D := EuclideanDomain.gcd F G
  have hDf : Polynomial.toLaurent D ∣ f := by
    have hd := map_dvd Polynomial.toLaurent (EuclideanDomain.gcd_dvd_left F G)
    rw [hF] at hd
    exact (LaurentPolynomial.isUnit_T n).dvd_mul_right.mp hd
  have hDg : Polynomial.toLaurent D ∣ g := by
    have hd := map_dvd Polynomial.toLaurent (EuclideanDomain.gcd_dvd_right F G)
    rw [hG] at hd
    exact (LaurentPolynomial.isUnit_T m).dvd_mul_right.mp hd
  have hunit : IsUnit (Polynomial.toLaurent D) := hcop hDf hDg
  obtain ⟨u, hu⟩ := isUnit_iff_exists_inv.mp hunit
  have hbez := congrArg (Polynomial.toLaurent : Polynomial K → LaurentPolynomial K)
    (EuclideanDomain.gcd_eq_gcd_ab F G)
  rw [map_add, map_mul, map_mul, hF, hG] at hbez
  refine ⟨LaurentPolynomial.T n * Polynomial.toLaurent (EuclideanDomain.gcdA F G) * u,
    LaurentPolynomial.T m * Polynomial.toLaurent (EuclideanDomain.gcdB F G) * u, ?_⟩
  calc
    _ = Polynomial.toLaurent D * u := by rw [hbez]; ring
    _ = 1 := hu

end KumarNivat
