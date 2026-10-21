module

public import KumarNivat.LaurentAlgebra
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.GroupTheory.MonoidLocalization.UniqueFactorization
public import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid

@[expose] public section

namespace KumarNivat

-- inverting the polynomial variable preserves unique factorization.
instance laurentPolynomialUniqueFactorization {K : Type*} [CommRing K]
    [UniqueFactorizationMonoid K] : UniqueFactorizationMonoid (LaurentPolynomial K) :=
  UniqueFactorizationMonoid.of_isLocalization (Submonoid.powers (Polynomial.X : Polynomial K))
    (LaurentPolynomial K)

-- the lattice laurent ring is the iterated one-variable laurent ring.
noncomputable def nestedLaurentEquiv {K : Type*} [CommRing K] :
    Laurent K ≃+* LaurentPolynomial (LaurentPolynomial K) := AddMonoidAlgebra.curryRingEquiv

-- this supplies the actual unique-factorization structure used for the common divisor.
instance laurentUniqueFactorization {K : Type*} [Field K] :
    UniqueFactorizationMonoid (Laurent K) :=
  (nestedLaurentEquiv (K := K)).symm.toMulEquiv.uniqueFactorizationMonoid inferInstance

-- choose normalized gcd representatives only after unique factorization has been established.
noncomputable instance laurentNormalizedGCD {K : Type*} [Field K] :
    NormalizedGCDMonoid (Laurent K) := Classical.arbitrary (NormalizedGCDMonoid (Laurent K))

end KumarNivat
