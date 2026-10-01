import KumarNivat.BinomialCoprime
import KumarNivat.DistinctDirectionProducts
import KumarNivat.LaurentFactorization
import KumarNivat.CommonAnnihilatorDivisor
import KumarNivat.KariSzabados

namespace KumarNivat

-- a binomial is relatively prime to a product whose every direction is independent of it.
theorem binomial_relPrime_differenceProduct {K : Type*} [Field K]
    (p : Site) (hs : List Site) (hind : ∀ q ∈ hs, determinant p q ≠ 0) :
    IsRelPrime (binomial p : Laurent K) (differenceProduct hs) := by
  induction hs with
  | nil => exact isRelPrime_one_right
  | cons q hs ih =>
    rw [differenceProduct_cons]
    exact (independent_binomials_isRelPrime p q (hind q List.mem_cons_self)).mul_right
      (ih (fun v hv => hind v (List.mem_cons_of_mem q hv)))

-- nonzero directions give a nonzero product operator.
theorem differenceProduct_ne_zero {K : Type*} [CommRing K] [Nontrivial K] [NoZeroDivisors K]
    (hs : List Site) (hdirs : ∀ h ∈ hs, h ≠ 0) : (differenceProduct hs : Laurent K) ≠ 0 := by
  induction hs with
  | nil => exact one_ne_zero
  | cons p hs ih =>
    rw [differenceProduct_cons]
    exact mul_ne_zero (binomial_ne_zero p (hdirs p List.mem_cons_self))
      (ih (fun v hv => hdirs v (List.mem_cons_of_mem p hv)))

-- characteristic zero and pairwise distinct directions make the whole product squarefree.
theorem differenceProduct_squarefree {K : Type*} [Field K] [CharZero K]
    (hs : List Site) (hdirs : ∀ h ∈ hs, h ≠ 0)
    (hpairs : hs.Pairwise (fun p q => determinant p q ≠ 0)) :
    Squarefree (differenceProduct hs : Laurent K) := by
  induction hs with
  | nil => exact squarefree_one
  | cons p hs ih =>
    obtain ⟨hind, htail⟩ := List.pairwise_cons.mp hpairs
    rw [differenceProduct_cons, squarefree_mul_iff]
    exact ⟨binomial_relPrime_differenceProduct p hs hind,
      binomial_squarefree p (hdirs p List.mem_cons_self),
      ih (fun v hv => hdirs v (List.mem_cons_of_mem p hv)) htail⟩

-- the common divisor and its coprime quotients now come from the original integer complexity bound.
theorem low_complexity_common_divisor_quotients {K : Type*} [Field K] [CharZero K] [Infinite K]
    (c : Site → ℤ) (hc : (Set.range c).Finite) (D : Finset Site)
    (hlow : complexity c D ≤ D.card) :
    ∃ hs : List Site, ∃ φ g a b : Laurent K,
      hs ≠ [] ∧ hs.Pairwise (fun p q => determinant p q ≠ 0) ∧ (∀ h ∈ hs, h ≠ 0) ∧
      φ ≠ 0 ∧ laurentAct g (fun u => (c u : K)) = 0 ∧
      differenceProduct hs = φ * a ∧ g = φ * b ∧
      (∀ f : Laurent K, laurentAct f (fun u => (c u : K)) = 0 → φ ∣ f) ∧
      IsRelPrime a b ∧ laurentAct a (laurentAct φ (fun u => (c u : K))) = 0 ∧
      laurentAct b (laurentAct φ (fun u => (c u : K))) = 0 := by
  obtain ⟨hs, hnil, hpairs, hdirs, hann⟩ := low_complexity_distinct_difference_product c hc D hlow
  have hcast : laurentAct (differenceProduct hs) (fun u => (c u : K)) = 0 :=
    cast_integer_difference_product c hs hann
  obtain ⟨φ, g, a, b, hφ, hg, ha, hb, hcommon, hcop, hA, hB⟩ :=
    exists_common_divisor_coprime_quotients (fun u => (c u : K)) (differenceProduct hs)
      (differenceProduct_ne_zero hs hdirs) (differenceProduct_squarefree hs hdirs hpairs) hcast
  exact ⟨hs, φ, g, a, b, hnil, hpairs, hdirs, hφ, hg, ha, hb, hcommon, hcop, hA, hB⟩

end KumarNivat
