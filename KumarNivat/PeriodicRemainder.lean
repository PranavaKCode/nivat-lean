module

public import KumarNivat.CoprimePeriods
public import KumarNivat.CommonAnnihilatorDivisor
public import KumarNivat.AffineCommonDivisor

@[expose] public section

namespace KumarNivat

-- lemma 2.4's common divisor leaves a fully periodic remainder, without assuming it annihilates c.
theorem exists_common_divisor_periodic_remainder {K : Type*} [Field K] [Infinite K]
    (c : Site → K) (hc : (Set.range c).Finite) (Q : Laurent K) (hQ : Q ≠ 0)
    (hsquare : Squarefree Q) (hann : laurentAct Q c = 0) :
    ∃ φ : Laurent K, φ ≠ 0 ∧ φ ∣ Q ∧ FullyPeriodic (laurentAct φ c) ∧
      ∀ f : Laurent K, laurentAct f c = 0 → φ ∣ f := by
  obtain ⟨φ, g, a, b, hφ, _hg, ha, _hb, hcommon, hcop, hA, hB⟩ :=
    exists_common_divisor_coprime_quotients c Q hQ hsquare hann
  have hane : a ≠ 0 := by
    intro hz
    apply hQ
    rw [ha, hz, mul_zero]
  have hfinite : (Set.range (laurentAct φ c)).Finite := finite_range_act c hc φ.coeff
  exact ⟨φ, hφ, ⟨a, ha⟩,
    fullyPeriodic_of_coprime_annihilators (laurentAct φ c) hfinite a b hane hcop hA hB, hcommon⟩

-- the actual product of distinct directions also gives divisibility of every affine relation.
theorem exists_periodic_remainder_of_difference_product {K : Type*} [Field K]
    [CharZero K] [Infinite K] (c : Site → K) (hc : (Set.range c).Finite)
    (hs : List Site) (hdirs : ∀ h ∈ hs, h ≠ 0)
    (hpairs : hs.Pairwise (fun p q => determinant p q ≠ 0))
    (hann : laurentAct (differenceProduct hs) c = 0) :
    ∃ φ : Laurent K, φ ≠ 0 ∧ φ ∣ differenceProduct hs ∧ FullyPeriodic (laurentAct φ c) ∧
      ∀ f : Laurent K, (∃ κ : K, laurentAct f c = fun _ => κ) → φ ∣ f := by
  obtain ⟨φ, hφ, hφQ, hperiodic, hcommon⟩ := exists_common_divisor_periodic_remainder c hc
    (differenceProduct hs) (differenceProduct_ne_zero hs hdirs)
    (differenceProduct_squarefree hs hdirs hpairs) hann
  exact ⟨φ, hφ, hφQ, hperiodic, common_divisor_divides_constant_output c φ hs hdirs hφQ hcommon⟩

-- the original integer complexity hypothesis now provides this common-divisor remainder data.
theorem low_complexity_periodic_remainder {K : Type*} [Field K] [CharZero K] [Infinite K]
    (c : Site → ℤ) (hc : (Set.range c).Finite) (D : Finset Site)
    (hlow : complexity c D ≤ D.card) :
    ∃ hs : List Site, ∃ φ : Laurent K,
      hs ≠ [] ∧ hs.Pairwise (fun p q => determinant p q ≠ 0) ∧ (∀ h ∈ hs, h ≠ 0) ∧
      φ ≠ 0 ∧ φ ∣ differenceProduct hs ∧ FullyPeriodic (laurentAct φ (fun g => (c g : K))) ∧
      ∀ f : Laurent K, (∃ κ : K, laurentAct f (fun g => (c g : K)) = fun _ => κ) → φ ∣ f := by
  obtain ⟨hs, hnil, hpairs, hdirs, hann⟩ := low_complexity_distinct_difference_product c hc D hlow
  have hcast : laurentAct (differenceProduct hs) (fun g => (c g : K)) = 0 :=
    cast_integer_difference_product c hs hann
  have hfinite : (Set.range (fun g => (c g : K))).Finite := (hc.image (fun z : ℤ => (z : K))).subset (by
    rintro y ⟨g, rfl⟩
    exact ⟨c g, ⟨g, rfl⟩, rfl⟩)
  obtain ⟨φ, hφ, hφQ, hperiodic, hdiv⟩ := exists_periodic_remainder_of_difference_product
    (fun g => (c g : K)) hfinite hs hdirs hpairs hcast
  exact ⟨hs, φ, hnil, hpairs, hdirs, hφ, hφQ, hperiodic, hdiv⟩

end KumarNivat
