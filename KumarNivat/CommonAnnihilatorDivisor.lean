module

public import KumarNivat.AnnihilatorIdeal
public import KumarNivat.LaurentFactorization
public import KumarNivat.SquarefreeDivisibility

@[expose] public section

namespace KumarNivat

-- one squarefree annihilator and finite-subspace avoidance give the gcd of every annihilator.
theorem exists_common_annihilator_divisor {K : Type*} [Field K] [Infinite K]
    (c : Site → K) (Q : Laurent K) (hQ : Q ≠ 0) (hsquare : Squarefree Q)
    (hann : laurentAct Q c = 0) :
    ∃ φ g : Laurent K, φ ≠ 0 ∧ laurentAct g c = 0 ∧ φ ∣ Q ∧ φ ∣ g ∧
      (∀ f : Laurent K, laurentAct f c = 0 → φ ∣ f) ∧
      (∀ d : Laurent K, (∀ f : Laurent K, laurentAct f c = 0 → d ∣ f) → d ∣ φ) ∧
      φ = GCDMonoid.gcd Q g := by
  classical
  let S := (UniqueFactorizationMonoid.normalizedFactors Q).toFinset.filter
    (fun p => ¬ ∀ f : Laurent K, laurentAct f c = 0 → p ∣ f)
  have hwitness (p : Laurent K) (hp : p ∈ S) :
      ∃ f : Laurent K, laurentAct f c = 0 ∧ ¬ p ∣ f := by
    have hnot := (Finset.mem_filter.mp hp).2
    simpa only [not_forall, not_imp, exists_prop] using hnot
  obtain ⟨g, hg, havoid⟩ := exists_annihilator_avoiding_factors c S hwitness
  let φ := GCDMonoid.gcd Q g
  have hφQ : φ ∣ Q := gcd_dvd_left Q g
  have hφg : φ ∣ g := gcd_dvd_right Q g
  have hφ : φ ≠ 0 := by
    intro hz
    exact hQ (zero_dvd_iff.mp (hz ▸ hφQ))
  have hφsquare : Squarefree φ := Squarefree.squarefree_of_dvd hφQ hsquare
  have hcommon (f : Laurent K) (hf : laurentAct f c = 0) : φ ∣ f := by
    apply squarefree_dvd_of_prime_factors φ f hφ hφsquare
    intro p hprime hpφ
    have hpQ := hpφ.trans hφQ
    have hpg := hpφ.trans hφg
    obtain ⟨q, hqmem, hpeq⟩ :=
      UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd hQ hprime.irreducible hpQ
    have hqg : q ∣ g := hpeq.symm.dvd.trans hpg
    have hqcommon : ∀ f : Laurent K, laurentAct f c = 0 → q ∣ f := by
      by_contra hnot
      have hqS : q ∈ S := Finset.mem_filter.mpr ⟨Multiset.mem_toFinset.mpr hqmem, hnot⟩
      exact havoid q hqS hqg
    exact hpeq.dvd.trans (hqcommon f hf)
  refine ⟨φ, g, hφ, hg, hφQ, hφg, hcommon, ?_, rfl⟩
  intro d hd
  exact dvd_gcd (hd Q hann) (hd g hg)

-- the two coprime quotients annihilate the actual filtered remainder, as in lemma 2.4.
theorem exists_common_divisor_coprime_quotients {K : Type*} [Field K] [Infinite K]
    (c : Site → K) (Q : Laurent K) (hQ : Q ≠ 0) (hsquare : Squarefree Q)
    (hann : laurentAct Q c = 0) :
    ∃ φ g a b : Laurent K, φ ≠ 0 ∧ laurentAct g c = 0 ∧ Q = φ * a ∧ g = φ * b ∧
      (∀ f : Laurent K, laurentAct f c = 0 → φ ∣ f) ∧ IsRelPrime a b ∧
      laurentAct a (laurentAct φ c) = 0 ∧ laurentAct b (laurentAct φ c) = 0 := by
  obtain ⟨φ, g, hφ, hg, hφQ, hφg, hcommon, _hmax, hgcd⟩ :=
    exists_common_annihilator_divisor c Q hQ hsquare hann
  obtain ⟨a, ha⟩ := hφQ
  obtain ⟨b, hb⟩ := hφg
  have hcop : IsRelPrime a b := by
    intro d hda hdb
    have hdQ : φ * d ∣ Q := ha ▸ mul_dvd_mul_left φ hda
    have hdg : φ * d ∣ g := hb ▸ mul_dvd_mul_left φ hdb
    have hdφ : φ * d ∣ φ := by
      have hd := dvd_gcd hdQ hdg
      rwa [← hgcd] at hd
    have hdunit : d ∣ 1 := (mul_dvd_mul_iff_left hφ).mp (by simpa only [mul_one] using hdφ)
    exact isUnit_of_dvd_one hdunit
  refine ⟨φ, g, a, b, hφ, hg, ha, hb, hcommon, hcop, ?_, ?_⟩
  · rw [← laurentAct_mul, mul_comm, ← ha]
    exact hann
  · rw [← laurentAct_mul, mul_comm, ← hb]
    exact hg

end KumarNivat
