module

public import Mathlib.GroupTheory.MonoidLocalization.UniqueFactorization

@[expose] public section

namespace KumarNivat

-- a prime not inverted by localization still detects divisibility in the original monoid.
theorem localization_prime_dvd_reflects {M N : Type*}
    [CommMonoidWithZero M] [CommMonoidWithZero N] [IsCancelMulZero M] [IsCancelMulZero N]
    {S : Submonoid M} (f : S.LocalizationMap N) (p a : M) (hp : Prime p)
    (hunit : ¬ IsUnit (f p)) (hdvd : f p ∣ f a) : p ∣ a := by
  obtain ⟨s, hs, hdiv⟩ := f.map_dvd_map.mp hdvd
  rcases hp.dvd_or_dvd hdiv with hps | hpa
  · exact (hunit (isUnit_of_dvd_unit (map_dvd f hps) (f.map_units ⟨s, hs⟩))).elim
  · exact hpa

-- lift a possible common prime from the localization before using the original coprimality.
theorem localization_preserves_relPrime {M N : Type*}
    [CommMonoidWithZero M] [CommMonoidWithZero N]
    [UniqueFactorizationMonoid M] [UniqueFactorizationMonoid N]
    {S : Submonoid M} (f : S.LocalizationMap N) (hinj : Function.Injective f)
    (a b : M) (ha : a ≠ 0) (hcop : IsRelPrime a b) : IsRelPrime (f a) (f b) := by
  intro d hda hdb
  by_contra hnot
  have hfa : f a ≠ 0 := by
    intro hz
    apply ha
    apply hinj
    simpa only [map_zero] using hz
  have hd : d ≠ 0 := ne_zero_of_dvd_ne_zero hfa hda
  obtain ⟨p, hp, hpd⟩ := WfDvdMonoid.exists_irreducible_factor hnot hd
  obtain ⟨⟨m, s⟩, hm⟩ := f.surj p
  have hmI : Irreducible (f m) := by
    rw [← hm, irreducible_mul_iff]
    exact Or.inl ⟨hp, f.map_units s⟩
  obtain ⟨u, q, hu, hq, hmq⟩ := f.eq_isUnit_map_mul_irreducible_of_irreducible_map hmI
  have hfqI : Irreducible (f q) := by
    rw [hmq, map_mul, irreducible_mul_iff] at hmI
    rcases hmI with hleft | hright
    · exact (hleft.1.not_isUnit hu).elim
    · exact hright.1
  have hq_m : q ∣ m := by rw [hmq]; exact dvd_mul_left _ _
  have hqp : f q ∣ p := by
    have he := map_dvd f hq_m
    rw [← hm] at he
    exact (f.map_units s).dvd_mul_right.mp he
  have hqa : q ∣ a := localization_prime_dvd_reflects f q a
    (UniqueFactorizationMonoid.irreducible_iff_prime.mp hq) hfqI.not_isUnit
    (hqp.trans (hpd.trans hda))
  have hqb : q ∣ b := localization_prime_dvd_reflects f q b
    (UniqueFactorizationMonoid.irreducible_iff_prime.mp hq) hfqI.not_isUnit
    (hqp.trans (hpd.trans hdb))
  exact hq.not_isUnit (hcop hqa hqb)

end KumarNivat
