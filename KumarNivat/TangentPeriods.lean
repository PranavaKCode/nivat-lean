module

public import KumarNivat.HalfplaneRecurrence
public import KumarNivat.RegionalBackground
public import KumarNivat.FactorDeletion

@[expose] public section

namespace KumarNivat

-- tangency keeps every forward period step inside the same closed half-plane.
theorem regional_tangent_period_nat_multiple {A : Type*} (c : Site → A)
    (ν : Site →+ ℤ) (b : ℤ) (h : Site) (htangent : ν h = 0)
    (hp : RegionalPeriod c {g | b ≤ ν g} h) (n : ℕ) :
    ∀ g : Site, b ≤ ν g → c (g + (n : ℤ) • h) = c g := by
  have hstable : ∀ g ∈ {g | b ≤ ν g}, g + h ∈ {g | b ≤ ν g} := by
    intro g hg
    change b ≤ ν (g + h)
    rw [map_add, htangent, add_zero]
    exact hg
  intro g hg
  exact (regional_period_forward_multiples c _ h hstable hp n g hg).2

-- lemma 5.3 cancels the sole parallel factor and extends the resulting transverse defect recurrence.
theorem global_period_multiple_of_tangent_regional_period {K : Type*} [CommRing K]
    [Nontrivial K] [NoZeroDivisors K] (c : Site → K) (hs : List Site)
    (hdirs : ∀ h ∈ hs, h ≠ 0) (hpairs : hs.Pairwise (fun p q => determinant p q ≠ 0))
    (hann : laurentAct (differenceProduct hs) c = 0) (ν : Site →+ ℤ) (hν : ν ≠ 0)
    (b : ℤ) (h : Site) (hh : h ≠ 0) (htangent : ν h = 0)
    (hp : RegionalPeriod c {g | b ≤ ν g} h) :
    ∃ n : ℕ, 0 < n ∧ IsPeriod c ((n : ℤ) • h) := by
  classical
  by_cases hex : ∃ p ∈ hs, ν p = 0
  · obtain ⟨p, hpmem, hpnormal⟩ := hex
    have hparallel := nonzero_normal_kernel_parallel ν hν p h hpnormal htangent
    obtain ⟨a, d, ha, hd, hcommon⟩ := parallel_common_integer_multiple p h (hdirs p hpmem) hh hparallel
    let n := (d * d).toNat
    have hpositive : (0 : ℤ) < d * d := mul_self_pos.mpr hd
    have hn : 0 < n := by dsimp [n]; omega
    have hncast : (n : ℤ) = d * d := by dsimp [n]; omega
    let H := (n : ℤ) • h
    have hH : H = (d * a) • p := by
      have he := congrArg (fun v : Site => d • v) hcommon
      simp only [smul_smul] at he
      simpa only [H, hncast] using he.symm
    obtain ⟨rest, _hlength, _hmem, _hpairrest, hprod, hind, _hcover⟩ :=
      differenceProduct_delete_factor (K := K) hs hpairs p hpmem
    let R : Laurent K := differenceProduct rest
    change differenceProduct (K := K) hs = binomial p * R at hprod
    have htransverse : ∀ q ∈ rest, ν q ≠ 0 := by
      intro q hq hz
      exact hind q hq (nonzero_normal_kernel_parallel ν hν p q hpnormal hz)
    have hdiv : (binomial p : Laurent K) ∣ binomial H := by
      rw [hH]
      exact binomial_dvd_integer_multiple p (d * a)
    obtain ⟨A, hA⟩ := hdiv
    have hdefectann : laurentAct R (difference H c) = 0 := by
      rw [← laurentAct_binomial, ← laurentAct_mul]
      have he : R * binomial H = A * differenceProduct hs := by rw [hA, hprod]; ring
      rw [he, laurentAct_mul, hann, laurentAct_config_zero]
    have hdefectzero : difference H c = 0 := zero_of_halfplane_transverse_difference_product
      (difference H c) rest hdefectann ν htransverse b (by
        intro g hg
        exact sub_eq_zero.mpr (regional_tangent_period_nat_multiple c ν b h htangent hp n g hg))
    refine ⟨n, hn, ?_⟩
    intro g
    exact sub_eq_zero.mp (congrFun hdefectzero g)
  · have htransverse : ∀ p ∈ hs, ν p ≠ 0 := by
      intro p hpmem hz
      exact hex ⟨p, hpmem, hz⟩
    have hdefectann : laurentAct (differenceProduct hs) (difference h c) = 0 := by
      rw [← laurentAct_binomial, ← laurentAct_mul, mul_comm, laurentAct_mul, hann, laurentAct_config_zero]
    have hdefectzero : difference h c = 0 := zero_of_halfplane_transverse_difference_product
      (difference h c) hs hdefectann ν htransverse b (by
        intro g hg
        have hnext : b ≤ ν (g + h) := by rw [map_add, htangent, add_zero]; exact hg
        exact sub_eq_zero.mpr (hp g hg hnext))
    have hglobal : IsPeriod c h := fun g => sub_eq_zero.mp (congrFun hdefectzero g)
    exact ⟨1, zero_lt_one, by simpa only [Nat.cast_one, one_smul] using hglobal⟩

-- the resulting multiple is nonzero and remains in the original tangent direction.
theorem global_period_of_tangent_regional_period {K : Type*} [CommRing K]
    [Nontrivial K] [NoZeroDivisors K] (c : Site → K) (hs : List Site)
    (hdirs : ∀ h ∈ hs, h ≠ 0) (hpairs : hs.Pairwise (fun p q => determinant p q ≠ 0))
    (hann : laurentAct (differenceProduct hs) c = 0) (ν : Site →+ ℤ) (hν : ν ≠ 0)
    (b : ℤ) (h : Site) (hh : h ≠ 0) (htangent : ν h = 0)
    (hp : RegionalPeriod c {g | b ≤ ν g} h) :
    ∃ H : Site, H ≠ 0 ∧ determinant h H = 0 ∧ IsPeriod c H := by
  obtain ⟨n, hn, hperiod⟩ := global_period_multiple_of_tangent_regional_period c hs hdirs hpairs
    hann ν hν b h hh htangent hp
  refine ⟨(n : ℤ) • h, smul_ne_zero (by exact_mod_cast Nat.ne_of_gt hn) hh, ?_, hperiod⟩
  simp [determinant]
  ring

end KumarNivat
