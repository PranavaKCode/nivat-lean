module

public import KumarNivat.OrientedNormals
public import KumarNivat.AnnihilatorDirections

@[expose] public section

namespace KumarNivat

-- a unique minimizing coefficient determines the next outward integer level.
theorem halfplane_zero_step_of_unique_minimum {K : Type*} [CommRing K] [NoZeroDivisors K]
    (c : Site → K) (f : Laurent K) (hann : laurentAct f c = 0)
    (ν : Site →+ ℤ) (v : Site) (hmin : UniqueNormalMinimum f (integerNormalAsReal ν) v)
    (b : ℤ) (hzero : ∀ g : Site, b ≤ ν g → c g = 0) :
    ∀ g : Site, b - 1 ≤ ν g → c g = 0 := by
  classical
  intro g hg
  have heval : laurentAct f c (g - v) = f.coeff v * c g := by
    unfold laurentAct act Finsupp.sum
    have he : (∑ u ∈ f.coeff.support, f.coeff u * c ((g - v) + u)) =
        f.coeff v * c ((g - v) + v) := by
      apply Finset.sum_eq_single v
      · intro u hu huv
        have hstrict := hmin.2 u hu huv
        change (ν v : ℝ) < (ν u : ℝ) at hstrict
        have hgap : ν v < ν u := by exact_mod_cast hstrict
        have hbound : b ≤ ν ((g - v) + u) := by
          rw [map_add, map_sub]
          omega
        rw [hzero _ hbound, mul_zero]
      · intro hn
        exact (hn hmin.1).elim
    simpa only [sub_add_cancel] using he
  have hz := congrFun hann (g - v)
  rw [heval] at hz
  exact (mul_eq_zero.mp hz).resolve_left (Finsupp.mem_support_iff.mp hmin.1)

-- successive integer slabs exhaust the plane, so the actual recurrence extends zero globally.
theorem zero_of_halfplane_unique_minimum {K : Type*} [CommRing K] [NoZeroDivisors K]
    (c : Site → K) (f : Laurent K) (hann : laurentAct f c = 0)
    (ν : Site →+ ℤ) (v : Site) (hmin : UniqueNormalMinimum f (integerNormalAsReal ν) v)
    (b : ℤ) (hzero : ∀ g : Site, b ≤ ν g → c g = 0) : c = 0 := by
  have hband (n : ℕ) : ∀ g : Site, b - (n : ℤ) ≤ ν g → c g = 0 := by
    induction n with
    | zero => simpa only [Nat.cast_zero, sub_zero] using hzero
    | succ n ih =>
      intro g hg
      apply halfplane_zero_step_of_unique_minimum c f hann ν v hmin (b - (n : ℤ)) ih g
      omega
  funext g
  exact hband (b - ν g).toNat g (by omega)

-- a product with no tangent factor has the unique extreme coefficient required for propagation.
theorem zero_of_halfplane_transverse_difference_product {K : Type*} [CommRing K]
    [Nontrivial K] [NoZeroDivisors K] (c : Site → K) (hs : List Site)
    (hann : laurentAct (differenceProduct hs) c = 0) (ν : Site →+ ℤ)
    (htransverse : ∀ h ∈ hs, ν h ≠ 0) (b : ℤ)
    (hzero : ∀ g : Site, b ≤ ν g → c g = 0) : c = 0 := by
  have htransverseR : ∀ h ∈ hs, integerNormalAsReal ν h ≠ 0 := by
    intro h hh
    change (ν h : ℝ) ≠ 0
    exact_mod_cast htransverse h hh
  obtain ⟨v, hv⟩ := differenceProduct_has_unique_normal_minimum (K := K) hs
    (integerNormalAsReal ν) htransverseR
  exact zero_of_halfplane_unique_minimum c (differenceProduct hs) hann ν v hv b hzero

-- two vectors in the kernel of a nonzero planar normal must be parallel.
theorem nonzero_normal_kernel_parallel (ν : Site →+ ℤ) (hν : ν ≠ 0)
    (p q : Site) (hp : ν p = 0) (hq : ν q = 0) : determinant p q = 0 := by
  have hex : ∃ g : Site, ν g ≠ 0 := by
    by_contra hn
    apply hν
    ext g
    by_contra hg
    exact hn ⟨g, hg⟩
  obtain ⟨g, hg⟩ := hex
  have he := normal_cramer_identity ν p q g
  rw [hp, hq, mul_zero, mul_zero, add_zero] at he
  exact (mul_eq_zero.mp he).resolve_right hg

end KumarNivat
