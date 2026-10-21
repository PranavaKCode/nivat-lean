module

public import KumarNivat.PairedStructureFiberLocal
public import KumarNivat.FactorDeletion
public import KumarNivat.BoundaryLineRecurrences

@[expose] public section

namespace KumarNivat

-- the deleted product annihilates the same binomial output at every selected orbit point.
theorem deleted_product_annihilates_binomial_output {K : Type*} [CommRing K]
    [TopologicalSpace K] [DiscreteTopology K] (c x : Site → K)
    (hx : x ∈ orbitClosure c) (hs rest : List Site) (p : Site)
    (hprod : differenceProduct (K := K) hs = binomial p * differenceProduct rest)
    (hann : laurentAct (differenceProduct hs) c = 0) :
    laurentAct (differenceProduct rest) (difference p x) = 0 := by
  have hxann : laurentAct (differenceProduct hs) x = 0 := by
    funext g
    exact annihilator_inherited_of_language x c (languageContained_of_mem_orbitClosure c x hx)
      (differenceProduct hs).coeff (fun t => congrFun hann t) g
  rw [← laurentAct_binomial, ← laurentAct_mul, mul_comm, ← hprod]
  exact hxann

-- opposite half-plane agreement forces equal filter outputs because every remaining factor is transverse.
theorem binomial_outputs_equal_of_opposite_halfplane {K : Type*} [CommRing K]
    [Nontrivial K] [NoZeroDivisors K] [TopologicalSpace K] [DiscreteTopology K]
    (c x y : Site → K) (hx : x ∈ orbitClosure c) (hy : y ∈ orbitClosure c)
    (hs : List Site) (hpairs : hs.Pairwise (fun p q => determinant p q ≠ 0))
    (hann : laurentAct (differenceProduct hs) c = 0) (p : Site) (hpmem : p ∈ hs)
    (ν : Site →+ ℤ) (hν : ν ≠ 0) (hp : ν p = 0) (b : ℤ)
    (hagree : ∀ g : Site, ν g ≤ b → x g = y g) : difference p x = difference p y := by
  obtain ⟨rest, _hlen, _hmem, _hpairs, hprod, hind, _hcover⟩ :=
    differenceProduct_delete_factor (K := K) hs hpairs p hpmem
  have hxann := deleted_product_annihilates_binomial_output c x hx hs rest p hprod hann
  have hyann := deleted_product_annihilates_binomial_output c y hy hs rest p hprod hann
  let δ := difference p x - difference p y
  have hδann : laurentAct (differenceProduct rest) δ = 0 := by
    rw [laurentAct_config_sub, hxann, hyann, sub_self]
  have htransverse : ∀ q ∈ rest, (-ν) q ≠ 0 := by
    intro q hq hz
    change -ν q = 0 at hz
    have hq₀ : ν q = 0 := neg_eq_zero.mp hz
    exact hind q hq (nonzero_normal_kernel_parallel ν hν p q hp hq₀)
  have hzero : δ = 0 := zero_of_halfplane_transverse_difference_product δ rest hδann
    (-ν) htransverse (-b) (by
      intro g hg
      have hfit : ν g ≤ b := by change -b ≤ -ν g at hg; omega
      have hnext : ν (g + p) ≤ b := by rw [map_add, hp, add_zero]; exact hfit
      change (x (g + p) - x g) - (y (g + p) - y g) = 0
      rw [hagree (g + p) hnext, hagree g hfit, sub_self])
  exact sub_eq_zero.mp hzero

end KumarNivat
