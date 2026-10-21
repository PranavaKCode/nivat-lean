module

public import KumarNivat.FactorDeletion
public import KumarNivat.MonomialNewtonTranslation
public import KumarNivat.TangentNewtonEndpoints
public import KumarNivat.TransverseWedgeOperators
public import KumarNivat.HalfplaneRecurrence

@[expose] public section

namespace KumarNivat

-- the original product has an attained tangent edge and an actual higher coefficient site.
theorem actual_newton_tangent_lower_edge {K : Type*} [CommRing K] [Nontrivial K] [NoZeroDivisors K]
    (hs : List Site) (hlen : 2 ≤ hs.length) (hdirs : ∀ h ∈ hs, h ≠ 0)
    (hpairs : hs.Pairwise (fun p q => determinant p q ≠ 0))
    (a : Site) (hprimitive : Int.gcd a.1 a.2 = 1) (p : Site) (hpmem : p ∈ hs)
    (hparallel : determinant a p = 0) :
    ∃ u₀ ∈ (differenceProduct (K := K) hs).coeff.support,
      u₀ + p ∈ (differenceProduct (K := K) hs).coeff.support ∧
      (∀ u ∈ (differenceProduct (K := K) hs).coeff.support,
        directionNormal a u₀ ≤ directionNormal a u) ∧
      ∃ u₁ ∈ (differenceProduct (K := K) hs).coeff.support,
        directionNormal a u₀ < directionNormal a u₁ := by
  have hane : a ≠ 0 := by rintro rfl; simp at hprimitive
  have hν := directionNormal_ne_zero a hane
  let ν := directionNormal a
  obtain ⟨rest, hlength, _hmem, _hpair, hprod, hind, _hcover⟩ :=
    differenceProduct_delete_factor (K := K) hs hpairs p hpmem
  have hrest : rest ≠ [] := by
    intro he
    rw [he] at hlength
    simp only [List.length_nil] at hlength
    omega
  have htransverse : ∀ q ∈ rest, ν q ≠ 0 := by
    intro q hq hn
    exact hind q hq (nonzero_normal_kernel_parallel ν hν p q hparallel hn)
  let ts := rest.map (orientNormalDirection ν)
  have hpos : ∀ q ∈ ts, 0 < ν q := oriented_difference_directions_positive rest ν htransverse
  have hts : ts ≠ [] := by
    intro he
    have hlen' : ts.length = rest.length := by simp [ts]
    rw [he] at hlen'
    exact hrest (List.length_eq_zero_iff.mp hlen'.symm)
  have hwidth := positive_normal_sum ts hts ν hpos
  let f := differenceProduct (K := K) hs
  let Q := (binomial p : Laurent K) * differenceProduct ts
  obtain ⟨v, ε, hε, he⟩ := oriented_difference_product_monomial (K := K) rest ν
  have hQ : Q = AddMonoidAlgebra.single v ε * f := by
    dsimp [Q, f, ts]
    rw [hprod, he]
    ring
  obtain ⟨h0, hp0, hsum, _hpsum, hbounds⟩ := tangent_product_normal_endpoints (K := K)
    p (hdirs p hpmem) ts ν hparallel hpos
  have htransfer (u : Site) (hu : u ∈ Q.coeff.support) : u - v ∈ f.coeff.support := by
    rw [hQ] at hu
    exact (nonzero_monomial_translate_mem_support v ε hε f u).mp hu
  have hforward (u : Site) (hu : u ∈ f.coeff.support) : u + v ∈ Q.coeff.support := by
    rw [hQ]
    apply (nonzero_monomial_translate_mem_support v ε hε f (u + v)).mpr
    simpa only [add_sub_cancel_right] using hu
  refine ⟨0 - v, htransfer 0 h0, ?_, ?_, ts.sum - v, htransfer ts.sum hsum, ?_⟩
  · have he : (0 - v) + p = p - v := by abel
    rw [he]
    exact htransfer p hp0
  · intro u hu
    have hb := (hbounds (u + v) (hforward u hu)).1
    change ν (0 - v) ≤ ν u
    rw [map_sub, map_zero]
    rw [map_add] at hb
    omega
  · change ν (0 - v) < ν (ts.sum - v)
    rw [map_sub, map_zero, map_sub, normal_list_sum]
    omega

end KumarNivat
