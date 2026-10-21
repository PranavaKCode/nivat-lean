module

public import KumarNivat.PairedStructureRayChainRegions
public import KumarNivat.PairedStructureRayChainSlopes
public import KumarNivat.SquarefreeProducts

@[expose] public section

namespace KumarNivat

open scoped Pointwise

-- the actual initial wedge packet constructs its adjacent factor-ray chain and locates the first failed period.
theorem first_failed_matching_factor_ray_chain {K : Type*}
    [CommRing K] [Nontrivial K] [NoZeroDivisors K]
    (x : Site → K) (hs : List Site) (hlen : 2 ≤ hs.length)
    (hdirs : ∀ r ∈ hs, r ≠ 0) (hpairs : hs.Pairwise (fun r s => determinant r s ≠ 0))
    (hann : laurentAct (differenceProduct hs) x = 0)
    (hnot : ¬ ∃ v : Site, v ≠ 0 ∧ IsPeriod x v)
    (a b G : Site) (ha : Int.gcd a.1 a.2 = 1) (hb : Int.gcd b.1 b.2 = 1)
    (hdet : 0 < determinant a b) (μ : Site →+ ℤ) (hμb : μ b = 0) (hμa : 0 < μ a)
    (pa pb : Site) (hpa : pa ∈ hs) (hpb : pb ∈ hs)
    (haparallel : determinant a pa = 0) (hbparallel : determinant b pb = 0)
    (hbetween : ∀ g ∈ hs, (¬ ((-directionNormal a) g < 0 ∧ 0 < μ g)) ∧
      (¬ ((-directionNormal a) (-g) < 0 ∧ 0 < μ (-g))))
    (p : ℕ) (hp : 0 < p)
    (hstart : RegionalPeriod x {g | latticeEmbedding g ∈ latticeHull (differenceProduct (K := K) hs).coeff.support +
      (lineRay (latticeEmbedding G) (latticeEmbedding a) 0 + lineRay 0 (latticeEmbedding b) 0)} ((p : ℤ) • a)) :
    ∃ q : ℕ, ∃ hq : 2 ≤ q,
      let _ : NeZero q := ⟨by omega⟩
      q = hs.length ∧ ∃ e : ZMod (2 * q) → Site, ∃ k : ℕ,
        AnchoredChainFanOrder e ∧ e 0 = a ∧ e 1 = b ∧ 0 < k ∧ k < q ∧
        (∀ i, Int.gcd (e i).1 (e i).2 = 1) ∧
        (∀ i, ∃ g ∈ hs, determinant (e i) g = 0) ∧
        (∀ r : ℕ, 0 < r → r ≤ k → RegionalPeriod x
          {g | latticeEmbedding g ∈ forwardFactorNewtonRegion (differenceProduct (K := K) hs).coeff.support G e r}
            ((p : ℤ) • a)) ∧
        (¬ RegionalPeriod x
          {g | latticeEmbedding g ∈ forwardFactorNewtonRegion (differenceProduct (K := K) hs).coeff.support G e (k + 1)}
            ((p : ℤ) • a)) ∧
        0 < (-directionNormal (e (k : ZMod (2 * q)))) a ∧
        (-directionNormal (e (k : ZMod (2 * q)))) (e (k : ZMod (2 * q))) = 0 ∧
        (∀ i : ℕ, k < i → i < q →
          0 < (-directionNormal (e (i : ZMod (2 * q)))) a ∧
          0 < (-directionNormal (e (i : ZMod (2 * q)))) (e (k : ZMod (2 * q)))) := by
  classical
  obtain ⟨q, hq, hqeq, e, j, hfan, he₀, hj₀, hjq, hej, hprimitive, hsource, _hcover⟩ :=
    actual_forward_factor_fan hs hlen hdirs hpairs a b ha hb hdet pa pb hpa hpb haparallel hbparallel
  let _ : NeZero q := ⟨by omega⟩
  have hj : j = 1 := initial_factor_ray_is_adjacent hs hdirs e hfan hprimitive hsource j hj₀ hjq μ
    (by rwa [hej]) (by rwa [he₀]) (by simpa only [he₀] using hbetween)
  have he₁ : e 1 = b := by simpa only [hj, Nat.cast_one] using hej
  have hS : (differenceProduct (K := K) hs).coeff.support.Nonempty := Finsupp.support_nonempty_iff.mpr
    (fun hz => differenceProduct_ne_zero hs hdirs (AddMonoidAlgebra.coeff_injective hz))
  have hstart' : RegionalPeriod x
      {g | latticeEmbedding g ∈ forwardFactorNewtonRegion (differenceProduct (K := K) hs).coeff.support G e 1}
        ((p : ℤ) • e 0) := by
    simpa only [forward_factor_newton_region_eq_two_rays _ _ _ 1 (by omega : 1 < q),
      Nat.cast_one, he₀, he₁] using hstart
  obtain ⟨k, hk₀, hkq, hgood, hfail⟩ := first_failed_actual_factor_ray_region x hs hdirs hpairs hann hnot
    (differenceProduct (K := K) hs).coeff.support hS G e hfan hq (hprimitive 0) 1 (by omega) (by omega) p hp hstart'
  obtain ⟨_hdetk, hηa, hηb, hslopes⟩ := forward_factor_ray_chain_slopes e hfan k (by omega) hkq
  refine ⟨q, hq, hqeq, e, k, hfan, he₀, he₁, by omega, hkq, hprimitive, hsource, ?_, ?_, ?_, hηb, ?_⟩
  · intro r hr₀ hrk
    simpa only [he₀] using hgood r (by omega) hrk
  · simpa only [he₀] using hfail
  · simpa only [he₀] using hηa
  · intro i hki hiq
    simpa only [he₀] using hslopes i hki hiq

end KumarNivat
