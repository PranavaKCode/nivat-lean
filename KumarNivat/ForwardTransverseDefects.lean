module

public import KumarNivat.FactorDeletion
public import KumarNivat.HalfplaneRecurrence
public import KumarNivat.PrimitiveDirections
public import KumarNivat.StableRegions

@[expose] public section

namespace KumarNivat

-- a positive multiple of the reference period cancels the sole parallel factor and leaves a nonempty transverse product.
theorem forward_transverse_defect_data {K : Type*} [CommRing K] (z w : Site → K)
    (hs : List Site) (hlen : 2 ≤ hs.length) (hdirs : ∀ p ∈ hs, p ≠ 0)
    (hpairs : hs.Pairwise (fun p q => determinant p q ≠ 0))
    (hann : laurentAct (differenceProduct hs) z = 0)
    (a : Site) (hprimitive : Int.gcd a.1 a.2 = 1) (p : Site) (hpmem : p ∈ hs)
    (hparallel : determinant a p = 0) (l : ℕ) (hl : 0 < l) (hw : IsPeriod w ((l : ℤ) • a)) :
    ∃ N : ℕ, 0 < N ∧ IsPeriod w ((N : ℤ) • a) ∧
      ∃ rest : List Site, rest ≠ [] ∧ rest.Pairwise (fun p q => determinant p q ≠ 0) ∧
        (∀ q ∈ rest, q ∈ hs ∧ q ≠ 0 ∧ directionNormal a q ≠ 0) ∧
        laurentAct (differenceProduct rest) (difference ((N : ℤ) • a) z) = 0 ∧
        (∀ q ∈ hs, q = p ∨ q ∈ rest) ∧ differenceProduct (K := K) hs = binomial p * differenceProduct rest := by
  have hane : a ≠ 0 := by rintro rfl; simp at hprimitive
  have hν := directionNormal_ne_zero a hane
  let h := (l : ℤ) • a
  have hh : h ≠ 0 := smul_ne_zero (by exact_mod_cast Nat.ne_of_gt hl) hane
  have hph : determinant p h = 0 := by
    have hpa : determinant p a = -determinant a p := by simp [determinant]; ring
    have he := determinant_zsmul p a 1 (l : ℤ)
    simpa only [one_smul, one_mul, hpa, hparallel, neg_zero, mul_zero] using he
  obtain ⟨A, d, _hA, hd, hcommon⟩ := parallel_common_integer_multiple p h (hdirs p hpmem) hh hph
  let n := (d * d).toNat
  have hn : 0 < n := by have hp := mul_self_pos.mpr hd; dsimp [n]; omega
  have hncast : (n : ℤ) = d * d := by have hp := mul_self_pos.mpr hd; dsimp [n]; omega
  have hH : (n : ℤ) • h = (d * A) • p := by
    have he := congrArg (fun v : Site => d • v) hcommon
    simp only [smul_smul] at he
    simpa only [hncast] using he.symm
  obtain ⟨rest, hlength, hmem, hpairrest, hprod, hind, hcover⟩ :=
    differenceProduct_delete_factor (K := K) hs hpairs p hpmem
  have hrest : rest ≠ [] := by intro he; rw [he] at hlength; simp only [List.length_nil] at hlength; omega
  have hannrest : laurentAct (differenceProduct rest) (difference ((n : ℤ) • h) z) = 0 := by
    rw [hH]
    apply difference_annihilator_of_binomial_factor
    rwa [← hprod]
  refine ⟨n * l, Nat.mul_pos hn hl, ?_, rest, hrest, hpairrest, ?_, ?_, hcover, hprod⟩
  · simpa only [Nat.cast_mul, smul_smul] using hw.zsmul (n : ℤ)
  · intro q hq
    refine ⟨hmem q hq, hdirs q (hmem q hq), ?_⟩
    intro hqzero
    exact hind q hq (nonzero_normal_kernel_parallel (directionNormal a) hν p q hparallel hqzero)
  · simpa only [h, Nat.cast_mul, smul_smul] using hannrest

-- agreement with the periodic reference kills that forward difference on the same forward-stable working region.
theorem forward_difference_zero_on_agreement_region {K : Type*} [CommRing K] (z w : Site → K)
    (R : Set Site) (a : Site) (hstable : ∀ g ∈ R, g + a ∈ R) (N : ℕ)
    (hw : IsPeriod w ((N : ℤ) • a)) (hagree : ∀ g ∈ R, z g = w g) :
    ∀ g ∈ R, difference ((N : ℤ) • a) z g = 0 := by
  intro g hg
  have hnext := forward_stable_nat_multiples R a hstable N g hg
  change z (g + (N : ℤ) • a) - z g = 0
  rw [hagree _ hnext, hagree g hg, hw g, sub_self]

end KumarNivat
