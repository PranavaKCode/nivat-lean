import KumarNivat.OrientedDifferenceProducts
import KumarNivat.PositiveProductSupport
import KumarNivat.ExtremalSlopeFactors
import Mathlib.Algebra.Order.BigOperators.Group.List

namespace KumarNivat

-- a lattice normal commutes with the actual finite sum of its factor vectors.
theorem normal_list_sum (ν : Site →+ ℤ) (hs : List Site) : ν hs.sum = (hs.map ν).sum := by
  induction hs with
  | nil => simp
  | cons h hs ih => simp only [List.sum_cons, List.map_cons, map_add, ih]

-- a nonempty list of positive integer factor heights has positive total width.
theorem positive_normal_sum (hs : List Site) (hne : hs ≠ []) (ν : Site →+ ℤ)
    (hν : ∀ h ∈ hs, 0 < ν h) : 0 < (hs.map ν).sum := by
  obtain ⟨h, tail, he⟩ := List.exists_cons_of_ne_nil hne
  have hh : 0 < ν h := hν h (by rw [he]; exact List.mem_cons_self)
  have htail : 0 ≤ (tail.map ν).sum := List.sum_nonneg (fun x hx => by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
    exact le_of_lt (hν q (by rw [he]; exact List.mem_cons_of_mem h hq)))
  rw [he, List.map_cons, List.sum_cons]
  omega

-- the original unoriented factor lines cannot enter the open wedge bounded by the extremal slope.
theorem no_original_factor_in_open_wedge (hs : List Site) (ν μ : Site →+ ℤ)
    (hμ : ∀ h ∈ hs.map (orientNormalDirection ν), 0 ≤ μ h) :
    ∀ h ∈ hs, (¬ (ν h < 0 ∧ 0 < μ h)) ∧ (¬ (ν (-h) < 0 ∧ 0 < μ (-h))) := by
  intro h hh
  have hsl := hμ (orientNormalDirection ν h) (List.mem_map.mpr ⟨h, hh, rfl⟩)
  by_cases hpos : 0 < ν h
  · simp only [orientNormalDirection, ite_eq_left hpos] at hsl
    constructor
    · rintro ⟨hneg, _hm⟩
      omega
    · rintro ⟨_hneg, hm⟩
      rw [map_neg] at hm
      omega
  · simp only [orientNormalDirection, ite_eq_right hpos, map_neg] at hsl
    constructor
    · rintro ⟨_hneg, hm⟩
      omega
    · rintro ⟨hneg, _hm⟩
      rw [map_neg] at hneg
      omega

-- the actual transverse product supplies the nonzero coefficients, bounded steps, and adjacent primitive ray used by the wedge recurrence.
theorem actual_transverse_wedge_operator_data {K : Type*} [CommRing K] [Nontrivial K] [NoZeroDivisors K]
    (δ : Site → K) (hs : List Site) (hne : hs ≠ []) (ν τ : Site →+ ℤ)
    (htransverse : ∀ h ∈ hs, ν h ≠ 0) (hann : laurentAct (differenceProduct hs) δ = 0)
    (a : Site) (hτa : τ a = 1) (hνa : ν a = 0) :
    ∃ ts : List Site, ts = hs.map (orientNormalDirection ν) ∧
      ∃ d : ℕ, ∃ p b : Site, ∃ k : ℕ, 0 < d ∧ p ∈ ts ∧ 0 < k ∧ p = (k : ℤ) • (-b) ∧
        Int.gcd b.1 b.2 = 1 ∧ ν b < 0 ∧ slopingNormal ν τ p b = 0 ∧ 0 < slopingNormal ν τ p a ∧
        laurentAct (differenceProduct ts) δ = 0 ∧
        (differenceProduct (K := K) ts).coeff 0 ≠ 0 ∧
        (differenceProduct (K := K) ts).coeff ts.sum ≠ 0 ∧ ν ts.sum = (d : ℤ) ∧
        (∀ u ∈ (differenceProduct (K := K) ts).coeff.support, u ≠ 0 → 1 ≤ ν u ∧ ν u ≤ (d : ℤ)) ∧
        (∀ u ∈ (differenceProduct (K := K) ts).coeff.support, 0 ≤ slopingNormal ν τ p u) ∧
        ∀ h ∈ hs, (¬ (ν h < 0 ∧ 0 < slopingNormal ν τ p h)) ∧
          (¬ (ν (-h) < 0 ∧ 0 < slopingNormal ν τ p (-h))) := by
  let ts := hs.map (orientNormalDirection ν)
  have htsne : ts ≠ [] := by
    intro heq
    obtain ⟨h, tail, hh⟩ := List.exists_cons_of_ne_nil hne
    dsimp [ts] at heq
    rw [hh, List.map_cons] at heq
    simp at heq
  have hpos := oriented_difference_directions_positive hs ν htransverse
  obtain ⟨p, hpmem, b, k, hk, hrep, hprimitive, hbν, hbμ, haμ, hslopes⟩ :=
    exists_extremal_primitive_boundary ts htsne ν τ hpos a hτa hνa
  let d := (ts.map ν).sum.toNat
  have hsumpos := positive_normal_sum ts htsne ν hpos
  have hd : 0 < d := by dsimp [d]; omega
  have hdcast : (d : ℤ) = (ts.map ν).sum := by dsimp [d]; omega
  have hends := positive_difference_product_endpoint_data (K := K) ts ν hpos
  have hbounds := positive_difference_product_support_bounds (K := K) ts ν (slopingNormal ν τ p) hpos hslopes
  refine ⟨ts, rfl, d, p, b, k, hd, hpmem, hk, hrep, hprimitive, hbν, hbμ, haμ,
    oriented_difference_product_annihilates δ hs ν hann,
    Finsupp.mem_support_iff.mp hends.1.1, Finsupp.mem_support_iff.mp hends.2.1, ?_, ?_, ?_, ?_⟩
  · rw [normal_list_sum, hdcast]
  · intro u hu hune
    have hstrict := hends.1.2 u hu hune
    change (ν 0 : ℝ) < (ν u : ℝ) at hstrict
    rw [map_zero, Int.cast_zero] at hstrict
    have hupos : 0 < ν u := by exact_mod_cast hstrict
    have hupper := (hbounds u hu).2.1
    rw [← hdcast] at hupper
    exact ⟨by omega, hupper⟩
  · intro u hu
    exact (hbounds u hu).2.2
  · exact no_original_factor_in_open_wedge hs ν (slopingNormal ν τ p) hslopes

end KumarNivat
