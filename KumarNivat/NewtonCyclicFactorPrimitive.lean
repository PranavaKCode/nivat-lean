module

public import KumarNivat.NewtonCyclicFactorSort
public import KumarNivat.PrimitiveDirections
public import KumarNivat.OrientedNormals
public import Mathlib.Data.List.OfFn

@[expose] public section

namespace KumarNivat

-- removing a positive integer coordinate gcd preserves the selected upper semicircle.
theorem upper_factor_half_of_positive_multiple (p : Site) (m : ℤ) (hm : 0 < m)
    (hupper : InUpperFactorHalf (m • p)) : InUpperFactorHalf p := by
  change 0 < m * p.2 ∨ m * p.2 = 0 ∧ 0 < m * p.1 at hupper
  rcases hupper with hy | ⟨hy, hx⟩
  · left
    by_contra hn
    exact not_le_of_gt hy (mul_nonpos_of_nonneg_of_nonpos (le_of_lt hm) (le_of_not_gt hn))
  · right
    refine ⟨(mul_eq_zero.mp hy).resolve_left (ne_of_gt hm), ?_⟩
    by_contra hn
    exact not_le_of_gt hx (mul_nonpos_of_nonneg_of_nonpos (le_of_lt hm) (le_of_not_gt hn))

-- actual sorted factors provide primitive ordered half-fan directions and their positive integer edge lengths.
theorem actual_sorted_primitive_factor_data (hs : List Site) (hlen : 2 ≤ hs.length)
    (hdirs : ∀ h ∈ hs, h ≠ 0) (hpairs : hs.Pairwise (fun p q => determinant p q ≠ 0)) :
    ∃ q : ℕ, q = hs.length ∧ 2 ≤ q ∧
      ∃ f e : Fin q → Site, ∃ k : Fin q → ℕ,
        List.ofFn f = upperSortedFactors hs ∧
        (∀ i, 0 < k i ∧ f i = (k i : ℤ) • e i ∧ Int.gcd (e i).1 (e i).2 = 1 ∧ InUpperFactorHalf (e i)) ∧
        (∀ i j : Fin q, i < j → 0 < determinant (e i) (e j)) ∧
        ∀ i, ∃ g ∈ hs, f i = g ∨ f i = -g := by
  classical
  obtain ⟨_hperm, hlength, hupper, hstrict, hsource⟩ := upperSortedFactors_actual_data hs hdirs hpairs
  let ts := upperSortedFactors hs
  let q := ts.length
  let f : Fin q → Site := fun i => ts.get i
  have hqeq : q = hs.length := hlength
  have hq : 2 ≤ q := by rw [hqeq]; exact hlen
  have hfupper (i : Fin q) : InUpperFactorHalf (f i) := hupper _ (List.get_mem _ _)
  have hfne (i : Fin q) : f i ≠ 0 := by
    intro he
    have h := hfupper i
    simp [he, InUpperFactorHalf] at h
  have hprimitive (i : Fin q) := exists_primitive_direction_coordinate (f i) (hfne i)
  choose e k hk hrep _hne τ hτ _hker using hprimitive
  have hpos (i : Fin q) : (0 : ℤ) < k i := by exact_mod_cast hk i
  have heupper (i : Fin q) : InUpperFactorHalf (e i) :=
    upper_factor_half_of_positive_multiple (e i) (k i : ℤ) (hpos i) (hrep i ▸ hfupper i)
  have hestrict : ∀ i j : Fin q, i < j → 0 < determinant (e i) (e j) := by
    intro i j hij
    have hfdet : 0 < determinant (f i) (f j) := hstrict.rel_get_of_lt hij
    have he := determinant_zsmul (e i) (e j) (k i : ℤ) (k j : ℤ)
    rw [← hrep i, ← hrep j] at he
    by_contra hn
    have hnonpos := mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (le_of_lt (hpos i)) (le_of_lt (hpos j))) (le_of_not_gt hn)
    rw [← he] at hnonpos
    exact not_le_of_gt hfdet hnonpos
  refine ⟨q, hqeq, hq, f, e, k, ?_, ?_, hestrict, ?_⟩
  · exact List.ofFn_get ts
  · intro i
    exact ⟨hk i, hrep i, primitive_gcd_of_line_coordinate (e i) (τ i) (hτ i), heupper i⟩
  · intro i
    exact hsource _ (List.get_mem _ _)

end KumarNivat
