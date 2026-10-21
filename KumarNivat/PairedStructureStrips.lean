module

public import KumarNivat.ForwardTransverseDefects
public import KumarNivat.TransverseWedgeOperators
public import KumarNivat.WedgeSlabPropagation

@[expose] public section

namespace KumarNivat

-- two actual normal extremes propagate a full-width zero strip to the entire plane.
theorem zero_of_transverse_difference_product_slab {K : Type*} [CommRing K]
    [Nontrivial K] [NoZeroDivisors K] (δ : Site → K) (hs : List Site)
    (hne : hs ≠ []) (ν : Site →+ ℤ) (htransverse : ∀ h ∈ hs, ν h ≠ 0)
    (hann : laurentAct (differenceProduct hs) δ = 0) :
    ∃ d : ℕ, 0 < d ∧ ∀ top : ℤ,
      (∀ g : Site, top - (d : ℤ) + 1 ≤ ν g → ν g ≤ top → δ g = 0) → δ = 0 := by
  let ts := hs.map (orientNormalDirection ν)
  have hpos : ∀ h ∈ ts, 0 < ν h := oriented_difference_directions_positive hs ν htransverse
  have htsne : ts ≠ [] := by
    intro hz
    obtain ⟨h, tail, he⟩ := List.exists_cons_of_ne_nil hne
    dsimp [ts] at hz
    rw [he, List.map_cons] at hz
    simp at hz
  have hsumpos := positive_normal_sum ts htsne ν hpos
  let d := (ts.map ν).sum.toNat
  have hd : 0 < d := by dsimp [d]; omega
  have hwidth : (ts.map ν).sum = (d : ℤ) := by dsimp [d]; omega
  have hends := positive_difference_product_endpoint_data (K := K) ts ν hpos
  have hbounds := positive_difference_product_support_bounds (K := K) ts ν 0 hpos
    (fun _ _ => le_rfl)
  have hann' : laurentAct (differenceProduct ts) δ = 0 :=
    oriented_difference_product_annihilates δ hs ν hann
  have hsteps : ∀ u ∈ (differenceProduct (K := K) ts).coeff.support, u ≠ 0 →
      1 ≤ ν u ∧ ν u ≤ (d : ℤ) := by
    intro u hu hune
    have hstrict := hends.1.2 u hu hune
    change (ν 0 : ℝ) < (ν u : ℝ) at hstrict
    rw [map_zero, Int.cast_zero] at hstrict
    have hu₀ : 0 < ν u := by exact_mod_cast hstrict
    have hu₁ := (hbounds u hu).2.1
    rw [hwidth] at hu₁
    exact ⟨by omega, hu₁⟩
  refine ⟨d, hd, ?_⟩
  intro top hseed
  have hlower : ∀ g : Site, ν g ≤ top → δ g = 0 := by
    intro g hg
    exact zero_on_wedge_of_initial_slab δ (differenceProduct ts) hann'
      (Finsupp.mem_support_iff.mp hends.1.1) ν 0 d hsteps (fun _ _ => le_rfl) top 0
      (fun u hlo hhi _ => hseed u hlo hhi) g hg le_rfl
  exact zero_of_halfplane_unique_minimum δ (differenceProduct ts) hann' (-ν) ts.sum hends.2
    (-top) (fun g hg => hlower g (by change -top ≤ -ν g at hg; omega))

-- full-strip agreement with a matching directional reference would force a global period of the same array.
theorem no_full_strip_agreement_with_directional_reference {K : Type*} [CommRing K]
    [Nontrivial K] [NoZeroDivisors K] (z w : Site → K) (hs : List Site)
    (hlen : 2 ≤ hs.length) (hdirs : ∀ p ∈ hs, p ≠ 0)
    (hpairs : hs.Pairwise (fun p q => determinant p q ≠ 0))
    (hann : laurentAct (differenceProduct hs) z = 0)
    (hnot : ¬ ∃ h : Site, h ≠ 0 ∧ IsPeriod z h)
    (a : Site) (hprimitive : Int.gcd a.1 a.2 = 1) (p : Site) (hpmem : p ∈ hs)
    (hparallel : determinant a p = 0) (l : ℕ) (hl : 0 < l)
    (hw : IsPeriod w ((l : ℤ) • a)) :
    ∃ d : ℕ, 0 < d ∧ ∀ top : ℤ,
      ¬ ∀ g : Site, top - (d : ℤ) + 1 ≤ directionNormal a g →
        directionNormal a g ≤ top → z g = w g := by
  obtain ⟨N, hN, hwN, rest, hrest, _hpairs, hmem, hδann, _hcover, _hprod⟩ :=
    forward_transverse_defect_data z w hs hlen hdirs hpairs hann
      a hprimitive p hpmem hparallel l hl hw
  obtain ⟨d, hd, hzero⟩ := zero_of_transverse_difference_product_slab
    (difference ((N : ℤ) • a) z) rest hrest (directionNormal a)
      (fun q hq => (hmem q hq).2.2) hδann
  refine ⟨d, hd, ?_⟩
  intro top hagree
  let R : Set Site := {g | top - (d : ℤ) + 1 ≤ directionNormal a g ∧ directionNormal a g ≤ top}
  have hstable : ∀ g ∈ R, g + a ∈ R := by
    intro g hg
    simpa only [R, Set.mem_ofPred_eq, map_add, directionNormal_self, add_zero] using hg
  have hδzero := forward_difference_zero_on_agreement_region z w R a hstable N hwN
    (fun g hg => hagree g hg.1 hg.2)
  have hglobal := hzero top (fun g hlo hhi => hδzero g ⟨hlo, hhi⟩)
  have hane : a ≠ 0 := by rintro rfl; simp at hprimitive
  apply hnot
  refine ⟨(N : ℤ) • a, smul_ne_zero (by exact_mod_cast Nat.ne_of_gt hN) hane, ?_⟩
  intro g
  exact sub_eq_zero.mp (congrFun hglobal g)

end KumarNivat
