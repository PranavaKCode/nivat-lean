module

public import KumarNivat.ForwardTransverseDefects
public import KumarNivat.NewtonHalfStripBases
public import KumarNivat.NewtonWedgePlacement
public import KumarNivat.SlopedHalfStripPropagation

@[expose] public section

namespace KumarNivat

open scoped Pointwise

-- the actual newton minkowski base and matching periodic half-strip construct the manuscript's initial adjacent-ray period.
theorem initial_wedge_from_newton_half_strip {K : Type*} [CommRing K] [Nontrivial K] [NoZeroDivisors K]
    (z w : Site → K) (hs : List Site) (hlen : 2 ≤ hs.length) (hdirs : ∀ p ∈ hs, p ≠ 0)
    (hpairs : hs.Pairwise (fun p q => determinant p q ≠ 0))
    (hann : laurentAct (differenceProduct hs) z = 0)
    (a : Site) (hprimitive : Int.gcd a.1 a.2 = 1) (p : Site) (hpmem : p ∈ hs)
    (hparallel : determinant a p = 0) (l : ℕ) (hl : 0 < l) (hw : IsPeriod w ((l : ℤ) • a))
    (F : Finset Site) (hF : LatticeConvex F) (C₀ : Set RealPlane) (hC₀ : C₀.Nonempty)
    (hbase : latticeHull F = latticeHull (differenceProduct (K := K) hs).coeff.support + C₀)
    (hagree : ∀ g : Site, latticeEmbedding g ∈ latticeHull F + lineRay 0 (latticeEmbedding a) 0 → z g = w g) :
    ∃ N : ℕ, ∃ b : Site, ∃ μ : Site →+ ℤ, ∃ E : Site,
      0 < N ∧ Int.gcd b.1 b.2 = 1 ∧ 0 < determinant a b ∧ μ b = 0 ∧ 0 < μ a ∧
      (∃ q ∈ hs, determinant b q = 0) ∧
      (∀ q ∈ hs, (¬ ((-directionNormal a) q < 0 ∧ 0 < μ q)) ∧
        (¬ ((-directionNormal a) (-q) < 0 ∧ 0 < μ (-q)))) ∧
      RegionalPeriod z {g | latticeEmbedding g ∈ latticeHull (differenceProduct (K := K) hs).coeff.support +
        (lineRay (latticeEmbedding E) (latticeEmbedding a) 0 + lineRay 0 (latticeEmbedding b) 0)}
        ((N : ℤ) • a) := by
  obtain ⟨N, hN, hwN, rest, hrest, _hpairrest, hrestmem, hδann, hcover, hprod⟩ :=
    forward_transverse_defect_data z w hs hlen hdirs hpairs hann a hprimitive p hpmem hparallel l hl hw
  obtain ⟨τ, hτ, hker⟩ := primitive_direction_coordinate a hprimitive
  let ν := -directionNormal a
  let δ := difference ((N : ℤ) • a) z
  have htransverse : ∀ q ∈ rest, ν q ≠ 0 := fun q hq => neg_ne_zero.mpr (hrestmem q hq).2.2
  have haν : ν a = 0 := by simp [ν, directionNormal, determinant, mul_comm]
  obtain ⟨ts, hts, d, q, b, k, hd, hq, _hk, hrep, hbprimitive, hbν, hbμ, haμ, hannδ,
    hconst, _hlast, hwidth, hsteps, hslope, hbetween⟩ :=
    actual_transverse_wedge_operator_data δ rest hrest ν τ htransverse hδann a hτ haν
  have hpos : ∀ q ∈ ts, 0 < ν q := by
    rw [hts]
    exact oriented_difference_directions_positive rest ν htransverse
  obtain ⟨C₁, hsegment, u₀, hu₀, u₁, hu₁, hZwidth⟩ := tangent_difference_product_newton_data
    (K := K) a hprimitive τ hker p (hdirs p hpmem) hparallel rest htransverse
  rw [← hprod] at hsegment hu₀ hu₁
  have hD : (ts.map ν).sum = (d : ℤ) := by rw [← normal_list_sum]; exact hwidth
  change ν u₁ = ν u₀ + ((rest.map (orientNormalDirection ν)).map ν).sum at hZwidth
  rw [← hts, hD] at hZwidth
  obtain ⟨CF, hFsegment, v₀, hv₀, v₁, hv₁, hFwidth⟩ := newton_minkowski_base_slab_geometry F
    (differenceProduct (K := K) hs).coeff.support ν a C₀ C₁ hC₀ hbase hsegment
    u₀ u₁ hu₀ hu₁ (d : ℤ) hZwidth
  have hstripEq := geometric_polygon_half_strip_eq_integer_translates F hF a CF hFsegment
  have hagree' : ∀ g ∈ polygonHalfStrip F a, z g = w g := by
    intro g hg
    apply hagree
    change g ∈ {g : Site | latticeEmbedding g ∈ latticeHull F + lineRay 0 (latticeEmbedding a) 0}
    rwa [hstripEq]
  have hstable : ∀ g ∈ polygonHalfStrip F a, g + a ∈ polygonHalfStrip F a := by
    intro g hg
    have he := sampled_half_strip_forward_nat_step (fun u : F => u.val) a 0 1 g hg
    simpa only [polygonHalfStrip, Nat.cast_one, one_smul] using he
  have hzero := forward_difference_zero_on_agreement_region z w (polygonHalfStrip F a) a hstable N hwN hagree'
  have hseedwidth : ν v₀ + (d : ℤ) - 1 ≤ ν v₁ := by omega
  obtain ⟨A, hwedge⟩ := wedge_zero_from_polygon_half_strip δ (differenceProduct ts) hannδ hconst
    F hF a hprimitive τ hτ hker CF hFsegment v₀ v₁ hv₀ hv₁ (ν v₀) d rfl
    hseedwidth q (hpos q hq) hsteps hslope hzero
  let μ := slopingNormal ν τ q
  obtain ⟨E, hplace⟩ := newton_two_ray_region_inside_wedge
    (differenceProduct (K := K) hs).coeff.support ν μ a b haν hbν haμ hbμ (ν v₀ + (d : ℤ) - 1) A
  have hdet : 0 < determinant a b := by change -determinant a b < 0 at hbν; omega
  have hfactor : ∃ q ∈ hs, determinant b q = 0 := by
    obtain ⟨t, ht, he⟩ := oriented_difference_direction_mem rest ν q (by rwa [← hts])
    have hbq : determinant b q = 0 := by
      rw [hrep]
      have hid := determinant_zsmul b (-b) 1 (k : ℤ)
      have hflat : determinant b (-b) = 0 := by simp [determinant]; ring
      simpa only [one_smul, hflat, mul_zero] using hid
    refine ⟨t, (hrestmem t ht).1, ?_⟩
    rcases he with he | he
    · rwa [he] at hbq
    · change directionNormal b q = 0 at hbq
      rw [he, map_neg] at hbq
      change directionNormal b t = 0
      omega
  refine ⟨N, b, μ, E, hN, hbprimitive, hdet, hbμ, haμ, hfactor, ?_, ?_⟩
  · intro t ht
    rcases hcover t ht with he | ht
    · subst t
      have hpν : ν p = 0 := by change -determinant a p = 0; rw [hparallel, neg_zero]
      constructor
      · rintro ⟨hn, _hm⟩
        change ν p < 0 at hn
        omega
      · rintro ⟨hn, _hm⟩
        change ν (-p) < 0 at hn
        rw [map_neg, hpν, neg_zero] at hn
        omega
    · exact hbetween t ht
  · intro g hg _hnext
    have hb := hplace (latticeEmbedding g) hg
    rw [latticeNormal_embedding, latticeNormal_embedding] at hb
    have hz := hwedge g (by exact_mod_cast hb.1) (by exact_mod_cast hb.2)
    exact sub_eq_zero.mp hz

end KumarNivat
