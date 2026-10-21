module

public import KumarNivat.AdjoinedFacetRegions
public import KumarNivat.PolyhedralBoundaryAmbiguity
public import KumarNivat.WedgeFromAmbiguousEdgeNegative

@[expose] public section

namespace KumarNivat

open scoped Pointwise

-- a negative orientation preserves the failed-facet ambiguity and constructs the same array's periodic wedge.
theorem background_wedge_from_failed_facet_negative_orientation {K I : Type*} [CommRing K] [NoZeroDivisors K]
    (c x : Site → K) (hc : (Set.range c).Finite) (hx : LanguageContained x c)
    (f : Laurent K) (hf : f ≠ 0) (hann : laurentAct f x = 0)
    (R S : Finset Site) (hgen : GeneratingPolygon c R S) (a b : Site)
    (hprimitiveA : Int.gcd a.1 a.2 = 1) (hprimitiveB : Int.gcd b.1 b.2 = 1)
    (hdet : determinant a b < 0) (m M cut : ℤ)
    (hbounds : ∀ u ∈ S, m ≤ (-directionNormal a) u ∧ (-directionNormal a) u ≤ M)
    (hlower : 2 ≤ (lowerLatticeFace S (-directionNormal a) m).card)
    (hupper : 2 ≤ (lowerLatticeFace S (directionNormal a) (-M)).card)
    (J : Finset I) (μ : I → Site →+ ℤ) (z : I → ℤ)
    (hμa : ∀ i ∈ J, 0 < μ i a) (hμb : ∀ i ∈ J, 0 < μ i b)
    (η : Site →+ ℤ) (hη : η ≠ 0) (hηa : 0 < η a) (hηb : η b = 0)
    (p : ℕ) (hp : 0 < p) (β : ℤ) (C : Set RealPlane)
    (hsum : inwardLayerRegion (-directionNormal a) cut (facetIndexSet J)
      (facetNormals η μ) (facetLevels β z) = latticeHull f.coeff.support + C)
    (hagree : ∀ g : Site, latticeEmbedding g ∈ inwardLayerRegion (-directionNormal a) cut
      (facetIndexSet J) (facetNormals η μ) (facetLevels (β + 1) z) →
        x g = shift ((p : ℤ) • a) x g)
    (hfail : ∃ g : Site, latticeEmbedding g ∈ inwardLayerRegion (-directionNormal a) cut
      (facetIndexSet J) (facetNormals η μ) (facetLevels β z) ∧
        x g ≠ shift ((p : ℤ) • a) x g) :
    Function.Injective ((-directionNormal a).prod (directionNormal b)) ∧
      ∃ E : Site, ∃ B : Site → K, FullyPeriodic B ∧
        AgreesOnWedge (-directionNormal a) (directionNormal b) ((-directionNormal a) E)
          (directionNormal b E) x B ∧ Set.range B ⊆ Set.range x := by
  let h := (p : ℤ) • a
  let y := shift h x
  have hy : LanguageContained y c := hx.shift h
  have hyann : laurentAct f y = 0 := by
    dsimp [y]
    rw [laurentAct_shift, hann]
    rfl
  have hswap := inward_region_adjoined_facet_swap (-directionNormal a) η cut β J μ z
  have hsum' : inwardLayerRegion η β (facetIndexSet J) (facetNormals (-directionNormal a) μ)
      (facetLevels cut z) = latticeHull f.coeff.support + C := by rw [← hswap]; exact hsum
  have hagree' : ∀ g : Site, latticeEmbedding g ∈ inwardLayerRegion η β (facetIndexSet J)
      (facetNormals (-directionNormal a) μ) (facetLevels cut z) → β + 1 ≤ η g → x g = y g := by
    intro g hg hlevel
    rw [← hswap] at hg
    have hm := (mem_inward_region_adjoined_facet (-directionNormal a) η cut β J μ z _).mp hg
    apply hagree
    apply (mem_inward_region_adjoined_facet (-directionNormal a) η cut (β + 1) J μ z _).mpr
    exact ⟨hm.1, by rw [latticeNormal_embedding]; exact_mod_cast hlevel, hm.2.2⟩
  have hfail' : ∃ g : Site, latticeEmbedding g ∈ inwardLayerRegion η β (facetIndexSet J)
      (facetNormals (-directionNormal a) μ) (facetLevels cut z) ∧ x g ≠ y g := by
    rw [← hswap]
    exact hfail
  have hfixedB : ∀ i ∈ facetIndexSet J, 0 < facetNormals (-directionNormal a) μ i b :=
    facetNormals_positive J (-directionNormal a) μ b (by change 0 < -determinant a b; omega) hμb
  obtain ⟨mB, E₀, N, hminB, _hfaceNonempty, hfaceB, hE₀, _hN, hplaced⟩ :=
    polyhedral_boundary_ambiguity_of_failed_extension c x y hc hx hy f hf hann hyann R S hgen
      η hη β (facetIndexSet J) (facetNormals (-directionNormal a) μ) (facetLevels cut z)
      b hηb hprimitiveB hfixedB C hsum' hagree' hfail'
  have hperiod : RegionalPeriod x {g | latticeEmbedding g ∈ inwardLayerRegion (-directionNormal a) cut
      (facetIndexSet J) (facetNormals η μ) (facetLevels (β + 1) z)} h := by
    intro g hg _hnext
    exact (hagree g hg).symm
  have hslopesA := facetNormals_positive J η μ a hηa hμa
  have hslopesB : ∀ i ∈ facetIndexSet J, 0 ≤ facetNormals η μ i b := by
    intro i hi
    cases i with
    | none => change 0 ≤ η b; rw [hηb]
    | some i => exact le_of_lt (hμb i ((mem_facetIndexSet_some J i).mp hi))
  have hamb := fun n hn => (hplaced n hn).2.2
  have hplace : ∀ n : ℤ, N ≤ n → ∀ u ∈ S \ lowerLatticeFace S η mB,
      latticeEmbedding (E₀ + n • b + u) ∈ inwardLayerRegion (-directionNormal a) cut
        (facetIndexSet J) (facetNormals η μ) (facetLevels (β + 1) z) := by
    intro n hn u hu
    obtain ⟨hus, huf⟩ := Finset.mem_sdiff.mp hu
    have hg := (hplaced n hn).1 u hus
    rw [← hswap] at hg
    have hm := (mem_inward_region_adjoined_facet (-directionNormal a) η cut β J μ z _).mp hg
    have hne : η u ≠ mB := by intro he; exact huf (Finset.mem_filter.mpr ⟨hus, he⟩)
    have hmin := hminB u hus
    have hlevel : β + 1 ≤ η (E₀ + n • b + u) := by
      rw [map_add, map_add, map_zsmul, hηb, smul_zero, add_zero, hE₀]
      omega
    apply (mem_inward_region_adjoined_facet (-directionNormal a) η cut (β + 1) J μ z _).mpr
    exact ⟨hm.1, by rw [latticeNormal_embedding]; exact_mod_cast hlevel, hm.2.2⟩
  exact background_wedge_from_ambiguous_edge_negative_orientation c x hc hx R S hgen a b hprimitiveA hprimitiveB hdet
    m M cut hbounds hlower hupper (facetIndexSet J) (facetNormals η μ) (facetLevels (β + 1) z)
    hslopesA hslopesB p hp hperiod η hη mB hminB hηa hηb hfaceB E₀ N hamb hplace

end KumarNivat
