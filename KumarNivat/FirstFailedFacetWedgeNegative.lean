import KumarNivat.PolyhedralFailureLayers
import KumarNivat.FailedFacetWedgeNegative
import KumarNivat.StableRegions

namespace KumarNivat

open scoped Pointwise

-- the first failed negative-orientation facet supplies the last agreement layer and the same array's periodic wedge.
theorem background_wedge_from_first_failed_facet_negative_orientation {K I : Type*} [CommRing K] [NoZeroDivisors K]
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
    (p : ℕ) (hp : 0 < p) (start : ℤ)
    (hperiod : RegionalPeriod x {g | latticeEmbedding g ∈ inwardLayerRegion (-directionNormal a) cut
      (facetIndexSet J) (facetNormals η μ) (facetLevels start z)} ((p : ℤ) • a))
    (hfail : ¬ RegionalPeriod x {g | cut ≤ (-directionNormal a) g ∧ ∀ i ∈ J, z i ≤ μ i g} ((p : ℤ) • a))
    (hsum : ∀ β : ℤ, β < start → ∃ C : Set RealPlane,
      inwardLayerRegion (-directionNormal a) cut (facetIndexSet J) (facetNormals η μ)
        (facetLevels β z) = latticeHull f.coeff.support + C) :
    Function.Injective ((-directionNormal a).prod (directionNormal b)) ∧
      ∃ E : Site, ∃ B : Site → K, FullyPeriodic B ∧
        AgreesOnWedge (-directionNormal a) (directionNormal b) ((-directionNormal a) E)
          (directionNormal b E) x B ∧ Set.range B ⊆ Set.range x := by
  classical
  let h := (p : ℤ) • a
  let y := shift h x
  have ha : (-directionNormal a) a = 0 := by simp [directionNormal, determinant, mul_comm]
  have hμpos := facetNormals_positive J η μ a hηa hμa
  have hstable : ∀ g : Site, latticeEmbedding g ∈ inwardLayerRegion (-directionNormal a) cut
      (facetIndexSet J) (facetNormals η μ) (facetLevels start z) →
      latticeEmbedding (g + h) ∈ inwardLayerRegion (-directionNormal a) cut
        (facetIndexSet J) (facetNormals η μ) (facetLevels start z) := by
    intro g hg
    rw [latticeEmbedding_add, latticeEmbedding_zsmul]
    exact inwardLayerRegion_nonnegative_motion (-directionNormal a) cut (facetIndexSet J)
      (facetNormals η μ) (facetLevels start z) a (le_of_eq ha.symm)
      (fun i hi => le_of_lt (hμpos i hi)) _ hg (p : ℝ) (Nat.cast_nonneg p)
  have hagree : ∀ g : Site, latticeEmbedding g ∈ inwardLayerRegion η start (facetIndexSet J)
      (facetNormals (-directionNormal a) μ) (facetLevels cut z) → x g = y g := by
    intro g hg
    rw [← inward_region_adjoined_facet_swap (-directionNormal a) η cut start J μ z] at hg
    exact (hperiod g hg (hstable g hg)).symm
  have hfailure : ∃ g : Site, (∀ i ∈ facetIndexSet J,
      facetLevels cut z i ≤ facetNormals (-directionNormal a) μ i g) ∧ x g ≠ y g := by
    change ¬ ∀ g : Site, (cut ≤ (-directionNormal a) g ∧ ∀ i ∈ J, z i ≤ μ i g) →
      (cut ≤ (-directionNormal a) (g + h) ∧ ∀ i ∈ J, z i ≤ μ i (g + h)) → x (g + h) = x g at hfail
    push Not at hfail
    obtain ⟨g, hg, _hnext, hneq⟩ := hfail
    refine ⟨g, ?_, hneq.symm⟩
    intro i hi
    cases i with
    | none => exact hg.1
    | some i => exact hg.2 i ((mem_facetIndexSet_some J i).mp hi)
  obtain ⟨β, g, hβ, _hgη, hg, hneq, hlast⟩ := first_failed_inward_layer x y η start
    (facetIndexSet J) (facetNormals (-directionNormal a) μ) (facetLevels cut z) hagree hfailure
  obtain ⟨C, hC⟩ := hsum β hβ
  apply background_wedge_from_failed_facet_negative_orientation c x hc hx f hf hann R S hgen a b hprimitiveA hprimitiveB
    hdet m M cut hbounds hlower hupper J μ z hμa hμb η hη hηa hηb p hp β C hC
  · intro u hu
    rw [inward_region_adjoined_facet_swap (-directionNormal a) η cut (β + 1) J μ z] at hu
    exact hlast u hu
  · refine ⟨g, ?_, hneq⟩
    rwa [inward_region_adjoined_facet_swap (-directionNormal a) η cut β J μ z]

end KumarNivat
