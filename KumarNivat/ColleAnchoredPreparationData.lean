import KumarNivat.AnchoredActualSequences
import KumarNivat.PairedStructureBoundaryLimit
import KumarNivat.SquarefreeProducts
import Mathlib.Topology.Instances.Int

namespace KumarNivat

open scoped Pointwise

-- this packet contains the actual original product, polygon, periodic phase, and maximal source sequence.
structure ColleAnchoredSourceData (c : Site → ℤ) (hs : List Site)
    {q : ℕ} [NeZero q] (e : ZMod (2 * q) → Site) where
  finite : (Set.range c).Finite
  nonperiodic : ¬ ∃ p : Site, p ≠ 0 ∧ IsPeriod c p
  length_two : 2 ≤ hs.length
  factor_nonzero : ∀ p ∈ hs, p ≠ 0
  factor_distinct : hs.Pairwise (fun p r => determinant p r ≠ 0)
  product_annihilates : laurentAct (differenceProduct hs) c = 0
  fan_size : 2 ≤ q
  fan_length : q = hs.length
  fan_order : AnchoredChainFanOrder e
  primitive : ∀ i, Int.gcd (e i).1 (e i).2 = 1
  factor_source : ∀ i, ∃ p ∈ hs, determinant (e i) p = 0
  factor_cover : ∀ p ∈ hs, ∃ i, determinant (e i) p = 0
  newton_polygon : OrderedCyclicLatticePolygon e (differenceProduct (K := ℤ) hs).coeff.support
  reference : Site → ℤ
  reference_orbit : reference ∈ orbitClosure c
  reference_full : FullyPeriodic reference
  reference_language : LanguageContained reference c
  reference_finite : (Set.range reference).Finite
  reference_product_annihilates : laurentAct (differenceProduct hs) reference = 0
  original_operator : Laurent ℤ
  original_operator_nonzero : original_operator ≠ 0
  original_annihilates : laurentAct original_operator c = 0
  reference_original_annihilates : laurentAct original_operator reference = 0
  periodLength : ℕ
  period_positive : 0 < periodLength
  reference_period : IsPeriod reference ((periodLength : ℤ) • e 0)
  no_half_strip : ∀ F : Finset Site,
    AnchoredCyclicEnvelope e (latticeHull (differenceProduct (K := ℤ) hs).coeff.support) F →
      LatticeConvex F → ∀ u : Site, ¬ ∀ g ∈ polygonHalfStrip F (e 0), shift u c g = reference g
  source_sequence : AnchoredCyclicMaximalSequence c reference e
    (latticeHull (differenceProduct (K := ℤ) hs).coeff.support) 0

-- the final geometric input is one actual retained failed facet of that source sequence's fixed periodic phase.
structure ColleAnchoredRetainedFacet (c : Site → ℤ) (hs : List Site)
    {q : ℕ} [NeZero q] (e : ZMod (2 * q) → Site) (B : Site → ℤ) where
  index : ℕ
  index_positive : 0 < index
  index_lt : index < q
  point : Site → ℤ
  point_orbit : point ∈ orbitClosure c
  level : ℤ
  fixed : ℕ → ℤ
  residual : Set RealPlane
  newton_sum : inwardLayerRegion (directionNormal (e (index : ZMod (2 * q)))) level
    (Finset.range index) (fun i : ℕ => directionNormal (e (i : ZMod (2 * q)))) fixed =
      latticeHull (differenceProduct (K := ℤ) hs).coeff.support + residual
  interior_agrees : ∀ g : Site, latticeEmbedding g ∈
    inwardLayerRegion (directionNormal (e (index : ZMod (2 * q)))) level (Finset.range index)
      (fun i : ℕ => directionNormal (e (i : ZMod (2 * q)))) fixed →
        level + 1 ≤ directionNormal (e (index : ZMod (2 * q))) g → point g = B g
  failure : ∃ g : Site, latticeEmbedding g ∈
    inwardLayerRegion (directionNormal (e (index : ZMod (2 * q)))) level (Finset.range index)
      (fun i : ℕ => directionNormal (e (i : ZMod (2 * q)))) fixed ∧ point g ≠ B g

-- the actual fan proves every slope and tangent prerequisite for the retained boundary theorem.
theorem paired_direction_of_colle_retained_facet (c : Site → ℤ) (hs : List Site)
    {q : ℕ} [NeZero q] (e : ZMod (2 * q) → Site)
    (D : ColleAnchoredSourceData c hs e) (R : ColleAnchoredRetainedFacet c hs e D.reference) :
    HasPairedOneSidedDirection c := by
  let b := e (R.index : ZMod (2 * q))
  let ν := directionNormal b
  have hbne : b ≠ 0 := by
    intro hz
    have h := D.primitive (R.index : ZMod (2 * q))
    change Int.gcd b.1 b.2 = 1 at h
    rw [hz] at h
    simp at h
  have hν : ν ≠ 0 := directionNormal_ne_zero b hbne
  have hbν : ν b = 0 := directionNormal_self b
  have hμ : ∀ i ∈ Finset.range R.index, 0 < directionNormal (e (i : ZMod (2 * q))) b := by
    intro i hi
    change 0 < determinant (e (i : ZMod (2 * q))) (e (R.index : ZMod (2 * q)))
    exact anchored_chain_first_half_pair_positive e D.fan_order i R.index (Finset.mem_range.mp hi) R.index_lt
  have hf : differenceProduct (K := ℤ) hs ≠ 0 := differenceProduct_ne_zero hs D.factor_nonzero
  obtain ⟨_y, _hy, _s, _hs, _hperiod, _hnotfull, _hhalf, _E, _hE, _hfailure, hpair⟩ :=
    retained_nonfull_periodic_boundary_limit c R.point D.reference D.finite R.point_orbit D.reference_orbit
      D.reference_full hs D.factor_nonzero D.factor_distinct D.product_annihilates
      (differenceProduct hs) hf D.product_annihilates ν hν R.level b hbν
      (D.primitive (R.index : ZMod (2 * q))) (Finset.range R.index)
      (fun i : ℕ => directionNormal (e (i : ZMod (2 * q)))) R.fixed hμ R.residual
      R.newton_sum R.interior_agrees R.failure
  exact hpair

end KumarNivat
