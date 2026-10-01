import KumarNivat.PairedStructureFiberDirections
import KumarNivat.PairedStructureExpansivity
import KumarNivat.KariSzabados
import Mathlib.Topology.Instances.Int

namespace KumarNivat

-- minimality prevents any remaining one-sided direction after the actual maximal-fiber elimination.
theorem symmetric_oneSided_directions_of_orbit_minimal_product {K : Type*} [CommRing K]
    [Nontrivial K] [NoZeroDivisors K] [TopologicalSpace K] [DiscreteTopology K]
    (c : Site → K) (hc : (Set.range c).Finite) (hs : List Site)
    (hdirs : ∀ p ∈ hs, p ≠ 0) (hpairs : hs.Pairwise (fun p q => determinant p q ≠ 0))
    (hann : laurentAct (differenceProduct hs) c = 0)
    (hminimal : ∀ x ∈ orbitClosure c, orbitClosure x = orbitClosure c) :
    ∀ ell : Site →+ ℝ, ¬ OneSidedNonexpansive c ell → ¬ OneSidedNonexpansive c (-ell) := by
  intro ell hnoNE hNEneg
  have hell : ell ≠ 0 := neg_ne_zero.mp hNEneg.1
  obtain ⟨p, hpmem, hpnormal⟩ := oneSidedNonexpansive_difference_product_direction
    c hs hann (-ell) hNEneg
  have hellp : ell p = 0 := by
    change -ell p = 0 at hpnormal
    exact neg_eq_zero.mp hpnormal
  obtain ⟨ts, a, v, L, κ, hκ, hL, hav, hmem, hpair, hann', hrep⟩ :=
    oriented_binomial_factor_basis_of_real_normal c hs hpairs hann ell hell p hpmem
      (hdirs p hpmem) hellp
  let μ := integerNormalAsReal (directionNormal a)
  have hhalf : ∀ g : Site, 0 ≤ ell g ↔ 0 ≤ μ g :=
    positive_scalar_same_halfplane ell μ κ hκ hrep
  have hnoμ : ¬ OneSidedNonexpansive c μ := by
    intro hNE
    exact hnoNE (hNE.congr_halfplanes (fun g => (hhalf g).symm))
  obtain ⟨d, hd, _hpos, hneg⟩ := remove_opposite_nonexpansive_factor_direction
    c hc ts hpair hann' a v hav L hL hmem hnoμ
  have hNEd : OneSidedNonexpansive d (-ell) := by
    rw [OneSidedNonexpansive, hminimal d hd]
    exact hNEneg
  have hrepneg (g : Site) : (-ell) g = κ * (-μ) g := by
    change -ell g = κ * (-μ g)
    rw [hrep g]
    ring
  exact hneg (hNEd.congr_halfplanes (positive_scalar_same_halfplane (-ell) (-μ) κ hκ hrepneg))

-- the kari-moutot symmetry point is selected in the original orbit closure with no symmetry premise.
theorem exists_symmetric_oneSided_orbit_point_of_difference_product {K : Type*} [CommRing K]
    [Nontrivial K] [NoZeroDivisors K] [TopologicalSpace K] [DiscreteTopology K]
    (c : Site → K) (hc : (Set.range c).Finite) (hs : List Site)
    (hdirs : ∀ p ∈ hs, p ≠ 0) (hpairs : hs.Pairwise (fun p q => determinant p q ≠ 0))
    (hann : laurentAct (differenceProduct hs) c = 0) :
    ∃ d ∈ orbitClosure c, ∀ ell : Site →+ ℝ,
      ¬ OneSidedNonexpansive d ell → ¬ OneSidedNonexpansive d (-ell) := by
  obtain ⟨d, hd, hminimal⟩ := exists_orbit_minimal_configuration c hc
  have hlang := languageContained_of_mem_orbitClosure c d hd
  have hfinite := finite_range_of_language d c hc hlang
  have hdann : laurentAct (differenceProduct hs) d = 0 := by
    funext g
    exact annihilator_inherited_of_language d c hlang (differenceProduct hs).coeff (congrFun hann) g
  exact ⟨d, hd, symmetric_oneSided_directions_of_orbit_minimal_product d hfinite hs
    hdirs hpairs hdann hminimal⟩

-- the paper's actual nonzero integer annihilator supplies every algebraic input to symmetry selection.
theorem exists_symmetric_oneSided_orbit_point_of_integer_annihilator
    (c : Site → ℤ) (hc : (Set.range c).Finite) (f : Laurent ℤ) (hf : f ≠ 0)
    (hann : laurentAct f c = 0) :
    ∃ d ∈ orbitClosure c, ∀ ell : Site →+ ℝ,
      ¬ OneSidedNonexpansive d ell → ¬ OneSidedNonexpansive d (-ell) := by
  obtain ⟨hs, _hne, hpairs, hdirs, hprod⟩ :=
    integer_annihilator_distinct_difference_product c hc f hf hann
  exact exists_symmetric_oneSided_orbit_point_of_difference_product c hc hs hdirs hpairs hprod

-- symmetry yields a fully periodic orbit point under exactly the original no-pair hypothesis.
theorem exists_fullyPeriodic_orbit_point_of_integer_annihilator_no_pair
    (c : Site → ℤ) (hc : (Set.range c).Finite) (f : Laurent ℤ) (hf : f ≠ 0)
    (hann : laurentAct f c = 0) (hnopair : ¬ HasPairedOneSidedDirection c) :
    ∃ d ∈ orbitClosure c, FullyPeriodic d := by
  obtain ⟨d, hd, hsym⟩ := exists_symmetric_oneSided_orbit_point_of_integer_annihilator c hc f hf hann
  exact ⟨d, hd, symmetric_orbit_point_fullyPeriodic_under_no_pair c d hc hd hnopair hsym⟩

end KumarNivat
