import KumarNivat.PairedStructureWideStripBackground
import KumarNivat.SquarefreeProducts

namespace KumarNivat

open scoped Pointwise

-- the matching half-strip case gives a new fully periodic orbit reference on the same actual initial two-ray region.
theorem fullyPeriodic_reference_from_matching_newton_half_strip {K : Type*}
    [CommRing K] [Nontrivial K] [NoZeroDivisors K] [TopologicalSpace K] [DiscreteTopology K]
    (c z w : Site → K) (hc : (Set.range c).Finite) (hz : z ∈ orbitClosure c)
    (hnopair : ¬ HasPairedOneSidedDirection c)
    (hs : List Site) (hlen : 2 ≤ hs.length) (hdirs : ∀ p ∈ hs, p ≠ 0)
    (hpairs : hs.Pairwise (fun p q => determinant p q ≠ 0))
    (hann : laurentAct (differenceProduct hs) c = 0)
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
        (lineRay (latticeEmbedding E) (latticeEmbedding a) 0 + lineRay 0 (latticeEmbedding b) 0)} ((N : ℤ) • a) ∧
      ∃ B ∈ orbitClosure c, FullyPeriodic B ∧ ∀ g : Site,
        latticeEmbedding g ∈ latticeHull (differenceProduct (K := K) hs).coeff.support +
          (lineRay (latticeEmbedding E) (latticeEmbedding a) 0 + lineRay 0 (latticeEmbedding b) 0) →
            z g = B g := by
  have hzann : laurentAct (differenceProduct hs) z = 0 := funext
    (annihilator_inherited_of_language z c (languageContained_of_mem_orbitClosure c z hz)
      (differenceProduct hs).coeff (congrFun hann))
  obtain ⟨N, b, μ, E, hN, hbprimitive, hdet, hμb, hμa, hfactor, hbetween, hperiod⟩ :=
    initial_wedge_from_newton_half_strip z w hs hlen hdirs hpairs hzann a hprimitive p hpmem
      hparallel l hl hw F hF C₀ hC₀ hbase hagree
  have hS : (differenceProduct (K := K) hs).coeff.support.Nonempty := Finsupp.support_nonempty_iff.mpr
    (fun hz => differenceProduct_ne_zero hs hdirs (AddMonoidAlgebra.coeff_injective hz))
  obtain ⟨B, hB, hfull, hBmatch⟩ := fullyPeriodic_orbit_reference_of_newton_ray_period c z hc hz hnopair
    hs hdirs hpairs hann (differenceProduct (K := K) hs).coeff.support hS E a b hprimitive hdet N hN hperiod
  exact ⟨N, b, μ, E, hN, hbprimitive, hdet, hμb, hμa, hfactor, hbetween, hperiod, B, hB, hfull, hBmatch⟩

end KumarNivat
