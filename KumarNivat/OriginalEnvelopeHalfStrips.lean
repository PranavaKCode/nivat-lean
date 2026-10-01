import KumarNivat.AnchoredSourceSequences
import KumarNivat.NewtonEnvelopeUnitSegments
import KumarNivat.InitialWedgeFromHalfStrip

namespace KumarNivat

open scoped Pointwise

-- the intrinsic original-product envelope carries its actual compact convex residual.
theorem OriginalNewtonCyclicEnvelope.minkowski_data {K : Type*} [CommRing K]
    {hs : List Site} {F : Finset Site} (hEnvelope : OriginalNewtonCyclicEnvelope (K := K) hs F) :
    ∃ C : Set RealPlane, Convex ℝ C ∧ IsCompact C ∧ C.Nonempty ∧
      latticeHull F = latticeHull (differenceProduct (K := K) hs).coeff.support + C := by
  obtain ⟨q, hq, hdata⟩ := hEnvelope
  let _ : NeZero q := ⟨by omega⟩
  obtain ⟨_hqeq, _e, _hfan, _hprimitive, _hsource, _hcover, _hP, hF⟩ := hdata
  exact hF.2

-- the paper's real half-strip and the actual integer observation rows coincide for every original envelope.
theorem OriginalNewtonCyclicEnvelope.half_strip_eq_integer_translates {K : Type*}
    [CommRing K] [Nontrivial K] [NoZeroDivisors K]
    {hs : List Site} {F : Finset Site} (hEnvelope : OriginalNewtonCyclicEnvelope (K := K) hs F)
    (hF : LatticeConvex F) (hdirs : ∀ p ∈ hs, p ≠ 0)
    (hpairs : hs.Pairwise (fun p q => determinant p q ≠ 0))
    (a : Site) (hprimitive : Int.gcd a.1 a.2 = 1) (p : Site) (hpmem : p ∈ hs)
    (hparallel : determinant a p = 0) :
    {g : Site | latticeEmbedding g ∈ latticeHull F + lineRay 0 (latticeEmbedding a) 0} =
      polygonHalfStrip F a := by
  obtain ⟨C, _hconvex, _hcompact, _hnonempty, hbase⟩ := hEnvelope.minkowski_data
  exact newton_envelope_half_strip_eq_integer_translates (K := K) hs hdirs hpairs a
    hprimitive p hpmem hparallel F hF C hbase

-- agreement on the original envelope's integer half-strip supplies the full initial-wedge theorem's actual geometric base.
theorem initial_wedge_from_original_envelope_half_strip {K : Type*}
    [CommRing K] [Nontrivial K] [NoZeroDivisors K]
    (z w : Site → K) (hs : List Site) (hlen : 2 ≤ hs.length) (hdirs : ∀ p ∈ hs, p ≠ 0)
    (hpairs : hs.Pairwise (fun p q => determinant p q ≠ 0))
    (hann : laurentAct (differenceProduct hs) z = 0)
    (a : Site) (hprimitive : Int.gcd a.1 a.2 = 1) (p : Site) (hpmem : p ∈ hs)
    (hparallel : determinant a p = 0) (l : ℕ) (hl : 0 < l) (hw : IsPeriod w ((l : ℤ) • a))
    (F : Finset Site) (hF : LatticeConvex F) (hEnvelope : OriginalNewtonCyclicEnvelope (K := K) hs F)
    (hagree : ∀ g ∈ polygonHalfStrip F a, z g = w g) :
    ∃ N : ℕ, ∃ b : Site, ∃ μ : Site →+ ℤ, ∃ E : Site,
      0 < N ∧ Int.gcd b.1 b.2 = 1 ∧ 0 < determinant a b ∧ μ b = 0 ∧ 0 < μ a ∧
      (∃ q ∈ hs, determinant b q = 0) ∧
      (∀ q ∈ hs, (¬ ((-directionNormal a) q < 0 ∧ 0 < μ q)) ∧
        (¬ ((-directionNormal a) (-q) < 0 ∧ 0 < μ (-q)))) ∧
      RegionalPeriod z {g | latticeEmbedding g ∈ latticeHull (differenceProduct (K := K) hs).coeff.support +
        (lineRay (latticeEmbedding E) (latticeEmbedding a) 0 + lineRay 0 (latticeEmbedding b) 0)}
          ((N : ℤ) • a) := by
  obtain ⟨C, _hconvex, _hcompact, hC, hbase⟩ := hEnvelope.minkowski_data
  apply initial_wedge_from_newton_half_strip z w hs hlen hdirs hpairs hann a hprimitive p hpmem
    hparallel l hl hw F hF C hC hbase
  intro g hg
  apply hagree
  have hEq := hEnvelope.half_strip_eq_integer_translates hF hdirs hpairs a hprimitive p hpmem hparallel
  change g ∈ {g : Site | latticeEmbedding g ∈ latticeHull F + lineRay 0 (latticeEmbedding a) 0} at hg
  rwa [hEq] at hg

end KumarNivat
