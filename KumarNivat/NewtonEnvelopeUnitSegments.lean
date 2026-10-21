module

public import KumarNivat.NewtonHalfStripBases
public import KumarNivat.FactorDeletion
public import KumarNivat.PolygonHalfStrips
public import KumarNivat.AnchoredMaximalCyclic

@[expose] public section

namespace KumarNivat

open scoped Pointwise

-- an actual factor supplies a unit segment in either primitive orientation of its original newton hull.
theorem original_newton_tangent_unit_summand {K : Type*} [CommRing K] [Nontrivial K]
    [NoZeroDivisors K] (hs : List Site) (hdirs : ∀ h ∈ hs, h ≠ 0)
    (hpairs : hs.Pairwise (fun p q => determinant p q ≠ 0))
    (a : Site) (hprimitive : Int.gcd a.1 a.2 = 1) (p : Site) (hpmem : p ∈ hs)
    (hparallel : determinant a p = 0) :
    ∃ C : Set RealPlane, latticeHull (differenceProduct (K := K) hs).coeff.support =
      lineInterval 0 (latticeEmbedding a) 0 1 + C := by
  have hane : a ≠ 0 := by rintro rfl; simp at hprimitive
  have hnormal : directionNormal a ≠ 0 := directionNormal_ne_zero a hane
  obtain ⟨τ, _hτ, hker⟩ := primitive_direction_coordinate a hprimitive
  obtain ⟨rest, _hlength, _hmem, _hpairs, hprod, hind, _hcover⟩ :=
    differenceProduct_delete_factor (K := K) hs hpairs p hpmem
  have htransverse : ∀ q ∈ rest, (-directionNormal a) q ≠ 0 := by
    intro q hq he
    have hzero : directionNormal a q = 0 := by
      change -directionNormal a q = 0 at he
      omega
    exact hind q hq (nonzero_normal_kernel_parallel (directionNormal a) hnormal p q hparallel hzero)
  obtain ⟨C, hunit, _hwidth⟩ := tangent_difference_product_newton_data (K := K)
    a hprimitive τ hker p (hdirs p hpmem) hparallel rest htransverse
  rw [← hprod] at hunit
  exact ⟨C, hunit⟩

-- the same original unit segment is retained by every exact newton envelope.
theorem newton_envelope_tangent_unit_summand {K : Type*} [CommRing K] [Nontrivial K]
    [NoZeroDivisors K] (hs : List Site) (hdirs : ∀ h ∈ hs, h ≠ 0)
    (hpairs : hs.Pairwise (fun p q => determinant p q ≠ 0))
    (a : Site) (hprimitive : Int.gcd a.1 a.2 = 1) (p : Site) (hpmem : p ∈ hs)
    (hparallel : determinant a p = 0) (F : Finset Site) (C₀ : Set RealPlane)
    (hbase : latticeHull F = latticeHull (differenceProduct (K := K) hs).coeff.support + C₀) :
    ∃ C : Set RealPlane, latticeHull F = lineInterval 0 (latticeEmbedding a) 0 1 + C := by
  obtain ⟨C₁, hunit⟩ := original_newton_tangent_unit_summand (K := K)
    hs hdirs hpairs a hprimitive p hpmem hparallel
  exact ⟨C₁ + C₀, by rw [hbase, hunit, add_assoc]⟩

-- the allowed geometric half-strip is exactly the original integer translates for an actual newton envelope.
theorem newton_envelope_half_strip_eq_integer_translates {K : Type*} [CommRing K]
    [Nontrivial K] [NoZeroDivisors K] (hs : List Site) (hdirs : ∀ h ∈ hs, h ≠ 0)
    (hpairs : hs.Pairwise (fun p q => determinant p q ≠ 0))
    (a : Site) (hprimitive : Int.gcd a.1 a.2 = 1) (p : Site) (hpmem : p ∈ hs)
    (hparallel : determinant a p = 0) (F : Finset Site) (hF : LatticeConvex F) (C₀ : Set RealPlane)
    (hbase : latticeHull F = latticeHull (differenceProduct (K := K) hs).coeff.support + C₀) :
    {g : Site | latticeEmbedding g ∈ latticeHull F + lineRay 0 (latticeEmbedding a) 0} =
      polygonHalfStrip F a := by
  obtain ⟨C, hunit⟩ := newton_envelope_tangent_unit_summand (K := K)
    hs hdirs hpairs a hprimitive p hpmem hparallel F C₀ hbase
  exact geometric_polygon_half_strip_eq_integer_translates F hF a C hunit

-- the source's actual cyclic base metadata supplies that half-strip identity without another segment premise.
theorem anchored_cyclic_base_half_strip_eq_integer_translates {K : Type*} [CommRing K]
    [Nontrivial K] [NoZeroDivisors K] {n : ℕ} [NeZero n]
    (hs : List Site) (hdirs : ∀ h ∈ hs, h ≠ 0)
    (hpairs : hs.Pairwise (fun p q => determinant p q ≠ 0))
    (e : ZMod n → Site) (hprimitive : Int.gcd (e 0).1 (e 0).2 = 1)
    (p : Site) (hpmem : p ∈ hs) (hparallel : determinant (e 0) p = 0)
    (F : Finset Site) (hF : LatticeConvex F)
    (hEnvelope : AnchoredCyclicEnvelope e (latticeHull (differenceProduct (K := K) hs).coeff.support) F) :
    {g : Site | latticeEmbedding g ∈ latticeHull F + lineRay 0 (latticeEmbedding (e 0)) 0} =
      polygonHalfStrip F (e 0) := by
  obtain ⟨_hpoly, C, _hconvex, _hcompact, _hnonempty, hbase⟩ := hEnvelope
  exact newton_envelope_half_strip_eq_integer_translates (K := K) hs hdirs hpairs (e 0)
    hprimitive p hpmem hparallel F hF C hbase

end KumarNivat
