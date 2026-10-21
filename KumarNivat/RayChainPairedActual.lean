module

public import KumarNivat.RayChainPairedLimit
public import KumarNivat.NewtonCyclicFactorOriginalAligned
public import KumarNivat.PairedStructureRayChainMatching
public import KumarNivat.PairedStructureWideStripMatching

@[expose] public section

namespace KumarNivat

open scoped Pointwise

-- the original factor list supplies the same aligned newton polygon and both actual initial rays internally.
theorem paired_direction_of_actual_initial_newton_reference {K : Type*}
    [CommRing K] [Nontrivial K] [NoZeroDivisors K] [TopologicalSpace K] [DiscreteTopology K]
    (c x B : Site → K) (hc : (Set.range c).Finite)
    (hx : x ∈ orbitClosure c) (hB : B ∈ orbitClosure c) (hBfull : FullyPeriodic B)
    (hs : List Site) (hlen : 2 ≤ hs.length) (hdirs : ∀ p ∈ hs, p ≠ 0)
    (hpairs : hs.Pairwise (fun p r => determinant p r ≠ 0))
    (hann : laurentAct (differenceProduct hs) c = 0)
    (hnot : ¬ ∃ v : Site, v ≠ 0 ∧ IsPeriod x v)
    (a b G : Site) (ha : Int.gcd a.1 a.2 = 1) (hb : Int.gcd b.1 b.2 = 1)
    (hab : 0 < determinant a b) (μ : Site →+ ℤ) (hμb : μ b = 0) (hμa : 0 < μ a)
    (pa pb : Site) (hpa : pa ∈ hs) (hpb : pb ∈ hs)
    (haparallel : determinant a pa = 0) (hbparallel : determinant b pb = 0)
    (hbetween : ∀ g ∈ hs, (¬ ((-directionNormal a) g < 0 ∧ 0 < μ g)) ∧
      (¬ ((-directionNormal a) (-g) < 0 ∧ 0 < μ (-g))))
    (p : ℕ) (hp : 0 < p)
    (hstart : RegionalPeriod x {g | latticeEmbedding g ∈ latticeHull (differenceProduct (K := K) hs).coeff.support +
      (lineRay (latticeEmbedding G) (latticeEmbedding a) 0 + lineRay 0 (latticeEmbedding b) 0)} ((p : ℤ) • a))
    (hmatch : ∀ g : Site, latticeEmbedding g ∈ latticeHull (differenceProduct (K := K) hs).coeff.support +
      (lineRay (latticeEmbedding G) (latticeEmbedding a) 0 + lineRay 0 (latticeEmbedding b) 0) → x g = B g) :
    HasPairedOneSidedDirection c := by
  classical
  obtain ⟨q, hq, _hqeq, e, he₀, hfan, hprimitive, hsource, hcover, ⟨P⟩⟩ :=
    actual_original_cyclic_model_with_prescribed_factor (K := K) hs hlen hdirs hpairs a ha pa hpa haparallel
  let _ : NeZero q := ⟨by omega⟩
  obtain ⟨i, hi⟩ := primitive_factor_occurs_in_fan hs e hfan.opposite hprimitive hcover
    b hb pb hpb (hdirs pb hpb) hbparallel
  have hj := positive_factor_fan_index e hfan i (by rwa [he₀, hi])
  have hej : e (i.val : ZMod (2 * q)) = b := by simpa only [ZMod.natCast_zmod_val] using hi
  have hadj : i.val = 1 := initial_factor_ray_is_adjacent hs hdirs e hfan hprimitive hsource
    i.val hj.1 hj.2 μ (by rwa [hej]) (by rwa [he₀]) (by simpa only [he₀] using hbetween)
  have he₁ : e 1 = b := by simpa only [hadj, Nat.cast_one] using hej
  have hfirst : RegionalPeriod x {g | latticeEmbedding g ∈
      forwardFactorNewtonRegion (differenceProduct (K := K) hs).coeff.support G e 1} ((p : ℤ) • e 0) := by
    simpa only [forward_factor_newton_region_eq_two_rays _ _ _ 1 (by omega : 1 < q),
      Nat.cast_one, he₀, he₁] using hstart
  have hagree : ∀ g : Site, latticeEmbedding g ∈
      forwardFactorNewtonRegion (differenceProduct (K := K) hs).coeff.support G e 1 → x g = B g := by
    simpa only [forward_factor_newton_region_eq_two_rays _ _ _ 1 (by omega : 1 < q),
      Nat.cast_one, he₀, he₁] using hmatch
  exact paired_direction_of_initial_factor_ray_reference hq c x B hc hx hB hBfull hs hdirs hpairs hann hnot
    e hfan hprimitive P G p hp hfirst hagree

-- a genuine matching original-newton half-strip completes the paired-direction branch without a supplied polygon or ray-chain selection.
theorem matching_newton_half_strip_forces_paired_direction {K : Type*}
    [CommRing K] [Nontrivial K] [NoZeroDivisors K] [TopologicalSpace K] [DiscreteTopology K]
    (c x w : Site → K) (hc : (Set.range c).Finite) (hx : x ∈ orbitClosure c)
    (hnopair : ¬ HasPairedOneSidedDirection c) (hnot : ¬ ∃ v : Site, v ≠ 0 ∧ IsPeriod x v)
    (hs : List Site) (hlen : 2 ≤ hs.length) (hdirs : ∀ p ∈ hs, p ≠ 0)
    (hpairs : hs.Pairwise (fun p r => determinant p r ≠ 0))
    (hann : laurentAct (differenceProduct hs) c = 0)
    (a : Site) (ha : Int.gcd a.1 a.2 = 1) (pa : Site) (hpa : pa ∈ hs)
    (haparallel : determinant a pa = 0) (l : ℕ) (hl : 0 < l) (hw : IsPeriod w ((l : ℤ) • a))
    (F : Finset Site) (hF : LatticeConvex F) (C₀ : Set RealPlane) (hC₀ : C₀.Nonempty)
    (hbase : latticeHull F = latticeHull (differenceProduct (K := K) hs).coeff.support + C₀)
    (hmatch : ∀ g : Site, latticeEmbedding g ∈ latticeHull F + lineRay 0 (latticeEmbedding a) 0 → x g = w g) :
    HasPairedOneSidedDirection c := by
  obtain ⟨N, b, μ, G, hN, hb, hab, hμb, hμa, ⟨pb, hpb, hbparallel⟩, hbetween,
    hperiod, B, hB, hBfull, hagree⟩ := fullyPeriodic_reference_from_matching_newton_half_strip
      c x w hc hx hnopair hs hlen hdirs hpairs hann a ha pa hpa haparallel l hl hw F hF C₀ hC₀ hbase hmatch
  exact paired_direction_of_actual_initial_newton_reference c x B hc hx hB hBfull hs hlen hdirs hpairs hann hnot
    a b G ha hb hab μ hμb hμa pa pb hpa hpb haparallel hbparallel hbetween N hN hperiod hagree

end KumarNivat
