module

public import KumarNivat.MainMatchingBackgroundFan
public import KumarNivat.NewtonCyclicFactorOriginalAligned
public import KumarNivat.PairedStructureRayChainMatching

@[expose] public section

namespace KumarNivat

open scoped Pointwise

-- the actual initial two-ray packet chooses its original aligned polygon internally before constructing the same array's background.
theorem background_wedge_of_actual_initial_newton_period {K : Type*}
    [CommRing K] [Nontrivial K] [NoZeroDivisors K]
    (c x : Site → K) (hc : (Set.range c).Finite) (hx : LanguageContained x c)
    (hs : List Site) (hlen : 2 ≤ hs.length) (hdirs : ∀ h ∈ hs, h ≠ 0)
    (hpairs : hs.Pairwise (fun h k => determinant h k ≠ 0))
    (hann : laurentAct (differenceProduct hs) x = 0)
    (hnot : ¬ ∃ v : Site, v ≠ 0 ∧ IsPeriod x v)
    (R S : Finset Site) (hgen : GeneratingPolygon c R S)
    (a b G : Site) (ha : Int.gcd a.1 a.2 = 1) (hb : Int.gcd b.1 b.2 = 1)
    (hab : 0 < determinant a b) (μ : Site →+ ℤ) (hμb : μ b = 0) (hμa : 0 < μ a)
    (pa pb : Site) (hpa : pa ∈ hs) (hpb : pb ∈ hs)
    (haparallel : determinant a pa = 0) (hbparallel : determinant b pb = 0)
    (hbetween : ∀ g ∈ hs, (¬ ((-directionNormal a) g < 0 ∧ 0 < μ g)) ∧
      (¬ ((-directionNormal a) (-g) < 0 ∧ 0 < μ (-g))))
    (m M : ℤ) (hbounds : ∀ u ∈ S, m ≤ directionNormal a u ∧ directionNormal a u ≤ M)
    (hlower : 2 ≤ (lowerLatticeFace S (directionNormal a) m).card)
    (hupper : 2 ≤ (lowerLatticeFace S (-directionNormal a) (-M)).card)
    (p : ℕ) (hp : 0 < p)
    (hstart : RegionalPeriod x {g | latticeEmbedding g ∈ latticeHull (differenceProduct (K := K) hs).coeff.support +
      (lineRay (latticeEmbedding G) (latticeEmbedding a) 0 + lineRay 0 (latticeEmbedding b) 0)} ((p : ℤ) • a)) :
    ∃ d : Site, Int.gcd d.1 d.2 = 1 ∧ 0 < determinant a d ∧
      (∃ h ∈ hs, determinant d h = 0) ∧ Function.Injective ((directionNormal a).prod (-directionNormal d)) ∧
      ∃ E : Site, ∃ B : Site → K, FullyPeriodic B ∧
        AgreesOnWedge (directionNormal a) (-directionNormal d) (directionNormal a E)
          ((-directionNormal d) E) x B ∧ Set.range B ⊆ Set.range x := by
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
  have hboundsE : ∀ u ∈ S, m ≤ directionNormal (e 0) u ∧ directionNormal (e 0) u ≤ M := by
    simpa only [he₀] using hbounds
  have hlowerE : 2 ≤ (lowerLatticeFace S (directionNormal (e 0)) m).card := by simpa only [he₀] using hlower
  have hupperE : 2 ≤ (lowerLatticeFace S (-directionNormal (e 0)) (-M)).card := by simpa only [he₀] using hupper
  simpa only [he₀] using background_wedge_of_initial_factor_ray_period hq c x hc hx hs hdirs hpairs hann hnot
    R S hgen e hfan hprimitive hsource P G m M hboundsE hlowerE hupperE p hp hfirst

end KumarNivat
