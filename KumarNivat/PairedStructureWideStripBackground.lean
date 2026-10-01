import KumarNivat.PairedStructureWideStripGeometry
import KumarNivat.PairedStructureBoundaryLimit

open Filter Topology

namespace KumarNivat

open scoped Pointwise

-- a same-array regional period selects a global directional-periodic reference agreeing on the actual initial two-ray region.
theorem fullyPeriodic_orbit_reference_of_newton_ray_period {K : Type*}
    [CommRing K] [Nontrivial K] [NoZeroDivisors K] [TopologicalSpace K] [DiscreteTopology K]
    (c x : Site → K) (hc : (Set.range c).Finite) (hx : x ∈ orbitClosure c)
    (hnopair : ¬ HasPairedOneSidedDirection c)
    (hs : List Site) (hdirs : ∀ p ∈ hs, p ≠ 0)
    (hpairs : hs.Pairwise (fun p q => determinant p q ≠ 0))
    (hann : laurentAct (differenceProduct hs) c = 0)
    (S : Finset Site) (hS : S.Nonempty) (E a b : Site)
    (hprimitive : Int.gcd a.1 a.2 = 1) (hdet : 0 < determinant a b)
    (q : ℕ) (hq : 0 < q)
    (hperiod : RegionalPeriod x {g | latticeEmbedding g ∈ latticeHull S +
      (lineRay (latticeEmbedding E) (latticeEmbedding a) 0 + lineRay 0 (latticeEmbedding b) 0)}
        ((q : ℤ) • a)) :
    ∃ B ∈ orbitClosure c, FullyPeriodic B ∧ ∀ g : Site,
      latticeEmbedding g ∈ latticeHull S +
        (lineRay (latticeEmbedding E) (latticeEmbedding a) 0 + lineRay 0 (latticeEmbedding b) 0) →
          x g = B g := by
  classical
  obtain ⟨u₀, hu₀⟩ := hS
  let R : Set Site := {g | latticeEmbedding g ∈ latticeHull S +
    (lineRay (latticeEmbedding E) (latticeEmbedding a) 0 + lineRay 0 (latticeEmbedding b) 0)}
  let step := (q : ℤ) • a
  let ν := directionNormal a
  let cut := ν (E + u₀)
  have hstable : ∀ g ∈ R, g + step ∈ R := by
    intro g hg
    have hfit := newton_two_ray_region_first_motion S E a b (latticeEmbedding g) hg
      (q : ℝ) (Nat.cast_nonneg _)
    change latticeEmbedding (g + step) ∈ latticeHull S +
      (lineRay (latticeEmbedding E) (latticeEmbedding a) 0 + lineRay 0 (latticeEmbedding b) 0)
    simpa only [step, latticeEmbedding_add, latticeEmbedding_zsmul, Int.cast_natCast] using hfit
  have hcofinal := newton_two_ray_region_first_ray_halfplane_cofinal S u₀ hu₀ E a b hprimitive hdet q hq
  let z : ℕ → Site → K := fun n => shift ((n : ℤ) • step) x
  obtain ⟨B, hB, φ, hφ, hlimit⟩ := finite_range_orbitClosure_subsequence c hc z
    (fun n => orbitClosure_shift_mem c x hx ((n : ℤ) • step))
  have hagree : ∀ g ∈ R, B g = x g := by
    apply configuration_limit_agrees_of_eventually (z ∘ φ) B x R hlimit
    intro g hg
    exact Eventually.of_forall (fun n =>
      (regional_period_forward_multiples x R step hstable hperiod (φ n) g hg).2)
  have hregional : RegionalPeriod B {g | cut ≤ ν g} step := by
    intro g hg _hnext
    obtain ⟨N, hN⟩ := hcofinal g hg
    have hevent : ∀ᶠ n in atTop, (z ∘ φ) n (g + step) = (z ∘ φ) n g := by
      filter_upwards [hφ.tendsto_atTop.eventually (eventually_ge_atTop N)] with n hn
      have hfit : g + (φ n : ℤ) • step ∈ R := hN (φ n) hn
      have he := hperiod _ hfit (hstable _ hfit)
      simpa only [z, Function.comp_apply, shift, add_assoc, add_comm, add_left_comm] using he
    obtain ⟨n, ⟨hg₀, hg₁⟩, hp⟩ :=
      (((configuration_limit_eventually_eq (z ∘ φ) B hlimit g).and
        (configuration_limit_eventually_eq (z ∘ φ) B hlimit (g + step))).and hevent).exists
    exact hg₁.symm.trans (hp.trans hg₀)
  have hane : a ≠ 0 := by rintro rfl; simp at hprimitive
  have hν : ν ≠ 0 := directionNormal_ne_zero a hane
  have hstepne : step ≠ 0 := smul_ne_zero (by exact_mod_cast Nat.ne_of_gt hq) hane
  have hstepν : ν step = 0 := by simp only [step, ν, map_zsmul, directionNormal_self, smul_zero]
  have hlang := languageContained_of_mem_orbitClosure c B hB
  have hBann : laurentAct (differenceProduct hs) B = 0 := funext
    (annihilator_inherited_of_language B c hlang (differenceProduct hs).coeff (congrFun hann))
  obtain ⟨n, hn, hglobal⟩ := global_period_multiple_of_tangent_regional_period B hs hdirs hpairs
    hBann ν hν cut step hstepne hstepν hregional
  have hfull : FullyPeriodic B := by
    by_contra hnot
    have hpair := hasPairedOneSidedDirection_of_periodic_not_fullyPeriodic B
      (finite_range_of_language B c hc hlang)
        ⟨(n : ℤ) • step, smul_ne_zero (by exact_mod_cast Nat.ne_of_gt hn) hstepne, hglobal⟩ hnot
    exact hnopair (hpair.of_mem_orbitClosure hB)
  exact ⟨B, hB, hfull, fun g hg => (hagree g hg).symm⟩

end KumarNivat
