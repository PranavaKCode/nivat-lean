module

public import KumarNivat.PairedStructureBoundaryBlocks
public import KumarNivat.PairedStructureBoundaryTransport
public import KumarNivat.PairedStructurePeriodic
public import KumarNivat.TangentPeriods

@[expose] public section

open Filter Topology

namespace KumarNivat

open scoped Pointwise

-- the actual failed facet retains a fixed finite witness in a non-full periodic ray limit and forces a paired direction.
theorem retained_nonfull_periodic_boundary_limit {K I : Type*}
    [CommRing K] [Nontrivial K] [NoZeroDivisors K] [TopologicalSpace K] [DiscreteTopology K]
    (c θ B : Site → K) (hc : (Set.range c).Finite)
    (hθ : θ ∈ orbitClosure c) (hB : B ∈ orbitClosure c) (hBfull : FullyPeriodic B)
    (hs : List Site) (hdirs : ∀ p ∈ hs, p ≠ 0)
    (hpairs : hs.Pairwise (fun p q => determinant p q ≠ 0))
    (hann : laurentAct (differenceProduct hs) c = 0)
    (f : Laurent K) (hf : f ≠ 0) (hfann : laurentAct f c = 0)
    (ν : Site →+ ℤ) (hν : ν ≠ 0) (β : ℤ) (b : Site) (hb : ν b = 0)
    (hprimitive : Int.gcd b.1 b.2 = 1) (J : Finset I)
    (μ : I → Site →+ ℤ) (cut : I → ℤ) (hμ : ∀ i ∈ J, 0 < μ i b)
    (C : Set RealPlane)
    (hsum : inwardLayerRegion ν β J μ cut = latticeHull f.coeff.support + C)
    (hagree : ∀ g : Site, latticeEmbedding g ∈ inwardLayerRegion ν β J μ cut →
      β + 1 ≤ ν g → θ g = B g)
    (hfail : ∃ g : Site, latticeEmbedding g ∈ inwardLayerRegion ν β J μ cut ∧ θ g ≠ B g) :
    ∃ y ∈ orbitClosure c, ∃ s : ℕ, 0 < s ∧ IsPeriod y ((s : ℤ) • b) ∧ ¬ FullyPeriodic y ∧
      (∀ g : Site, β + 1 ≤ ν g → y g = B g) ∧ ∃ E : Finset Site,
        (∀ g ∈ E, ν g = β ∧ latticeEmbedding g ∈ inwardLayerRegion ν β J μ cut) ∧
        (∃ g ∈ E, y g ≠ B g) ∧ HasPairedOneSidedDirection c := by
  classical
  have hθlang := languageContained_of_mem_orbitClosure c θ hθ
  have hBlang := languageContained_of_mem_orbitClosure c B hB
  have hθann : laurentAct f θ = 0 := funext
    (annihilator_inherited_of_language θ c hθlang f.coeff (congrFun hfann))
  have hBann : laurentAct f B = 0 := funext
    (annihilator_inherited_of_language B c hBlang f.coeff (congrFun hfann))
  have hforward := inwardLayerRegion_forward_stable ν β J μ cut b hb
    (fun i hi => le_of_lt (hμ i hi))
  obtain ⟨A, t, _ht, hAlevel, hAregion, hblocks⟩ :=
    failed_minkowski_boundary_has_finite_disagreement_blocks θ B f hf hθann hBann
      ν hν β b hb hprimitive (inwardLayerRegion ν β J μ cut) C hsum
        (fun _z hz => hz.1) hforward hagree hfail
  obtain ⟨q, hq, hperiod⟩ := hBfull.exists_period_multiple b
  let step : Site := (q : ℤ) • b
  let E : Finset Site := Finset.univ.image (fun i : Fin t => A + (i.val : ℤ) • b)
  let x : ℕ → Site → K := fun n => shift ((n : ℤ) • step) θ
  have hstepν : ν step = 0 := by simp only [step, map_zsmul, hb, smul_zero]
  have hstepμ (i : I) (hi : i ∈ J) : 0 < μ i step := by
    simp only [step, map_zsmul, smul_eq_mul]
    exact mul_pos (by exact_mod_cast hq) (hμ i hi)
  have hxmem (n : ℕ) : x n ∈ orbitClosure c := orbitClosure_shift_mem c θ hθ ((n : ℤ) • step)
  have hfixed (n : ℕ) : ∃ g ∈ E, x n g ≠ B g :=
    directional_disagreement_blocks_retain_fixed_window θ B A b t q hperiod hblocks n
  have hinward := eventually_shifted_polyhedral_interior_agreement θ B ν β J μ cut step
    hstepν hstepμ hperiod hagree
  obtain ⟨y, hy, φ, hφ, hlimit⟩ := finite_range_orbitClosure_subsequence c hc x hxmem
  have hyagree : ∀ g : Site, β + 1 ≤ ν g → y g = B g :=
    configuration_limit_agrees_of_eventually (x ∘ φ) y B {g | β + 1 ≤ ν g} hlimit
      (fun g hg => hφ.tendsto_atTop.eventually (hinward g hg))
  obtain ⟨g₀, hg₀, hneq⟩ := configuration_limit_retains_finite_disagreement
    (x ∘ φ) y B E hlimit (Eventually.of_forall (fun n => hfixed (φ n)))
  have hynotfull : ¬ FullyPeriodic y := by
    intro hyfull
    obtain ⟨v, hv⟩ := exists_positive_integer_normal_vector ν hν
    have he := fully_periodic_halfplane_agreement y B hyfull hBfull ν (β + 1) v hv hyagree
    exact hneq (congrFun he g₀)
  have hbne : b ≠ 0 := by rintro rfl; simp at hprimitive
  have hstepne : step ≠ 0 := smul_ne_zero (by exact_mod_cast Nat.ne_of_gt hq) hbne
  have hregional : RegionalPeriod y {g | β + 1 ≤ ν g} step := by
    intro g hg hnext
    exact (hyagree (g + step) hnext).trans ((hperiod g).trans (hyagree g hg).symm)
  have hylang := languageContained_of_mem_orbitClosure c y hy
  have hyann : laurentAct (differenceProduct hs) y = 0 := funext
    (annihilator_inherited_of_language y c hylang (differenceProduct hs).coeff (congrFun hann))
  obtain ⟨r, hr, hglobal⟩ := global_period_multiple_of_tangent_regional_period y hs hdirs hpairs
    hyann ν hν (β + 1) step hstepne hstepν hregional
  let s := r * q
  have hspos : 0 < s := Nat.mul_pos hr hq
  have hsperiod : IsPeriod y ((s : ℤ) • b) := by
    simpa only [s, step, Nat.cast_mul, smul_smul] using hglobal
  have hypair : HasPairedOneSidedDirection y := hasPairedOneSidedDirection_of_periodic_not_fullyPeriodic
    y (finite_range_of_language y c hc hylang)
      ⟨(s : ℤ) • b, smul_ne_zero (by exact_mod_cast Nat.ne_of_gt hspos) hbne, hsperiod⟩ hynotfull
  refine ⟨y, hy, s, hspos, hsperiod, hynotfull, hyagree, E, ?_, ⟨g₀, hg₀, hneq⟩,
    hypair.of_mem_orbitClosure hy⟩
  intro g hg
  obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hg
  constructor
  · rw [map_add, map_zsmul, hb, smul_zero, add_zero, hAlevel]
  · rw [latticeEmbedding_add, latticeEmbedding_zsmul]
    exact hforward (latticeEmbedding A) hAregion (i.val : ℝ) (Nat.cast_nonneg _)

end KumarNivat
