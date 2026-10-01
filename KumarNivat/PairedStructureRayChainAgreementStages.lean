import KumarNivat.PairedStructureRayChainAgreement

namespace KumarNivat

open scoped Pointwise

-- the actual fan regions supply both the attained old-normal bound and forward stability needed to extend agreement.
theorem agreement_on_actual_factor_ray_period_region {A : Type*}
    {q : ℕ} [NeZero (2 * q)]
    (x B : Site → A) (hB : FullyPeriodic B) (S : Finset Site) (hS : S.Nonempty) (G : Site)
    (e : ZMod (2 * q) → Site) (hfan : AnchoredChainFanOrder e) (hq : 2 ≤ q)
    (hprimitive : Int.gcd (e 0).1 (e 0).2 = 1) (p : ℕ) (hp : 0 < p)
    (k : ℕ) (hk₀ : 0 < k) (hkq : k < q)
    (hfirst : RegionalPeriod x {g | latticeEmbedding g ∈ forwardFactorNewtonRegion S G e 1} ((p : ℤ) • e 0))
    (hperiod : RegionalPeriod x {g | latticeEmbedding g ∈ forwardFactorNewtonRegion S G e k} ((p : ℤ) • e 0))
    (hmatch : ∀ g : Site, latticeEmbedding g ∈ forwardFactorNewtonRegion S G e 1 → x g = B g) :
    IsPeriod B ((p : ℤ) • e 0) ∧
      ∀ g : Site, latticeEmbedding g ∈ forwardFactorNewtonRegion S G e k → x g = B g := by
  have h1q : 1 < q := by omega
  have hdet₁ : 0 < determinant (e 0) (e 1) := by
    simpa only [Nat.cast_zero, Nat.cast_one] using anchored_chain_first_half_pair_positive e hfan 0 1 (by omega) h1q
  have hmatch' : ∀ g : Site, latticeEmbedding g ∈ latticeHull S +
      (lineRay (latticeEmbedding G) (latticeEmbedding (e 0)) 0 + lineRay 0 (latticeEmbedding (e 1)) 0) → x g = B g := by
    simpa only [forward_factor_newton_region_eq_two_rays S G e 1 h1q, Nat.cast_one] using hmatch
  have hfirst' : RegionalPeriod x {g | latticeEmbedding g ∈ latticeHull S +
      (lineRay (latticeEmbedding G) (latticeEmbedding (e 0)) 0 + lineRay 0 (latticeEmbedding (e 1)) 0)} ((p : ℤ) • e 0) := by
    simpa only [forward_factor_newton_region_eq_two_rays S G e 1 h1q, Nat.cast_one] using hfirst
  have hBperiod := fullyPeriodic_reference_inherits_exact_two_ray_period x B hB S hS G (e 0) (e 1) hdet₁ p hp hfirst' hmatch'
  obtain ⟨u₀, hu₀, _hmin, hhalf⟩ := newton_hull_plus_homogeneous_halfplane S hS G (directionNormal (e 0))
  obtain ⟨hregions, _hfinal⟩ := forward_factor_newton_regions_chain S hS G e hfan hq
  have hfinalCone := (forward_factor_ray_cones_chain e hfan hq).2
  have hfinalRegion : forwardFactorNewtonRegion S G e q =
      {x | (directionNormal (e 0) (G + u₀) : ℝ) ≤ latticeNormal (directionNormal (e 0)) x} := by
    simpa only [forwardFactorNewtonRegion, hfinalCone] using hhalf
  let R : Set Site := {g | latticeEmbedding g ∈ forwardFactorNewtonRegion S G e k}
  have hbound : ∀ g ∈ R, directionNormal (e 0) (G + u₀) ≤ directionNormal (e 0) g := by
    intro g hg
    have h := hregions k q hk₀ hkq.le le_rfl hg
    rw [hfinalRegion] at h
    simpa only [Set.mem_ofPred_eq, latticeNormal_embedding, Int.cast_le] using h
  have hstable : ∀ g ∈ R, g + (p : ℤ) • e 0 ∈ R := by
    intro g hg
    change latticeEmbedding g ∈ forwardFactorNewtonRegion S G e k at hg
    have hg' : latticeEmbedding g ∈ latticeHull S +
        (lineRay (latticeEmbedding G) (latticeEmbedding (e 0)) 0 + lineRay 0 (latticeEmbedding (e (k : ZMod (2 * q)))) 0) := by
      simpa only [forward_factor_newton_region_eq_two_rays S G e k hkq] using hg
    have hfit := newton_two_ray_region_first_motion S G (e 0) (e (k : ZMod (2 * q)))
      (latticeEmbedding g) hg' (p : ℝ) (Nat.cast_nonneg p)
    change latticeEmbedding (g + (p : ℤ) • e 0) ∈ forwardFactorNewtonRegion S G e k
    rw [forward_factor_newton_region_eq_two_rays S G e k hkq]
    simpa only [latticeEmbedding_add, latticeEmbedding_zsmul, Int.cast_natCast] using hfit
  exact ⟨hBperiod, agreement_on_forward_periodic_superset x B S u₀ hu₀ G (e 0) (e 1)
    hprimitive hdet₁ p hp R hbound hstable hperiod hBperiod hmatch'⟩

-- failure of the exact old period gives a genuine disagreement with its inherited-period reference in the enlarged region.
theorem failed_regional_period_has_reference_disagreement {A : Type*}
    (x B : Site → A) (R : Set Site) (h : Site) (hB : IsPeriod B h)
    (hfail : ¬ RegionalPeriod x R h) : ∃ g ∈ R, x g ≠ B g := by
  by_contra hnot
  push Not at hnot
  apply hfail
  intro g hg hnext
  rw [hnot (g + h) hnext, hnot g hg]
  exact hB g

end KumarNivat
