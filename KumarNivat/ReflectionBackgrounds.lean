import KumarNivat.ReflectionPeriods
import KumarNivat.InwardWedgeBackground

namespace KumarNivat

-- a global period follows the reflected sites and vector together.
theorem IsPeriod.reflection {A : Type*} {x : Site → A} {h : Site} (hp : IsPeriod x h) :
    IsPeriod (reflectedConfig x) (siteReflection h) := by
  intro g
  change x (siteReflection (g + siteReflection h)) = x (siteReflection g)
  rw [map_add, siteReflection_twice, hp]

-- independent global periods remain independent after the orientation reversal.
theorem FullyPeriodic.reflection {A : Type*} {x : Site → A} (hp : FullyPeriodic x) :
    FullyPeriodic (reflectedConfig x) := by
  obtain ⟨a, b, hdet, ha, hb⟩ := hp
  exact ⟨siteReflection a, siteReflection b, by rw [determinant_siteReflection]; exact neg_ne_zero.mpr hdet,
    ha.reflection, hb.reflection⟩

-- the reflected ray periods construct a periodic background on the original negatively oriented wedge.
theorem background_on_wedge_of_negative_inward_ray_periods {A I : Type*} (x : Site → A) (a b : Site)
    (hprimitive : Int.gcd a.1 a.2 = 1) (hdet : determinant a b < 0)
    (cut : ℤ) (J : Finset I) (μ : I → Site →+ ℤ) (z : I → ℤ)
    (hμa : ∀ i ∈ J, 0 < μ i a) (hμb : ∀ i ∈ J, 0 ≤ μ i b)
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hperiodA : RegionalPeriod x {g | latticeEmbedding g ∈ inwardLayerRegion (-directionNormal a) cut J μ z} ((p : ℤ) • a))
    (hperiodB : RegionalPeriod x {g | latticeEmbedding g ∈ inwardLayerRegion (-directionNormal a) cut J μ z} ((q : ℤ) • b)) :
    Function.Injective ((-directionNormal a).prod (directionNormal b)) ∧
      ∃ E : Site, ∃ B : Site → A, FullyPeriodic B ∧
        AgreesOnWedge (-directionNormal a) (directionNormal b) ((-directionNormal a) E) (directionNormal b E) x B ∧
        Set.range B ⊆ Set.range x := by
  let ν := -directionNormal a
  let ell := directionNormal b
  let μa := fun i => reflectedNormal (μ i)
  have hnormalA : directionNormal (siteReflection a) = reflectedNormal ν := directionNormal_siteReflection a
  have hnormalB : -directionNormal (siteReflection b) = reflectedNormal ell := by
    rw [directionNormal_siteReflection, reflectedNormal_neg, neg_neg]
  have hperiodA' : RegionalPeriod (reflectedConfig x) {g | latticeEmbedding g ∈ inwardLayerRegion
      (directionNormal (siteReflection a)) cut J μa z} ((p : ℤ) • siteReflection a) := by
    rw [hnormalA]
    simpa only [map_zsmul] using regional_period_inward_reflection x ν cut J μ z ((p : ℤ) • a) hperiodA
  have hperiodB' : RegionalPeriod (reflectedConfig x) {g | latticeEmbedding g ∈ inwardLayerRegion
      (directionNormal (siteReflection a)) cut J μa z} ((q : ℤ) • siteReflection b) := by
    rw [hnormalA]
    simpa only [map_zsmul] using regional_period_inward_reflection x ν cut J μ z ((q : ℤ) • b) hperiodB
  obtain ⟨hinj, E', B', hB', hagree, hrange⟩ := background_on_wedge_of_inward_ray_periods
    (reflectedConfig x) (siteReflection a) (siteReflection b) (primitive_siteReflection a hprimitive)
    (by rw [determinant_siteReflection]; omega) cut J μa z
    (fun i hi => by change 0 < reflectedNormal (μ i) (siteReflection a); rw [reflectedNormal_reflected_site]; exact hμa i hi)
    (fun i hi => by change 0 ≤ reflectedNormal (μ i) (siteReflection b); rw [reflectedNormal_reflected_site]; exact hμb i hi)
    p q hp hq hperiodA' hperiodB'
  rw [hnormalA, hnormalB] at hinj hagree
  refine ⟨?_, siteReflection E', reflectedConfig B', hB'.reflection, ?_, ?_⟩
  · intro g h he
    apply siteReflection.injective
    apply hinj
    apply Prod.ext
    · have he' := congrArg Prod.fst he
      simpa only [AddMonoidHom.prod_apply, reflectedNormal_reflected_site] using he'
    · have he' := congrArg Prod.snd he
      simpa only [AddMonoidHom.prod_apply, reflectedNormal_reflected_site] using he'
  · intro g hν hEll
    have hν' : reflectedNormal ν E' ≤ reflectedNormal ν (siteReflection g) := by
      change ν (siteReflection E') ≤ ν g at hν
      change ν (siteReflection E') ≤ ν (siteReflection (siteReflection g))
      rw [siteReflection_twice]
      exact hν
    have hEll' : reflectedNormal ell E' ≤ reflectedNormal ell (siteReflection g) := by
      change ell (siteReflection E') ≤ ell g at hEll
      change ell (siteReflection E') ≤ ell (siteReflection (siteReflection g))
      rw [siteReflection_twice]
      exact hEll
    have he := hagree (siteReflection g) hν' hEll'
    simpa only [reflectedConfig, siteReflection_twice] using he
  · rw [reflectedConfig_range] at hrange
    rw [reflectedConfig_range]
    exact hrange

end KumarNivat
