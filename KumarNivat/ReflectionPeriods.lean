import KumarNivat.ReflectionGeometry
import KumarNivat.RegionalBackground

namespace KumarNivat

-- periods transform with their vectors on the exact reflected working region.
theorem regional_period_inward_reflection {A I : Type*} (x : Site → A) (ν : Site →+ ℤ) (cut : ℤ)
    (J : Finset I) (μ : I → Site →+ ℤ) (z : I → ℤ) (h : Site)
    (hp : RegionalPeriod x {g | latticeEmbedding g ∈ inwardLayerRegion ν cut J μ z} h) :
    RegionalPeriod (reflectedConfig x) {g | latticeEmbedding g ∈ inwardLayerRegion (reflectedNormal ν) cut J
      (fun i => reflectedNormal (μ i)) z} (siteReflection h) := by
  intro g hg hnext
  change latticeEmbedding g ∈ inwardLayerRegion (reflectedNormal ν) cut J (fun i => reflectedNormal (μ i)) z at hg
  change latticeEmbedding (g + siteReflection h) ∈ inwardLayerRegion (reflectedNormal ν) cut J
    (fun i => reflectedNormal (μ i)) z at hnext
  have hg' : latticeEmbedding (siteReflection g) ∈ inwardLayerRegion ν cut J μ z :=
    (mem_inwardLayerRegion_reflected_site ν cut J μ z (siteReflection g)).mp
      (by simpa only [siteReflection_twice] using hg)
  have hnext' : latticeEmbedding (siteReflection g + h) ∈ inwardLayerRegion ν cut J μ z := by
    have he := (mem_inwardLayerRegion_reflected_site ν cut J μ z (siteReflection (g + siteReflection h))).mp
      (by simpa only [siteReflection_twice] using hnext)
    simpa only [map_add, siteReflection_twice] using he
  have he := hp (siteReflection g) hg' hnext'
  simpa only [reflectedConfig, map_add, siteReflection_twice] using he

-- the inverse reflection carries the derived regional period back to the original array.
theorem regional_period_of_inward_reflection {A I : Type*} (x : Site → A) (ν : Site →+ ℤ) (cut : ℤ)
    (J : Finset I) (μ : I → Site →+ ℤ) (z : I → ℤ) (h : Site)
    (hp : RegionalPeriod (reflectedConfig x) {g | latticeEmbedding g ∈ inwardLayerRegion (reflectedNormal ν) cut J
      (fun i => reflectedNormal (μ i)) z} (siteReflection h)) :
    RegionalPeriod x {g | latticeEmbedding g ∈ inwardLayerRegion ν cut J μ z} h := by
  intro g hg hnext
  change latticeEmbedding g ∈ inwardLayerRegion ν cut J μ z at hg
  change latticeEmbedding (g + h) ∈ inwardLayerRegion ν cut J μ z at hnext
  have hg' := (mem_inwardLayerRegion_reflected_site ν cut J μ z g).mpr hg
  have hnext' := (mem_inwardLayerRegion_reflected_site ν cut J μ z (g + h)).mpr hnext
  rw [map_add] at hnext'
  have he := hp (siteReflection g) hg' hnext'
  simpa only [reflectedConfig, map_add, siteReflection_twice] using he

end KumarNivat
