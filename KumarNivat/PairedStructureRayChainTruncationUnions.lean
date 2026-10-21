module

public import KumarNivat.PairedStructureRayChainFacetLimits

@[expose] public section

namespace KumarNivat

open scoped Pointwise

-- equal integer truncation bounds exhaust both actual rays simultaneously.
theorem line_interval_truncations_exhaust_two_ray_cone (a b : Site) :
    (⋃ N : ℕ, lineInterval 0 (latticeEmbedding a) 0 N + lineInterval 0 (latticeEmbedding b) 0 N) =
      forwardTwoRayCone a b := by
  ext x
  constructor
  · intro hx
    obtain ⟨N, _, ⟨α, hα, rfl⟩, _, ⟨β, hβ, rfl⟩, rfl⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_add.mpr ⟨0 + α • latticeEmbedding a, ⟨α, hα.1, rfl⟩,
      0 + β • latticeEmbedding b, ⟨β, hβ.1, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨α, hα, rfl⟩, _, ⟨β, hβ, rfl⟩, rfl⟩
    obtain ⟨N, hN⟩ := exists_nat_ge (max α β)
    exact Set.mem_iUnion.mpr ⟨N, Set.mem_add.mpr
      ⟨0 + α • latticeEmbedding a, ⟨α, ⟨hα, (le_max_left _ _).trans hN⟩, rfl⟩,
        0 + β • latticeEmbedding b, ⟨β, ⟨hβ, (le_max_right _ _).trans hN⟩, rfl⟩, rfl⟩⟩

-- the unchanged original newton hull commutes with this actual exhaustion.
theorem newton_ray_truncations_union (S : Finset Site) (a b : Site) :
    (⋃ N : ℕ, latticeHull S +
      (lineInterval 0 (latticeEmbedding a) 0 N + lineInterval 0 (latticeEmbedding b) 0 N)) =
        latticeHull S + forwardTwoRayCone a b := by
  rw [← line_interval_truncations_exhaust_two_ray_cone a b]
  ext x
  constructor
  · intro hx
    obtain ⟨N, u, hu, v, hv, rfl⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_add.mpr ⟨u, hu, v, Set.mem_iUnion.mpr ⟨N, hv⟩, rfl⟩
  · rintro ⟨u, hu, v, hv, rfl⟩
    obtain ⟨N, hN⟩ := Set.mem_iUnion.mp hv
    exact Set.mem_iUnion.mpr ⟨N, Set.mem_add.mpr ⟨u, hu, v, hN, rfl⟩⟩

-- translating an actual finite inward presentation translates each attained support level by the same lattice normal value.
theorem translated_finite_inward_region {I : Type*} (G : Site)
    (J : Finset I) (μ : I → Site →+ ℤ) (z : I → ℤ) :
    ({latticeEmbedding G} : Set RealPlane) + finiteInwardRegion J μ z =
      finiteInwardRegion J μ (fun i => z i + μ i G) := by
  ext x
  constructor
  · rintro ⟨u, hu, v, hv, rfl⟩ i hi
    have hu' := Set.mem_singleton_iff.mp hu
    subst hu'
    change ((z i + μ i G : ℤ) : ℝ) ≤ latticeNormal (μ i) (latticeEmbedding G + v)
    rw [Int.cast_add, map_add, latticeNormal_embedding]
    have h := hv i hi
    linarith
  · intro hx
    refine Set.mem_add.mpr ⟨latticeEmbedding G, Set.mem_singleton _, x - latticeEmbedding G, ?_, ?_⟩
    · intro i hi
      have h := hx i hi
      change ((z i + μ i G : ℤ) : ℝ) ≤ latticeNormal (μ i) x at h
      rw [Int.cast_add] at h
      rw [map_sub, latticeNormal_embedding]
      linarith
    · abel

end KumarNivat
