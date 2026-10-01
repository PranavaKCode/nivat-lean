import KumarNivat.PolyhedralRays
import KumarNivat.PrimitiveRetention

namespace KumarNivat

-- the actual inward slopes give one backward translation threshold for every site of a prescribed finite subset of the reference half-plane.
theorem uniform_backward_translation_into_inward_region {I : Type*} (a : Site) (cut : ℤ)
    (J : Finset I) (μ : I → Site →+ ℤ) (z : I → ℤ)
    (hμ : ∀ i ∈ J, 0 < μ i (-a)) (S : Finset Site)
    (hS : ∀ g ∈ S, cut ≤ directionNormal a g) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ g ∈ S,
      latticeEmbedding (g - (n : ℤ) • a) ∈ inwardLayerRegion (directionNormal a) cut J μ z := by
  obtain ⟨N, hN, hfixed⟩ := eventually_translated_window_in_fixed_halfplanes J μ z S 0 (-a) hμ
  have hnormal : directionNormal a a = 0 := by simp [directionNormal, determinant, mul_comm]
  refine ⟨N.toNat, ?_⟩
  intro n hn g hg
  apply (mem_inwardLayerRegion_lattice (directionNormal a) cut J μ z _).mpr
  refine ⟨?_, ?_⟩
  · rw [map_sub, map_zsmul, hnormal, smul_zero, sub_zero]
    exact hS g hg
  · have hn' : N ≤ (n : ℤ) := by omega
    have he : g - (n : ℤ) • a = 0 + (n : ℤ) • (-a) + g := by
      rw [smul_neg]
      abel
    rw [he]
    exact hfixed (n : ℤ) hn' g hg

-- the finite-set transport implies the same backward cofinality used by the retained-disagreement theorem.
theorem backward_cofinal_inward_region {I : Type*} (a : Site) (cut : ℤ)
    (J : Finset I) (μ : I → Site →+ ℤ) (z : I → ℤ)
    (hμ : ∀ i ∈ J, 0 < μ i (-a)) :
    BackwardCofinal {g | latticeEmbedding g ∈ inwardLayerRegion (directionNormal a) cut J μ z}
      {g | cut ≤ directionNormal a g} a := by
  classical
  intro g hg
  obtain ⟨N, hN⟩ := uniform_backward_translation_into_inward_region a cut J μ z hμ {g}
    (fun u hu => Finset.mem_singleton.mp hu ▸ hg)
  exact ⟨N, fun n hn => hN n hn g (Finset.mem_singleton_self g)⟩

end KumarNivat
