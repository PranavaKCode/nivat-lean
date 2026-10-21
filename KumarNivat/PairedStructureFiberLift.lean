module

public import KumarNivat.PairedStructureFiberLimits

@[expose] public section

open Filter Topology

namespace KumarNivat

-- a prescribed orbit point lifts to a complete fiber family while every finite-patch separation survives.
theorem exists_binomial_fiber_lift_with_separation {K I : Type*} [CommRing K] [Finite I]
    [TopologicalSpace K] [DiscreteTopology K] (c : Site → K) (hc : (Set.range c).Finite)
    (q : I → Site → K) (hmem : ∀ i, q i ∈ orbitClosure c) (p : Site)
    (hfilter : ∀ i j, difference p (q i) = difference p (q j)) (B : Finset Site)
    (hsep : ∀ i j : I, i ≠ j → ∀ t : Site, ∃ u ∈ B, q i (t + u) ≠ q j (t + u))
    (i₀ : I) (x : Site → K) (hx : x ∈ orbitClosure (q i₀)) :
    ∃ e : I → Site → K, e i₀ = x ∧ (∀ i, e i ∈ orbitClosure c) ∧
      (∀ i j, difference p (e i) = difference p (e j)) ∧
      ∀ i j : I, i ≠ j → ∀ t : Site, ∃ u ∈ B, e i (t + u) ≠ e j (t + u) := by
  obtain ⟨u, hu⟩ := shifts_tendsto_prescribed_orbit_point (q i₀) x hx
  obtain ⟨e, he, φ, hφ, hlimit⟩ := finite_orbit_family_joint_subsequence c hc q hmem u
  have he₀ : e i₀ = x := tendsto_nhds_unique (hlimit i₀) (hu.comp hφ.tendsto_atTop)
  have hefilter (i j : I) : difference p (e i) = difference p (e j) := by
    apply difference_outputs_equal_of_limits _ _ _ _ _ (hlimit i) (hlimit j)
    intro n
    rw [Function.comp_apply, Function.comp_apply, difference_shift_configuration,
      difference_shift_configuration, hfilter i j]
  refine ⟨e, he₀, he, hefilter, ?_⟩
  intro i j hij t
  let E := B.image (fun z => t + z)
  have hfail : ∀ᶠ n in atTop, ∃ g ∈ E,
      shift (u (φ n)) (q i) g ≠ shift (u (φ n)) (q j) g := by
    apply Eventually.of_forall
    intro n
    obtain ⟨z, hz, hne⟩ := hsep i j hij (t + u (φ n))
    refine ⟨t + z, Finset.mem_image.mpr ⟨z, hz, rfl⟩, ?_⟩
    simpa only [shift, add_assoc, add_comm, add_left_comm] using hne
  obtain ⟨g, hg, hne⟩ := configuration_limits_retain_finite_disagreement
    ((fun n => shift (u n) (q i)) ∘ φ) ((fun n => shift (u n) (q j)) ∘ φ)
    (e i) (e j) E (hlimit i) (hlimit j) hfail
  obtain ⟨z, hz, heq⟩ := Finset.mem_image.mp hg
  exact ⟨z, hz, by simpa only [heq] using hne⟩

end KumarNivat
