module

public import KumarNivat.AnchoredConstructedChain
public import KumarNivat.PrimitiveRetention
public import KumarNivat.OrbitLanguage

@[expose] public section

open Filter Topology

namespace KumarNivat

-- compactness reindexes the same actual source shifts and retains a disagreement on the fixed finite witness.
theorem AnchoredCyclicMaximalSequence.retained_orbit_limit {A : Type*}
    [TopologicalSpace A] [DiscreteTopology A] {q : ℕ} [NeZero (2 * q)]
    {c w : Site → A} {e : ZMod (2 * q) → Site} {Z : Set RealPlane} {G : Site}
    (seq : AnchoredCyclicMaximalSequence c w e Z G) (hc : (Set.range c).Finite)
    (E : Finset Site)
    (hfail : ∀ᶠ N in atTop, ∃ g ∈ E, shift (seq.sourceShift N) c g ≠ w g) :
    ∃ θ ∈ orbitClosure c, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto ((fun N => shift (seq.sourceShift N) c) ∘ φ) atTop (𝓝 θ) ∧
      (∀ g : Site, latticeEmbedding g ∈ ⋃ N, latticeHull (seq.polygon N) → θ g = w g) ∧
      ∃ g ∈ E, θ g ≠ w g := by
  obtain ⟨θ, hθ, φ, hφ, hlimit⟩ := finite_range_orbit_subsequence c hc seq.sourceShift
  let D := {g : Site | latticeEmbedding g ∈ ⋃ N, latticeHull (seq.polygon N)}
  have hagree : ∀ g ∈ D, θ g = w g := by
    apply configuration_limit_agrees_of_eventually _ θ w D hlimit
    intro g hg
    obtain ⟨N, hN⟩ := Set.mem_iUnion.mp hg
    have hsite : g ∈ seq.polygon N := seq.convex N g hN
    have hlate : ∀ᶠ m in atTop, N ≤ φ m := hφ.tendsto_atTop.eventually (eventually_ge_atTop N)
    exact hlate.mono (fun m hm => (seq.agreement (φ m)).2.2.2.2 g
      (seq.polygons_monotone hm hsite))
  have hdisagree : ∃ g ∈ E, θ g ≠ w g := configuration_limit_retains_finite_disagreement
    _ θ w E hlimit (hφ.tendsto_atTop.eventually hfail)
  exact ⟨θ, hθ, φ, hφ, hlimit, hagree, hdisagree⟩

-- the constructed chain's backwards transport proves that the retained point cannot acquire any nonzero period.
theorem AnchoredCyclicMaximalSequence.retained_nonperiodic_limit {A : Type*}
    [TopologicalSpace A] [DiscreteTopology A] {q : ℕ} [NeZero (2 * q)]
    {c w : Site → A} {e : ZMod (2 * q) → Site} {Z : Set RealPlane} {G : Site}
    (seq : AnchoredCyclicMaximalSequence c w e Z G) (hfan : AnchoredChainFanOrder e)
    (hc : (Set.range c).Finite) (hprimitive : Int.gcd (e 0).1 (e 0).2 = 1)
    (l : ℕ) (hl : 0 < l) (hperiod : IsPeriod w ((l : ℤ) • e 0))
    (hnotFull : ¬ FullyRegionallyPeriodic w {g | directionNormal (e 0) G ≤ directionNormal (e 0) g})
    (E : Finset Site) (hE : ∀ g ∈ E, directionNormal (e 0) G ≤ directionNormal (e 0) g)
    (hfail : ∀ᶠ N in atTop, ∃ g ∈ E, shift (seq.sourceShift N) c g ≠ w g) :
    ∃ θ ∈ orbitClosure c,
      (∀ g : Site, latticeEmbedding g ∈ ⋃ N, latticeHull (seq.polygon N) → θ g = w g) ∧
      (∃ g ∈ E, θ g ≠ w g) ∧ ¬ ∃ p : Site, p ≠ 0 ∧ IsPeriod θ p := by
  obtain ⟨θ, hθ, _φ, _hφ, _hlimit, hagree, hfailure⟩ := seq.retained_orbit_limit hc E hfail
  obtain ⟨b, hb₀, hbq, _hbdiv, _B, _hB, fixed, hfixed₀, _hfixed, hUnion⟩ := seq.actual_chain_union hfan
  have htravel := anchored_chain_backward_cofinal e hfan b hb₀ hbq fixed
  rw [← hUnion, hfixed₀] at htravel
  have hnot : ¬ ∃ p : Site, p ≠ 0 ∧ IsPeriod θ p :=
    nonperiodic_of_primitive_retained_disagreement θ w
      {g | latticeEmbedding g ∈ ⋃ N, latticeHull (seq.polygon N)}
        {g | directionNormal (e 0) G ≤ directionNormal (e 0) g}
      (e 0) hprimitive l hl hperiod hagree htravel hnotFull (by
        obtain ⟨g, hg, hne⟩ := hfailure
        exact ⟨g, hE g hg, hne⟩)
  exact ⟨θ, hθ, hagree, hfailure, hnot⟩

end KumarNivat
