module

public import KumarNivat.AnchoredRelaxedChainUnions
public import KumarNivat.AnchoredEnvelopeLengthsResidual
public import KumarNivat.AnchoredResidualConvexity

@[expose] public section

open Filter Topology

namespace KumarNivat

open scoped Pointwise

-- the union of the actual finite residuals retains the very same original newton hull.
theorem anchored_relaxed_regions_newton_union {n : ℕ} [NeZero n]
    (e : ZMod n → Site) (horder : CyclicEdgeOrder e) (Z : Finset Site)
    (Q : OrderedCyclicLatticePolygon e Z) (F : ℕ → Finset Site)
    (P : ∀ N, OrderedCyclicLatticePolygon e (F N))
    (hlen : ∀ N k, Q.edgeLength k ≤ (P N).edgeLength k) (i : ZMod n)
    (hbuffer : ∀ N, Q.edgeLength i + |determinant (e (i - 1)) (e (i + 1))| + 1 ≤ (P N).edgeLength i)
    (j : ℤ) (hj₀ : 0 ≤ j) (hjm : j ≤ cyclicFacetRelaxationScale e i) :
    (⋃ N, cyclicFacetRelaxedRegion e (F N) (P N) i j) =
      latticeHull Z + ⋃ N, cyclicFacetRelaxedResidual e Z (F N) Q (P N) i j := by
  have hsum (N : ℕ) := cyclic_facet_relaxed_region_minkowski e horder Z (F N) Q (P N)
    (hlen N) i j hj₀ hjm (hbuffer N)
  ext x
  constructor
  · intro hx
    obtain ⟨N, hN⟩ := Set.mem_iUnion.mp hx
    rw [hsum N] at hN
    obtain ⟨z, hz, v, hv, he⟩ := Set.mem_add.mp hN
    exact Set.mem_add.mpr ⟨z, hz, v, Set.mem_iUnion.mpr ⟨N, hv⟩, he⟩
  · intro hx
    obtain ⟨z, hz, v, hv, he⟩ := Set.mem_add.mp hx
    obtain ⟨N, hN⟩ := Set.mem_iUnion.mp hv
    apply Set.mem_iUnion.mpr
    refine ⟨N, ?_⟩
    rw [hsum N]
    exact Set.mem_add.mpr ⟨z, hz, v, hN, he⟩

-- the actual relaxed chain therefore has an explicitly constructed convex residual of the original newton hull.
theorem AnchoredCyclicMaximalSequence.relaxed_chain_original_newton_envelope {A : Type*}
    {q : ℕ} [NeZero (2 * q)] {c w : Site → A} {e : ZMod (2 * q) → Site}
    {Z : Finset Site} {G : Site} (seq : AnchoredCyclicMaximalSequence c w e (latticeHull Z) G)
    (hfan : AnchoredChainFanOrder e) (Q : OrderedCyclicLatticePolygon e Z)
    (b : ℕ) (hb₀ : 0 < b) (hbq : b < q)
    (hbdiv : Tendsto (fun N => ((seq.cyclic N).edgeLength (b : ZMod (2 * q))).toNat) atTop atTop)
    (B : Site) (hB : ∀ᶠ N in atTop, (seq.cyclic N).vertex (b : ZMod (2 * q)) = B)
    (fixed : ℕ → ℤ)
    (hfixed : ∀ i : ℕ, i ≤ b → ∀ᶠ N in atTop,
      anchoredCyclicSupport e (seq.polygon N) (seq.cyclic N) i = fixed i)
    (hbuffer : ∀ N, Q.edgeLength (b : ZMod (2 * q)) +
      |determinant (e ((b : ZMod (2 * q)) - 1)) (e ((b : ZMod (2 * q)) + 1))| + 1 ≤
        (seq.cyclic N).edgeLength (b : ZMod (2 * q)))
    (j : ℤ) (hj₀ : 0 ≤ j) (hjm : j ≤ cyclicFacetRelaxationScale e (b : ZMod (2 * q))) :
    ∃ C : Set RealPlane,
      C = convexHull ℝ (⋃ N, cyclicFacetRelaxedResidual e Z (seq.polygon N) Q (seq.cyclic N) (b : ZMod (2 * q)) j) ∧
      Convex ℝ C ∧ C.Nonempty ∧ anchoredRelaxedChainRegion e fixed b j = latticeHull Z + C := by
  have hlen : ∀ N k, Q.edgeLength k ≤ (seq.cyclic N).edgeLength k := fun N =>
    anchored_cyclic_envelope_edge_lengths e hfan.order Z (seq.polygon N) Q (seq.cyclic N) (seq.agreement N).1
  have hsum := anchored_relaxed_regions_newton_union e hfan.order Z Q seq.polygon seq.cyclic hlen
    (b : ZMod (2 * q)) hbuffer j hj₀ hjm
  rw [seq.relaxed_chain_union hfan b hb₀ hbq hbdiv B hB fixed hfixed j] at hsum
  let D : Set RealPlane := ⋃ N, cyclicFacetRelaxedResidual e Z (seq.polygon N) Q (seq.cyclic N) (b : ZMod (2 * q)) j
  have hD : D.Nonempty := by
    obtain ⟨v, hv⟩ := (cyclic_facet_relaxed_residual_geometry e Z (seq.polygon 0) Q (seq.cyclic 0)
      (b : ZMod (2 * q)) j).2.2
    exact ⟨v, Set.mem_iUnion.mpr ⟨0, hv⟩⟩
  have hR : Convex ℝ (anchoredRelaxedChainRegion e fixed b j) :=
    (finiteInwardRegion_closed_convex (Finset.range (b + 1))
      (fun i => directionNormal (e (i : ZMod (2 * q)))) (anchoredRelaxedChainCut fixed b j)).2
  refine ⟨convexHull ℝ D, rfl, convex_convexHull ℝ _, ?_, ?_⟩
  · obtain ⟨v, hv⟩ := hD
    exact ⟨v, subset_convexHull ℝ _ hv⟩
  · exact convexify_exact_minkowski_residual _ (latticeHull Z) D hR (convex_convexHull ℝ _) hsum

-- the finite natural layer range uses the same original-plane residual without an extra cast bound.
theorem AnchoredCyclicMaximalSequence.relaxed_chain_original_newton_envelope_nat {A : Type*}
    {q : ℕ} [NeZero (2 * q)] {c w : Site → A} {e : ZMod (2 * q) → Site}
    {Z : Finset Site} {G : Site} (seq : AnchoredCyclicMaximalSequence c w e (latticeHull Z) G)
    (hfan : AnchoredChainFanOrder e) (Q : OrderedCyclicLatticePolygon e Z)
    (b : ℕ) (hb₀ : 0 < b) (hbq : b < q)
    (hbdiv : Tendsto (fun N => ((seq.cyclic N).edgeLength (b : ZMod (2 * q))).toNat) atTop atTop)
    (B : Site) (hB : ∀ᶠ N in atTop, (seq.cyclic N).vertex (b : ZMod (2 * q)) = B)
    (fixed : ℕ → ℤ)
    (hfixed : ∀ i : ℕ, i ≤ b → ∀ᶠ N in atTop,
      anchoredCyclicSupport e (seq.polygon N) (seq.cyclic N) i = fixed i)
    (hbuffer : ∀ N, Q.edgeLength (b : ZMod (2 * q)) +
      |determinant (e ((b : ZMod (2 * q)) - 1)) (e ((b : ZMod (2 * q)) + 1))| + 1 ≤
        (seq.cyclic N).edgeLength (b : ZMod (2 * q)))
    (j : ℕ) (hj : j ≤ (cyclicFacetRelaxationScale e (b : ZMod (2 * q))).toNat) :
    ∃ C : Set RealPlane,
      C = convexHull ℝ (⋃ N, cyclicFacetRelaxedResidual e Z (seq.polygon N) Q (seq.cyclic N) (b : ZMod (2 * q)) (j : ℤ)) ∧
      Convex ℝ C ∧ C.Nonempty ∧ anchoredRelaxedChainRegion e fixed b (j : ℤ) = latticeHull Z + C := by
  have hM := cyclic_facet_relaxation_scale_positive e hfan.order (b : ZMod (2 * q))
  have hjM : (j : ℤ) ≤ cyclicFacetRelaxationScale e (b : ZMod (2 * q)) := by omega
  exact seq.relaxed_chain_original_newton_envelope hfan Q b hb₀ hbq hbdiv B hB fixed hfixed hbuffer
    (j : ℤ) (Int.natCast_nonneg j) hjM

end KumarNivat
