import KumarNivat.AnchoredChainSupports
import KumarNivat.AnchoredChainSelection
import KumarNivat.AnchoredRegionUnions
import KumarNivat.InwardBackwardCofinality

open Filter Topology

namespace KumarNivat

open scoped Pointwise

-- actual nested hulls make every attained supporting level nonincreasing.
theorem anchored_cyclic_support_antitone {n : ℕ} [NeZero n]
    (e : ZMod n → Site) (horder : CyclicEdgeOrder e)
    (F : ℕ → Finset Site) (P : ∀ N, OrderedCyclicLatticePolygon e (F N))
    (hmono : Monotone (fun N => latticeHull (F N))) :
    ∀ i : ℕ, Antitone (fun N => anchoredCyclicSupport e (F N) (P N) i) := by
  intro i N M hNM
  have hvertex : latticeEmbedding ((P N).vertex (i : ZMod n)) ∈ latticeHull (F N) :=
    subset_convexHull ℝ _ ⟨(P N).vertex (i : ZMod n), (P N).vertex_mem _, rfl⟩
  have hpoint := hmono hNM hvertex
  change latticeEmbedding ((P N).vertex (i : ZMod n)) ∈ latticeHull (F M) at hpoint
  rw [(P M).hull_eq, ordered_cyclic_walk_facet_presentation e horder
    (P M).vertex (P M).edgeLength (P M).length_pos (P M).edge_eq] at hpoint
  have hbound := hpoint (i : ZMod n)
  rw [latticeNormal_embedding] at hbound
  exact_mod_cast hbound

-- the actual vertices before the first unbounded edge stabilize all of the surviving support lines.
theorem anchored_chain_surviving_supports_fixed {n : ℕ} [NeZero n]
    (e : ZMod n → Site) (F : ℕ → Finset Site) (P : ∀ N, OrderedCyclicLatticePolygon e (F N))
    (G : Site) (hanchor : ∀ N, (P N).vertex 1 = G) (b : ℕ)
    (hstable : ∀ j : ℕ, 0 < j → j < b → ∃ r : ℤ,
      ∀ᶠ N in atTop, (P N).edgeLength (j : ZMod n) = r) :
    ∃ fixed : ℕ → ℤ, fixed 0 = directionNormal (e 0) G ∧
      ∀ i : ℕ, i ≤ b → ∀ᶠ N in atTop, anchoredCyclicSupport e (F N) (P N) i = fixed i := by
  classical
  have hex : ∀ i : ℕ, ∃ c : ℤ, (i = 0 → c = directionNormal (e 0) G) ∧
      (i ≤ b → ∀ᶠ N in atTop, anchoredCyclicSupport e (F N) (P N) i = c) := by
    intro i
    by_cases hi : i = 0
    · subst i
      refine ⟨directionNormal (e 0) G, fun _ => rfl, fun _ => Eventually.of_forall ?_⟩
      intro N
      simpa only [anchoredCyclicSupport, Nat.cast_zero] using anchored_initial_support_fixed e F P G hanchor N
    · by_cases hib : i ≤ b
      · obtain ⟨B, hB⟩ := anchored_chain_vertex_stabilizes e F P G hanchor i (by omega)
          (fun j hj₀ hji => hstable j hj₀ (by omega))
        exact ⟨directionNormal (e (i : ZMod n)) B, fun h => False.elim (hi h),
          fun _ => hB.mono (fun N hN => by simp only [anchoredCyclicSupport, hN])⟩
      · exact ⟨0, fun h => False.elim (hi h), fun h => False.elim (hib h)⟩
  choose fixed hfixed using hex
  exact ⟨fixed, hfixed 0 |>.1 rfl, fun i hi => (hfixed i).2 hi⟩

-- stabilized actual supports are lower bounds at every earlier stage of the nested sequence.
theorem antitone_support_fixed_lower_bound (z : ℕ → ℤ) (hz : Antitone z) (c : ℤ)
    (hc : ∀ᶠ N in atTop, z N = c) : ∀ N, c ≤ z N := by
  intro N
  obtain ⟨M, hMc, hNM⟩ := (hc.and (eventually_ge_atTop N)).exists
  have hle := hz hNM
  rwa [hMc] at hle

-- the selected anchored union is exactly the surviving finite inward chain, derived from the actual width and edge lengths.
theorem anchored_actual_chain_union {q : ℕ} [NeZero (2 * q)]
    (e : ZMod (2 * q) → Site) (hfan : AnchoredChainFanOrder e)
    (F : ℕ → Finset Site) (P : ∀ N, OrderedCyclicLatticePolygon e (F N))
    (G : Site) (hanchor : ∀ N, (P N).vertex 1 = G)
    (hmono : ∀ N M, N ≤ M → ∀ i, (P N).edgeLength i ≤ (P M).edgeLength i)
    (ha : Tendsto (fun N => ((P N).edgeLength 0).toNat) atTop atTop)
    (hwidth : Tendsto (fun N => ((directionNormal (e 0) ((P N).vertex (q : ZMod (2 * q))) -
      directionNormal (e 0) G : ℤ) : ℝ)) atTop atTop) :
    ∃ b : ℕ, 0 < b ∧ b < q ∧
      Tendsto (fun N => ((P N).edgeLength (b : ZMod (2 * q))).toNat) atTop atTop ∧
      ∃ B : Site, (∀ᶠ N in atTop, (P N).vertex (b : ZMod (2 * q)) = B) ∧
      ∃ fixed : ℕ → ℤ, fixed 0 = directionNormal (e 0) G ∧
        (∀ i : ℕ, i ≤ b → ∀ᶠ N in atTop, anchoredCyclicSupport e (F N) (P N) i = fixed i) ∧
        (⋃ N, latticeHull (F N)) = finiteInwardRegion (Finset.range (b + 1))
          (fun i => directionNormal (e (i : ZMod (2 * q)))) fixed := by
  classical
  obtain ⟨b, hb₀, hbq, hbdiv, hstable⟩ :=
    anchored_actual_width_selects_first_unbounded e F P G hanchor hmono hwidth
  obtain ⟨B, hB⟩ := anchored_chain_vertex_stabilizes e F P G hanchor b hb₀ hstable
  obtain ⟨fixed, hfixed₀, hfixed⟩ := anchored_chain_surviving_supports_fixed e F P G hanchor b hstable
  have hhulls := anchored_cyclic_sequence_hulls_monotone e hfan.order F P G hanchor hmono
  have hcuts := anchored_cyclic_support_antitone e hfan.order F P hhulls
  have hlevels : ∀ N, ∀ i ∈ Finset.range (b + 1), fixed i ≤ anchoredCyclicSupport e (F N) (P N) i := by
    intro N i hi
    exact antitone_support_fixed_lower_bound _ (hcuts i) (fixed i) (hfixed i (by
      have h := Finset.mem_range.mp hi
      omega)) N
  have hstabilized : ∀ i ∈ Finset.range (b + 1), ∀ᶠ N in atTop,
      anchoredCyclicSupport e (F N) (P N) i = fixed i :=
    fun i hi => hfixed i (by have h := Finset.mem_range.mp hi; omega)
  have hescape : ∀ i ∈ Finset.range (2 * q), i ∉ Finset.range (b + 1) →
      Tendsto (fun N => (anchoredCyclicSupport e (F N) (P N) i : ℝ)) atTop atBot := by
    intro i hi hnot
    apply anchored_chain_removed_supports_escape e hfan F P G hanchor ha b hb₀ hbq hbdiv B hB i
    · have h : ¬ i < b + 1 := fun hi => hnot (Finset.mem_range.mpr hi)
      omega
    · exact Finset.mem_range.mp hi
  have hsub : Finset.range (b + 1) ⊆ Finset.range (2 * q) := by
    intro i hi
    apply Finset.mem_range.mpr
    have h := Finset.mem_range.mp hi
    omega
  refine ⟨b, hb₀, hbq, hbdiv, B, hB, fixed, hfixed₀, hfixed, ?_⟩
  have hpoly : (fun N => latticeHull (F N)) = (fun N => finiteInwardRegion (Finset.range (2 * q))
      (fun i => directionNormal (e (i : ZMod (2 * q)))) (anchoredCyclicSupport e (F N) (P N))) := by
    funext N
    exact anchored_cyclic_hull_nat_facets e hfan.order (F N) (P N)
  rw [hpoly]
  exact finite_inward_region_union (Finset.range (2 * q)) (Finset.range (b + 1)) hsub
    (fun i => directionNormal (e (i : ZMod (2 * q))))
    (fun N => anchoredCyclicSupport e (F N) (P N)) fixed hlevels hstabilized hescape

-- the finite chain has exactly the reference half-plane normal plus strictly inward normals for backwards travel.
theorem anchored_chain_region_eq_inward_halfplane {q : ℕ} [NeZero (2 * q)]
    (e : ZMod (2 * q) → Site) (b : ℕ) (fixed : ℕ → ℤ) :
    finiteInwardRegion (Finset.range (b + 1)) (fun i => directionNormal (e (i : ZMod (2 * q)))) fixed =
      inwardLayerRegion (directionNormal (e 0)) (fixed 0) (Finset.Icc 1 b)
        (fun i => directionNormal (e (i : ZMod (2 * q)))) fixed := by
  ext x
  constructor
  · intro hx
    refine ⟨by simpa only [Nat.cast_zero] using hx 0 (Finset.mem_range.mpr (by omega)), ?_⟩
    intro i hi
    obtain ⟨_hil, hir⟩ := Finset.mem_Icc.mp hi
    exact hx i (Finset.mem_range.mpr (by omega))
  · intro hx i hi
    by_cases hzero : i = 0
    · subst i
      simpa only [Nat.cast_zero] using hx.1
    · have hbound := Finset.mem_range.mp hi
      exact hx.2 i (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)

-- the actual surviving signs give uniform backwards transport for every finite subset of the reference half-plane.
theorem anchored_chain_uniform_backward_transport {q : ℕ} [NeZero (2 * q)]
    (e : ZMod (2 * q) → Site) (hfan : AnchoredChainFanOrder e)
    (b : ℕ) (hb₀ : 0 < b) (hbq : b < q) (fixed : ℕ → ℤ)
    (S : Finset Site) (hS : ∀ g ∈ S, fixed 0 ≤ directionNormal (e 0) g) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ g ∈ S,
      latticeEmbedding (g - (n : ℤ) • e 0) ∈ finiteInwardRegion (Finset.range (b + 1))
        (fun i => directionNormal (e (i : ZMod (2 * q)))) fixed := by
  rw [anchored_chain_region_eq_inward_halfplane]
  apply uniform_backward_translation_into_inward_region (e 0) (fixed 0) (Finset.Icc 1 b)
    (fun i => directionNormal (e (i : ZMod (2 * q)))) fixed _ S hS
  intro i hi
  obtain ⟨hil, hir⟩ := Finset.mem_Icc.mp hi
  exact (anchored_chain_surviving_normal_signs e hfan b hb₀ hbq i hir).2.2 (by omega)

-- the same proved inward signs give the retained-disagreement theorem its actual backward cofinality.
theorem anchored_chain_backward_cofinal {q : ℕ} [NeZero (2 * q)]
    (e : ZMod (2 * q) → Site) (hfan : AnchoredChainFanOrder e)
    (b : ℕ) (hb₀ : 0 < b) (hbq : b < q) (fixed : ℕ → ℤ) :
    BackwardCofinal {g : Site | latticeEmbedding g ∈ finiteInwardRegion (Finset.range (b + 1))
      (fun i => directionNormal (e (i : ZMod (2 * q)))) fixed}
      {g | fixed 0 ≤ directionNormal (e 0) g} (e 0) := by
  rw [anchored_chain_region_eq_inward_halfplane]
  apply backward_cofinal_inward_region (e 0) (fixed 0) (Finset.Icc 1 b)
    (fun i => directionNormal (e (i : ZMod (2 * q)))) fixed
  intro i hi
  obtain ⟨hil, hir⟩ := Finset.mem_Icc.mp hi
  exact (anchored_chain_surviving_normal_signs e hfan b hb₀ hbq i hir).2.2 (by omega)

-- the same constructed chain retains every exact original newton summand of its actual polygons.
theorem anchored_chain_union_retains_newton_summand (F : ℕ → Finset Site) (Z : Set RealPlane)
    (henvelope : ∀ N, ∃ C : Set RealPlane, latticeHull (F N) = Z + C) :
    ∃ C : Set RealPlane, (⋃ N, latticeHull (F N)) = Z + C := by
  choose C hC using henvelope
  exact ⟨⋃ N, C N, minkowski_summand_of_anchored_union F Z C hC⟩

end KumarNivat
