import KumarNivat.AnchoredActualSequences
import KumarNivat.AnchoredIntegerExpansionLayers

open Filter Topology

namespace KumarNivat

-- the selected chain keeps every old support except for the named relaxed facet.
def anchoredRelaxedChainCut (fixed : ℕ → ℤ) (b : ℕ) (j : ℤ) (i : ℕ) : ℤ :=
  fixed i - if i = b then j else 0

-- this is the actual finite inward chain with precisely that single changed support.
def anchoredRelaxedChainRegion {q : ℕ} [NeZero (2 * q)]
    (e : ZMod (2 * q) → Site) (fixed : ℕ → ℤ) (b : ℕ) (j : ℤ) : Set RealPlane :=
  finiteInwardRegion (Finset.range (b + 1))
    (fun i => directionNormal (e (i : ZMod (2 * q)))) (anchoredRelaxedChainCut fixed b j)

-- natural indices below the modulus give the exact changed-cut presentation of each actual relaxation.
theorem cyclic_facet_relaxed_region_nat_facets {n : ℕ} [NeZero n]
    (e : ZMod n → Site) (F : Finset Site) (P : OrderedCyclicLatticePolygon e F)
    (b : ℕ) (hbn : b < n) (j : ℤ) :
    cyclicFacetRelaxedRegion e F P (b : ZMod n) j =
      finiteInwardRegion (Finset.range n) (fun i => directionNormal (e (i : ZMod n)))
        (anchoredRelaxedChainCut (anchoredCyclicSupport e F P) b j) := by
  have hinj (i : ℕ) (hi : i < n) : (i : ZMod n) = (b : ZMod n) ↔ i = b := by
    constructor
    · intro he
      have hv := congrArg ZMod.val he
      rwa [ZMod.val_natCast_of_lt hi, ZMod.val_natCast_of_lt hbn] at hv
    · rintro rfl
      rfl
  ext x
  constructor
  · intro hx i hi
    have hb := hx (i : ZMod n) (Finset.mem_univ _)
    have hie := hinj i (Finset.mem_range.mp hi)
    simpa only [cyclicFacetRelaxedCut, anchoredRelaxedChainCut, anchoredCyclicSupport, hie] using hb
  · intro hx k _hk
    have hb := hx k.val (Finset.mem_range.mpr (ZMod.val_lt k))
    have hke : k.val = b ↔ k = (b : ZMod n) := by
      simpa only [ZMod.natCast_zmod_val] using (hinj k.val (ZMod.val_lt k)).symm
    simpa only [cyclicFacetRelaxedCut, anchoredRelaxedChainCut, anchoredCyclicSupport,
      ZMod.natCast_zmod_val, hke] using hb

-- the same long actual edges remove all omitted supports after any fixed integer relaxation.
theorem anchored_actual_relaxed_chain_union {q : ℕ} [NeZero (2 * q)]
    (e : ZMod (2 * q) → Site) (hfan : AnchoredChainFanOrder e)
    (F : ℕ → Finset Site) (P : ∀ N, OrderedCyclicLatticePolygon e (F N))
    (G : Site) (hanchor : ∀ N, (P N).vertex 1 = G)
    (hmono : ∀ N M, N ≤ M → ∀ i, (P N).edgeLength i ≤ (P M).edgeLength i)
    (ha : Tendsto (fun N => ((P N).edgeLength 0).toNat) atTop atTop)
    (b : ℕ) (hb₀ : 0 < b) (hbq : b < q)
    (hbdiv : Tendsto (fun N => ((P N).edgeLength (b : ZMod (2 * q))).toNat) atTop atTop)
    (B : Site) (hB : ∀ᶠ N in atTop, (P N).vertex (b : ZMod (2 * q)) = B)
    (fixed : ℕ → ℤ)
    (hfixed : ∀ i : ℕ, i ≤ b → ∀ᶠ N in atTop, anchoredCyclicSupport e (F N) (P N) i = fixed i)
    (j : ℤ) :
    (⋃ N, cyclicFacetRelaxedRegion e (F N) (P N) (b : ZMod (2 * q)) j) =
      anchoredRelaxedChainRegion e fixed b j := by
  have hhulls := anchored_cyclic_sequence_hulls_monotone e hfan.order F P G hanchor hmono
  have hcuts := anchored_cyclic_support_antitone e hfan.order F P hhulls
  have hsub : Finset.range (b + 1) ⊆ Finset.range (2 * q) := by
    intro i hi
    apply Finset.mem_range.mpr
    have h := Finset.mem_range.mp hi
    omega
  have hlevels : ∀ N, ∀ i ∈ Finset.range (b + 1),
      anchoredRelaxedChainCut fixed b j i ≤
        anchoredRelaxedChainCut (anchoredCyclicSupport e (F N) (P N)) b j i := by
    intro N i hi
    have hib : i ≤ b := by have h := Finset.mem_range.mp hi; omega
    exact sub_le_sub_right
      (antitone_support_fixed_lower_bound _ (hcuts i) (fixed i) (hfixed i hib) N) _
  have hstabilized : ∀ i ∈ Finset.range (b + 1), ∀ᶠ N in atTop,
      anchoredRelaxedChainCut (anchoredCyclicSupport e (F N) (P N)) b j i = anchoredRelaxedChainCut fixed b j i := by
    intro i hi
    have hib : i ≤ b := by have h := Finset.mem_range.mp hi; omega
    exact (hfixed i hib).mono (fun N hN => by simp only [anchoredRelaxedChainCut, hN])
  have hescape : ∀ i ∈ Finset.range (2 * q), i ∉ Finset.range (b + 1) →
      Tendsto (fun N => (anchoredRelaxedChainCut (anchoredCyclicSupport e (F N) (P N)) b j i : ℝ)) atTop atBot := by
    intro i hi hnot
    have hbi : b < i := by
      have hn : ¬ i < b + 1 := fun h => hnot (Finset.mem_range.mpr h)
      omega
    have hne : i ≠ b := by omega
    simpa only [anchoredRelaxedChainCut, ite_eq_right hne, sub_zero] using
      anchored_chain_removed_supports_escape e hfan F P G hanchor ha b hb₀ hbq hbdiv B hB i hbi (Finset.mem_range.mp hi)
  have hpresentation : (fun N => cyclicFacetRelaxedRegion e (F N) (P N) (b : ZMod (2 * q)) j) =
      (fun N => finiteInwardRegion (Finset.range (2 * q))
        (fun i => directionNormal (e (i : ZMod (2 * q))))
        (anchoredRelaxedChainCut (anchoredCyclicSupport e (F N) (P N)) b j)) := by
    funext N
    exact cyclic_facet_relaxed_region_nat_facets e (F N) (P N) b (by omega) j
  rw [hpresentation]
  exact finite_inward_region_union (Finset.range (2 * q)) (Finset.range (b + 1)) hsub
    (fun i => directionNormal (e (i : ZMod (2 * q))))
    (fun N => anchoredRelaxedChainCut (anchoredCyclicSupport e (F N) (P N)) b j)
    (anchoredRelaxedChainCut fixed b j) hlevels hstabilized hescape

-- the actual maximal sequence uses its own anchor, nesting and tangent growth in that exact union calculation.
theorem AnchoredCyclicMaximalSequence.relaxed_chain_union {A : Type*} {q : ℕ} [NeZero (2 * q)]
    {c w : Site → A} {e : ZMod (2 * q) → Site} {Z : Set RealPlane} {G : Site}
    (seq : AnchoredCyclicMaximalSequence c w e Z G) (hfan : AnchoredChainFanOrder e)
    (b : ℕ) (hb₀ : 0 < b) (hbq : b < q)
    (hbdiv : Tendsto (fun N => ((seq.cyclic N).edgeLength (b : ZMod (2 * q))).toNat) atTop atTop)
    (B : Site) (hB : ∀ᶠ N in atTop, (seq.cyclic N).vertex (b : ZMod (2 * q)) = B)
    (fixed : ℕ → ℤ)
    (hfixed : ∀ i : ℕ, i ≤ b → ∀ᶠ N in atTop,
      anchoredCyclicSupport e (seq.polygon N) (seq.cyclic N) i = fixed i) (j : ℤ) :
    (⋃ N, cyclicFacetRelaxedRegion e (seq.polygon N) (seq.cyclic N) (b : ZMod (2 * q)) j) =
      anchoredRelaxedChainRegion e fixed b j :=
  anchored_actual_relaxed_chain_union e hfan seq.polygon seq.cyclic G seq.anchor
    (fun _N _M hNM i => seq.lengths_monotone hNM i) seq.tangent_diverges b hb₀ hbq hbdiv B hB fixed hfixed j

-- relaxing a later chain facet preserves the exact reference half-plane inequality.
theorem anchored_relaxed_chain_keeps_reference_halfplane {q : ℕ} [NeZero (2 * q)]
    (e : ZMod (2 * q) → Site) (fixed : ℕ → ℤ) (b : ℕ) (hb₀ : 0 < b) (j : ℤ) :
    anchoredRelaxedChainRegion e fixed b j ⊆
      {x : RealPlane | (fixed 0 : ℝ) ≤ latticeNormal (directionNormal (e 0)) x} := by
  intro x hx
  change (fixed 0 : ℝ) ≤ latticeNormal (directionNormal (e 0)) x
  have h0 := hx 0 (Finset.mem_range.mpr (by omega))
  simpa only [anchoredRelaxedChainCut, ite_eq_right (by omega : (0 : ℕ) ≠ b), sub_zero, Nat.cast_zero] using h0

-- the same actual inward signs give each relaxed chain backwards cofinality in the original half-plane.
theorem anchored_relaxed_chain_backward_cofinal {q : ℕ} [NeZero (2 * q)]
    (e : ZMod (2 * q) → Site) (hfan : AnchoredChainFanOrder e)
    (fixed : ℕ → ℤ) (b : ℕ) (hb₀ : 0 < b) (hbq : b < q) (j : ℤ) :
    BackwardCofinal {g : Site | latticeEmbedding g ∈ anchoredRelaxedChainRegion e fixed b j}
      {g | fixed 0 ≤ directionNormal (e 0) g} (e 0) := by
  simpa only [anchoredRelaxedChainRegion, anchoredRelaxedChainCut,
    ite_eq_right (by omega : (0 : ℕ) ≠ b), sub_zero] using
    anchored_chain_backward_cofinal e hfan b hb₀ hbq (anchoredRelaxedChainCut fixed b j)

-- one backwards threshold places every site of any finite reference-half-plane set in the actual relaxed chain.
theorem anchored_relaxed_chain_uniform_backward_transport {q : ℕ} [NeZero (2 * q)]
    (e : ZMod (2 * q) → Site) (hfan : AnchoredChainFanOrder e)
    (fixed : ℕ → ℤ) (b : ℕ) (hb₀ : 0 < b) (hbq : b < q) (j : ℤ)
    (S : Finset Site) (hS : ∀ g ∈ S, fixed 0 ≤ directionNormal (e 0) g) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ g ∈ S,
      latticeEmbedding (g - (n : ℤ) • e 0) ∈ anchoredRelaxedChainRegion e fixed b j := by
  have hS' : ∀ g ∈ S, anchoredRelaxedChainCut fixed b j 0 ≤ directionNormal (e 0) g := by
    simpa only [anchoredRelaxedChainCut, ite_eq_right (by omega : (0 : ℕ) ≠ b), sub_zero] using hS
  exact anchored_chain_uniform_backward_transport e hfan b hb₀ hbq (anchoredRelaxedChainCut fixed b j) S hS'

-- the exact union calculation carries its original half-plane and backwards cofinality along with it.
theorem AnchoredCyclicMaximalSequence.relaxed_chain_geometry {A : Type*} {q : ℕ} [NeZero (2 * q)]
    {c w : Site → A} {e : ZMod (2 * q) → Site} {Z : Set RealPlane} {G : Site}
    (seq : AnchoredCyclicMaximalSequence c w e Z G) (hfan : AnchoredChainFanOrder e)
    (b : ℕ) (hb₀ : 0 < b) (hbq : b < q)
    (hbdiv : Tendsto (fun N => ((seq.cyclic N).edgeLength (b : ZMod (2 * q))).toNat) atTop atTop)
    (B : Site) (hB : ∀ᶠ N in atTop, (seq.cyclic N).vertex (b : ZMod (2 * q)) = B)
    (fixed : ℕ → ℤ)
    (hfixed : ∀ i : ℕ, i ≤ b → ∀ᶠ N in atTop,
      anchoredCyclicSupport e (seq.polygon N) (seq.cyclic N) i = fixed i) (j : ℤ) :
    (⋃ N, cyclicFacetRelaxedRegion e (seq.polygon N) (seq.cyclic N) (b : ZMod (2 * q)) j) =
        anchoredRelaxedChainRegion e fixed b j ∧
      (⋃ N, cyclicFacetRelaxedRegion e (seq.polygon N) (seq.cyclic N) (b : ZMod (2 * q)) j) ⊆
        {x : RealPlane | (fixed 0 : ℝ) ≤ latticeNormal (directionNormal (e 0)) x} ∧
      BackwardCofinal {g : Site | latticeEmbedding g ∈
        ⋃ N, cyclicFacetRelaxedRegion e (seq.polygon N) (seq.cyclic N) (b : ZMod (2 * q)) j}
        {g | fixed 0 ≤ directionNormal (e 0) g} (e 0) := by
  have hUnion := seq.relaxed_chain_union hfan b hb₀ hbq hbdiv B hB fixed hfixed j
  refine ⟨hUnion, ?_, ?_⟩
  · rw [hUnion]
    exact anchored_relaxed_chain_keeps_reference_halfplane e fixed b hb₀ j
  · rw [hUnion]
    exact anchored_relaxed_chain_backward_cofinal e hfan fixed b hb₀ hbq j

-- finite backwards transport lands in the union of the actual relaxed polygons themselves.
theorem AnchoredCyclicMaximalSequence.relaxed_chain_uniform_backward_transport {A : Type*}
    {q : ℕ} [NeZero (2 * q)] {c w : Site → A} {e : ZMod (2 * q) → Site}
    {Z : Set RealPlane} {G : Site} (seq : AnchoredCyclicMaximalSequence c w e Z G)
    (hfan : AnchoredChainFanOrder e) (b : ℕ) (hb₀ : 0 < b) (hbq : b < q)
    (hbdiv : Tendsto (fun N => ((seq.cyclic N).edgeLength (b : ZMod (2 * q))).toNat) atTop atTop)
    (B : Site) (hB : ∀ᶠ N in atTop, (seq.cyclic N).vertex (b : ZMod (2 * q)) = B)
    (fixed : ℕ → ℤ)
    (hfixed : ∀ i : ℕ, i ≤ b → ∀ᶠ N in atTop,
      anchoredCyclicSupport e (seq.polygon N) (seq.cyclic N) i = fixed i)
    (j : ℤ) (S : Finset Site) (hS : ∀ g ∈ S, fixed 0 ≤ directionNormal (e 0) g) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ g ∈ S,
      latticeEmbedding (g - (n : ℤ) • e 0) ∈
        ⋃ M, cyclicFacetRelaxedRegion e (seq.polygon M) (seq.cyclic M) (b : ZMod (2 * q)) j := by
  rw [seq.relaxed_chain_union hfan b hb₀ hbq hbdiv B hB fixed hfixed j]
  exact anchored_relaxed_chain_uniform_backward_transport e hfan fixed b hb₀ hbq j S hS

end KumarNivat
