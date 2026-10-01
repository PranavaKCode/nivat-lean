import KumarNivat.AnchoredActualSequences
import KumarNivat.AnchoredCyclicFacesRelaxation

open Filter Topology

namespace KumarNivat

-- a subsequence carries the same actual polygons, source shifts and maximality witnesses.
def AnchoredCyclicMaximalSequence.reindex {A : Type*} {q : ℕ} [NeZero (2 * q)]
    {c w : Site → A} {e : ZMod (2 * q) → Site} {Z : Set RealPlane} {G : Site}
    (seq : AnchoredCyclicMaximalSequence c w e Z G) (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    AnchoredCyclicMaximalSequence c w e Z G where
  base := seq.base ∘ φ
  polygon := seq.polygon ∘ φ
  sourceShift := seq.sourceShift ∘ φ
  cyclic N := seq.cyclic (φ N)
  anchor N := seq.anchor (φ N)
  convex N := seq.convex (φ N)
  base_convex N := seq.base_convex (φ N)
  base_envelope N := seq.base_envelope (φ N)
  agreement N := seq.agreement (φ N)
  maximal N := seq.maximal (φ N)
  lengths_monotone := seq.lengths_monotone.comp hφ.monotone
  polygons_monotone := seq.polygons_monotone.comp hφ.monotone
  tangent_diverges := seq.tangent_diverges.comp hφ.tendsto_atTop
  width_diverges := seq.width_diverges.comp hφ.tendsto_atTop

-- discarding a finite prefix changes no reference phase, polygon witness or source equation.
def AnchoredCyclicMaximalSequence.tail {A : Type*} {q : ℕ} [NeZero (2 * q)]
    {c w : Site → A} {e : ZMod (2 * q) → Site} {Z : Set RealPlane} {G : Site}
    (seq : AnchoredCyclicMaximalSequence c w e Z G) (d : ℕ) :
    AnchoredCyclicMaximalSequence c w e Z G :=
  seq.reindex (fun N => N + d) (by intro N M hNM; change N + d < M + d; omega)

-- cofinal reindexing preserves the entire actual real polygon union.
theorem AnchoredCyclicMaximalSequence.reindex_hull_union {A : Type*} {q : ℕ} [NeZero (2 * q)]
    {c w : Site → A} {e : ZMod (2 * q) → Site} {Z : Set RealPlane} {G : Site}
    (seq : AnchoredCyclicMaximalSequence c w e Z G) (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    (⋃ N, latticeHull ((seq.reindex φ hφ).polygon N)) = ⋃ N, latticeHull (seq.polygon N) := by
  ext x
  constructor
  · intro hx
    obtain ⟨N, hN⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨φ N, hN⟩
  · intro hx
    obtain ⟨N, hN⟩ := Set.mem_iUnion.mp hx
    apply Set.mem_iUnion.mpr
    refine ⟨N, ?_⟩
    have hsub : seq.polygon N ⊆ seq.polygon (φ N) := seq.polygons_monotone (hφ.id_le N)
    exact (latticeConvex_hull_inclusion_iff _ _ (seq.convex (φ N))).mp hsub hN

-- the actual stable vertex and divergent moving edge give one tail satisfying every finite-layer buffer.
theorem AnchoredCyclicMaximalSequence.exists_stable_buffer_tail {A : Type*}
    {q : ℕ} [NeZero (2 * q)] {c w : Site → A} {e : ZMod (2 * q) → Site}
    {Z : Set RealPlane} {G : Site} (seq : AnchoredCyclicMaximalSequence c w e Z G)
    (T : Finset Site) (P₀ : OrderedCyclicLatticePolygon e T) (i : ZMod (2 * q)) (B : Site)
    (hB : ∀ᶠ N in atTop, (seq.cyclic N).vertex i = B)
    (hdiv : Tendsto (fun N => ((seq.cyclic N).edgeLength i).toNat) atTop atTop) :
    ∃ d : ℕ, (∀ N, ((seq.tail d).cyclic N).vertex i = B) ∧
      ∀ N, P₀.edgeLength i + |determinant (e (i - 1)) (e (i + 1))| + 1 ≤
        ((seq.tail d).cyclic N).edgeLength i := by
  have hbuffer := unbounded_facet_length_eventually_has_buffer e T P₀ seq.polygon seq.cyclic i hdiv
  obtain ⟨d, hd⟩ := eventually_atTop.mp (hB.and hbuffer)
  refine ⟨d, ?_, ?_⟩
  · intro N
    exact (hd (N + d) (by omega)).1
  · intro N
    exact (hd (N + d) (by omega)).2

end KumarNivat
