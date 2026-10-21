module

public import KumarNivat.AnchoredSequenceTails

@[expose] public section

open Filter Topology

namespace KumarNivat

-- the first divergent edge determines one tail with the actual fixed endpoint and every expansion buffer.
theorem AnchoredCyclicMaximalSequence.prepared_chain {A : Type*}
    {q : ℕ} [NeZero (2 * q)] {c w : Site → A} {e : ZMod (2 * q) → Site}
    {Z : Set RealPlane} {G : Site} (seq : AnchoredCyclicMaximalSequence c w e Z G)
    (hfan : AnchoredChainFanOrder e) (T : Finset Site)
    (Q : OrderedCyclicLatticePolygon e T) :
    ∃ b : ℕ, 0 < b ∧ b < q ∧ ∃ d : ℕ, ∃ B : Site, ∃ fixed : ℕ → ℤ,
      (∀ N, ((seq.tail d).cyclic N).vertex (b : ZMod (2 * q)) = B) ∧
      (∀ N, Q.edgeLength (b : ZMod (2 * q)) +
        |determinant (e ((b : ZMod (2 * q)) - 1)) (e ((b : ZMod (2 * q)) + 1))| + 1 ≤
          ((seq.tail d).cyclic N).edgeLength (b : ZMod (2 * q))) ∧
      Tendsto (fun N => (((seq.tail d).cyclic N).edgeLength (b : ZMod (2 * q))).toNat) atTop atTop ∧
      fixed 0 = directionNormal (e 0) G ∧
      fixed b = directionNormal (e (b : ZMod (2 * q))) B ∧
      (∀ i : ℕ, i ≤ b → ∀ᶠ N in atTop,
        anchoredCyclicSupport e ((seq.tail d).polygon N) ((seq.tail d).cyclic N) i = fixed i) ∧
      (⋃ N, latticeHull ((seq.tail d).polygon N)) = finiteInwardRegion (Finset.range (b + 1))
        (fun i => directionNormal (e (i : ZMod (2 * q)))) fixed := by
  obtain ⟨b, hb₀, hbq, hbdiv, B, hB, fixed, hfixed₀, hfixed, hUnion⟩ := seq.actual_chain_union hfan
  obtain ⟨d, hdB, hdbuffer⟩ := seq.exists_stable_buffer_tail T Q (b : ZMod (2 * q)) B hB hbdiv
  have hφ : StrictMono (fun N : ℕ => N + d) := by
    intro N M hNM
    change N + d < M + d
    omega
  have hfixedb : fixed b = directionNormal (e (b : ZMod (2 * q))) B := by
    obtain ⟨N, hNB, hNfixed⟩ := (hB.and (hfixed b (le_refl b))).exists
    simpa only [anchoredCyclicSupport, hNB] using hNfixed.symm
  refine ⟨b, hb₀, hbq, d, B, fixed, hdB, hdbuffer, ?_, hfixed₀, hfixedb, ?_, ?_⟩
  · exact hbdiv.comp hφ.tendsto_atTop
  · intro i hi
    exact hφ.tendsto_atTop.eventually (hfixed i hi)
  · exact (seq.reindex_hull_union (fun N => N + d) hφ).trans hUnion

end KumarNivat
