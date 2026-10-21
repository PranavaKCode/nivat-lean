module

public import KumarNivat.AnchoredChainFan

@[expose] public section

namespace KumarNivat

-- rotating the original cyclic list changes only the starting edge, not its angular order.
theorem CyclicEdgeOrder.rotation {n : ℕ} [NeZero n] {e : ZMod n → Site}
    (horder : CyclicEdgeOrder e) (j : ZMod n) : CyclicEdgeOrder (fun i => e (i + j)) := by
  constructor
  · intro i
    simpa only [add_sub_assoc, sub_add_eq_add_sub] using horder.adjacent_pos (i + j)
  · intro i
    obtain ⟨k, hkn, hpositive, hnegative⟩ := horder.normal_turn (i + j)
    refine ⟨k, hkn, ?_, ?_⟩
    · intro t ht
      simpa only [add_assoc, add_comm, add_left_comm] using hpositive t ht
    · intro t hkt htn
      simpa only [add_assoc, add_comm, add_left_comm] using hnegative t hkt htn

-- the actual antipodal and strict half-turn data rotate with the same factor fan.
theorem AnchoredChainFanOrder.rotation {q : ℕ} [NeZero (2 * q)] {e : ZMod (2 * q) → Site}
    (hfan : AnchoredChainFanOrder e) (j : ZMod (2 * q)) :
    AnchoredChainFanOrder (fun i => e (i + j)) := by
  refine ⟨hfan.order.rotation j, ?_, ?_⟩
  · intro i
    simpa only [add_assoc, add_comm, add_left_comm] using hfan.opposite (i + j)
  · intro i d hd₀ hdq
    simpa only [add_assoc, add_comm, add_left_comm] using hfan.nonparallel (i + j) d hd₀ hdq

-- choosing any actual factor edge as the first edge preserves the original polygon and every vertex.
noncomputable def OrderedCyclicLatticePolygon.rotation {n : ℕ} [NeZero n]
    {e : ZMod n → Site} {F : Finset Site} (P : OrderedCyclicLatticePolygon e F) (j : ZMod n) :
    OrderedCyclicLatticePolygon (fun i => e (i + j)) F where
  vertex i := P.vertex (i + j)
  edgeLength i := P.edgeLength (i + j)
  length_pos i := P.length_pos (i + j)
  edge_eq i := by
    simpa only [add_assoc, add_comm, add_left_comm] using P.edge_eq (i + j)
  vertex_mem i := P.vertex_mem (i + j)
  hull_eq := by
    rw [P.hull_eq]
    congr 1
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      refine ⟨i - j, ?_⟩
      simp only [sub_add_cancel]
    · rintro ⟨i, rfl⟩
      exact ⟨i + j, rfl⟩

end KumarNivat
