import KumarNivat.NewtonCyclicMinkowski
import KumarNivat.AnchoredChainLengths

open Filter Topology

namespace KumarNivat

-- the actual cyclic vertices are the anchored partial sums of their integer edge vectors.
theorem anchored_cyclic_vertex_prefix {n : ℕ} [NeZero n]
    (e : ZMod n → Site) (F : Finset Site) (P : OrderedCyclicLatticePolygon e F) (k : ℕ) :
    P.vertex ((k + 1 : ℕ) : ZMod n) = P.vertex 1 +
      ∑ j ∈ Finset.range k, P.edgeLength ((j + 1 : ℕ) : ZMod n) • e ((j + 1 : ℕ) : ZMod n) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hindex : (((k + 1 : ℕ) : ZMod n) + 1) = ((k + 1 + 1 : ℕ) : ZMod n) := by
      simp only [Nat.cast_add, Nat.cast_one]
    rw [← hindex, P.edge_eq, ih, Finset.sum_range_succ]
    abel

-- a common final tangent endpoint turns nondecreasing edge lengths into actual nested hulls.
theorem anchored_cyclic_sequence_hulls_monotone {n : ℕ} [NeZero n]
    (e : ZMod n → Site) (horder : CyclicEdgeOrder e)
    (F : ℕ → Finset Site) (P : ∀ N, OrderedCyclicLatticePolygon e (F N))
    (G : Site) (hanchor : ∀ N, (P N).vertex 1 = G)
    (hmono : ∀ N M, N ≤ M → ∀ i, (P N).edgeLength i ≤ (P M).edgeLength i) :
    Monotone (fun N => latticeHull (F N)) := by
  intro N M hNM
  obtain ⟨_C, _hconvex, _hcompact, _hzero, _hsum, hinclusion⟩ :=
    ordered_cyclic_anchored_minkowski_inclusion e horder (F N) (F M) (P N) (P M)
      (hmono N M hNM) 1 ((hanchor M).trans (hanchor N).symm)
  exact hinclusion

-- stabilized preceding edge lengths stabilize the actual next anchored vertex.
theorem anchored_chain_vertex_stabilizes {n : ℕ} [NeZero n]
    (e : ZMod n → Site) (F : ℕ → Finset Site) (P : ∀ N, OrderedCyclicLatticePolygon e (F N))
    (G : Site) (hanchor : ∀ N, (P N).vertex 1 = G) (b : ℕ) (hb : 0 < b)
    (hstable : ∀ j : ℕ, 0 < j → j < b → ∃ r : ℤ,
      ∀ᶠ N in atTop, (P N).edgeLength (j : ZMod n) = r) :
    ∃ B : Site, ∀ᶠ N in atTop, (P N).vertex (b : ZMod n) = B := by
  classical
  have hchoices : ∀ j : ℕ, ∃ r : ℤ, j ∈ Finset.range (b - 1) →
      ∀ᶠ N in atTop, (P N).edgeLength ((j + 1 : ℕ) : ZMod n) = r := by
    intro j
    by_cases hj : j < b - 1
    · obtain ⟨r, hr⟩ := hstable (j + 1) (by omega) (by omega)
      exact ⟨r, fun _ => hr⟩
    · exact ⟨0, fun h => False.elim (hj (Finset.mem_range.mp h))⟩
  choose r hr using hchoices
  let B : Site := G + ∑ j ∈ Finset.range (b - 1), r j • e ((j + 1 : ℕ) : ZMod n)
  refine ⟨B, ?_⟩
  have hevent := (Finset.range (b - 1)).eventually_all.mpr (fun j hj => hr j hj)
  exact hevent.mono (fun N hN => by
    have hvertex := anchored_cyclic_vertex_prefix e (F N) (P N) (b - 1)
    have hindex : b - 1 + 1 = b := by omega
    rw [hindex, hanchor N] at hvertex
    rw [hvertex]
    congr 1
    exact Finset.sum_congr rfl (fun j hj => by rw [hN j hj]))

-- the initial tangent support stays on the anchor line even as its edge grows backwards.
theorem anchored_initial_support_fixed {n : ℕ} [NeZero n]
    (e : ZMod n → Site) (F : ℕ → Finset Site) (P : ∀ N, OrderedCyclicLatticePolygon e (F N))
    (G : Site) (hanchor : ∀ N, (P N).vertex 1 = G) :
    ∀ N, directionNormal (e 0) ((P N).vertex 0) = directionNormal (e 0) G := by
  intro N
  have he := congrArg (directionNormal (e 0)) ((P N).edge_eq 0)
  simp only [zero_add, map_add, map_zsmul, directionNormal_self, smul_zero, add_zero] at he
  rw [hanchor N] at he
  exact he.symm

end KumarNivat
