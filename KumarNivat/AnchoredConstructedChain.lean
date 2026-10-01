import KumarNivat.AnchoredActualSequences
import KumarNivat.AnchoredResidualConvexity
import KumarNivat.AnchoredChainRecession

open Filter Topology

namespace KumarNivat

open scoped Pointwise

-- the actual constructed sequence retains the original convex newton summand in its exact finite-chain union.
theorem AnchoredCyclicMaximalSequence.constructed_chain {A : Type*} {q : ℕ} [NeZero (2 * q)]
    {c w : Site → A} {e : ZMod (2 * q) → Site} {Z : Set RealPlane} {G : Site}
    (seq : AnchoredCyclicMaximalSequence c w e Z G) (hfan : AnchoredChainFanOrder e)
    (hZ : Convex ℝ Z) :
    ∃ b : ℕ, 0 < b ∧ b < q ∧
      Tendsto (fun N => ((seq.cyclic N).edgeLength (b : ZMod (2 * q))).toNat) atTop atTop ∧
      ∃ B : Site, (∀ᶠ N in atTop, (seq.cyclic N).vertex (b : ZMod (2 * q)) = B) ∧
      ∃ fixed : ℕ → ℤ, fixed 0 = directionNormal (e 0) G ∧
        (∀ i : ℕ, i ≤ b → ∀ᶠ N in atTop, anchoredCyclicSupport e (seq.polygon N) (seq.cyclic N) i = fixed i) ∧
        (⋃ N, latticeHull (seq.polygon N)) = finiteInwardRegion (Finset.range (b + 1))
          (fun i => directionNormal (e (i : ZMod (2 * q)))) fixed ∧
        (∃ C : Set RealPlane, Convex ℝ C ∧ finiteInwardRegion (Finset.range (b + 1))
          (fun i => directionNormal (e (i : ZMod (2 * q)))) fixed = Z + C) ∧
        BackwardCofinal {g : Site | latticeEmbedding g ∈ finiteInwardRegion (Finset.range (b + 1))
          (fun i => directionNormal (e (i : ZMod (2 * q)))) fixed}
            {g | fixed 0 ≤ directionNormal (e 0) g} (e 0) := by
  obtain ⟨b, hb₀, hbq, hbdiv, B, hB, fixed, hfixed₀, hfixed, hUnion⟩ := seq.actual_chain_union hfan
  have hconvex : Convex ℝ (⋃ N, latticeHull (seq.polygon N)) := by
    rw [hUnion]
    exact (finiteInwardRegion_closed_convex _ _ _).2
  have henvelope (N : ℕ) : ∃ C : Set RealPlane, latticeHull (seq.polygon N) = Z + C := by
    obtain ⟨C, _hconvex, _hcompact, _hnonempty, hsum⟩ := (seq.agreement N).1.2
    exact ⟨C, hsum⟩
  obtain ⟨C, hC, hsum⟩ := anchored_union_convex_newton_residual seq.polygon Z hZ hconvex henvelope
  rw [hUnion] at hsum
  exact ⟨b, hb₀, hbq, hbdiv, B, hB, fixed, hfixed₀, hfixed, hUnion, ⟨C, hC, hsum⟩,
    anchored_chain_backward_cofinal e hfan b hb₀ hbq fixed⟩

end KumarNivat
