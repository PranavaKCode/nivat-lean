module

public import KumarNivat.AnchoredChainWalk
public import KumarNivat.AnchoredChainFan

@[expose] public section

open Filter Topology

namespace KumarNivat

-- shifting the finite prefix index gives the same actual first-half edge sum.
theorem anchored_sum_range_successor (f : ℕ → ℤ) (k : ℕ) :
    (∑ j ∈ Finset.range k, f (j + 1)) = ∑ j ∈ Finset.Icc 1 k, f j := by
  apply Finset.sum_bij (fun j _ => j + 1)
  · intro j hj
    exact Finset.mem_Icc.mpr ⟨by omega, by have h := Finset.mem_range.mp hj; omega⟩
  · intro i _hi j _hj hij
    omega
  · intro j hj
    obtain ⟨hjl, hjr⟩ := Finset.mem_Icc.mp hj
    exact ⟨j - 1, Finset.mem_range.mpr (by omega), by omega⟩
  · intro _j _hj
    rfl

-- the measured transverse width is exactly the sum of the actual first-half edge heights.
theorem anchored_cyclic_actual_width_formula {q : ℕ} [NeZero (2 * q)]
    (e : ZMod (2 * q) → Site) (F : Finset Site) (P : OrderedCyclicLatticePolygon e F)
    (G : Site) (hanchor : P.vertex 1 = G) :
    directionNormal (e 0) (P.vertex (q : ZMod (2 * q))) - directionNormal (e 0) G =
      ∑ j ∈ Finset.Icc 1 (q - 1), P.edgeLength (j : ZMod (2 * q)) *
        determinant (e 0) (e (j : ZMod (2 * q))) := by
  have hqne : 2 * q ≠ 0 := NeZero.ne _
  have hqpos : 0 < q := by omega
  have hvertex := anchored_cyclic_vertex_prefix e F P (q - 1)
  have hindex : q - 1 + 1 = q := by omega
  rw [hindex, hanchor] at hvertex
  rw [hvertex, map_add, map_sum]
  simp only [map_zsmul, smul_eq_mul, add_sub_cancel_left]
  exact anchored_sum_range_successor
    (fun j => P.edgeLength (j : ZMod (2 * q)) * determinant (e 0) (e (j : ZMod (2 * q)))) (q - 1)

-- actual width divergence selects the first unbounded edge without an assumed boundary direction or stabilized chain.
theorem anchored_actual_width_selects_first_unbounded {q : ℕ} [NeZero (2 * q)]
    (e : ZMod (2 * q) → Site) (F : ℕ → Finset Site)
    (P : ∀ N, OrderedCyclicLatticePolygon e (F N)) (G : Site)
    (hanchor : ∀ N, (P N).vertex 1 = G)
    (hmono : ∀ N M, N ≤ M → ∀ i, (P N).edgeLength i ≤ (P M).edgeLength i)
    (hwidth : Tendsto (fun N => ((directionNormal (e 0) ((P N).vertex (q : ZMod (2 * q))) -
      directionNormal (e 0) G : ℤ) : ℝ)) atTop atTop) :
    ∃ b : ℕ, 0 < b ∧ b < q ∧
      Tendsto (fun N => ((P N).edgeLength (b : ZMod (2 * q))).toNat) atTop atTop ∧
      ∀ j : ℕ, 0 < j → j < b → ∃ r : ℤ,
        ∀ᶠ N in atTop, (P N).edgeLength (j : ZMod (2 * q)) = r := by
  let lengths : ℕ → ℕ → ℕ := fun N j => ((P N).edgeLength (j : ZMod (2 * q))).toNat
  have hcast : ∀ N j, (lengths N j : ℤ) = (P N).edgeLength (j : ZMod (2 * q)) := by
    intro N j
    have hpos := (P N).length_pos (j : ZMod (2 * q))
    dsimp [lengths]
    omega
  have hmonoNat : ∀ j, Monotone (fun N => lengths N j) := by
    intro j N M hNM
    have hle := hmono N M hNM (j : ZMod (2 * q))
    dsimp [lengths]
    omega
  have hweighted : Tendsto (fun N =>
      ((∑ j ∈ Finset.Icc 1 (q - 1), (lengths N j : ℤ) *
        determinant (e 0) (e (j : ZMod (2 * q))) : ℤ) : ℝ)) atTop atTop := by
    convert hwidth using 1
    funext N
    rw [anchored_cyclic_actual_width_formula e (F N) (P N) G (hanchor N)]
    congr 1
    exact Finset.sum_congr rfl (fun j _hj => by rw [hcast N j])
  obtain ⟨b, hb₀, hbq, hdiv, hstable⟩ := first_unbounded_anchored_chain_length q lengths hmonoNat
    (fun j => determinant (e 0) (e (j : ZMod (2 * q)))) hweighted
  refine ⟨b, hb₀, hbq, hdiv, ?_⟩
  intro j hj₀ hjb
  obtain ⟨r, hr⟩ := hstable j hj₀ hjb
  refine ⟨(r : ℤ), hr.mono (fun N hN => ?_)⟩
  calc
    (P N).edgeLength (j : ZMod (2 * q)) = (lengths N j : ℤ) := (hcast N j).symm
    _ = (r : ℤ) := by rw [hN]

end KumarNivat
