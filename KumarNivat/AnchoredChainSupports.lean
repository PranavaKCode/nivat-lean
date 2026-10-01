import KumarNivat.AnchoredChainFan
import KumarNivat.AnchoredChainWalk
import KumarNivat.PolyhedralLimits
import KumarNivat.NewtonCyclicFacets

open Filter Topology

namespace KumarNivat

-- support levels are the actual attained integer minima at the cyclic vertices.
def anchoredCyclicSupport {n : ℕ} [NeZero n] (e : ZMod n → Site)
    (F : Finset Site) (P : OrderedCyclicLatticePolygon e F) (i : ℕ) : ℤ :=
  directionNormal (e (i : ZMod n)) (P.vertex (i : ZMod n))

-- the fixed natural index list describes exactly the same actual cyclic polygon hull.
theorem anchored_cyclic_hull_nat_facets {n : ℕ} [NeZero n]
    (e : ZMod n → Site) (horder : CyclicEdgeOrder e) (F : Finset Site)
    (P : OrderedCyclicLatticePolygon e F) :
    latticeHull F = finiteInwardRegion (Finset.range n)
      (fun i => directionNormal (e (i : ZMod n))) (anchoredCyclicSupport e F P) := by
  rw [P.hull_eq, ordered_cyclic_walk_facet_presentation e horder P.vertex P.edgeLength P.length_pos P.edge_eq]
  ext x
  constructor
  · intro hx i _hi
    exact hx (i : ZMod n)
  · intro hx i
    have h := hx i.val (Finset.mem_range.mpr (ZMod.val_lt i))
    simpa only [anchoredCyclicSupport, ZMod.natCast_zmod_val] using h

-- a containing long ray need only be present eventually; the finite initial prefix does not affect escape.
theorem inward_support_escapes_along_eventual_long_ray (μ : Site →+ ℤ) (p : Site) (hp : μ p < 0)
    (B : RealPlane) (lengths : ℕ → ℕ) (hlengths : Tendsto lengths atTop atTop) (z : ℕ → ℤ)
    (hbound : ∀ᶠ N in atTop,
      (z N : ℝ) ≤ latticeNormal μ (B + (lengths N : ℝ) • latticeEmbedding p)) :
    Tendsto (fun N => (z N : ℝ)) atTop atBot := by
  classical
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hbound
  let adjusted : ℕ → ℤ := fun N => if N₀ ≤ N then z N else
    ⌊latticeNormal μ (B + (lengths N : ℝ) • latticeEmbedding p)⌋
  have hfit : ∀ N, (adjusted N : ℝ) ≤
      latticeNormal μ (B + (lengths N : ℝ) • latticeEmbedding p) := by
    intro N
    by_cases hN : N₀ ≤ N
    · simpa only [adjusted, ite_eq_left hN] using hN₀ N hN
    · simpa only [adjusted, ite_eq_right hN] using
        Int.floor_le (latticeNormal μ (B + (lengths N : ℝ) • latticeEmbedding p))
  have htend := inward_support_escapes_along_long_ray μ p hp B lengths hlengths adjusted hfit
  apply htend.congr'
  exact (eventually_ge_atTop N₀).mono (fun N hN => by simp only [adjusted, ite_eq_left hN])

-- the backwards tangent endpoint is an actual vertex at the full increasing primitive edge length.
theorem anchored_cyclic_backward_vertex {n : ℕ} [NeZero n]
    (e : ZMod n → Site) (F : Finset Site) (P : OrderedCyclicLatticePolygon e F)
    (G : Site) (hanchor : P.vertex 1 = G) :
    P.vertex 0 = G + (P.edgeLength 0).toNat • (-e 0) := by
  have he := P.edge_eq 0
  simp only [zero_add] at he
  rw [hanchor] at he
  have hcast : ((P.edgeLength 0).toNat : ℤ) = P.edgeLength 0 := by
    have hpos := P.length_pos 0
    omega
  rw [← natCast_zsmul, hcast, smul_neg, he]
  abel

-- every actual facet is bounded above by the contained long backwards tangent endpoint.
theorem anchored_cyclic_backward_support_bound {n : ℕ} [NeZero n]
    (e : ZMod n → Site) (horder : CyclicEdgeOrder e) (F : Finset Site)
    (P : OrderedCyclicLatticePolygon e F) (G : Site) (hanchor : P.vertex 1 = G) (i : ℕ) :
    (anchoredCyclicSupport e F P i : ℝ) ≤
      latticeNormal (directionNormal (e (i : ZMod n)))
        (latticeEmbedding G + ((P.edgeLength 0).toNat : ℝ) • latticeEmbedding (-e 0)) := by
  have hmin := ordered_cyclic_walk_normal_minimum e horder P.vertex P.edgeLength
    (fun j => le_of_lt (P.length_pos j)) P.edge_eq (i : ZMod n) 0
  have he := congrArg latticeEmbedding (anchored_cyclic_backward_vertex e F P G hanchor)
  rw [latticeEmbedding_add] at he
  have hsmul : latticeEmbedding ((P.edgeLength 0).toNat • (-e 0)) =
      ((P.edgeLength 0).toNat : ℝ) • latticeEmbedding (-e 0) := by
    rw [← natCast_zsmul, latticeEmbedding_zsmul, Int.cast_natCast]
  rw [hsmul] at he
  rw [← he, latticeNormal_embedding]
  exact_mod_cast hmin

-- the stabilized first unbounded edge supplies its actual far endpoint to every facet inequality.
theorem anchored_cyclic_forward_support_bound {n : ℕ} [NeZero n]
    (e : ZMod n → Site) (horder : CyclicEdgeOrder e) (F : Finset Site)
    (P : OrderedCyclicLatticePolygon e F) (b i : ℕ) (B : Site)
    (hB : P.vertex (b : ZMod n) = B) :
    (anchoredCyclicSupport e F P i : ℝ) ≤
      latticeNormal (directionNormal (e (i : ZMod n)))
        (latticeEmbedding B + ((P.edgeLength (b : ZMod n)).toNat : ℝ) •
          latticeEmbedding (e (b : ZMod n))) := by
  have hmin := ordered_cyclic_walk_normal_minimum e horder P.vertex P.edgeLength
    (fun j => le_of_lt (P.length_pos j)) P.edge_eq (i : ZMod n) ((b : ZMod n) + 1)
  have he := congrArg latticeEmbedding (P.edge_eq (b : ZMod n))
  rw [hB, latticeEmbedding_add, latticeEmbedding_zsmul] at he
  have hcast : ((P.edgeLength (b : ZMod n)).toNat : ℤ) = P.edgeLength (b : ZMod n) := by
    have hpos := P.length_pos (b : ZMod n)
    omega
  have hreal : ((P.edgeLength (b : ZMod n)).toNat : ℝ) =
      (P.edgeLength (b : ZMod n) : ℝ) := by exact_mod_cast hcast
  rw [hreal, ← he, latticeNormal_embedding]
  exact_mod_cast hmin

-- all remaining actual support levels escape because their normal is negative on a contained long ray.
theorem anchored_chain_removed_supports_escape {q : ℕ} [NeZero (2 * q)]
    (e : ZMod (2 * q) → Site) (hfan : AnchoredChainFanOrder e)
    (F : ℕ → Finset Site) (P : ∀ N, OrderedCyclicLatticePolygon e (F N))
    (G : Site) (hanchor : ∀ N, (P N).vertex 1 = G)
    (ha : Tendsto (fun N => ((P N).edgeLength 0).toNat) atTop atTop)
    (b : ℕ) (hb₀ : 0 < b) (hbq : b < q)
    (hb : Tendsto (fun N => ((P N).edgeLength (b : ZMod (2 * q))).toNat) atTop atTop)
    (B : Site) (hB : ∀ᶠ N in atTop, (P N).vertex (b : ZMod (2 * q)) = B) :
    ∀ i : ℕ, b < i → i < 2 * q →
      Tendsto (fun N => (anchoredCyclicSupport e (F N) (P N) i : ℝ)) atTop atBot := by
  intro i hbi hiq
  obtain hneg | hneg := anchored_chain_removed_normal_signs e hfan b hb₀ hbq i hbi hiq
  · apply inward_support_escapes_along_long_ray _ (-e 0) hneg (latticeEmbedding G) _ ha
    intro N
    exact anchored_cyclic_backward_support_bound e hfan.order (F N) (P N) G (hanchor N) i
  · apply inward_support_escapes_along_eventual_long_ray _ (e (b : ZMod (2 * q))) hneg
      (latticeEmbedding B) _ hb
    exact hB.mono (fun N hN => anchored_cyclic_forward_support_bound e hfan.order (F N) (P N) b i B hN)

end KumarNivat
