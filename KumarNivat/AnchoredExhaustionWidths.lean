import KumarNivat.AnchoredPolygonExhaustion
import KumarNivat.AnchoredChainFan

open Filter Topology

namespace KumarNivat

-- the actual facet presentation bounds every lattice observation site by its starting vertex.
theorem ordered_cyclic_site_normal_minimum {n : ℕ} [NeZero n]
    (e : ZMod n → Site) (horder : CyclicEdgeOrder e) (M : Finset Site)
    (P : OrderedCyclicLatticePolygon e M) (i : ZMod n) (g : Site) (hg : g ∈ M) :
    directionNormal (e i) (P.vertex i) ≤ directionNormal (e i) g := by
  have hmem : latticeEmbedding g ∈ latticeHull M := subset_convexHull ℝ _ ⟨g, hg, rfl⟩
  rw [P.hull_eq, ordered_cyclic_walk_facet_presentation e horder P.vertex
    P.edgeLength P.length_pos P.edge_eq] at hmem
  have h := hmem i
  rw [latticeNormal_embedding] at h
  exact_mod_cast h

-- two actual boundary sites separated by primitive tangent steps force the tangent edge to be at least that long.
theorem ordered_cyclic_tangent_edge_length_lower_bound {n : ℕ} [NeZero n]
    (e : ZMod n → Site) (horder : CyclicEdgeOrder e) (M : Finset Site)
    (P : OrderedCyclicLatticePolygon e M) (G : Site) (hG : G ∈ M) (cut : ℤ)
    (hprimitive : Int.gcd (e 0).1 (e 0).2 = 1)
    (hcut : directionNormal (e 0) G = cut)
    (hhalf : ∀ g ∈ M, cut ≤ directionNormal (e 0) g) (N : ℕ)
    (hminus : G - (N : ℤ) • e 0 ∈ M) (hplus : G + (N : ℤ) • e 0 ∈ M) :
    2 * (N : ℤ) ≤ P.edgeLength 0 := by
  obtain ⟨k, hk⟩ := ordered_cyclic_tangent_anchor_shift e horder M P G hG cut hprimitive hcut hhalf
  have hv0 : P.vertex 0 = G + (k - P.edgeLength 0) • e 0 := by
    have he := P.edge_eq 0
    simp only [zero_add] at he
    calc
      P.vertex 0 = P.vertex 1 - P.edgeLength 0 • e 0 := by rw [he]; abel
      _ = G + (k - P.edgeLength 0) • e 0 := by rw [hk, sub_smul]; abel
  have hnext := ordered_cyclic_site_normal_minimum e horder M P 1 _ hplus
  rw [hk, map_add, map_add, map_zsmul, map_zsmul, smul_eq_mul, smul_eq_mul] at hnext
  have hnextneg : directionNormal (e 1) (e 0) < 0 := by
    have h := horder.adjacent_pos 1
    simp only [sub_self] at h
    change determinant (e 1) (e 0) < 0
    have he : determinant (e 1) (e 0) = -determinant (e 0) (e 1) := by
      simp only [determinant]
      ring
    rw [he]
    omega
  have hkle : (N : ℤ) ≤ k := by nlinarith [hnext]
  have hprev := ordered_cyclic_site_normal_minimum e horder M P (-1) _ hminus
  have hprevvertex : directionNormal (e (-1)) (P.vertex 0) =
      directionNormal (e (-1)) (P.vertex (-1)) := by
    have he := congrArg (directionNormal (e (-1))) (P.edge_eq (-1))
    simpa only [neg_add_cancel, map_add, map_zsmul, directionNormal_self, smul_zero, add_zero] using he
  rw [← hprevvertex, hv0, map_add, map_sub, map_zsmul, map_zsmul, smul_eq_mul, smul_eq_mul] at hprev
  have hprevpos : 0 < directionNormal (e (-1)) (e 0) := by
    change 0 < determinant (e (-1)) (e 0)
    simpa only [zero_sub] using horder.adjacent_pos 0
  nlinarith [hprev]

-- the actual antipodal normal identifies the opposite vertex as a maximum of the original tangent normal.
theorem ordered_cyclic_opposite_vertex_normal_maximum {q : ℕ} [NeZero (2 * q)]
    (e : ZMod (2 * q) → Site) (hfan : AnchoredChainFanOrder e) (M : Finset Site)
    (P : OrderedCyclicLatticePolygon e M) (g : Site) (hg : g ∈ M) :
    directionNormal (e 0) g ≤ directionNormal (e 0) (P.vertex (q : ZMod (2 * q))) := by
  have h := ordered_cyclic_site_normal_minimum e hfan.order M P (q : ZMod (2 * q)) g hg
  have he := hfan.opposite 0
  simp only [zero_add] at he
  rw [he] at h
  have hnormal : directionNormal (-e 0) = -directionNormal (e 0) := by
    ext v
    simp [directionNormal, determinant]
    ring
  rw [hnormal] at h
  change -directionNormal (e 0) (P.vertex (q : ZMod (2 * q))) ≤ -directionNormal (e 0) g at h
  omega

-- exhaustive boundary agreement sets force the actual tangent edge lengths to diverge.
theorem exhaustive_cyclic_tangent_lengths_diverge {n : ℕ} [NeZero n]
    (e : ZMod n → Site) (horder : CyclicEdgeOrder e)
    (M : ℕ → Finset Site) (P : ∀ N, OrderedCyclicLatticePolygon e (M N))
    (G : Site) (cut : ℤ) (hprimitive : Int.gcd (e 0).1 (e 0).2 = 1)
    (hcut : directionNormal (e 0) G = cut)
    (hG : ∀ N, G ∈ M N) (hhalf : ∀ N, ∀ g ∈ M N, cut ≤ directionNormal (e 0) g)
    (hexhaust : ∀ g : Site, cut ≤ directionNormal (e 0) g →
      ∃ N : ℕ, ∀ m : ℕ, N ≤ m → g ∈ M m) :
    Tendsto (fun N => ((P N).edgeLength 0).toNat) atTop atTop := by
  apply tendsto_atTop.2
  intro L
  have hminus : cut ≤ directionNormal (e 0) (G - (L : ℤ) • e 0) := by
    rw [map_sub, map_zsmul, directionNormal_self, smul_zero, sub_zero, hcut]
  have hplus : cut ≤ directionNormal (e 0) (G + (L : ℤ) • e 0) := by
    rw [map_add, map_zsmul, directionNormal_self, smul_zero, add_zero, hcut]
  obtain ⟨N₁, hN₁⟩ := hexhaust _ hminus
  obtain ⟨N₂, hN₂⟩ := hexhaust _ hplus
  refine (eventually_ge_atTop (max N₁ N₂)).mono ?_
  intro N hN
  have hlength := ordered_cyclic_tangent_edge_length_lower_bound e horder (M N) (P N) G (hG N)
    cut hprimitive hcut (hhalf N) L (hN₁ N (le_trans (le_max_left _ _) hN))
      (hN₂ N (le_trans (le_max_right _ _) hN))
  omega

-- actual half-plane exhaustion forces the opposite supporting height, hence transverse width, to diverge.
theorem exhaustive_cyclic_transverse_width_diverges {q : ℕ} [NeZero (2 * q)]
    (e : ZMod (2 * q) → Site) (hfan : AnchoredChainFanOrder e)
    (M : ℕ → Finset Site) (P : ∀ N, OrderedCyclicLatticePolygon e (M N))
    (G : Site) (cut : ℤ) (hprimitive : Int.gcd (e 0).1 (e 0).2 = 1)
    (hcut : directionNormal (e 0) G = cut)
    (hexhaust : ∀ g : Site, cut ≤ directionNormal (e 0) g →
      ∃ N : ℕ, ∀ m : ℕ, N ≤ m → g ∈ M m) :
    Tendsto (fun N => ((directionNormal (e 0) ((P N).vertex (q : ZMod (2 * q))) -
      directionNormal (e 0) G : ℤ) : ℝ)) atTop atTop := by
  obtain ⟨τ, hτ, _hker⟩ := primitive_direction_coordinate (e 0) hprimitive
  obtain ⟨v, hv⟩ := primitive_basis_of_line_coordinate (e 0) τ hτ
  apply tendsto_atTop.2
  intro L
  obtain ⟨s, hs⟩ := exists_nat_ge L
  have hheight : directionNormal (e 0) (G + (s : ℤ) • v) = cut + (s : ℤ) := by
    rw [map_add, map_zsmul, hcut]
    change cut + (s : ℤ) • determinant (e 0) v = cut + (s : ℤ)
    rw [hv, smul_eq_mul, mul_one]
  obtain ⟨N, hN⟩ := hexhaust (G + (s : ℤ) • v) (by rw [hheight]; omega)
  refine (eventually_ge_atTop N).mono ?_
  intro m hm
  have hbound := ordered_cyclic_opposite_vertex_normal_maximum e hfan (M m) (P m) _ (hN m hm)
  rw [hheight, ← hcut] at hbound
  have hwidth : (s : ℤ) ≤ directionNormal (e 0) ((P m).vertex (q : ZMod (2 * q))) -
      directionNormal (e 0) G := by omega
  have hwidthR : (s : ℝ) ≤ ((directionNormal (e 0) ((P m).vertex (q : ZMod (2 * q))) -
      directionNormal (e 0) G : ℤ) : ℝ) := by exact_mod_cast hwidth
  exact hs.trans hwidthR

end KumarNivat
