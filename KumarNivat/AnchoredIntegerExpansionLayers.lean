module

public import KumarNivat.AnchoredEnvelopeLengthsScaled

@[expose] public section

namespace KumarNivat

-- the zeroth relaxation is the exact original polygon hull.
theorem cyclic_facet_relaxed_region_zero {n : ℕ} [NeZero n]
    (e : ZMod n → Site) (horder : CyclicEdgeOrder e) (F : Finset Site)
    (P : OrderedCyclicLatticePolygon e F) (i : ZMod n) :
    cyclicFacetRelaxedRegion e F P i 0 = latticeHull F := by
  rw [P.hull_eq, ordered_cyclic_walk_facet_presentation e horder P.vertex
    P.edgeLength P.length_pos P.edge_eq]
  ext x
  constructor
  · intro hx k
    have hb := hx k (Finset.mem_univ k)
    simpa only [cyclicFacetRelaxedCut, ite_self, sub_zero] using hb
  · intro hx k _hk
    simpa only [cyclicFacetRelaxedCut, ite_self, sub_zero] using hx k

-- increasing the relaxed level only enlarges the actual region.
theorem cyclic_facet_relaxed_region_monotone {n : ℕ} [NeZero n]
    (e : ZMod n → Site) (F : Finset Site) (P : OrderedCyclicLatticePolygon e F) (i : ZMod n) :
    Monotone (cyclicFacetRelaxedRegion e F P i) := by
  intro j l hjl x hx k hk
  have hcut : cyclicFacetRelaxedCut e F P i l k ≤ cyclicFacetRelaxedCut e F P i j k := by
    unfold cyclicFacetRelaxedCut
    split_ifs <;> omega
  exact (Int.cast_le.mpr hcut).trans (hx k hk)

-- one integer normal level above the new face is already in the previous layer.
theorem cyclic_facet_relaxed_previous_integer_layer {n : ℕ} [NeZero n]
    (e : ZMod n → Site) (F : Finset Site) (P : OrderedCyclicLatticePolygon e F)
    (i : ZMod n) (j : ℤ) (g : Site)
    (hg : latticeEmbedding g ∈ cyclicFacetRelaxedRegion e F P i (j + 1))
    (hlevel : directionNormal (e i) (P.vertex i) - (j + 1) + 1 ≤ directionNormal (e i) g) :
    latticeEmbedding g ∈ cyclicFacetRelaxedRegion e F P i j := by
  intro k hk
  by_cases hki : k = i
  · subst k
    have he : directionNormal (e i) (P.vertex i) - (j + 1) + 1 =
        directionNormal (e i) (P.vertex i) - j := by omega
    rw [he] at hlevel
    change (cyclicFacetRelaxedCut e F P i j i : ℝ) ≤
      latticeNormal (directionNormal (e i)) (latticeEmbedding g)
    simp only [cyclicFacetRelaxedCut, ite_true, latticeNormal_embedding]
    exact_mod_cast hlevel
  · have hb := hg k hk
    change (cyclicFacetRelaxedCut e F P i (j + 1) k : ℝ) ≤
      latticeNormal (directionNormal (e k)) (latticeEmbedding g) at hb
    simpa only [cyclicFacetRelaxedCut, ite_eq_right hki, sub_zero] using hb

end KumarNivat
