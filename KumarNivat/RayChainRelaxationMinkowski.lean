import KumarNivat.RayChainRelaxationRealCones
import KumarNivat.RayChainRelaxationNormals
import KumarNivat.NewtonSingleRayFacetsSegmentRotation

namespace KumarNivat

open scoped Pointwise

-- the same actual cyclic vertices translate the original hull by its lattice anchor.
theorem translated_lattice_cyclic_vertex_hull {n : ℕ} [NeZero n]
    (e : ZMod n → Site) (T : Finset Site) (P : OrderedCyclicLatticePolygon e T) (G : Site) :
    convexHull ℝ (Set.range (fun i => latticeEmbedding (P.vertex i + G))) =
      latticeHull T + ({latticeEmbedding G} : Set RealPlane) := by
  have hrange : Set.range (fun i => latticeEmbedding (P.vertex i + G)) =
      Set.range (fun i => latticeEmbedding (P.vertex i)) + ({latticeEmbedding G} : Set RealPlane) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      change latticeEmbedding (P.vertex i + G) ∈
        Set.range (fun i => latticeEmbedding (P.vertex i)) + ({latticeEmbedding G} : Set RealPlane)
      rw [latticeEmbedding_add]
      exact Set.add_mem_add ⟨i, rfl⟩ (Set.mem_singleton _)
    · rintro ⟨u, ⟨i, rfl⟩, v, hv, rfl⟩
      have he := Set.mem_singleton_iff.mp hv
      subst he
      exact ⟨i, latticeEmbedding_add _ _⟩
  rw [hrange, convexHull_add, convexHull_singleton, ← P.hull_eq]

-- every outward moving-facet relaxation is the original newton hull plus the actual cone and one real successor segment.
theorem forward_factor_relaxation_original_minkowski_summand {q : ℕ} [NeZero q]
    (hq : 2 ≤ q) (e : ZMod (2 * q) → Site) (hfan : AnchoredChainFanOrder e)
    (T : Finset Site) (P : OrderedCyclicLatticePolygon e T) (G : Site)
    (k : ℕ) (hk₀ : 0 < k) (hkq : k < q) (β : ℤ)
    (hβ : β < (-directionNormal (e (k : ZMod (2 * q))))
      (P.vertex ((q + k : ℕ) : ZMod (2 * q)) + G)) :
    ∃ t : ℝ, 0 < t ∧
      t = (((-directionNormal (e (k : ZMod (2 * q))))
        (P.vertex ((q + k : ℕ) : ZMod (2 * q)) + G) - β : ℤ) : ℝ) /
          (-(((-directionNormal (e (k : ZMod (2 * q)))) (e ((k + 1 : ℕ) : ZMod (2 * q)))) : ℝ)) ∧
      inwardLayerRegion (-directionNormal (e (k : ZMod (2 * q)))) β
        (facetIndexSet (Finset.Icc (k + 1) (q - 1)))
        (facetNormals (directionNormal (e 0)) (fun i => -directionNormal (e (i : ZMod (2 * q)))))
        (facetLevels (directionNormal (e 0) (P.vertex 0 + G))
          (fun i => (-directionNormal (e (i : ZMod (2 * q)))) (P.vertex ((q + i : ℕ) : ZMod (2 * q)) + G))) =
          latticeHull T + (({latticeEmbedding G} : Set RealPlane) +
            (forwardTwoRayCone (e 0) (e (k : ZMod (2 * q))) +
              lineInterval 0 (latticeEmbedding (e ((k + 1 : ℕ) : ZMod (2 * q)))) 0 t)) := by
  classical
  let μ : ℕ → Site →+ ℤ := fun i => -directionNormal (e (i : ZMod (2 * q)))
  let z : ℕ → ℤ := fun i => μ i (P.vertex ((q + i : ℕ) : ZMod (2 * q)) + G)
  let η := μ k
  let a := e 0
  let b := e (k : ZMod (2 * q))
  let j : ZMod (2 * q) := ((k + 1 : ℕ) : ZMod (2 * q))
  let d := e j
  let cut := directionNormal a (P.vertex 0 + G)
  let t : ℝ := ((z k - β : ℤ) : ℝ) / (-(η d : ℝ))
  obtain ⟨hηd, hνd, hμd⟩ := forward_factor_successor_relaxation_signs e hfan k hk₀ hkq
  have hden : 0 < -(η d : ℝ) := by exact_mod_cast neg_pos.mpr hηd
  have ht : 0 < t := div_pos (by exact_mod_cast sub_pos.mpr hβ) hden
  have htprod : t * (η d : ℝ) = ((β - z k : ℤ) : ℝ) := by
    have h := div_mul_cancel₀ ((z k - β : ℤ) : ℝ) (ne_of_gt hden)
    change t * (-(η d : ℝ)) = ((z k - β : ℤ) : ℝ) at h
    rw [Int.cast_sub]
    rw [Int.cast_sub] at h
    nlinarith
  let v : ZMod (2 * q) → RealPlane := fun i => latticeEmbedding (P.vertex i + G)
  let r : ZMod (2 * q) → ℝ := fun i => (P.edgeLength i : ℝ)
  have hr : ∀ i, 0 < r i := fun i => by dsimp [r]; exact_mod_cast P.length_pos i
  have hv : ∀ i, v (i + 1) = v i + r i • latticeEmbedding (e i) := by
    intro i
    dsimp [v, r]
    rw [P.edge_eq, latticeEmbedding_add, latticeEmbedding_add, latticeEmbedding_zsmul, latticeEmbedding_add]
    abel
  let w := cyclicFactorSegmentVertices q e j t
  let lengths := cyclicFactorSegmentLengths q j t
  have hd : ∀ i, 0 ≤ lengths i := cyclicFactorSegmentLengths_nonnegative q j t ht.le
  have hw : ∀ i, w (i + 1) = w i + lengths i • latticeEmbedding (e i) :=
    cyclicFactorSegmentVertices_next e hfan.opposite j t
  have hsum := ordered_real_cyclic_walk_minkowski e hfan.order v w r lengths hr hd hv hw
  have hvHull : convexHull ℝ (Set.range v) = latticeHull T + ({latticeEmbedding G} : Set RealPlane) :=
    translated_lattice_cyclic_vertex_hull e T P G
  have hwHull : convexHull ℝ (Set.range w) = lineInterval 0 (latticeEmbedding d) 0 t :=
    cyclicFactorSegmentVertices_hull e j t ht.le
  rw [hvHull, hwHull] at hsum
  have hpos : ∀ i, 0 < r i + lengths i := fun i => add_pos_of_pos_of_nonneg (hr i) (hd i)
  have hedge : ∀ i, v (i + 1) + w (i + 1) = v i + w i + (r i + lengths i) • latticeEmbedding (e i) := by
    intro i
    rw [hv, hw, add_smul]
    abel
  let zR : ℕ → ℝ := fun i => latticeNormal (directionNormal (e (i : ZMod (2 * q))))
    (v (i : ZMod (2 * q)) + w (i : ZMod (2 * q)))
  have hcone := ordered_real_cyclic_two_ray_facets hq e hfan (fun i => v i + w i)
    (fun i => r i + lengths i) hpos hedge k hk₀ hkq
  rw [hsum] at hcone
  have hreindex := real_forward_surviving_facets_reindex e hfan k hk₀ hkq zR
  have hnormal (u : Site) : directionNormal (-u) = -directionNormal u := by
    ext g
    simp [directionNormal, determinant]
    ring
  have hindex (i : ℕ) : e ((q + i : ℕ) : ZMod (2 * q)) = -e (i : ZMod (2 * q)) := by
    rw [Nat.cast_add, add_comm, hfan.opposite]
  have hzero : zR 0 = (cut : ℝ) := by
    simp only [zR, Nat.cast_zero]
    change latticeNormal (directionNormal (e 0)) (latticeEmbedding (P.vertex 0 + G) + w 0) = (cut : ℝ)
    rw [map_add, latticeNormal_embedding, cyclicFactorSegmentVertices_normal_minimum e hfan.order hfan.opposite j t ht.le 0]
    rw [min_eq_left (by exact_mod_cast hνd : (0 : ℝ) ≤ (directionNormal (e 0) d : ℝ)), mul_zero, add_zero]
  have hlevel (i : ℕ) : zR (q + i) = (z i : ℝ) + t * min 0 (μ i d : ℝ) := by
    change latticeNormal (directionNormal (e ((q + i : ℕ) : ZMod (2 * q))))
      (latticeEmbedding (P.vertex ((q + i : ℕ) : ZMod (2 * q)) + G) + w ((q + i : ℕ) : ZMod (2 * q))) = _
    rw [map_add, latticeNormal_embedding,
      cyclicFactorSegmentVertices_normal_minimum e hfan.order hfan.opposite j t ht.le, hindex, hnormal]
  have hfirst : zR (q + k) = (β : ℝ) := by
    rw [hlevel, min_eq_right (by exact_mod_cast hηd.le : (η d : ℝ) ≤ 0), htprod, Int.cast_sub]
    ring
  have hlater : ∀ i ∈ Finset.Icc (k + 1) (q - 1), zR (q + i) = (z i : ℝ) := by
    intro i hi
    rw [hlevel, min_eq_left (by exact_mod_cast hμd i hi : (0 : ℝ) ≤ (μ i d : ℝ)), mul_zero, add_zero]
  have hidentify : {x : RealPlane | zR 0 ≤ latticeNormal (directionNormal (e 0)) x ∧
      ∀ i ∈ Finset.Icc k (q - 1), zR (q + i) ≤ latticeNormal (-directionNormal (e (i : ZMod (2 * q)))) x} =
        inwardLayerRegion η β (facetIndexSet (Finset.Icc (k + 1) (q - 1)))
          (facetNormals (directionNormal a) μ) (facetLevels cut z) := by
    ext x
    rw [mem_inward_region_adjoined_facet]
    constructor
    · intro hx
      have hfirst' := hx.2 k (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)
      rw [hfirst] at hfirst'
      refine ⟨hfirst', by simpa only [hzero] using hx.1, ?_⟩
      intro i hi
      obtain ⟨hki, hiq⟩ := Finset.mem_Icc.mp hi
      have h := hx.2 i (Finset.mem_Icc.mpr ⟨by omega, hiq⟩)
      rwa [hlater i hi] at h
    · rintro ⟨hη, hν, hrest⟩
      refine ⟨by rwa [hzero], ?_⟩
      intro i hi
      obtain ⟨hki, hiq⟩ := Finset.mem_Icc.mp hi
      by_cases he : i = k
      · subst i
        rwa [hfirst]
      · have hi' : i ∈ Finset.Icc (k + 1) (q - 1) := Finset.mem_Icc.mpr ⟨by omega, hiq⟩
        rw [hlater i hi']
        exact hrest i hi'
  refine ⟨t, ht, rfl, ?_⟩
  have hresult := hcone.trans (hreindex.trans hidentify)
  calc
    _ = (latticeHull T + {latticeEmbedding G} + lineInterval 0 (latticeEmbedding d) 0 t) + forwardTwoRayCone a b := hresult.symm
    _ = _ := by ac_rfl

end KumarNivat
