module

public import KumarNivat.PolyhedralRays

@[expose] public section

namespace KumarNivat

-- one extra index records the moving facet alongside the same finite fixed constraints.
noncomputable def facetIndexSet {I : Type*} (J : Finset I) : Finset (Option I) := by
  classical
  exact insert none (J.image some)

-- the extra facet has its own normal while every old index keeps its original normal.
def facetNormals {I : Type*} (η : Site →+ ℤ) (μ : I → Site →+ ℤ) : Option I → Site →+ ℤ
  | none => η
  | some i => μ i

-- relaxing the extra facet changes only its own support level.
def facetLevels {I : Type*} (β : ℤ) (z : I → ℤ) : Option I → ℤ
  | none => β
  | some i => z i

@[simp] theorem mem_facetIndexSet_none {I : Type*} (J : Finset I) : none ∈ facetIndexSet J := by
  classical
  simp [facetIndexSet]

@[simp] theorem mem_facetIndexSet_some {I : Type*} (J : Finset I) (i : I) :
    some i ∈ facetIndexSet J ↔ i ∈ J := by
  classical
  simp [facetIndexSet]

-- the extended index set is exactly the two displayed facet bounds and the original remaining constraints.
theorem mem_inward_region_adjoined_facet {I : Type*} (ν η : Site →+ ℤ) (cut β : ℤ)
    (J : Finset I) (μ : I → Site →+ ℤ) (z : I → ℤ) (w : RealPlane) :
    w ∈ inwardLayerRegion ν cut (facetIndexSet J) (facetNormals η μ) (facetLevels β z) ↔
      (cut : ℝ) ≤ latticeNormal ν w ∧ (β : ℝ) ≤ latticeNormal η w ∧
        ∀ i ∈ J, (z i : ℝ) ≤ latticeNormal (μ i) w := by
  constructor
  · intro h
    exact ⟨h.1, h.2 none (mem_facetIndexSet_none J),
      fun i hi => h.2 (some i) ((mem_facetIndexSet_some J i).mpr hi)⟩
  · rintro ⟨hν, hη, hμ⟩
    refine ⟨hν, ?_⟩
    intro i hi
    cases i with
    | none => exact hη
    | some i => exact hμ i ((mem_facetIndexSet_some J i).mp hi)

-- either boundary may be displayed as the moving facet without changing the real working region.
theorem inward_region_adjoined_facet_swap {I : Type*} (ν η : Site →+ ℤ) (cut β : ℤ)
    (J : Finset I) (μ : I → Site →+ ℤ) (z : I → ℤ) :
    inwardLayerRegion ν cut (facetIndexSet J) (facetNormals η μ) (facetLevels β z) =
      inwardLayerRegion η β (facetIndexSet J) (facetNormals ν μ) (facetLevels cut z) := by
  ext w
  rw [mem_inward_region_adjoined_facet, mem_inward_region_adjoined_facet]
  exact ⟨fun h => ⟨h.2.1, h.1, h.2.2⟩, fun h => ⟨h.2.1, h.1, h.2.2⟩⟩

-- the old half-plane and all unchanged inequalities give the strict transverse slopes required for ambiguity placement.
theorem facetNormals_positive {I : Type*} (J : Finset I) (η : Site →+ ℤ) (μ : I → Site →+ ℤ)
    (b : Site) (hη : 0 < η b) (hμ : ∀ i ∈ J, 0 < μ i b) :
    ∀ i ∈ facetIndexSet J, 0 < facetNormals η μ i b := by
  intro i hi
  cases i with
  | none => exact hη
  | some i => exact hμ i ((mem_facetIndexSet_some J i).mp hi)

end KumarNivat
