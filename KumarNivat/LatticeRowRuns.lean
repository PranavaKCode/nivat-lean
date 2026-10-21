module

public import KumarNivat.LineFaceGeometry
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Tactic.Choose

@[expose] public section

namespace KumarNivat

open scoped Pointwise

-- a contained real segment gives an integer starting site for its run without requiring a global summand.
theorem lattice_row_run_from_residual_line_point_of_subset (S : Finset Site) (hS : LatticeConvex S)
    (p : Site) (r : ℕ) (hr : 0 < r) (C : Set RealPlane)
    (hsum : lineInterval 0 (latticeEmbedding p) 0 (r : ℝ) + C ⊆ latticeHull S)
    (u : Site) (s : ℝ) (v : RealPlane) (hv : v ∈ C)
    (he : s • latticeEmbedding p + v = latticeEmbedding u) :
    ∃ E : Site, ∃ d : ℤ, u = E + d • p ∧ E ∈ S ∧
      ∀ i : Fin r, E + (i.val : ℤ) • p ∈ S := by
  let d : ℤ := ⌊s⌋
  let E := u - d • p
  have hd₀ : (d : ℝ) ≤ s := Int.floor_le s
  have hd₁ : s < (d : ℝ) + 1 := Int.lt_floor_add_one s
  have hemb : latticeEmbedding E = (s - (d : ℝ)) • latticeEmbedding p + v := by
    dsimp [E]
    rw [latticeEmbedding_sub, latticeEmbedding_zsmul, ← he, sub_smul]
    abel
  have hrun (i : Fin r) : E + (i.val : ℤ) • p ∈ S := by
    apply hS
    apply hsum
    rw [latticeEmbedding_add, latticeEmbedding_zsmul, hemb]
    have hi : (i.val : ℝ) + 1 ≤ (r : ℝ) := by exact_mod_cast Nat.succ_le_of_lt i.isLt
    have hi₀ : (0 : ℝ) ≤ (i.val : ℝ) := Nat.cast_nonneg _
    have hseg : (s - (d : ℝ) + (i.val : ℝ)) • latticeEmbedding p ∈
        lineInterval 0 (latticeEmbedding p) 0 (r : ℝ) := by
      refine ⟨s - (d : ℝ) + (i.val : ℝ), ⟨by linarith, by linarith⟩, by simp only [zero_add]⟩
    have hm := Set.add_mem_add hseg hv
    have hpoint : (s - (d : ℝ)) • latticeEmbedding p + v +
        ((i.val : ℤ) : ℝ) • latticeEmbedding p =
        (s - (d : ℝ) + (i.val : ℝ)) • latticeEmbedding p + v := by
      rw [Int.cast_natCast, add_smul]
      ac_rfl
    rw [hpoint]
    exact hm
  refine ⟨E, d, ?_, ?_, hrun⟩
  · dsimp [E]
    abel
  · simpa only [Fin.val_zero, Nat.cast_zero, zero_smul, add_zero] using hrun ⟨0, hr⟩

-- the original segment-summand API delegates to the same local row-run construction.
theorem lattice_row_run_from_residual_line_point (S : Finset Site) (hS : LatticeConvex S)
    (p : Site) (r : ℕ) (hr : 0 < r) (C : Set RealPlane)
    (hsum : latticeHull S = lineInterval 0 (latticeEmbedding p) 0 (r : ℝ) + C)
    (u : Site) (s : ℝ) (v : RealPlane) (hv : v ∈ C)
    (he : s • latticeEmbedding p + v = latticeEmbedding u) :
    ∃ E : Site, ∃ d : ℤ, u = E + d • p ∧ E ∈ S ∧
      ∀ i : Fin r, E + (i.val : ℤ) • p ∈ S :=
  lattice_row_run_from_residual_line_point_of_subset S hS p r hr C
    (by intro z hz; rw [hsum]; exact hz) u s v hv he

-- every row through an actual polygon site meets the residual summand on that same line.
theorem lattice_row_run_of_segment_summand (S : Finset Site) (hS : LatticeConvex S)
    (p : Site) (r : ℕ) (hr : 0 < r) (C : Set RealPlane)
    (hsum : latticeHull S = lineInterval 0 (latticeEmbedding p) 0 (r : ℝ) + C)
    (u : Site) (hu : u ∈ S) :
    ∃ E : Site, ∃ d : ℤ, u = E + d • p ∧ E ∈ S ∧
      ∀ i : Fin r, E + (i.val : ℤ) • p ∈ S := by
  have hum : latticeEmbedding u ∈ latticeHull S := subset_convexHull ℝ _ ⟨u, hu, rfl⟩
  rw [hsum] at hum
  obtain ⟨w, ⟨s, _hs, rfl⟩, v, hv, he⟩ := Set.mem_add.mp hum
  simp only [zero_add] at he
  exact lattice_row_run_from_residual_line_point S hS p r hr C hsum u s v hv he

-- deleting a tangent supporting face preserves every run on each remaining normal level.
theorem lattice_row_run_off_tangent_face (S : Finset Site) (hS : LatticeConvex S)
    (p : Site) (r : ℕ) (hr : 0 < r) (C : Set RealPlane)
    (hsum : latticeHull S = lineInterval 0 (latticeEmbedding p) 0 (r : ℝ) + C)
    (ν : Site →+ ℤ) (m : ℤ) (hp : ν p = 0) (u : Site)
    (hu : u ∈ S \ lowerLatticeFace S ν m) :
    ∃ E : Site, ∃ d : ℤ, u = E + d • p ∧ E ∈ S \ lowerLatticeFace S ν m ∧
      ∀ i : Fin r, E + (i.val : ℤ) • p ∈ S \ lowerLatticeFace S ν m := by
  classical
  obtain ⟨hus, huf⟩ := Finset.mem_sdiff.mp hu
  obtain ⟨E, d, he, hEs, hrun⟩ := lattice_row_run_of_segment_summand S hS p r hr C hsum u hus
  have huν : ν u ≠ m := by
    intro huν
    exact huf (Finset.mem_filter.mpr ⟨hus, huν⟩)
  have hEν : ν E = ν u := by rw [he, map_add, map_zsmul, hp, smul_zero, add_zero]
  have hEr : E ∈ S \ lowerLatticeFace S ν m := by
    refine Finset.mem_sdiff.mpr ⟨hEs, ?_⟩
    intro hf
    exact huν (hEν.symm.trans (Finset.mem_filter.mp hf).2)
  refine ⟨E, d, he, hEr, ?_⟩
  intro i
  refine Finset.mem_sdiff.mpr ⟨hrun i, ?_⟩
  intro hf
  have hlevel : ν (E + (i.val : ℤ) • p) = ν u := by
    rw [map_add, map_zsmul, hp, smul_zero, add_zero, hEν]
  exact huν (hlevel.symm.trans (Finset.mem_filter.mp hf).2)

-- the row choice retains an integer translate of every original off-face site.
theorem exists_off_face_row_run_selector (S : Finset Site) (hS : LatticeConvex S)
    (p : Site) (r : ℕ) (hr : 0 < r) (C : Set RealPlane)
    (hsum : latticeHull S = lineInterval 0 (latticeEmbedding p) 0 (r : ℝ) + C)
    (ν : Site →+ ℤ) (m : ℤ) (hp : ν p = 0) :
    ∃ E : {u : Site // u ∈ S \ lowerLatticeFace S ν m} → Site,
      (∀ u, E u ∈ S \ lowerLatticeFace S ν m) ∧
      (∀ u, ∃ d : ℤ, u.val = E u + d • p) ∧
      ∀ u, ∀ i : Fin r, E u + (i.val : ℤ) • p ∈ S \ lowerLatticeFace S ν m := by
  classical
  have hruns (u : {u : Site // u ∈ S \ lowerLatticeFace S ν m}) :=
    lattice_row_run_off_tangent_face S hS p r hr C hsum ν m hp u.val u.property
  choose E d he hmem hrun using hruns
  exact ⟨E, hmem, fun u => ⟨d u, he u⟩, hrun⟩

end KumarNivat
