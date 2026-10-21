module

public import KumarNivat.NewtonCyclicFactorOrientation
public import Mathlib.Data.List.Sort

@[expose] public section

namespace KumarNivat

-- sort the actual signed factors by decreasing rational slope, including the horizontal endpoint.
def upperSortedFactors (hs : List Site) : List Site :=
  (hs.map upperFactorDirection).mergeSort (fun p q => decide (upperFactorSlope q ≤ upperFactorSlope p))

-- sorting preserves the complete actual signed factor list.
theorem upperSortedFactors_perm (hs : List Site) :
    (upperSortedFactors hs).Perm (hs.map upperFactorDirection) := List.mergeSort_perm _ _

-- no factor disappears when its slope is sorted.
theorem upperSortedFactors_length (hs : List Site) : (upperSortedFactors hs).length = hs.length := by
  simpa only [List.length_map] using (upperSortedFactors_perm hs).length_eq

-- signing either input cannot turn distinct factor lines into a parallel pair.
theorem upperFactorDirection_det_ne_zero (p q : Site) (hpq : determinant p q ≠ 0) :
    determinant (upperFactorDirection p) (upperFactorDirection q) ≠ 0 := by
  have hleft : determinant (-p) q = -determinant p q := by simp [determinant]; ring
  have hright : determinant p (-q) = -determinant p q := by simp [determinant]; ring
  have hboth : determinant (-p) (-q) = determinant p q := by simp [determinant]
  rcases upperFactorDirection_choice p with hp | hp <;> rcases upperFactorDirection_choice q with hq | hq
  · rwa [hp, hq]
  · rw [hp, hq, hright]
    exact neg_ne_zero.mpr hpq
  · rw [hp, hq, hleft]
    exact neg_ne_zero.mpr hpq
  · rwa [hp, hq, hboth]

-- the sorted list retains every actual factor and makes all earlier-to-later turns strictly positive.
theorem upperSortedFactors_actual_data (hs : List Site) (hdirs : ∀ h ∈ hs, h ≠ 0)
    (hpairs : hs.Pairwise (fun p q => determinant p q ≠ 0)) :
    (upperSortedFactors hs).Perm (hs.map upperFactorDirection) ∧
      (upperSortedFactors hs).length = hs.length ∧
      (∀ h ∈ upperSortedFactors hs, InUpperFactorHalf h) ∧
      (upperSortedFactors hs).Pairwise (fun p q => 0 < determinant p q) ∧
      ∀ h ∈ upperSortedFactors hs, ∃ q ∈ hs, h = q ∨ h = -q := by
  classical
  let R : Site → Site → Prop := fun p q => upperFactorSlope q ≤ upperFactorSlope p
  let _ : IsTrans Site R := ⟨fun _p _q _s hpq hqs => le_trans hqs hpq⟩
  let _ : Std.Total R := ⟨fun p q => le_total (upperFactorSlope q) (upperFactorSlope p)⟩
  have hperm : (upperSortedFactors hs).Perm (hs.map upperFactorDirection) :=
    upperSortedFactors_perm hs
  have hupper (h : Site) (hh : h ∈ upperSortedFactors hs) : InUpperFactorHalf h := by
    have hm := hperm.mem_iff.mp hh
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hm
    exact upperFactorDirection_in_upper q (hdirs q hq)
  have hmap : (hs.map upperFactorDirection).Pairwise (fun p q => determinant p q ≠ 0) := by
    rw [List.pairwise_map]
    exact hpairs.imp (fun {p q} hpq => upperFactorDirection_det_ne_zero p q hpq)
  have hsymm : ∀ {p q : Site}, determinant p q ≠ 0 → determinant q p ≠ 0 := by
    intro p q hpq
    have he : determinant q p = -determinant p q := by simp [determinant]; ring
    rw [he]
    exact neg_ne_zero.mpr hpq
  have hnonparallel := (hperm.pairwise_iff hsymm).mpr hmap
  have hsort : (upperSortedFactors hs).Pairwise R := List.pairwise_mergeSort' R _
  have hpositive : (upperSortedFactors hs).Pairwise (fun p q => 0 < determinant p q) := by
    apply (hsort.and hnonparallel).imp_of_mem
    intro p q hp hq hrel
    have hnonneg := upperFactorSlope_det_nonnegative p q (hupper p hp) (hupper q hq) hrel.1
    exact lt_of_le_of_ne hnonneg (Ne.symm hrel.2)
  refine ⟨hperm, ?_, hupper, hpositive, ?_⟩
  · simpa only [List.length_map] using hperm.length_eq
  · intro h hh
    obtain ⟨q, hq, he⟩ := List.mem_map.mp (hperm.mem_iff.mp hh)
    refine ⟨q, hq, ?_⟩
    rw [← he]
    exact upperFactorDirection_choice q

end KumarNivat
