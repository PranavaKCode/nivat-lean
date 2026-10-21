module

public import KumarNivat.PrimitiveDirections
public import KumarNivat.RectangleQuotient
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace KumarNivat

noncomputable section

-- real coordinates give the manuscript's actual convex hull of the lattice polygon.
abbrev RealPlane := ℝ × ℝ

-- the embedding changes only the coefficient field, not the lattice basis.
def latticeEmbedding (u : Site) : RealPlane := ((u.1 : ℝ), (u.2 : ℝ))

-- different lattice sites remain different real points.
theorem latticeEmbedding_injective : Function.Injective latticeEmbedding := by
  intro u v he
  exact Prod.ext (Int.cast_injective (congrArg Prod.fst he))
    (Int.cast_injective (congrArg Prod.snd he))

-- this is the actual convex hull of the finite lattice observation set.
def latticeHull (S : Finset Site) : Set RealPlane :=
  convexHull ℝ (latticeEmbedding '' (S : Set Site))

-- lattice convexity requires every lattice point of the convex hull to belong to the set.
def LatticeConvex (S : Finset Site) : Prop :=
  ∀ u : Site, latticeEmbedding u ∈ latticeHull S → u ∈ S

-- vertices are the extreme points of that convex hull.
def IsLatticeVertex (S : Finset Site) (v : Site) : Prop :=
  latticeEmbedding v ∈ (latticeHull S).extremePoints ℝ

-- a finite hull's vertices are actual sites of the original set.
theorem latticeVertex_mem (S : Finset Site) (v : Site) (hv : IsLatticeVertex S v) : v ∈ S := by
  obtain ⟨u, hu, he⟩ := extremePoints_convexHull_subset hv
  exact latticeEmbedding_injective he ▸ hu

-- a vertex cannot be recovered by taking the convex hull of all the other sites.
theorem latticeVertex_notMem_erased_hull (S : Finset Site) (v : Site)
    (hv : IsLatticeVertex S v) : latticeEmbedding v ∉ latticeHull (S.erase v) := by
  have hext := (Convex.mem_extremePoints_iff_mem_sdiff_convexHull_sdiff
    (convex_convexHull ℝ (latticeEmbedding '' (S : Set Site)))).mp hv
  have hsub : latticeEmbedding '' (S.erase v : Set Site) ⊆ latticeHull S \ {latticeEmbedding v} := by
    rintro _ ⟨u, hu, rfl⟩
    have hum := Finset.mem_erase.mp hu
    refine ⟨subset_convexHull ℝ _ ⟨u, hum.2, rfl⟩, ?_⟩
    intro he
    exact hum.1 (latticeEmbedding_injective (Set.mem_singleton_iff.mp he))
  exact fun hmem => hext.2 (convexHull_mono hsub hmem)

-- deleting a vertex preserves lattice convexity.
theorem LatticeConvex.erase_vertex {S : Finset Site} (hS : LatticeConvex S)
    (v : Site) (hv : IsLatticeVertex S v) : LatticeConvex (S.erase v) := by
  intro u hu
  have hsub : latticeEmbedding '' (S.erase v : Set Site) ⊆ latticeEmbedding '' (S : Set Site) :=
    Set.image_mono (by intro x hx; exact Finset.mem_of_mem_erase hx)
  have hum : u ∈ S := hS u (convexHull_mono hsub hu)
  apply Finset.mem_erase.mpr
  refine ⟨?_, hum⟩
  intro he
  exact latticeVertex_notMem_erased_hull S v hv (he ▸ hu)

-- an integer lattice normal extends to a real linear functional.
def latticeNormal (ν : Site →+ ℤ) : RealPlane →ₗ[ℝ] ℝ where
  toFun x := (ν (1, 0) : ℝ) * x.1 + (ν (0, 1) : ℝ) * x.2
  map_add' x y := by simp; ring
  map_smul' a x := by simp; ring

-- the real functional agrees exactly with the given integer normal on lattice sites.
theorem latticeNormal_embedding (ν : Site →+ ℤ) (u : Site) :
    latticeNormal ν (latticeEmbedding u) = (ν u : ℝ) := by
  have he := normal_cramer_identity ν (1, 0) (0, 1) u
  simp only [determinant, one_mul, mul_one, zero_mul, mul_zero, sub_zero] at he
  change (ν (1, 0) : ℝ) * (u.1 : ℝ) + (ν (0, 1) : ℝ) * (u.2 : ℝ) = (ν u : ℝ)
  rw [he]
  push_cast
  ring

-- intersecting with an integer half-plane preserves every lattice point of the hull.
theorem LatticeConvex.halfplane_filter {S : Finset Site} (hS : LatticeConvex S)
    (ν : Site →+ ℤ) (m : ℤ) : LatticeConvex (S.filter (fun u => m ≤ ν u)) := by
  classical
  intro u hu
  have hsub : latticeEmbedding '' (S.filter (fun u => m ≤ ν u) : Set Site) ⊆
      latticeEmbedding '' (S : Set Site) := Set.image_mono (by
    intro x hx
    exact (Finset.mem_filter.mp hx).1)
  have hum : u ∈ S := hS u (convexHull_mono hsub hu)
  have hhalf : latticeEmbedding '' (S.filter (fun u => m ≤ ν u) : Set Site) ⊆
      {x : RealPlane | (m : ℝ) ≤ latticeNormal ν x} := by
    rintro _ ⟨x, hx, rfl⟩
    change (m : ℝ) ≤ latticeNormal ν (latticeEmbedding x)
    rw [latticeNormal_embedding]
    exact_mod_cast (Finset.mem_filter.mp hx).2
  have hconv : Convex ℝ {x : RealPlane | (m : ℝ) ≤ latticeNormal ν x} :=
    (convex_Ici (m : ℝ)).linear_preimage (latticeNormal ν)
  have hbound := convexHull_min hhalf hconv hu
  change (m : ℝ) ≤ latticeNormal ν (latticeEmbedding u) at hbound
  rw [latticeNormal_embedding] at hbound
  exact Finset.mem_filter.mpr ⟨hum, by exact_mod_cast hbound⟩

-- the supporting face contains exactly the sites on the minimizing integer normal level.
def lowerLatticeFace (S : Finset Site) (ν : Site →+ ℤ) (m : ℤ) : Finset Site :=
  S.filter (fun u => ν u = m)

-- deleting a supporting face is intersection with the next inward integer half-plane.
theorem LatticeConvex.sdiff_lower_face {S : Finset Site} (hS : LatticeConvex S)
    (ν : Site →+ ℤ) (m : ℤ) (hmin : ∀ u ∈ S, m ≤ ν u) :
    LatticeConvex (S \ lowerLatticeFace S ν m) := by
  classical
  have he : S \ lowerLatticeFace S ν m = S.filter (fun u => m + 1 ≤ ν u) := by
    ext u
    simp only [Finset.mem_sdiff, lowerLatticeFace, Finset.mem_filter]
    constructor
    · rintro ⟨hu, hn⟩
      have hb := hmin u hu
      have hne : ν u ≠ m := fun he => hn ⟨hu, he⟩
      exact ⟨hu, by omega⟩
    · rintro ⟨hu, hb⟩
      exact ⟨hu, fun he => by have hlevel := he.2; omega⟩
  rw [he]
  exact hS.halfplane_filter ν (m + 1)

-- each axis-aligned observation rectangle is already lattice convex.
theorem latticeConvex_rectangle (k n : ℕ) : LatticeConvex (rectangle k n) := by
  let box : Set RealPlane := Set.Icc (0 : ℝ) ((k : ℝ) - 1) ×ˢ Set.Icc (0 : ℝ) ((n : ℝ) - 1)
  have hconv : Convex ℝ box := (convex_Icc _ _).prod (convex_Icc _ _)
  have hsub : latticeEmbedding '' (rectangle k n : Set Site) ⊆ box := by
    rintro _ ⟨u, hu, rfl⟩
    have hb := (mem_rectangle_iff u k n).mp hu
    change ((0 : ℝ) ≤ (u.1 : ℝ) ∧ (u.1 : ℝ) ≤ (k : ℝ) - 1) ∧
      ((0 : ℝ) ≤ (u.2 : ℝ) ∧ (u.2 : ℝ) ≤ (n : ℝ) - 1)
    refine ⟨⟨by exact_mod_cast hb.1, ?_⟩, ⟨by exact_mod_cast hb.2.2.1, ?_⟩⟩
    · exact_mod_cast (show u.1 ≤ (k : ℤ) - 1 by omega)
    · exact_mod_cast (show u.2 ≤ (n : ℤ) - 1 by omega)
  intro u hu
  have hb := convexHull_min hsub hconv hu
  change ((0 : ℝ) ≤ (u.1 : ℝ) ∧ (u.1 : ℝ) ≤ (k : ℝ) - 1) ∧
    ((0 : ℝ) ≤ (u.2 : ℝ) ∧ (u.2 : ℝ) ≤ (n : ℝ) - 1) at hb
  apply (mem_rectangle_iff u k n).mpr
  have hxlo : (0 : ℤ) ≤ u.1 := by exact_mod_cast hb.1.1
  have hxhi : u.1 ≤ (k : ℤ) - 1 := by exact_mod_cast hb.1.2
  have hylo : (0 : ℤ) ≤ u.2 := by exact_mod_cast hb.2.1
  have hyhi : u.2 ≤ (n : ℤ) - 1 := by exact_mod_cast hb.2.2
  omega

end

end KumarNivat
