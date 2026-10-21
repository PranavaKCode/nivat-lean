module

public import KumarNivat.NewtonProductZonotope
public import Mathlib.Data.Int.Interval

@[expose] public section

namespace KumarNivat

-- saturating a finite lattice hull adds all its lattice points and preserves that exact hull.
theorem exists_latticeConvex_hull_saturation (T : Finset Site) :
    ∃ F : Finset Site, LatticeConvex F ∧ T ⊆ F ∧ latticeHull F = latticeHull T ∧
      ∀ g : Site, g ∈ F ↔ latticeEmbedding g ∈ latticeHull T := by
  classical
  let B : ℤ := ∑ u ∈ T, (|u.1| + |u.2|)
  have hb (u : Site) (hu : u ∈ T) : -B ≤ u.1 ∧ u.1 ≤ B ∧ -B ≤ u.2 ∧ u.2 ≤ B := by
    have ht : |u.1| + |u.2| ≤ B :=
      Finset.single_le_sum (fun v _hv => add_nonneg (abs_nonneg v.1) (abs_nonneg v.2)) hu
    have hx : |u.1| ≤ B := by linarith [abs_nonneg u.2]
    have hy : |u.2| ≤ B := by linarith [abs_nonneg u.1]
    exact ⟨(abs_le.mp hx).1, (abs_le.mp hx).2, (abs_le.mp hy).1, (abs_le.mp hy).2⟩
  have hgen : latticeEmbedding '' (T : Set Site) ⊆
      Set.Icc (-(B : ℝ)) (B : ℝ) ×ˢ Set.Icc (-(B : ℝ)) (B : ℝ) := by
    rintro _ ⟨u, hu, rfl⟩
    have he := hb u hu
    change (-(B : ℝ) ≤ (u.1 : ℝ) ∧ (u.1 : ℝ) ≤ (B : ℝ)) ∧
      (-(B : ℝ) ≤ (u.2 : ℝ) ∧ (u.2 : ℝ) ≤ (B : ℝ))
    exact ⟨⟨by exact_mod_cast he.1, by exact_mod_cast he.2.1⟩,
      ⟨by exact_mod_cast he.2.2.1, by exact_mod_cast he.2.2.2⟩⟩
  have hhull : latticeHull T ⊆
      Set.Icc (-(B : ℝ)) (B : ℝ) ×ˢ Set.Icc (-(B : ℝ)) (B : ℝ) :=
    convexHull_min hgen ((convex_Icc _ _).prod (convex_Icc _ _))
  let D := (Finset.Icc (-B) B).product (Finset.Icc (-B) B)
  let F := D.filter (fun g => latticeEmbedding g ∈ latticeHull T)
  have hbox (g : Site) (hg : latticeEmbedding g ∈ latticeHull T) : g ∈ D := by
    have he := hhull hg
    change (-(B : ℝ) ≤ (g.1 : ℝ) ∧ (g.1 : ℝ) ≤ (B : ℝ)) ∧
      (-(B : ℝ) ≤ (g.2 : ℝ) ∧ (g.2 : ℝ) ≤ (B : ℝ)) at he
    apply Finset.mem_product.mpr
    exact ⟨Finset.mem_Icc.mpr ⟨by exact_mod_cast he.1.1, by exact_mod_cast he.1.2⟩,
      Finset.mem_Icc.mpr ⟨by exact_mod_cast he.2.1, by exact_mod_cast he.2.2⟩⟩
  have hmem (g : Site) : g ∈ F ↔ latticeEmbedding g ∈ latticeHull T := by
    constructor
    · intro hg
      exact (Finset.mem_filter.mp hg).2
    · intro hg
      exact Finset.mem_filter.mpr ⟨hbox g hg, hg⟩
  have hTF : T ⊆ F := by
    intro u hu
    exact (hmem u).mpr (subset_convexHull ℝ _ ⟨u, hu, rfl⟩)
  have heq : latticeHull F = latticeHull T := by
    apply Set.Subset.antisymm
    · apply convexHull_min ?_ (convex_convexHull ℝ _)
      rintro _ ⟨u, hu, rfl⟩
      exact (hmem u).mp hu
    · exact convexHull_mono (Set.image_mono hTF)
  refine ⟨F, ?_, hTF, heq, hmem⟩
  intro g hg
  exact (hmem g).mpr (heq ▸ hg)

end KumarNivat
