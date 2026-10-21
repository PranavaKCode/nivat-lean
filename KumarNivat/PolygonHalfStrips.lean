module

public import KumarNivat.HalfStripTuplePeriods
public import KumarNivat.LatticeRowRuns

@[expose] public section

namespace KumarNivat

open scoped Pointwise

-- use every actual lattice site of the finite polygon as a forward row base.
def polygonHalfStrip (F : Finset Site) (a : Site) : Set Site :=
  sampledHalfStrip (fun u : F => u.val) a 0

-- a unit tangent summand makes the real geometric half-strip exactly the union of its forward integer translates.
theorem geometric_polygon_half_strip_eq_integer_translates (F : Finset Site) (hF : LatticeConvex F)
    (a : Site) (C : Set RealPlane)
    (hsum : latticeHull F = lineInterval 0 (latticeEmbedding a) 0 1 + C) :
    {g : Site | latticeEmbedding g ∈ latticeHull F + lineRay 0 (latticeEmbedding a) 0} =
      polygonHalfStrip F a := by
  ext g
  constructor
  · intro hg
    obtain ⟨v, hv, w, hw, he⟩ := Set.mem_add.mp hg
    rw [hsum] at hv
    obtain ⟨z, ⟨s, hs, rfl⟩, c, hc, hv⟩ := Set.mem_add.mp hv
    obtain ⟨t, ht, rfl⟩ := hw
    change (0 + s • latticeEmbedding a) + c = v at hv
    change v + (0 + t • latticeEmbedding a) = latticeEmbedding g at he
    have hrep : latticeEmbedding g = (s + t) • latticeEmbedding a + c := by
      rw [← he, ← hv]
      simp only [zero_add, add_smul]
      abel
    let d : ℤ := ⌊s + t⌋
    let E := g - d • a
    have hd : 0 ≤ d := Int.floor_nonneg.mpr (add_nonneg hs.1 ht)
    have hemb : latticeEmbedding E = (s + t - (d : ℝ)) • latticeEmbedding a + c := by
      dsimp [E]
      rw [latticeEmbedding_sub, latticeEmbedding_zsmul, hrep, sub_smul]
      abel
    have hEmem : E ∈ F := by
      apply hF
      rw [hsum, hemb]
      refine Set.add_mem_add ⟨s + t - (d : ℝ), ⟨Int.fract_nonneg (s + t), le_of_lt (Int.fract_lt_one (s + t))⟩,
        by simp only [zero_add]⟩ hc
    refine ⟨(⟨E, hEmem⟩, d.toNat), ?_⟩
    change E + (0 + (d.toNat : ℤ)) • a = g
    have hdcast : (d.toNat : ℤ) = d := by omega
    rw [zero_add, hdcast]
    dsimp [E]
    abel
  · intro hg
    obtain ⟨⟨u, n⟩, he⟩ := hg
    change u.val + (0 + (n : ℤ)) • a = g at he
    change latticeEmbedding g ∈ latticeHull F + lineRay 0 (latticeEmbedding a) 0
    rw [← he, latticeEmbedding_add, latticeEmbedding_zsmul]
    refine Set.add_mem_add (subset_convexHull ℝ _ ⟨u.val, u.property, rfl⟩) ?_
    refine ⟨((0 + (n : ℤ) : ℤ) : ℝ), ?_, by simp only [zero_add]⟩
    simpa only [Set.mem_Ici, zero_add, Int.cast_natCast] using (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))

end KumarNivat
