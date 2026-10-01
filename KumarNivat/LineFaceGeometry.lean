import KumarNivat.SupportingFaceGeometry

namespace KumarNivat

open scoped Pointwise

-- real endpoint parameters allow rational endpoints without changing the lattice direction.
def lineInterval (A v : RealPlane) (a b : ℝ) : Set RealPlane :=
  (fun s : ℝ => A + s • v) '' Set.Icc a b

-- a ray uses the same parameterization and its actual lower endpoint.
def lineRay (A v : RealPlane) (a : ℝ) : Set RealPlane :=
  (fun s : ℝ => A + s • v) '' Set.Ici a

-- parameter intervals are ordinary real segments, including the degenerate case.
theorem lineInterval_eq_segment (A v : RealPlane) (a b : ℝ) (hab : a ≤ b) :
    lineInterval A v a b = segment ℝ (A + a • v) (A + b • v) := by
  have he : (AffineMap.lineMap A (A + v) : ℝ → RealPlane) = (fun s => A + s • v) := by
    funext s
    simp only [AffineMap.lineMap_apply_module', add_sub_cancel_left, add_comm]
  have hs := image_segment ℝ (AffineMap.lineMap A (A + v)) a b
  rw [segment_eq_Icc hab, he] at hs
  simpa only [lineInterval, AffineMap.lineMap_apply_module', add_sub_cancel_left, add_comm] using hs

-- convexity follows from the actual segment description.
theorem lineInterval_convex (A v : RealPlane) (a b : ℝ) (hab : a ≤ b) :
    Convex ℝ (lineInterval A v a b) := by
  rw [lineInterval_eq_segment A v a b hab]
  exact convex_segment _ _

-- the real embedding preserves subtraction of lattice sites.
theorem latticeEmbedding_sub (u v : Site) :
    latticeEmbedding (u - v) = latticeEmbedding u - latticeEmbedding v := by
  ext <;> simp [latticeEmbedding]

-- an integer step becomes the corresponding real parameter on the same line.
theorem latticeEmbedding_zsmul (n : ℤ) (p : Site) :
    latticeEmbedding (n • p) = (n : ℝ) • latticeEmbedding p := by
  ext <;> simp [latticeEmbedding, zsmul_eq_mul]

-- scalar interval addition gives the exact finite face of the minkowski sum.
theorem lineInterval_add (A B v : RealPlane) (t a b : ℝ) (ht : 0 ≤ t) (hab : a ≤ b) :
    lineInterval A v 0 t + lineInterval B v a b = lineInterval (A + B) v a (b + t) := by
  ext x
  constructor
  · intro hx
    obtain ⟨u, ⟨r, ⟨hr₀, hrt⟩, rfl⟩, w, ⟨s, ⟨hsa, hsb⟩, rfl⟩, rfl⟩ := Set.mem_add.mp hx
    refine ⟨r + s, ⟨by linarith, by linarith⟩, ?_⟩
    simp only [add_smul]
    abel
  · rintro ⟨s, ⟨hsa, hst⟩, rfl⟩
    by_cases hsb : s ≤ b
    · refine Set.mem_add.mpr ⟨A, ⟨0, ⟨le_rfl, ht⟩, by simp⟩,
        B + s • v, ⟨s, ⟨hsa, hsb⟩, rfl⟩, ?_⟩
      abel
    · refine Set.mem_add.mpr ⟨A + (s - b) • v, ⟨s - b, ⟨by linarith, by linarith⟩, rfl⟩,
        B + b • v, ⟨b, ⟨hab, le_rfl⟩, rfl⟩, ?_⟩
      simp only [sub_smul]
      abel

-- adding a bounded face to a forward ray leaves the ray's initial endpoint unchanged.
theorem lineInterval_add_ray (A B v : RealPlane) (t a : ℝ) (ht : 0 ≤ t) :
    lineInterval A v 0 t + lineRay B v a = lineRay (A + B) v a := by
  ext x
  constructor
  · intro hx
    obtain ⟨u, ⟨r, ⟨hr₀, _hrt⟩, rfl⟩, w, ⟨s, hsa, rfl⟩, rfl⟩ := Set.mem_add.mp hx
    change a ≤ s at hsa
    refine ⟨r + s, by change a ≤ r + s; linarith, ?_⟩
    simp only [add_smul]
    abel
  · rintro ⟨s, hsa, rfl⟩
    refine Set.mem_add.mpr ⟨A, ⟨0, ⟨le_rfl, ht⟩, by simp⟩,
      B + s • v, ⟨s, hsa, rfl⟩, ?_⟩
    abel

-- the actual exposed coefficient endpoints determine the whole real newton face.
theorem normalFace_latticeHull_eq_lineInterval (S : Finset Site) (ν : Site →+ ℤ) (m : ℤ)
    (hmin : ∀ u ∈ S, m ≤ ν u) (q₀ p : Site) (t : ℕ) (hq₀ : q₀ ∈ S)
    (hq₁ : q₀ + (t : ℤ) • p ∈ S) (hlevel : ν q₀ = m) (hp : ν p = 0)
    (hpoints : ∀ u ∈ S, ν u = m → ∃ i : Fin (t + 1), u = q₀ + (i.val : ℤ) • p) :
    normalFace (latticeHull S) (latticeNormal ν) (m : ℝ) =
      lineInterval (latticeEmbedding q₀) (latticeEmbedding p) 0 (t : ℝ) := by
  classical
  rw [normalFace_latticeHull S ν m hmin q₀ hq₀ hlevel]
  apply Set.Subset.antisymm
  · apply convexHull_min _ (lineInterval_convex _ _ _ _ (Nat.cast_nonneg t))
    rintro _ ⟨u, hu, rfl⟩
    obtain ⟨hum, he⟩ := Finset.mem_filter.mp hu
    obtain ⟨i, rfl⟩ := hpoints u hum he
    refine ⟨(i.val : ℝ), ⟨Nat.cast_nonneg _, ?_⟩, ?_⟩
    · exact_mod_cast Nat.le_of_lt_succ i.isLt
    · rw [latticeEmbedding_add, latticeEmbedding_zsmul]
      simp only [Int.cast_natCast]
  · rw [lineInterval_eq_segment _ _ _ _ (Nat.cast_nonneg t)]
    simp only [zero_smul, add_zero]
    apply (convex_convexHull ℝ _).segment_subset
    · exact subset_convexHull ℝ _ ⟨q₀, Finset.mem_filter.mpr ⟨hq₀, hlevel⟩, rfl⟩
    · have hnormal : ν (q₀ + (t : ℤ) • p) = m := by
        rw [map_add, map_zsmul, hp, smul_zero, add_zero, hlevel]
      have he := subset_convexHull ℝ (latticeEmbedding ''
        (S.filter (fun u => ν u = m) : Set Site))
        ⟨q₀ + (t : ℤ) • p, Finset.mem_filter.mpr ⟨hq₁, hnormal⟩, rfl⟩
      simpa only [latticeEmbedding_add, latticeEmbedding_zsmul, Int.cast_natCast] using he

end KumarNivat
