module

public import KumarNivat.PrimitiveRealLines
public import KumarNivat.PolygonStripPeriods
public import KumarNivat.ConvexNormalSlices

@[expose] public section

namespace KumarNivat

open scoped Pointwise

-- the band contains every lattice site between the two actual integer normal levels.
def normalBand (ν : Site →+ ℤ) (m M : ℤ) : Set Site := {g | m ≤ ν g ∧ ν g ≤ M}

-- convexity supplies a real hull point on every level between two attained lattice levels.
theorem hull_point_on_intermediate_normal_level (S : Finset Site) (ν : Site →+ ℤ) (m M : ℤ)
    (u₀ u₁ : Site) (hu₀ : u₀ ∈ S) (hu₁ : u₁ ∈ S) (h₀ : ν u₀ = m) (h₁ : ν u₁ = M)
    (g : Site) (hg : g ∈ normalBand ν m M) :
    ∃ z : RealPlane, z ∈ latticeHull S ∧ latticeNormal ν z = (ν g : ℝ) := by
  exact convex_point_on_intermediate_normal_level (latticeHull S) (convex_convexHull ℝ _)
    (latticeNormal ν) (m : ℝ) (M : ℝ) (latticeEmbedding u₀) (latticeEmbedding u₁)
    (subset_convexHull ℝ _ ⟨u₀, hu₀, rfl⟩) (subset_convexHull ℝ _ ⟨u₁, hu₁, rfl⟩)
    (by rw [latticeNormal_embedding, h₀]) (by rw [latticeNormal_embedding, h₁]) (ν g : ℝ)
    ⟨by exact_mod_cast hg.1, by exact_mod_cast hg.2⟩

-- primitivity converts a real point of an intermediate row into an actual consecutive lattice run.
theorem lattice_row_run_on_intermediate_primitive_level (S : Finset Site) (hS : LatticeConvex S)
    (p : Site) (hprimitive : Int.gcd p.1 p.2 = 1) (r : ℕ) (hr : 0 < r) (C : Set RealPlane)
    (hsum : latticeHull S = lineInterval 0 (latticeEmbedding p) 0 (r : ℝ) + C)
    (m M : ℤ) (u₀ u₁ : Site) (hu₀ : u₀ ∈ S) (hu₁ : u₁ ∈ S)
    (h₀ : directionNormal p u₀ = m) (h₁ : directionNormal p u₁ = M)
    (g : Site) (hg : g ∈ normalBand (directionNormal p) m M) :
    ∃ E : Site, ∃ d : ℤ, g = E + d • p ∧ E ∈ S ∧ ∀ i : Fin r, E + (i.val : ℤ) • p ∈ S := by
  obtain ⟨z, hz, hlevel⟩ := hull_point_on_intermediate_normal_level S (directionNormal p) m M
    u₀ u₁ hu₀ hu₁ h₀ h₁ g hg
  rw [hsum] at hz
  obtain ⟨w, ⟨s, _hs, rfl⟩, v, hv, he⟩ := Set.mem_add.mp hz
  simp only [zero_add] at he
  have hp : directionNormal p p = 0 := by simp [directionNormal, determinant, mul_comm]
  have hvz : latticeNormal (directionNormal p) v = latticeNormal (directionNormal p) z := by
    simpa only [map_add, map_smul, latticeNormal_embedding, hp, Int.cast_zero, smul_zero, zero_add]
      using congrArg (latticeNormal (directionNormal p)) he
  obtain ⟨κ, hκ⟩ := real_point_on_primitive_lattice_line p hprimitive g v (hvz.trans hlevel)
  have hline : (-κ) • latticeEmbedding p + v = latticeEmbedding g := by
    rw [hκ, neg_smul]
    abel
  exact lattice_row_run_from_residual_line_point S hS p r hr C hsum g (-κ) v hv hline

-- the segment summand fills every primitive row, so the translated strip is exactly the normal band.
theorem bilateralTranslateStrip_eq_normalBand (S : Finset Site) (hS : LatticeConvex S)
    (p : Site) (hprimitive : Int.gcd p.1 p.2 = 1) (r : ℕ) (hr : 0 < r) (C : Set RealPlane)
    (hsum : latticeHull S = lineInterval 0 (latticeEmbedding p) 0 (r : ℝ) + C)
    (m M : ℤ) (u₀ u₁ : Site) (hu₀ : u₀ ∈ S) (hu₁ : u₁ ∈ S)
    (h₀ : directionNormal p u₀ = m) (h₁ : directionNormal p u₁ = M)
    (hbounds : ∀ u ∈ S, m ≤ directionNormal p u ∧ directionNormal p u ≤ M) :
    bilateralTranslateStrip S p = normalBand (directionNormal p) m M := by
  have hp : directionNormal p p = 0 := by simp [directionNormal, determinant, mul_comm]
  ext g
  constructor
  · rintro ⟨⟨u, n⟩, rfl⟩
    change m ≤ directionNormal p (u.val + n • p) ∧ directionNormal p (u.val + n • p) ≤ M
    rw [map_add, map_zsmul, hp, smul_zero, add_zero]
    exact hbounds u.val u.property
  · intro hg
    obtain ⟨E, d, he, hE, _hrun⟩ := lattice_row_run_on_intermediate_primitive_level S hS p hprimitive
      r hr C hsum m M u₀ u₁ hu₀ hu₁ h₀ h₁ g hg
    exact ⟨(⟨E, hE⟩, d), he.symm⟩

-- deleting the facing edge deletes exactly its normal level from the complete translated strip.
theorem off_face_bilateralTranslateStrip_eq_normalBand (S : Finset Site) (hS : LatticeConvex S)
    (p : Site) (hprimitive : Int.gcd p.1 p.2 = 1) (r : ℕ) (hr : 0 < r) (C : Set RealPlane)
    (hsum : latticeHull S = lineInterval 0 (latticeEmbedding p) 0 (r : ℝ) + C)
    (m M : ℤ) (u₀ u₁ : Site) (hu₀ : u₀ ∈ S) (hu₁ : u₁ ∈ S)
    (h₀ : directionNormal p u₀ = m) (h₁ : directionNormal p u₁ = M)
    (hbounds : ∀ u ∈ S, m ≤ directionNormal p u ∧ directionNormal p u ≤ M) :
    bilateralTranslateStrip (S \ lowerLatticeFace S (directionNormal p) m) p =
      normalBand (directionNormal p) (m + 1) M := by
  classical
  have hp : directionNormal p p = 0 := by simp [directionNormal, determinant, mul_comm]
  have hwhole := bilateralTranslateStrip_eq_normalBand S hS p hprimitive r hr C hsum m M
    u₀ u₁ hu₀ hu₁ h₀ h₁ hbounds
  ext g
  constructor
  · rintro ⟨⟨u, n⟩, rfl⟩
    obtain ⟨hus, huf⟩ := Finset.mem_sdiff.mp u.property
    have hnormal : directionNormal p u.val ≠ m := by
      intro he
      exact huf (Finset.mem_filter.mpr ⟨hus, he⟩)
    have hb := hbounds u.val hus
    change m + 1 ≤ directionNormal p (u.val + n • p) ∧ directionNormal p (u.val + n • p) ≤ M
    rw [map_add, map_zsmul, hp, smul_zero, add_zero]
    omega
  · intro hg
    have hg' : g ∈ normalBand (directionNormal p) m M := ⟨by have h := hg.1; omega, hg.2⟩
    rw [← hwhole] at hg'
    obtain ⟨⟨u, n⟩, he⟩ := hg'
    have hnormal : directionNormal p g = directionNormal p u.val := by
      rw [← he, map_add, map_zsmul, hp, smul_zero, add_zero]
    have hum : u.val ∈ S \ lowerLatticeFace S (directionNormal p) m := by
      refine Finset.mem_sdiff.mpr ⟨u.property, ?_⟩
      intro hf
      have hface := (Finset.mem_filter.mp hf).2
      have hlow := hg.1
      rw [hnormal, hface] at hlow
      omega
    exact ⟨(⟨u.val, hum⟩, n), he⟩

end KumarNivat
