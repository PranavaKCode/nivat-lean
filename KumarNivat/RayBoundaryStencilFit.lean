module

public import KumarNivat.ExposedFacetGeometry
public import KumarNivat.MinkowskiStencilFit
public import KumarNivat.SupportingFaceGeometry
public import KumarNivat.PairedDirections

@[expose] public section

namespace KumarNivat

open scoped Pointwise

-- the supporting segment and forward recession direction fit the entire stencil at every boundary point.
theorem boundary_stencil_fit_of_minkowski_recession {K : Type*} [CommRing K]
    (f : Laurent K) (ν : Site →+ ℤ) (m β : ℤ)
    (hmin : ∀ u ∈ f.coeff.support, m ≤ ν u) (q₀ p : Site)
    (hq₀mem : q₀ ∈ f.coeff.support) (hq₀ : ν q₀ = m) (t : ℕ)
    (hface : normalFace (latticeHull f.coeff.support) (latticeNormal ν) (m : ℝ) =
      lineInterval (latticeEmbedding q₀) (latticeEmbedding p) 0 (t : ℝ))
    (P C : Set RealPlane) (hsum : P = latticeHull f.coeff.support + C)
    (hbound : ∀ z ∈ P, (β : ℝ) ≤ latticeNormal ν z)
    (hforward : ∀ z ∈ P, ∀ s : ℝ, 0 ≤ s → z + s • latticeEmbedding p ∈ P)
    (g : Site) (hg : latticeEmbedding g ∈ P) (hlevel : ν g = β) :
    ∀ u ∈ f.coeff.support, latticeEmbedding (g - q₀ + u) ∈ P := by
  have hq₀hull : latticeEmbedding q₀ ∈ latticeHull f.coeff.support :=
    subset_convexHull ℝ _ ⟨q₀, hq₀mem, rfl⟩
  have hC : ∀ z ∈ C, ((β - m : ℤ) : ℝ) ≤ latticeNormal ν z := by
    intro z hz
    have hmem : latticeEmbedding q₀ + z ∈ P := by
      rw [hsum]
      exact Set.add_mem_add hq₀hull hz
    have hb := hbound _ hmem
    rw [map_add, latticeNormal_embedding, hq₀] at hb
    push_cast
    linarith
  have hfacet : latticeEmbedding g ∈ normalFace (latticeHull f.coeff.support + C)
      (latticeNormal ν) ((m : ℝ) + ((β - m : ℤ) : ℝ)) := by
    refine ⟨by rwa [← hsum], ?_⟩
    rw [latticeNormal_embedding, hlevel]
    push_cast
    ring
  rw [normalFace_add _ _ _ _ _ (lower_face_hull_bound f.coeff.support ν m hmin) hC, hface] at hfacet
  obtain ⟨z, hz, w, hw, he⟩ := Set.mem_add.mp hfacet
  obtain ⟨s, hs, hzs⟩ := hz
  have hsite : latticeEmbedding g = latticeEmbedding q₀ + s • latticeEmbedding p + w := by
    rw [← he, ← hzs]
  intro u hu
  have huhull : latticeEmbedding u ∈ latticeHull f.coeff.support :=
    subset_convexHull ℝ _ ⟨u, hu, rfl⟩
  have humem : latticeEmbedding u + w ∈ P := by
    rw [hsum]
    exact Set.add_mem_add huhull hw.1
  have hfit := hforward (latticeEmbedding u + w) humem s hs.1
  have hemb : latticeEmbedding (g - q₀ + u) =
      (latticeEmbedding u + w) + s • latticeEmbedding p := by
    rw [latticeEmbedding_add, latticeEmbedding_sub, hsite]
    abel
  rwa [← hemb] at hfit

end KumarNivat
