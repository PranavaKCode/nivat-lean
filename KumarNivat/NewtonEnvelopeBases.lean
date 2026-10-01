import KumarNivat.NewtonEnvelopeCentering
import KumarNivat.NewtonEnvelopeDilates
import KumarNivat.NewtonEnvelopeResidual
import KumarNivat.NewtonEnvelopeSupport

namespace KumarNivat

open scoped Pointwise

-- an actual lower tangent edge lets integer dilations cover finite half-plane data while retaining the exact newton summand.
theorem finite_lattice_hull_halfplane_base (T : Finset Site) (a : Site)
    (hprimitive : Int.gcd a.1 a.2 = 1) (p : Site) (hp : p ≠ 0)
    (hparallel : directionNormal a p = 0) (u₀ : Site) (hu₀ : u₀ ∈ T) (hu₀p : u₀ + p ∈ T)
    (hmin : ∀ u ∈ T, directionNormal a u₀ ≤ directionNormal a u)
    (u₁ : Site) (hu₁ : u₁ ∈ T) (hheight : directionNormal a u₀ < directionNormal a u₁)
    (cut : ℤ) (S : Finset Site) (hS : ∀ g ∈ S, cut ≤ directionNormal a g) :
    ∃ F : Finset Site, LatticeConvex F ∧ S ⊆ F ∧
      (∀ g ∈ F, cut ≤ directionNormal a g) ∧
      ∃ N : ℕ, ∃ U B : Site, 0 < N ∧ directionNormal a B = cut ∧ B ∈ F ∧
        B + (N : ℤ) • a ∈ F ∧ B - (N : ℤ) • a ∈ F ∧
        latticeHull F = (fun z : RealPlane => latticeEmbedding U + (2 * (N : ℝ)) • z) '' latticeHull T ∧
        ∃ C : Set RealPlane, C = (fun z : RealPlane =>
          latticeEmbedding U + (2 * (N : ℝ) - 1) • z) '' latticeHull T ∧
          Convex ℝ C ∧ IsCompact C ∧ C.Nonempty ∧ latticeHull F = latticeHull T + C := by
  classical
  obtain ⟨D, hD, hlow, h0, ha, hna, v, hv, hheightv⟩ :=
    centered_doubled_lattice_hull T a hprimitive p hp hparallel u₀ hu₀ hu₀p hmin u₁ hu₁ hheight
  obtain ⟨N, B, hN, hB, hcover⟩ := finite_primitive_halfplane_cover_by_dilates (latticeHull D)
    (convex_convexHull ℝ _) a hprimitive h0 ha hna v
    (subset_convexHull ℝ _ ⟨v, hv, rfl⟩) hheightv cut S hS
  let A := D.image (fun u => B + (N : ℤ) • u)
  have hA : latticeHull A = (fun z : RealPlane => latticeEmbedding B + (N : ℝ) • z) '' latticeHull D := by
    simpa only [Int.cast_natCast] using latticeHull_integer_affinity D (N : ℤ) B
  let c := (2 : ℤ) • u₀ + p
  let U := B + (N : ℤ) • (-c)
  have hfull : latticeHull A = (fun z : RealPlane =>
      latticeEmbedding U + (2 * (N : ℝ)) • z) '' latticeHull T := by
    rw [hA, hD, Set.image_image]
    congr 1
    funext z
    simp only [U, latticeEmbedding_add, latticeEmbedding_zsmul,
      Int.cast_natCast, smul_add, smul_smul]
    rw [mul_comm (N : ℝ) 2]
    abel
  obtain ⟨F, hF, _hAF, hFA, hFmem⟩ := exists_latticeConvex_hull_saturation A
  have hHull : latticeHull F = (fun z : RealPlane =>
      latticeEmbedding U + (2 * (N : ℝ)) • z) '' latticeHull T := hFA.trans hfull
  have hSF : S ⊆ F := by
    intro g hg
    apply (hFmem g).mpr
    rw [hA]
    obtain ⟨_w, ⟨z, hz, rfl⟩, he⟩ := hcover g hg
    exact ⟨z, hz, he⟩
  have hDhull : ∀ z ∈ latticeHull D, (0 : ℝ) ≤ latticeNormal (directionNormal a) z := by
    apply convexHull_min ?_ ((convex_Ici (0 : ℝ)).linear_preimage (latticeNormal (directionNormal a)))
    rintro _ ⟨u, hu, rfl⟩
    change (0 : ℝ) ≤ latticeNormal (directionNormal a) (latticeEmbedding u)
    rw [latticeNormal_embedding]
    exact_mod_cast hlow u hu
  have hhalf : ∀ g ∈ F, cut ≤ directionNormal a g := by
    intro g hg
    have hm := (hFmem g).mp hg
    rw [hA] at hm
    obtain ⟨z, hz, he⟩ := hm
    have hn : (cut : ℝ) ≤ latticeNormal (directionNormal a) (latticeEmbedding g) := by
      rw [← he, map_add, map_smul, latticeNormal_embedding, hB, smul_eq_mul]
      exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg N) (hDhull z hz))
    rw [latticeNormal_embedding] at hn
    exact_mod_cast hn
  have hBF : B ∈ F := by
    apply (hFmem B).mpr
    rw [hA]
    exact ⟨0, h0, by simp⟩
  have hplus : B + (N : ℤ) • a ∈ F := by
    apply (hFmem _).mpr
    rw [hA]
    refine ⟨latticeEmbedding a, ha, ?_⟩
    rw [latticeEmbedding_add, latticeEmbedding_zsmul]
    simp only [Int.cast_natCast]
  have hminus : B - (N : ℤ) • a ∈ F := by
    apply (hFmem _).mpr
    rw [hA]
    refine ⟨-latticeEmbedding a, hna, ?_⟩
    rw [latticeEmbedding_sub, latticeEmbedding_zsmul]
    simp only [Int.cast_natCast, smul_neg, sub_eq_add_neg]
  let C : Set RealPlane := (fun z : RealPlane =>
    latticeEmbedding U + (2 * (N : ℝ) - 1) • z) '' latticeHull T
  have hCconv : Convex ℝ C := (convex_convexHull ℝ _).affinity _ _
  have hCcompact : IsCompact C :=
    (T.finite_toSet.image latticeEmbedding).isCompact_convexHull ℝ |>.image (by fun_prop)
  have hCnonempty : C.Nonempty :=
    ⟨latticeEmbedding U + (2 * (N : ℝ) - 1) • latticeEmbedding u₀,
      ⟨latticeEmbedding u₀, subset_convexHull ℝ _ ⟨u₀, hu₀, rfl⟩, rfl⟩⟩
  have hMinkowski : latticeHull F = latticeHull T + C := by
    rw [hHull]
    apply convex_dilate_translate_minkowski_residual (latticeHull T) (convex_convexHull ℝ _)
    have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
    linarith
  exact ⟨F, hF, hSF, hhalf, N, U, B, hN, hB, hBF, hplus, hminus,
    hHull, C, rfl, hCconv, hCcompact, hCnonempty, hMinkowski⟩

-- the original distinct-direction annihilator itself supplies every edge and width premise for those actual bases.
theorem actual_newton_halfplane_base {K : Type*} [CommRing K] [Nontrivial K] [NoZeroDivisors K]
    (hs : List Site) (hlen : 2 ≤ hs.length) (hdirs : ∀ h ∈ hs, h ≠ 0)
    (hpairs : hs.Pairwise (fun p q => determinant p q ≠ 0))
    (a : Site) (hprimitive : Int.gcd a.1 a.2 = 1) (p : Site) (hpmem : p ∈ hs)
    (hparallel : determinant a p = 0) (cut : ℤ) (S : Finset Site)
    (hS : ∀ g ∈ S, cut ≤ directionNormal a g) :
    ∃ F : Finset Site, LatticeConvex F ∧ S ⊆ F ∧
      (∀ g ∈ F, cut ≤ directionNormal a g) ∧
      ∃ N : ℕ, ∃ U B : Site, 0 < N ∧ directionNormal a B = cut ∧ B ∈ F ∧
        B + (N : ℤ) • a ∈ F ∧ B - (N : ℤ) • a ∈ F ∧
        latticeHull F = (fun z : RealPlane => latticeEmbedding U + (2 * (N : ℝ)) • z) ''
          latticeHull (differenceProduct (K := K) hs).coeff.support ∧
        ∃ C : Set RealPlane, C = (fun z : RealPlane =>
          latticeEmbedding U + (2 * (N : ℝ) - 1) • z) ''
            latticeHull (differenceProduct (K := K) hs).coeff.support ∧
          Convex ℝ C ∧ IsCompact C ∧ C.Nonempty ∧
          latticeHull F = latticeHull (differenceProduct (K := K) hs).coeff.support + C := by
  obtain ⟨u₀, hu₀, hu₀p, hmin, u₁, hu₁, hheight⟩ :=
    actual_newton_tangent_lower_edge (K := K) hs hlen hdirs hpairs a hprimitive p hpmem hparallel
  exact finite_lattice_hull_halfplane_base (differenceProduct (K := K) hs).coeff.support
    a hprimitive p (hdirs p hpmem) hparallel u₀ hu₀ hu₀p hmin u₁ hu₁ hheight cut S hS

end KumarNivat
