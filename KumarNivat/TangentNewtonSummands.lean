module

public import KumarNivat.TangentNewtonEndpoints
public import KumarNivat.PrimitiveUnitSegments
public import KumarNivat.TransverseWedgeOperators

@[expose] public section

namespace KumarNivat

open scoped Pointwise

-- the surviving opposite endpoints force a unit primitive tangent summand of the actual newton hull.
theorem tangent_positive_product_unit_summand {K : Type*} [CommRing K] [Nontrivial K] [NoZeroDivisors K]
    (a : Site) (hprimitive : Int.gcd a.1 a.2 = 1) (τ : Site →+ ℤ)
    (hker : ∀ g : Site, directionNormal a g = 0 → g = τ g • a)
    (p : Site) (hp : p ≠ 0) (hparallel : directionNormal a p = 0)
    (hs : List Site) (hpos : ∀ h ∈ hs, 0 < (-directionNormal a) h) :
    ∃ C : Set RealPlane, Convex ℝ C ∧
      latticeHull ((binomial p : Laurent K) * differenceProduct hs).coeff.support =
        lineInterval 0 (latticeEmbedding a) 0 1 + C := by
  let f := (binomial p : Laurent K) * differenceProduct hs
  let D : ℤ := (hs.map (-directionNormal a)).sum
  have hflat : (-directionNormal a) p = 0 := by simp only [AddMonoidHom.neg_apply, hparallel, neg_zero]
  obtain ⟨h0, hp0, ht, hpt, hbounds⟩ := tangent_product_normal_endpoints (K := K) p hp hs
    (-directionNormal a) hflat hpos
  have hmem (u : Site) (hu : u ∈ f.coeff.support) : latticeEmbedding u ∈ latticeHull f.coeff.support :=
    subset_convexHull ℝ _ ⟨u, hu, rfl⟩
  obtain ⟨E₀, hE₀, hE₀a, hE₀level⟩ := primitive_unit_anchor_in_convex_set (latticeHull f.coeff.support)
    (convex_convexHull ℝ _) a τ hker p hp hparallel hs.sum (hmem hs.sum ht)
    (by simpa only [add_comm] using hmem (p + hs.sum) hpt)
  obtain ⟨E₁, hE₁, hE₁a, hE₁level⟩ := primitive_unit_anchor_in_convex_set (latticeHull f.coeff.support)
    (convex_convexHull ℝ _) a τ hker p hp hparallel 0 (hmem 0 h0)
    (by simpa only [zero_add] using hmem p hp0)
  have hsub : latticeEmbedding '' (f.coeff.support : Set Site) ⊆
      {x : RealPlane | (-D : ℝ) ≤ latticeNormal (directionNormal a) x ∧
        latticeNormal (directionNormal a) x ≤ 0} := by
    rintro _ ⟨u, hu, rfl⟩
    have hb := hbounds u hu
    change 0 ≤ -directionNormal a u ∧ -directionNormal a u ≤ D at hb
    change (-D : ℝ) ≤ latticeNormal (directionNormal a) (latticeEmbedding u) ∧
      latticeNormal (directionNormal a) (latticeEmbedding u) ≤ 0
    rw [latticeNormal_embedding]
    constructor
    · exact_mod_cast (by omega : -D ≤ directionNormal a u)
    · exact_mod_cast (by omega : directionNormal a u ≤ 0)
  have hHullBounds : ∀ x ∈ latticeHull f.coeff.support,
      (-D : ℝ) ≤ latticeNormal (directionNormal a) x ∧ latticeNormal (directionNormal a) x ≤ 0 :=
    convexHull_min hsub ((convex_Icc (-D : ℝ) 0).linear_preimage (latticeNormal (directionNormal a)))
  have hsum : directionNormal a hs.sum = -D := by
    have he := normal_list_sum (-directionNormal a) hs
    change -directionNormal a hs.sum = D at he
    omega
  apply primitive_segment_summand_of_opposite_anchors (latticeHull f.coeff.support)
    (convex_convexHull ℝ _) a hprimitive 1 (by norm_num) (-D : ℝ) 0 E₀ E₁
  · exact hE₀
  · simpa only [one_smul] using hE₀a
  · exact hE₁
  · simpa only [one_smul] using hE₁a
  · simpa only [hsum, Int.cast_neg] using hE₀level
  · simpa only [map_zero, Int.cast_zero] using hE₁level
  · exact hHullBounds

end KumarNivat
