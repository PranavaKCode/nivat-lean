import KumarNivat.MonomialNewtonTranslation
import KumarNivat.TangentNewtonSummands

namespace KumarNivat

open scoped Pointwise

-- reorientation gives both a genuine tangent summand and two surviving original support sites at the full transverse width.
theorem tangent_difference_product_newton_data {K : Type*} [CommRing K] [Nontrivial K] [NoZeroDivisors K]
    (a : Site) (hprimitive : Int.gcd a.1 a.2 = 1) (τ : Site →+ ℤ)
    (hker : ∀ g : Site, directionNormal a g = 0 → g = τ g • a)
    (p : Site) (hp : p ≠ 0) (hparallel : directionNormal a p = 0)
    (hs : List Site) (htransverse : ∀ h ∈ hs, (-directionNormal a) h ≠ 0) :
    let f := (binomial p : Laurent K) * differenceProduct hs
    let ts := hs.map (orientNormalDirection (-directionNormal a))
    ∃ C : Set RealPlane,
      latticeHull f.coeff.support = lineInterval 0 (latticeEmbedding a) 0 1 + C ∧
      ∃ u₀ ∈ f.coeff.support, ∃ u₁ ∈ f.coeff.support,
        (-directionNormal a) u₁ = (-directionNormal a) u₀ + (ts.map (-directionNormal a)).sum := by
  let ν := -directionNormal a
  let ts := hs.map (orientNormalDirection ν)
  let f := (binomial p : Laurent K) * differenceProduct hs
  let q := (binomial p : Laurent K) * differenceProduct ts
  have hpos := oriented_difference_directions_positive hs ν htransverse
  obtain ⟨v, ε, hε, he⟩ := oriented_difference_product_monomial (K := K) hs ν
  have hq : q = AddMonoidAlgebra.single v ε * f := by
    dsimp [q, f, ts]
    rw [he]
    ring
  obtain ⟨C, _hC, hsum⟩ := tangent_positive_product_unit_summand (K := K) a hprimitive τ hker
    p hp hparallel ts hpos
  have htranslate := latticeHull_nonzero_monomial_translate v ε hε f
  have hsum' : (fun z : RealPlane => latticeEmbedding v + z) '' latticeHull f.coeff.support =
      lineInterval 0 (latticeEmbedding a) 0 1 + C := by
    rw [← htranslate, ← hq]
    exact hsum
  have hbase := undo_translated_minkowski_summand (latticeHull f.coeff.support)
    (lineInterval 0 (latticeEmbedding a) 0 1) C (latticeEmbedding v) hsum'
  have hflat : ν p = 0 := by simp only [ν, AddMonoidHom.neg_apply, hparallel, neg_zero]
  obtain ⟨h0, _hp0, ht, _hpt, _hbounds⟩ := tangent_product_normal_endpoints (K := K) p hp ts ν hflat hpos
  have htransfer (u : Site) (hu : u ∈ q.coeff.support) : u - v ∈ f.coeff.support := by
    rw [hq] at hu
    exact (nonzero_monomial_translate_mem_support v ε hε f u).mp hu
  refine ⟨(fun z : RealPlane => z - latticeEmbedding v) '' C, hbase,
    0 - v, htransfer 0 h0, ts.sum - v, htransfer ts.sum ht, ?_⟩
  change ν (ts.sum - v) = ν (0 - v) + (ts.map ν).sum
  rw [map_sub, map_sub, map_zero, normal_list_sum]
  omega

-- the actual newton summand gives the base polygon its required segment and enough attained integer levels.
theorem newton_minkowski_base_slab_geometry (F S : Finset Site) (ν : Site →+ ℤ) (a : Site)
    (C₀ C₁ : Set RealPlane) (hC₀ : C₀.Nonempty)
    (hbase : latticeHull F = latticeHull S + C₀)
    (hsegment : latticeHull S = lineInterval 0 (latticeEmbedding a) 0 1 + C₁)
    (u₀ u₁ : Site) (hu₀ : u₀ ∈ S) (hu₁ : u₁ ∈ S) (D : ℤ) (hwidth : ν u₁ = ν u₀ + D) :
    ∃ C : Set RealPlane, latticeHull F = lineInterval 0 (latticeEmbedding a) 0 1 + C ∧
      ∃ v₀ ∈ F, ∃ v₁ ∈ F, ν v₀ + D ≤ ν v₁ := by
  classical
  obtain ⟨c, hc⟩ := hC₀
  have hpoints (u : Site) (hu : u ∈ S) : latticeEmbedding u + c ∈ latticeHull F := by
    rw [hbase]
    exact Set.add_mem_add (subset_convexHull ℝ _ ⟨u, hu, rfl⟩) hc
  have hF : F.Nonempty := by
    by_contra hn
    have he := Finset.not_nonempty_iff_eq_empty.mp hn
    have hz := hpoints u₀ hu₀
    simp only [he, latticeHull, Finset.coe_empty, Set.image_empty, convexHull_empty, Set.mem_empty_iff_false] at hz
  obtain ⟨v₀, hv₀, hmin⟩ := F.exists_min_image ν hF
  obtain ⟨v₁, hv₁, hmax⟩ := F.exists_max_image ν hF
  have hsub : latticeEmbedding '' (F : Set Site) ⊆
      {z : RealPlane | (ν v₀ : ℝ) ≤ latticeNormal ν z ∧ latticeNormal ν z ≤ (ν v₁ : ℝ)} := by
    rintro _ ⟨u, hu, rfl⟩
    change (ν v₀ : ℝ) ≤ latticeNormal ν (latticeEmbedding u) ∧
      latticeNormal ν (latticeEmbedding u) ≤ (ν v₁ : ℝ)
    rw [latticeNormal_embedding]
    exact ⟨by exact_mod_cast hmin u hu, by exact_mod_cast hmax u hu⟩
  have hhull : ∀ z ∈ latticeHull F, (ν v₀ : ℝ) ≤ latticeNormal ν z ∧
      latticeNormal ν z ≤ (ν v₁ : ℝ) :=
    convexHull_min hsub ((convex_Icc (ν v₀ : ℝ) (ν v₁ : ℝ)).linear_preimage (latticeNormal ν))
  have hlo := (hhull _ (hpoints u₀ hu₀)).1
  have hhi := (hhull _ (hpoints u₁ hu₁)).2
  rw [map_add, latticeNormal_embedding] at hlo hhi
  have hgap : (ν u₁ : ℝ) = (ν u₀ : ℝ) + (D : ℝ) := by exact_mod_cast hwidth
  refine ⟨C₁ + C₀, ?_, v₀, hv₀, v₁, hv₁, ?_⟩
  · rw [hbase, hsegment, add_assoc]
  · have h : (ν v₀ : ℝ) + (D : ℝ) ≤ (ν v₁ : ℝ) := by linarith
    exact_mod_cast h

end KumarNivat
