module

public import KumarNivat.PairedStructureRayChainCones
public import KumarNivat.FirstFailedRegionPeriods

@[expose] public section

namespace KumarNivat

open scoped Pointwise

-- every region uses the original newton hull and the actual translated fan cone.
def forwardFactorNewtonRegion {q : ℕ} [NeZero (2 * q)]
    (S : Finset Site) (G : Site) (e : ZMod (2 * q) → Site) (k : ℕ) : Set RealPlane :=
  latticeHull S + ({latticeEmbedding G} + forwardFactorRayCone e k)

-- translating the cone's vertex gives precisely the original two-ray expression.
theorem translated_forward_two_ray_cone (G a b : Site) :
    ({latticeEmbedding G} : Set RealPlane) + forwardTwoRayCone a b =
      lineRay (latticeEmbedding G) (latticeEmbedding a) 0 + lineRay 0 (latticeEmbedding b) 0 := by
  ext x
  constructor
  · rintro ⟨_, hG, _, ⟨_, ⟨α, hα, rfl⟩, _, ⟨β, hβ, rfl⟩, rfl⟩, rfl⟩
    have hG' := Set.mem_singleton_iff.mp hG
    subst hG'
    refine Set.mem_add.mpr ⟨latticeEmbedding G + α • latticeEmbedding a, ⟨α, hα, rfl⟩,
      0 + β • latticeEmbedding b, ⟨β, hβ, rfl⟩, ?_⟩
    change (latticeEmbedding G + α • latticeEmbedding a) + (0 + β • latticeEmbedding b) =
      latticeEmbedding G + ((0 + α • latticeEmbedding a) + (0 + β • latticeEmbedding b))
    simp only [zero_add]
    exact add_assoc _ _ _
  · rintro ⟨_, ⟨α, hα, rfl⟩, _, ⟨β, hβ, rfl⟩, rfl⟩
    refine Set.mem_add.mpr ⟨latticeEmbedding G, Set.mem_singleton _,
      α • latticeEmbedding a + β • latticeEmbedding b,
      Set.mem_add.mpr ⟨α • latticeEmbedding a, ⟨α, hα, by simp⟩,
        β • latticeEmbedding b, ⟨β, hβ, by simp⟩, rfl⟩, ?_⟩
    change latticeEmbedding G + (α • latticeEmbedding a + β • latticeEmbedding b) =
      (latticeEmbedding G + α • latticeEmbedding a) + (0 + β • latticeEmbedding b)
    simp only [zero_add]
    exact (add_assoc _ _ _).symm

-- each named intermediate stage is the actual original two-ray newton region.
theorem forward_factor_newton_region_eq_two_rays {q : ℕ} [NeZero (2 * q)]
    (S : Finset Site) (G : Site) (e : ZMod (2 * q) → Site) (k : ℕ) (hk : k < q) :
    forwardFactorNewtonRegion S G e k = latticeHull S +
      (lineRay (latticeEmbedding G) (latticeEmbedding (e 0)) 0 +
        lineRay 0 (latticeEmbedding (e (k : ZMod (2 * q)))) 0) := by
  simp only [forwardFactorNewtonRegion, forwardFactorRayCone, hk, ite_true,
    translated_forward_two_ray_cone]

-- the original hull's attained minimum turns its homogeneous final cone into an exact affine half-plane.
theorem newton_hull_plus_homogeneous_halfplane (S : Finset Site) (hS : S.Nonempty)
    (G : Site) (ν : Site →+ ℤ) :
    ∃ u₀ ∈ S, (∀ u ∈ S, ν u₀ ≤ ν u) ∧
      latticeHull S + (({latticeEmbedding G} : Set RealPlane) + {x | 0 ≤ latticeNormal ν x}) =
        {x | (ν (G + u₀) : ℝ) ≤ latticeNormal ν x} := by
  classical
  obtain ⟨u₀, hu₀, hmin⟩ := S.exists_min_image ν hS
  have hhull : ∀ z ∈ latticeHull S, (ν u₀ : ℝ) ≤ latticeNormal ν z := by
    apply convexHull_min ?_ ((convex_Ici (ν u₀ : ℝ)).linear_preimage (latticeNormal ν))
    rintro _ ⟨u, hu, rfl⟩
    change (ν u₀ : ℝ) ≤ latticeNormal ν (latticeEmbedding u)
    rw [latticeNormal_embedding]
    exact_mod_cast hmin u hu
  refine ⟨u₀, hu₀, hmin, ?_⟩
  ext x
  constructor
  · rintro ⟨u, hu, _, ⟨_, hG, v, hv, rfl⟩, rfl⟩
    have hG' := Set.mem_singleton_iff.mp hG
    subst hG'
    change (ν (G + u₀) : ℝ) ≤ latticeNormal ν (u + (latticeEmbedding G + v))
    have hm := hhull u hu
    change 0 ≤ latticeNormal ν v at hv
    simp only [map_add, latticeNormal_embedding, Int.cast_add]
    linarith
  · intro hx
    change (ν (G + u₀) : ℝ) ≤ latticeNormal ν x at hx
    refine Set.mem_add.mpr ⟨latticeEmbedding u₀, subset_convexHull ℝ _ ⟨u₀, hu₀, rfl⟩,
      latticeEmbedding G + (x - latticeEmbedding (G + u₀)),
      Set.mem_add.mpr ⟨latticeEmbedding G, Set.mem_singleton _, x - latticeEmbedding (G + u₀), ?_, rfl⟩, ?_⟩
    · change 0 ≤ latticeNormal ν (x - latticeEmbedding (G + u₀))
      rw [map_sub, latticeNormal_embedding]
      exact sub_nonneg.mpr hx
    · rw [latticeEmbedding_add]
      abel

-- the actual sorted ray chain is nested and terminates in the original tangent half-plane.
theorem forward_factor_newton_regions_chain {q : ℕ} [NeZero (2 * q)]
    (S : Finset Site) (hS : S.Nonempty) (G : Site)
    (e : ZMod (2 * q) → Site) (hfan : AnchoredChainFanOrder e) (hq : 2 ≤ q) :
    (∀ i j : ℕ, 0 < i → i ≤ j → j ≤ q →
      forwardFactorNewtonRegion S G e i ⊆ forwardFactorNewtonRegion S G e j) ∧
      ∃ cut : ℤ, forwardFactorNewtonRegion S G e q =
        {x | (cut : ℝ) ≤ latticeNormal (directionNormal (e 0)) x} := by
  obtain ⟨hmono, hfinal⟩ := forward_factor_ray_cones_chain e hfan hq
  refine ⟨?_, ?_⟩
  · intro i j hi hij hjq x hx
    rcases hx with ⟨u, hu, v, hv, rfl⟩
    rcases hv with ⟨w, hw, t, ht, rfl⟩
    exact Set.mem_add.mpr ⟨u, hu, w + t, Set.mem_add.mpr ⟨w, hw, t, hmono i j hi hij hjq ht, rfl⟩, rfl⟩
  · obtain ⟨u₀, _hu₀, _hmin, hhalf⟩ := newton_hull_plus_homogeneous_halfplane S hS G (directionNormal (e 0))
    refine ⟨directionNormal (e 0) (G + u₀), ?_⟩
    simpa only [forwardFactorNewtonRegion, hfinal] using hhalf

-- an original nonperiodic configuration has an actual first failed period along this constructed factor-ray chain.
theorem first_failed_actual_factor_ray_region {K : Type*}
    [CommRing K] [Nontrivial K] [NoZeroDivisors K]
    {q : ℕ} [NeZero (2 * q)]
    (x : Site → K) (hs : List Site) (hdirs : ∀ p ∈ hs, p ≠ 0)
    (hpairs : hs.Pairwise (fun p r => determinant p r ≠ 0))
    (hann : laurentAct (differenceProduct hs) x = 0)
    (hnot : ¬ ∃ v : Site, v ≠ 0 ∧ IsPeriod x v)
    (S : Finset Site) (hS : S.Nonempty) (G : Site)
    (e : ZMod (2 * q) → Site) (hfan : AnchoredChainFanOrder e) (hq : 2 ≤ q)
    (hprimitive : Int.gcd (e 0).1 (e 0).2 = 1) (j : ℕ) (_hj₀ : 0 < j) (hjq : j < q)
    (p : ℕ) (hp : 0 < p)
    (hstart : RegionalPeriod x {g | latticeEmbedding g ∈ forwardFactorNewtonRegion S G e j}
      ((p : ℤ) • e 0)) :
    ∃ k : ℕ, j ≤ k ∧ k < q ∧
      (∀ r : ℕ, j ≤ r → r ≤ k →
        RegionalPeriod x {g | latticeEmbedding g ∈ forwardFactorNewtonRegion S G e r} ((p : ℤ) • e 0)) ∧
      ¬ RegionalPeriod x {g | latticeEmbedding g ∈ forwardFactorNewtonRegion S G e (k + 1)} ((p : ℤ) • e 0) := by
  obtain ⟨_hmono, cut, hfinal⟩ := forward_factor_newton_regions_chain S hS G e hfan hq
  have hbad : ¬ RegionalPeriod x {g | latticeEmbedding g ∈ forwardFactorNewtonRegion S G e q}
      ((p : ℤ) • e 0) := by
    have hhalf := nonperiodic_no_tangent_halfplane_period x hs hdirs hpairs hann hnot
      (e 0) hprimitive cut p hp
    simpa only [hfinal, Set.mem_ofPred_eq, latticeNormal_embedding, Int.cast_le] using hhalf
  let P : ℕ → Set Site := fun r => {g | latticeEmbedding g ∈ forwardFactorNewtonRegion S G e (j + r)}
  have hfinalP : ¬ RegionalPeriod x (P (q - j)) ((p : ℤ) • e 0) := by
    simpa only [P, Nat.add_sub_of_le hjq.le] using hbad
  obtain ⟨i, hi, hgood, hfail⟩ := first_failed_region_period x P ((p : ℤ) • e 0) (q - j) hstart hfinalP
  refine ⟨j + i, by omega, by omega, ?_, ?_⟩
  · intro r hjr hri
    have h := hgood (r - j) (by omega)
    simpa only [P, Nat.add_sub_of_le hjr] using h
  · simpa only [P, Nat.add_assoc] using hfail

end KumarNivat
