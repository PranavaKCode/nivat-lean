import KumarNivat.PairedStructureRayChainRegions
import KumarNivat.PairedStructureWideStripBackground

namespace KumarNivat

open scoped Pointwise

-- positive motion on the strict interior ray eventually puts every site in the actual newton two-ray region.
theorem newton_two_ray_region_interior_motion_cofinal (S : Finset Site) (hS : S.Nonempty)
    (G a b : Site) (hab : 0 < determinant a b) (q : ℕ) (hq : 0 < q) (g : Site) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → latticeEmbedding (g + (n : ℤ) • ((q : ℤ) • (a + b))) ∈
      latticeHull S + (lineRay (latticeEmbedding G) (latticeEmbedding a) 0 + lineRay 0 (latticeEmbedding b) 0) := by
  obtain ⟨u₀, hu₀⟩ := hS
  let ν := directionNormal a
  let η := -directionNormal b
  let res := g - (G + u₀)
  let N := (ν res).natAbs + (η res).natAbs
  let step := (q : ℤ) • (a + b)
  have hν : ν (a + b) = determinant a b := by simp only [ν, map_add, directionNormal_self, zero_add]; rfl
  have hη : η (a + b) = determinant a b := by simp [η, directionNormal, determinant]; ring
  have hqD : 1 ≤ (q : ℤ) * determinant a b := by
    have hq' : (0 : ℤ) < q := by exact_mod_cast hq
    have h := mul_pos hq' hab
    omega
  refine ⟨N, ?_⟩
  intro n hn
  have hn' : (N : ℤ) ≤ n := by exact_mod_cast hn
  have hn₀ : (0 : ℤ) ≤ n := Int.natCast_nonneg n
  have hboundν : -(N : ℤ) ≤ ν res := by
    have h : -ν res ≤ ((-ν res).natAbs : ℤ) := Int.le_natAbs
    simp only [Int.natAbs_neg] at h
    dsimp [N]
    have hηabs := Int.natCast_nonneg (η res).natAbs
    omega
  have hboundη : -(N : ℤ) ≤ η res := by
    have h : -η res ≤ ((-η res).natAbs : ℤ) := Int.le_natAbs
    simp only [Int.natAbs_neg] at h
    dsimp [N]
    have hνabs := Int.natCast_nonneg (ν res).natAbs
    omega
  have hinside (σ : Site →+ ℤ) (hσ : σ (a + b) = determinant a b) (hbound : -(N : ℤ) ≤ σ res) :
      0 ≤ latticeNormal σ (latticeEmbedding (g + (n : ℤ) • step) - latticeEmbedding (G + u₀)) := by
    have he : σ (g + (n : ℤ) • step) - σ (G + u₀) = σ res + (n : ℤ) * (q : ℤ) * determinant a b := by
      calc
        σ (g + (n : ℤ) • step) - σ (G + u₀) = σ res + (n : ℤ) * σ step := by
          rw [map_add, map_zsmul, smul_eq_mul]
          dsimp [res]
          rw [map_sub]
          ring
        _ = _ := by simp only [step, map_zsmul, smul_eq_mul, hσ]; ring
    have hz : 0 ≤ σ (g + (n : ℤ) • step) - σ (G + u₀) := by rw [he]; nlinarith
    rw [map_sub, latticeNormal_embedding, latticeNormal_embedding]
    exact_mod_cast hz
  apply Set.mem_add.mpr
  refine ⟨latticeEmbedding u₀, subset_convexHull ℝ _ ⟨u₀, hu₀, rfl⟩,
    latticeEmbedding G + (latticeEmbedding (g + (n : ℤ) • step) - latticeEmbedding (G + u₀)), ?_, ?_⟩
  · rw [← translated_forward_two_ray_cone]
    exact Set.mem_add.mpr ⟨latticeEmbedding G, Set.mem_singleton _,
      latticeEmbedding (g + (n : ℤ) • step) - latticeEmbedding (G + u₀),
      (forward_two_ray_cone_normals a b hab).symm ▸ ⟨hinside ν hν hboundν, hinside η hη hboundη⟩, rfl⟩
  · change latticeEmbedding u₀ + (latticeEmbedding G +
      (latticeEmbedding (g + (n : ℤ) • step) - latticeEmbedding (G + u₀))) =
        latticeEmbedding (g + (n : ℤ) • step)
    rw [latticeEmbedding_add G u₀]
    abel

-- the fully periodic reference inherits the exact old tangent period from agreement on the initial actual region.
theorem fullyPeriodic_reference_inherits_exact_two_ray_period {A : Type*}
    (x B : Site → A) (hB : FullyPeriodic B) (S : Finset Site) (hS : S.Nonempty)
    (G a b : Site) (hab : 0 < determinant a b) (p : ℕ) (_hp : 0 < p)
    (hperiod : RegionalPeriod x {g | latticeEmbedding g ∈ latticeHull S +
      (lineRay (latticeEmbedding G) (latticeEmbedding a) 0 + lineRay 0 (latticeEmbedding b) 0)} ((p : ℤ) • a))
    (hmatch : ∀ g : Site, latticeEmbedding g ∈ latticeHull S +
      (lineRay (latticeEmbedding G) (latticeEmbedding a) 0 + lineRay 0 (latticeEmbedding b) 0) → x g = B g) :
    IsPeriod B ((p : ℤ) • a) := by
  obtain ⟨q, hq, hglobal⟩ := hB.exists_period_multiple (a + b)
  intro g
  obtain ⟨N, hN⟩ := newton_two_ray_region_interior_motion_cofinal S hS G a b hab q hq g
  let step := (q : ℤ) • (a + b)
  let u := g + (N : ℤ) • step
  have hu := hN N le_rfl
  have hunext := newton_two_ray_region_first_motion S G a b (latticeEmbedding u) hu (p : ℝ) (Nat.cast_nonneg p)
  have hunext' : latticeEmbedding (u + (p : ℤ) • a) ∈ latticeHull S +
      (lineRay (latticeEmbedding G) (latticeEmbedding a) 0 + lineRay 0 (latticeEmbedding b) 0) := by
    simpa only [latticeEmbedding_add, latticeEmbedding_zsmul, Int.cast_natCast] using hunext
  have hper := hperiod u hu hunext'
  have hBg : B u = B g := hglobal.zsmul (N : ℤ) g
  have hBp : B (u + (p : ℤ) • a) = B (g + (p : ℤ) • a) := by
    simpa only [u, add_assoc, add_comm, add_left_comm] using hglobal.zsmul (N : ℤ) (g + (p : ℤ) • a)
  calc
    B (g + (p : ℤ) • a) = B (u + (p : ℤ) • a) := hBp.symm
    _ = x (u + (p : ℤ) • a) := (hmatch _ hunext').symm
    _ = x u := hper
    _ = B u := hmatch _ hu
    _ = B g := hBg

-- forward tangent periodicity and the attained minimum support level extend initial agreement to any actual larger stable region.
theorem agreement_on_forward_periodic_superset {A : Type*}
    (x B : Site → A) (S : Finset Site) (u₀ : Site) (hu₀ : u₀ ∈ S)
    (G a b : Site) (ha : Int.gcd a.1 a.2 = 1) (hab : 0 < determinant a b) (p : ℕ) (hp : 0 < p)
    (R : Set Site) (hbound : ∀ g ∈ R, directionNormal a (G + u₀) ≤ directionNormal a g)
    (hstable : ∀ g ∈ R, g + (p : ℤ) • a ∈ R)
    (hperiod : RegionalPeriod x R ((p : ℤ) • a)) (hBperiod : IsPeriod B ((p : ℤ) • a))
    (hmatch : ∀ g : Site, latticeEmbedding g ∈ latticeHull S +
      (lineRay (latticeEmbedding G) (latticeEmbedding a) 0 + lineRay 0 (latticeEmbedding b) 0) → x g = B g) :
    ∀ g ∈ R, x g = B g := by
  intro g hg
  obtain ⟨N, hN⟩ := newton_two_ray_region_first_ray_halfplane_cofinal S u₀ hu₀ G a b ha hab p hp g (hbound g hg)
  have hx := (regional_period_forward_multiples x R ((p : ℤ) • a) hstable hperiod N g hg).2
  have hB := hBperiod.zsmul (N : ℤ) g
  exact hx.symm.trans ((hmatch _ (hN N le_rfl)).trans hB)

end KumarNivat
