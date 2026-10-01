import KumarNivat.CyclicExposedFacetData
import KumarNivat.AnchoredCyclicFacesResidual
import KumarNivat.AnchoredIntegerExpansionLayers
import KumarNivat.AnchoredStableSeeds

namespace KumarNivat

open scoped Pointwise

-- actual cyclic faces and stabilized left vertices produce one finite seed set for every failed expansion.
theorem actual_cyclic_relaxation_failures_fixed_seeds {K : Type*}
    [CommRing K] [NoZeroDivisors K] {n : ℕ} [NeZero n]
    (f : Laurent K) (e : ZMod n → Site) (horder : CyclicEdgeOrder e)
    (Q : OrderedCyclicLatticePolygon e f.coeff.support) (i : ZMod n)
    (hprimitive : Int.gcd (e i).1 (e i).2 = 1)
    (F : ℕ → Finset Site) (P : ∀ N, OrderedCyclicLatticePolygon e (F N))
    (B : Site) (hfixed : ∀ N, (P N).vertex i = B)
    (hlen : ∀ N k, Q.edgeLength k ≤ (P N).edgeLength k)
    (hbuffer : ∀ N, Q.edgeLength i + |determinant (e (i - 1)) (e (i + 1))| + 1 ≤
      (P N).edgeLength i)
    (δ : ℕ → Site → K) (hann : ∀ N, laurentAct f (δ N) = 0)
    (hzero : ∀ N g, latticeEmbedding g ∈ latticeHull (F N) → δ N g = 0)
    (hfailure : ∀ N, ∃ g : Site, latticeEmbedding g ∈
      cyclicFacetRelaxedRegion e (F N) (P N) i (cyclicFacetRelaxationScale e i) ∧ δ N g ≠ 0) :
    ∃ E : Finset Site,
      (∀ N, ∃ g ∈ E, δ N g ≠ 0) ∧
      (∀ g ∈ E, ∃ j : ℕ, 1 ≤ j ∧ j ≤ (cyclicFacetRelaxationScale e i).toNat ∧
        directionNormal (e i) g = directionNormal (e i) B - (j : ℤ)) ∧
      ∀ N, ∀ g ∈ E, ∃ j : ℕ, 1 ≤ j ∧ j ≤ (cyclicFacetRelaxationScale e i).toNat ∧
        latticeEmbedding g ∈ normalFace (cyclicFacetRelaxedRegion e (F N) (P N) i (j : ℤ))
          (latticeNormal (directionNormal (e i))) ((directionNormal (e i) B - (j : ℤ) : ℤ) : ℝ) := by
  obtain ⟨t, α, _ht, _htpos, _hfirst, hlast, _hcoeff, hdecomp, hSface⟩ :=
    actual_cyclic_exposed_operator_data f e horder Q i hprimitive
  let m := directionNormal (e i) (Q.vertex i)
  let β := directionNormal (e i) B
  let M := (cyclicFacetRelaxationScale e i).toNat
  have hscale := cyclic_facet_relaxation_scale_positive e horder i
  have hscaleR : (0 : ℝ) < (cyclicFacetRelaxationScale e i : ℝ) := by exact_mod_cast hscale
  have hMz : (M : ℤ) = cyclicFacetRelaxationScale e i := by dsimp [M]; omega
  have hmin : ∀ u ∈ f.coeff.support, m ≤ directionNormal (e i) u := by
    intro u hu
    have h := ordered_cyclic_real_point_normal_minimum e horder f.coeff.support Q
      (latticeEmbedding u) (subset_convexHull ℝ _ ⟨u, hu, rfl⟩) i
    rw [latticeNormal_embedding] at h
    exact_mod_cast h
  let C := fun N j : ℕ => cyclicFacetRelaxedResidual e f.coeff.support (F N) Q (P N) i (j : ℤ)
  let A := fun N j : ℕ => (cyclicFacetRelaxationScale e i : ℝ)⁻¹ • latticeEmbedding
    (scaledFacetRelaxationVertex e (F N) (P N) i (j : ℤ) i - cyclicFacetRelaxationScale e i • Q.vertex i)
  let right := fun N j : ℕ => (cyclicFacetRelaxationScale e i : ℝ)⁻¹ *
    ((scaledFacetRelaxationLength e (F N) (P N) i (j : ℤ) i -
      cyclicFacetRelaxationScale e i * Q.edgeLength i : ℤ) : ℝ)
  have hjscale (j : ℕ) (hj : j ≤ M) : (j : ℤ) ≤ cyclicFacetRelaxationScale e i := by omega
  have hcut (N j : ℕ) : cyclicFacetRelaxedCut e (F N) (P N) i (j : ℤ) i = β - (j : ℤ) := by
    simp only [cyclicFacetRelaxedCut, ite_true, hfixed N, β]
  have hregion (N j : ℕ) (hj : j ≤ M) :
      cyclicFacetRelaxedRegion e (F N) (P N) i (j : ℤ) = latticeHull f.coeff.support + C N j :=
    cyclic_facet_relaxed_region_minkowski e horder f.coeff.support (F N) Q (P N) (hlen N)
      i (j : ℤ) (Int.natCast_nonneg j) (hjscale j hj) (hbuffer N)
  have hC : ∀ N j, j ≤ M → ∀ x ∈ C N j,
      ((β - (j : ℤ) - m : ℤ) : ℝ) ≤ latticeNormal (directionNormal (e i)) x := by
    intro N j hj x hx
    have h := cyclic_facet_relaxed_residual_normal_lower e horder f.coeff.support (F N) Q (P N)
      (hlen N) i (j : ℤ) (Int.natCast_nonneg j) (hjscale j hj) (hbuffer N) x hx
    rwa [hcut N j] at h
  have hab : ∀ N j, j ≤ M → (0 : ℝ) ≤ right N j := by
    intro N j hj
    apply mul_nonneg (le_of_lt (inv_pos.mpr hscaleR))
    exact_mod_cast scaled_facet_relaxation_residual_lengths_nonnegative e horder f.coeff.support
      (F N) Q (P N) (hlen N) i (j : ℤ) (Int.natCast_nonneg j) (hjscale j hj) (hbuffer N) i
  have hCface : ∀ N j, j ≤ M →
      normalFace (C N j) (latticeNormal (directionNormal (e i))) ((β - (j : ℤ) - m : ℤ) : ℝ) =
        lineInterval (A N j) (latticeEmbedding (e i)) 0 (right N j) := by
    intro N j hj
    have h := cyclic_facet_relaxed_residual_face e horder f.coeff.support (F N) Q (P N)
      (hlen N) i (j : ℤ) (Int.natCast_nonneg j) (hjscale j hj) (hbuffer N)
    rwa [hcut N j] at h
  have hprevious : ∀ N j, j < M → ∀ g : Site,
      latticeEmbedding g ∈ latticeHull f.coeff.support + C N (j + 1) →
      β - ((j + 1 : ℕ) : ℤ) + 1 ≤ directionNormal (e i) g →
      latticeEmbedding g ∈ latticeHull f.coeff.support + C N j := by
    intro N j hj g hg hlevel
    rw [← hregion N (j + 1) (by omega)] at hg
    rw [← hregion N j (by omega)]
    apply cyclic_facet_relaxed_previous_integer_layer e (F N) (P N) i (j : ℤ) g
    · simpa only [Nat.cast_add, Nat.cast_one] using hg
    · rw [hfixed N]
      simpa only [β, Nat.cast_add, Nat.cast_one] using hlevel
  let V := fun j : ℕ => latticeEmbedding B +
    ((j : ℝ) / (determinant (e (i - 1)) (e i) : ℝ)) • latticeEmbedding (e (i - 1))
  have hstable : ∀ N j, j ≤ M → 0 < j →
      latticeEmbedding (Q.vertex i) + A N j + (0 : ℝ) • latticeEmbedding (e i) = V j := by
    intro N j _hj _hpos
    dsimp [A, V]
    rw [cyclic_facet_relaxed_residual_left_endpoint e horder f.coeff.support (F N) Q (P N) i (j : ℤ),
      hfixed N, zero_smul, add_zero, Int.cast_natCast]
    abel
  have hzeroC : ∀ N g, latticeEmbedding g ∈ latticeHull f.coeff.support + C N 0 → δ N g = 0 := by
    intro N g hg
    rw [← hregion N 0 (by omega)] at hg
    have hHull : cyclicFacetRelaxedRegion e (F N) (P N) i (0 : ℤ) = latticeHull (F N) :=
      cyclic_facet_relaxed_region_zero e horder (F N) (P N) i
    simp only [Nat.cast_zero, hHull] at hg
    exact hzero N g hg
  have hfailureC : ∀ N, ∃ g : Site,
      latticeEmbedding g ∈ latticeHull f.coeff.support + C N M ∧ δ N g ≠ 0 := by
    intro N
    rw [← hregion N M le_rfl, hMz]
    exact hfailure N
  obtain ⟨E, hEfail, hElevels, hEplaced⟩ := anchored_relaxation_failures_have_fixed_seeds δ f
    (e i) hprimitive m β hmin (Q.vertex i) rfl t α hlast hdecomp hann M C A
    (fun _ _ => 0) right hC hSface hab hCface hprevious V hstable hzeroC hfailureC
  refine ⟨E, hEfail, hElevels, ?_⟩
  intro N g hg
  obtain ⟨j, hj₀, hj₁, hpoint⟩ := hEplaced N g hg
  refine ⟨j, hj₀, hj₁, ?_⟩
  rwa [← hregion N j hj₁] at hpoint

end KumarNivat
