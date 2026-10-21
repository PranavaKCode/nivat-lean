module

public import KumarNivat.PairedStructureRayChainTruncationUnions
public import KumarNivat.PairedStructureRayChainRegions
public import KumarNivat.NewtonCyclicFactorOriginalTruncations

@[expose] public section

namespace KumarNivat

open scoped Pointwise

-- actual sparse ray rectangles and their escaping supports derive the complete cone-sum facet presentation.
theorem forward_factor_newton_two_ray_facets {q : ℕ} [NeZero q]
    (hq : 2 ≤ q) (e : ZMod (2 * q) → Site) (hfan : AnchoredChainFanOrder e)
    (T : Finset Site) (P : OrderedCyclicLatticePolygon e T)
    (k : ℕ) (hk₀ : 0 < k) (hkq : k < q) :
    latticeHull T + forwardTwoRayCone (e 0) (e (k : ZMod (2 * q))) =
      finiteInwardRegion ((Finset.range (2 * q)).filter (fun i : ℕ =>
        0 ≤ directionNormal (e (i : ZMod (2 * q))) (e 0) ∧
          0 ≤ directionNormal (e (i : ZMod (2 * q))) (e (k : ZMod (2 * q)))))
        (fun i : ℕ => directionNormal (e (i : ZMod (2 * q))))
        (fun i : ℕ => directionNormal (e (i : ZMod (2 * q))) (P.vertex (i : ZMod (2 * q)))) := by
  classical
  let μ : ℕ → Site →+ ℤ := fun i => directionNormal (e (i : ZMod (2 * q)))
  let z : ℕ → ℤ := fun i => μ i (P.vertex (i : ZMod (2 * q)))
  have htrunc (N : ℕ) : latticeHull T +
      (lineInterval 0 (latticeEmbedding (e 0)) 0 N + lineInterval 0 (latticeEmbedding (e (k : ZMod (2 * q)))) 0 N) =
        finiteInwardRegion (Finset.range (2 * q)) μ
          (fun i => z i + (N : ℤ) * (min 0 (μ i (e 0)) + min 0 (μ i (e (k : ZMod (2 * q)))))) := by
    rw [← add_assoc, finite_factor_ray_truncation_facets hq e hfan.order hfan.opposite T P k N hk₀ hkq]
    ext x
    constructor
    · intro hx i _hi
      simpa only [μ, z, Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_min, Int.cast_zero] using hx (i : ZMod (2 * q))
    · intro hx i
      have h := hx i.val (Finset.mem_range.mpr (ZMod.val_lt i))
      simpa only [μ, z, ZMod.natCast_zmod_val, Int.cast_add, Int.cast_mul, Int.cast_natCast,
        Int.cast_min, Int.cast_zero] using h
  calc
    latticeHull T + forwardTwoRayCone (e 0) (e (k : ZMod (2 * q))) =
        ⋃ N : ℕ, latticeHull T +
          (lineInterval 0 (latticeEmbedding (e 0)) 0 N + lineInterval 0 (latticeEmbedding (e (k : ZMod (2 * q)))) 0 N) :=
      (newton_ray_truncations_union T (e 0) (e (k : ZMod (2 * q)))).symm
    _ = ⋃ N : ℕ, finiteInwardRegion (Finset.range (2 * q)) μ
        (fun i => z i + (N : ℤ) * (min 0 (μ i (e 0)) + min 0 (μ i (e (k : ZMod (2 * q)))))) := by
      congr 1
      funext N
      exact htrunc N
    _ = _ := finite_ray_truncation_facet_union (Finset.range (2 * q)) μ z (e 0) (e (k : ZMod (2 * q)))

-- translating that exact presentation gives every actual intermediate newton region its finite inward inequalities.
theorem forward_factor_newton_region_integer_facets {q : ℕ} [NeZero q]
    (hq : 2 ≤ q) (e : ZMod (2 * q) → Site) (hfan : AnchoredChainFanOrder e)
    (T : Finset Site) (P : OrderedCyclicLatticePolygon e T) (G : Site)
    (k : ℕ) (hk₀ : 0 < k) (hkq : k < q) :
    forwardFactorNewtonRegion T G e k =
      inwardLayerRegion (directionNormal (e 0)) (directionNormal (e 0) (P.vertex 0 + G))
        (Finset.Icc k (q - 1)) (fun i => -directionNormal (e (i : ZMod (2 * q))))
        (fun i => (-directionNormal (e (i : ZMod (2 * q)))) (P.vertex ((q + i : ℕ) : ZMod (2 * q)) + G)) := by
  classical
  let μ : ℕ → Site →+ ℤ := fun i => directionNormal (e (i : ZMod (2 * q)))
  let z : ℕ → ℤ := fun i => μ i (P.vertex (i : ZMod (2 * q)))
  let J := (Finset.range (2 * q)).filter (fun i : ℕ => 0 ≤ μ i (e 0) ∧ 0 ≤ μ i (e (k : ZMod (2 * q))))
  have hcone : latticeHull T + forwardTwoRayCone (e 0) (e (k : ZMod (2 * q))) = finiteInwardRegion J μ z :=
    forward_factor_newton_two_ray_facets hq e hfan T P k hk₀ hkq
  have hregion : forwardFactorNewtonRegion T G e k =
      finiteInwardRegion J μ (fun i => z i + μ i G) := by
    simp only [forwardFactorNewtonRegion, forwardFactorRayCone, hkq, ite_true]
    rw [← add_assoc, add_comm (latticeHull T) ({latticeEmbedding G} : Set RealPlane), add_assoc,
      hcone, translated_finite_inward_region]
  rw [hregion]
  have hnormal (a : Site) : directionNormal (-a) = -directionNormal a := by
    ext g
    simp [directionNormal, determinant]
    ring
  have hindex (i : ℕ) : e ((q + i : ℕ) : ZMod (2 * q)) = -e (i : ZMod (2 * q)) := by
    rw [Nat.cast_add, add_comm, hfan.opposite]
  simpa only [μ, z, Nat.cast_zero, hindex, hnormal, map_add] using
    forward_factor_surviving_facets_eq_inward_region e hfan k hk₀ hkq (fun i => z i + μ i G)

end KumarNivat
