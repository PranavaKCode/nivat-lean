import KumarNivat.RayChainRelaxationMinkowski
import KumarNivat.RayChainPairedFacets
import KumarNivat.FirstFailedFacetWedge
import KumarNivat.SquarefreeProducts

namespace KumarNivat

open scoped Pointwise

-- the actual first failed factor-ray period gives the same nonperiodic array its section seven background wedge.
theorem background_wedge_of_initial_factor_ray_period {K : Type*}
    [CommRing K] [Nontrivial K] [NoZeroDivisors K]
    {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    (c x : Site → K) (hc : (Set.range c).Finite) (hx : LanguageContained x c)
    (hs : List Site) (hdirs : ∀ h ∈ hs, h ≠ 0)
    (hpairs : hs.Pairwise (fun h k => determinant h k ≠ 0))
    (hann : laurentAct (differenceProduct hs) x = 0)
    (hnot : ¬ ∃ v : Site, v ≠ 0 ∧ IsPeriod x v)
    (R S : Finset Site) (hgen : GeneratingPolygon c R S)
    (e : ZMod (2 * q) → Site) (hfan : AnchoredChainFanOrder e)
    (hprimitive : ∀ i, Int.gcd (e i).1 (e i).2 = 1)
    (hsource : ∀ i, ∃ h ∈ hs, determinant (e i) h = 0)
    (P : OrderedCyclicLatticePolygon e (differenceProduct (K := K) hs).coeff.support)
    (G : Site) (m M : ℤ)
    (hbounds : ∀ u ∈ S, m ≤ directionNormal (e 0) u ∧ directionNormal (e 0) u ≤ M)
    (hlower : 2 ≤ (lowerLatticeFace S (directionNormal (e 0)) m).card)
    (hupper : 2 ≤ (lowerLatticeFace S (-directionNormal (e 0)) (-M)).card)
    (p : ℕ) (hp : 0 < p)
    (hstart : RegionalPeriod x {g | latticeEmbedding g ∈
      forwardFactorNewtonRegion (differenceProduct (K := K) hs).coeff.support G e 1} ((p : ℤ) • e 0)) :
    ∃ b : Site, Int.gcd b.1 b.2 = 1 ∧ 0 < determinant (e 0) b ∧
      (∃ h ∈ hs, determinant b h = 0) ∧
      Function.Injective ((directionNormal (e 0)).prod (-directionNormal b)) ∧
      ∃ E : Site, ∃ B : Site → K, FullyPeriodic B ∧
        AgreesOnWedge (directionNormal (e 0)) (-directionNormal b) (directionNormal (e 0) E)
          ((-directionNormal b) E) x B ∧ Set.range B ⊆ Set.range x := by
  classical
  let T := (differenceProduct (K := K) hs).coeff.support
  have hT : T.Nonempty := ⟨P.vertex 0, P.vertex_mem 0⟩
  obtain ⟨k, hk₀, hkq, hgood, hfail⟩ := first_failed_actual_factor_ray_region x hs hdirs hpairs hann hnot
    T hT G e hfan hq (hprimitive 0) 1 (by omega) (by omega) p hp hstart
  have hkpos : 0 < k := by omega
  let ν := directionNormal (e 0)
  let μ : ℕ → Site →+ ℤ := fun i => -directionNormal (e (i : ZMod (2 * q)))
  let z : ℕ → ℤ := fun i => μ i (P.vertex ((q + i : ℕ) : ZMod (2 * q)) + G)
  let η := μ k
  let b := e (k : ZMod (2 * q))
  let cut := ν (P.vertex 0 + G)
  let J := Finset.Icc (k + 1) (q - 1)
  have hPk : forwardFactorNewtonRegion T G e k =
      inwardLayerRegion ν cut (facetIndexSet J) (facetNormals η μ) (facetLevels (z k) z) := by
    calc
      _ = inwardLayerRegion ν cut (Finset.Icc k (q - 1)) μ z :=
        forward_factor_newton_region_integer_facets hq e hfan T P G k hkpos hkq
      _ = _ := inward_chain_eq_adjoined_first_facet ν cut q k hkq μ z
  have hperiod : RegionalPeriod x {g | latticeEmbedding g ∈
      inwardLayerRegion ν cut (facetIndexSet J) (facetNormals η μ) (facetLevels (z k) z)} ((p : ℤ) • e 0) := by
    simpa only [hPk] using hgood k hk₀ le_rfl
  have hPnext : forwardFactorNewtonRegion T G e (k + 1) = inwardLayerRegion ν cut J μ z :=
    forward_factor_region_after_current_facet_removal hq e hfan T P G k hkpos hkq
  have hfailure : ¬ RegionalPeriod x {g | cut ≤ ν g ∧ ∀ i ∈ J, z i ≤ μ i g} ((p : ℤ) • e 0) := by
    simpa only [hPnext, mem_inwardLayerRegion_lattice] using hfail
  have hsum : ∀ β : ℤ, β < z k → ∃ C : Set RealPlane,
      inwardLayerRegion ν cut (facetIndexSet J) (facetNormals η μ) (facetLevels β z) = latticeHull T + C := by
    intro β hβ
    obtain ⟨t, _ht, _htratio, hbase⟩ := forward_factor_relaxation_original_minkowski_summand hq e hfan T P G k hkpos hkq β hβ
    refine ⟨({latticeEmbedding G} : Set RealPlane) + (forwardTwoRayCone (e 0) b +
      lineInterval 0 (latticeEmbedding (e ((k + 1 : ℕ) : ZMod (2 * q)))) 0 t), ?_⟩
    exact (inward_region_adjoined_facet_swap ν η cut β J μ z).trans hbase
  obtain ⟨hdet, hηa, hηb, hslopes⟩ := forward_factor_ray_chain_slopes e hfan k hkpos hkq
  have hbne : b ≠ 0 := by
    intro hz
    have h := hprimitive (k : ZMod (2 * q))
    change Int.gcd b.1 b.2 = 1 at h
    rw [hz] at h
    simp at h
  have hη : η ≠ 0 := neg_ne_zero.mpr (directionNormal_ne_zero b hbne)
  have hμa : ∀ i ∈ J, 0 < μ i (e 0) := by
    intro i hi
    obtain ⟨hki, hiq⟩ := Finset.mem_Icc.mp hi
    exact (hslopes i (by omega) (by omega)).1
  have hμb : ∀ i ∈ J, 0 < μ i b := by
    intro i hi
    obtain ⟨hki, hiq⟩ := Finset.mem_Icc.mp hi
    exact (hslopes i (by omega) (by omega)).2
  have hf : differenceProduct (K := K) hs ≠ 0 := differenceProduct_ne_zero hs hdirs
  obtain ⟨hinj, E, B, hBfull, hagree, hrange⟩ := background_wedge_from_first_failed_facet c x hc hx
    (differenceProduct hs) hf hann R S hgen (e 0) b (hprimitive 0) (hprimitive (k : ZMod (2 * q)))
    hdet m M cut hbounds hlower hupper J μ z hμa hμb η hη hηa hηb p hp (z k) hperiod hfailure hsum
  exact ⟨b, hprimitive (k : ZMod (2 * q)), hdet, hsource (k : ZMod (2 * q)), hinj,
    E, B, hBfull, hagree, hrange⟩

end KumarNivat
