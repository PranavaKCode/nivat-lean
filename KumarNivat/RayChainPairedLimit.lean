module

public import KumarNivat.RayChainRelaxationMinkowski
public import KumarNivat.RayChainPairedFacets
public import KumarNivat.PairedStructureRayChainAgreementStages
public import KumarNivat.PairedStructureBoundaryLimit
public import KumarNivat.PolyhedralFailureLayers
public import KumarNivat.SquarefreeProducts

@[expose] public section

namespace KumarNivat

open scoped Pointwise

-- the constructed first failed ray region retains a non-full directional-periodic boundary limit of the same original array.
theorem paired_direction_of_initial_factor_ray_reference {K : Type*}
    [CommRing K] [Nontrivial K] [NoZeroDivisors K] [TopologicalSpace K] [DiscreteTopology K]
    {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    (c x B : Site → K) (hc : (Set.range c).Finite)
    (hx : x ∈ orbitClosure c) (hB : B ∈ orbitClosure c) (hBfull : FullyPeriodic B)
    (hs : List Site) (hdirs : ∀ p ∈ hs, p ≠ 0)
    (hpairs : hs.Pairwise (fun p r => determinant p r ≠ 0))
    (hann : laurentAct (differenceProduct hs) c = 0)
    (hnot : ¬ ∃ v : Site, v ≠ 0 ∧ IsPeriod x v)
    (e : ZMod (2 * q) → Site) (hfan : AnchoredChainFanOrder e)
    (hprimitive : ∀ i, Int.gcd (e i).1 (e i).2 = 1)
    (P : OrderedCyclicLatticePolygon e (differenceProduct (K := K) hs).coeff.support)
    (G : Site) (p : ℕ) (hp : 0 < p)
    (hstart : RegionalPeriod x {g | latticeEmbedding g ∈
      forwardFactorNewtonRegion (differenceProduct (K := K) hs).coeff.support G e 1} ((p : ℤ) • e 0))
    (hmatch : ∀ g : Site, latticeEmbedding g ∈
      forwardFactorNewtonRegion (differenceProduct (K := K) hs).coeff.support G e 1 → x g = B g) :
    HasPairedOneSidedDirection c := by
  classical
  let T := (differenceProduct (K := K) hs).coeff.support
  have hT : T.Nonempty := ⟨P.vertex 0, P.vertex_mem 0⟩
  have hxann : laurentAct (differenceProduct hs) x = 0 := funext
    (annihilator_inherited_of_language x c (languageContained_of_mem_orbitClosure c x hx)
      (differenceProduct hs).coeff (congrFun hann))
  obtain ⟨k, hk₀, hkq, hgood, hfail⟩ := first_failed_actual_factor_ray_region x hs hdirs hpairs hxann hnot
    T hT G e hfan hq (hprimitive 0) 1 (by omega) (by omega) p hp hstart
  have hkpos : 0 < k := by omega
  obtain ⟨hBperiod, hagree⟩ := agreement_on_actual_factor_ray_period_region x B hBfull T hT G e hfan hq
    (hprimitive 0) p hp k hkpos hkq hstart (hgood k hk₀ le_rfl) hmatch
  obtain ⟨g₀, hg₀, hneq₀⟩ := failed_regional_period_has_reference_disagreement x B
    {g | latticeEmbedding g ∈ forwardFactorNewtonRegion T G e (k + 1)} ((p : ℤ) • e 0) hBperiod hfail
  let ν := directionNormal (e 0)
  let μ : ℕ → Site →+ ℤ := fun i => -directionNormal (e (i : ZMod (2 * q)))
  let z : ℕ → ℤ := fun i => μ i (P.vertex ((q + i : ℕ) : ZMod (2 * q)) + G)
  let η := μ k
  let b := e (k : ZMod (2 * q))
  let cut := ν (P.vertex 0 + G)
  let J := Finset.Icc (k + 1) (q - 1)
  let Jfull := facetIndexSet J
  let μfull := facetNormals ν μ
  let zfull := facetLevels cut z
  have hPk : forwardFactorNewtonRegion T G e k = inwardLayerRegion η (z k) Jfull μfull zfull := by
    calc
      _ = inwardLayerRegion ν cut (Finset.Icc k (q - 1)) μ z :=
        forward_factor_newton_region_integer_facets hq e hfan T P G k hkpos hkq
      _ = inwardLayerRegion ν cut Jfull (facetNormals η μ) (facetLevels (z k) z) :=
        inward_chain_eq_adjoined_first_facet ν cut q k hkq μ z
      _ = _ := inward_region_adjoined_facet_swap ν η cut (z k) J μ z
  have hPnext : forwardFactorNewtonRegion T G e (k + 1) = inwardLayerRegion ν cut J μ z :=
    forward_factor_region_after_current_facet_removal hq e hfan T P G k hkpos hkq
  have hinitial : ∀ g : Site, latticeEmbedding g ∈ inwardLayerRegion η (z k) Jfull μfull zfull → x g = B g := by
    intro g hg
    apply hagree g
    rwa [hPk]
  have hfailure : ∃ g : Site, (∀ i ∈ Jfull, zfull i ≤ μfull i g) ∧ x g ≠ B g := by
    rw [hPnext] at hg₀
    have hg := (mem_inwardLayerRegion_lattice ν cut J μ z g₀).mp hg₀
    refine ⟨g₀, ?_, hneq₀⟩
    intro i hi
    cases i with
    | none => exact hg.1
    | some i => exact hg.2 i ((mem_facetIndexSet_some J i).mp hi)
  obtain ⟨β, g, hβ, _hgη, hg, hneq, hlast⟩ := first_failed_inward_layer x B η (z k) Jfull μfull zfull hinitial hfailure
  obtain ⟨t, _ht, _htratio, hsum⟩ := forward_factor_relaxation_original_minkowski_summand hq e hfan T P G k hkpos hkq β hβ
  have hf : differenceProduct (K := K) hs ≠ 0 := differenceProduct_ne_zero hs hdirs
  have hbne : b ≠ 0 := by
    intro hz
    have h := hprimitive (k : ZMod (2 * q))
    change Int.gcd b.1 b.2 = 1 at h
    rw [hz] at h
    simp at h
  have hη : η ≠ 0 := by
    exact neg_ne_zero.mpr (directionNormal_ne_zero b hbne)
  have hbη : η b = 0 := by simp only [η, μ, b, AddMonoidHom.neg_apply, directionNormal_self, neg_zero]
  obtain ⟨hdet, _hηa, _hηb, hslopes⟩ := forward_factor_ray_chain_slopes e hfan k hkpos hkq
  have hμ : ∀ i ∈ Jfull, 0 < μfull i b := by
    intro i hi
    cases i with
    | none => exact hdet
    | some i =>
      obtain ⟨hki, hiq⟩ := Finset.mem_Icc.mp ((mem_facetIndexSet_some J i).mp hi)
      exact (hslopes i (by omega) (by omega)).2
  have hinterior : ∀ u : Site, latticeEmbedding u ∈ inwardLayerRegion η β Jfull μfull zfull →
      β + 1 ≤ η u → x u = B u := by
    intro u hu hηu
    apply hlast u
    exact (mem_inwardLayerRegion_lattice η (β + 1) Jfull μfull zfull u).mpr
      ⟨hηu, ((mem_inwardLayerRegion_lattice η β Jfull μfull zfull u).mp hu).2⟩
  obtain ⟨_y, _hy, _s, _hs, _hperiod, _hnotfull, _hhalf, _E, _hE, _hfailure, hpair⟩ :=
    retained_nonfull_periodic_boundary_limit c x B hc hx hB hBfull hs hdirs hpairs hann
      (differenceProduct hs) hf hann η hη β b hbη (hprimitive (k : ZMod (2 * q))) Jfull μfull zfull hμ
      (({latticeEmbedding G} : Set RealPlane) + (forwardTwoRayCone (e 0) b +
        lineInterval 0 (latticeEmbedding (e ((k + 1 : ℕ) : ZMod (2 * q)))) 0 t))
      hsum hinterior ⟨g, hg, hneq⟩
  exact hpair

end KumarNivat
