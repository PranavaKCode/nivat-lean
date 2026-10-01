import KumarNivat.PolyhedralRays
import KumarNivat.FailedRayContinuation
import KumarNivat.ExposedPolygonFaces
import KumarNivat.BoundaryAmbiguity

namespace KumarNivat

open scoped Pointwise

-- a failed outward layer places an actual generated edge and makes every sufficiently far legal base ambiguous.
theorem polyhedral_boundary_ambiguity_of_failed_extension {K I : Type*}
    [CommRing K] [NoZeroDivisors K] (c x y : Site → K)
    (hc : (Set.range c).Finite) (hx : LanguageContained x c) (hy : LanguageContained y c)
    (f : Laurent K) (hf : f ≠ 0) (hxann : laurentAct f x = 0) (hyann : laurentAct f y = 0)
    (R S : Finset Site) (hgen : GeneratingPolygon c R S)
    (ν : Site →+ ℤ) (hν : ν ≠ 0) (β : ℤ) (J : Finset I)
    (μ : I → Site →+ ℤ) (a : I → ℤ) (p : Site) (hp : ν p = 0)
    (hprimitive : Int.gcd p.1 p.2 = 1) (hμ : ∀ i ∈ J, 0 < μ i p)
    (C : Set RealPlane) (hsum : inwardLayerRegion ν β J μ a = latticeHull f.coeff.support + C)
    (hagree : ∀ g : Site, latticeEmbedding g ∈ inwardLayerRegion ν β J μ a →
      β + 1 ≤ ν g → x g = y g)
    (hfail : ∃ g : Site, latticeEmbedding g ∈ inwardLayerRegion ν β J μ a ∧ x g ≠ y g) :
    ∃ m : ℤ, ∃ E : Site, ∃ N : ℤ, (∀ u ∈ S, m ≤ ν u) ∧
      (lowerLatticeFace S ν m).Nonempty ∧ 2 ≤ (lowerLatticeFace S ν m).card ∧
      ν E = β - m ∧ 0 ≤ N ∧ ∀ n : ℤ, N ≤ n →
        (∀ u ∈ S, latticeEmbedding (E + n • p + u) ∈ inwardLayerRegion ν β J μ a) ∧
        (∀ u ∈ S \ lowerLatticeFace S ν m, x (E + n • p + u) = y (E + n • p + u)) ∧
        2 ≤ extensionCount c S (S \ lowerLatticeFace S ν m) Finset.sdiff_subset
          (legalTranslatedPattern c x hx (S \ lowerLatticeFace S ν m) (E + n • p)) := by
  classical
  obtain ⟨g₀, hg₀, hneq⟩ := hfail
  have hg₀level : ν g₀ = β := by
    have hlow := (mem_inwardLayerRegion_lattice ν β J μ a g₀).mp hg₀
    by_contra hne
    exact hneq (hagree g₀ hg₀ (by omega))
  obtain ⟨u, hu, _hrest⟩ := hgen.2.2.1
  obtain ⟨v, hv, hmin⟩ := S.exists_min_image ν ⟨u, hu⟩
  have hface : (lowerLatticeFace S ν (ν v)).Nonempty :=
    ⟨v, Finset.mem_filter.mpr ⟨hv, rfl⟩⟩
  obtain ⟨q₀, t, hq₀, hfirst, hlast, hblock, hpoints, hcard, _hgenfirst, hgenlast⟩ :=
    exists_generating_polygon_face_block c R S hgen ν hν (ν v) hmin hface p hp hprimitive
  let E := g₀ - q₀
  have hE : ν E = β - ν v := by dsimp [E]; rw [map_sub, hg₀level, hq₀]
  obtain ⟨N, hN, hfixed⟩ := eventually_translated_window_in_fixed_halfplanes J μ a S E p hμ
  have hfit (n : ℤ) (hn : N ≤ n) (u : Site) (hu : u ∈ S) :
      latticeEmbedding (E + n • p + u) ∈ inwardLayerRegion ν β J μ a := by
    apply (mem_inwardLayerRegion_lattice ν β J μ a _).mpr
    refine ⟨?_, hfixed n hn u hu⟩
    rw [map_add, map_add, map_zsmul, hE, hp, smul_zero, add_zero]
    have hb := hmin u hu
    omega
  have hinterior (n : ℤ) (hn : N ≤ n) (u : Site)
      (hu : u ∈ S \ lowerLatticeFace S ν (ν v)) :
      x (E + n • p + u) = y (E + n • p + u) := by
    obtain ⟨hus, huf⟩ := Finset.mem_sdiff.mp hu
    have hne : ν u ≠ ν v := by intro he; exact huf (Finset.mem_filter.mpr ⟨hus, he⟩)
    apply hagree _ (hfit n hn u hus)
    rw [map_add, map_add, map_zsmul, hE, hp, smul_zero, add_zero]
    have hb := hmin u hus
    omega
  have hforward := inwardLayerRegion_forward_stable ν β J μ a p hp (fun i hi => le_of_lt (hμ i hi))
  have hnotail := no_parallel_agreement_tail_of_failed_minkowski_extension x y f hf hxann hyann
    ν hν β p hp hprimitive (inwardLayerRegion ν β J μ a) C hsum (fun _z hz => hz.1)
      hforward hagree ⟨g₀, hg₀, hneq⟩ (E + q₀) (by dsimp [E]; simpa only [sub_add_cancel] using hg₀level)
  have hnotailN : ¬ ∃ b : ℤ, N ≤ b ∧ ∀ n : ℤ, b ≤ n →
      x (E + q₀ + n • p) = y (E + q₀ + n • p) := by
    rintro ⟨b, _hb, htail⟩
    exact hnotail ⟨b, htail⟩
  have ht := positive_edge_degree_of_no_agreement_tail c x y hx hy S (lowerLatticeFace S ν (ν v))
    q₀ p E t hlast hgenlast hpoints N hinterior hnotailN
  have hamb := all_forward_bases_ambiguous_of_no_agreement_tail c x y hc hx hy S
    (lowerLatticeFace S ν (ν v)) q₀ p E t hlast hgenlast hpoints
      (fun i => hblock ⟨i.val, by omega⟩) N hinterior hnotailN
  refine ⟨ν v, E, N, hmin, ⟨v, Finset.mem_filter.mpr ⟨hv, rfl⟩⟩, by omega, hE, hN, ?_⟩
  intro n hn
  exact ⟨hfit n hn, hinterior n hn, hamb n hn⟩

end KumarNivat
