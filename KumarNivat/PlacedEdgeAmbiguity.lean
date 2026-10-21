module

public import KumarNivat.ExposedPolygonFaces
public import KumarNivat.BoundaryLineRecurrences
public import KumarNivat.BoundaryAmbiguity

@[expose] public section

namespace KumarNivat

-- shared annihilation rules out an equality tail on a boundary with an actual retained disagreement.
theorem placed_edge_bases_ambiguous_of_boundary_disagreement {K : Type*} [CommRing K] [NoZeroDivisors K]
    (c x y : Site → K) (hc : (Set.range c).Finite)
    (hx : LanguageContained x c) (hy : LanguageContained y c)
    (f : Laurent K) (hf : f ≠ 0) (hxann : laurentAct f x = 0) (hyann : laurentAct f y = 0)
    (R S : Finset Site) (hgen : GeneratingPolygon c R S)
    (ν : Site →+ ℤ) (hν : ν ≠ 0) (m : ℤ) (hmin : ∀ u ∈ S, m ≤ ν u)
    (hface : (lowerLatticeFace S ν m).Nonempty) (p : Site) (hp : ν p = 0)
    (hprimitive : Int.gcd p.1 p.2 = 1) (β : ℤ) (E : Site) (hE : ν E = β - m)
    (hhalf : ∀ g : Site, β + 1 ≤ ν g → x g = y g)
    (g₀ : Site) (hg₀ : ν g₀ = β) (hneq : x g₀ ≠ y g₀) :
    ∀ n : ℤ, 2 ≤ extensionCount c S (S \ lowerLatticeFace S ν m) Finset.sdiff_subset
      (legalTranslatedPattern c x hx (S \ lowerLatticeFace S ν m) (E + n • p)) := by
  obtain ⟨q₀, t, hq₀, _hq₀mem, hq₁mem, hblock, hpoints, _hcard, _hgen₀, hgen₁⟩ :=
    exists_generating_polygon_face_block c R S hgen ν hν m hmin hface p hp hprimitive
  have hline : ν (E + q₀) = β := by rw [map_add, hE, hq₀]; omega
  have hinterior (n : ℤ) (u : Site) (hu : u ∈ S \ lowerLatticeFace S ν m) :
      x (E + n • p + u) = y (E + n • p + u) := by
    obtain ⟨hum, huf⟩ := Finset.mem_sdiff.mp hu
    have hnot : ν u ≠ m := by
      intro he
      exact huf (Finset.mem_filter.mpr ⟨hum, he⟩)
    have hlow := hmin u hum
    apply hhalf
    rw [map_add, map_add, map_zsmul, hp, smul_zero, add_zero, hE]
    omega
  have hnotail (N : ℤ) : ¬ ∃ b : ℤ, N ≤ b ∧ ∀ n : ℤ, b ≤ n →
      x (E + q₀ + n • p) = y (E + q₀ + n • p) := by
    rintro ⟨b, _hb, htail⟩
    exact hneq (boundary_agreement_of_inward_halfplane_and_tail x y f hf hxann hyann ν hν p hp
      hprimitive β (E + q₀) hline hhalf b htail g₀ hg₀)
  intro n
  exact all_forward_bases_ambiguous_of_no_agreement_tail c x y hc hx hy S (lowerLatticeFace S ν m)
    q₀ p E t hq₁mem hgen₁ hpoints (fun i => hblock i.castSucc) n
    (fun j _hj u hu => hinterior j u hu) (hnotail n) n le_rfl

end KumarNivat
