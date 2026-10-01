import KumarNivat.ExposedPolygonFaces
import KumarNivat.BoundaryEdgeAgreement
import KumarNivat.RegionalRowAgreement
import KumarNivat.PolyhedralRays
import KumarNivat.MinkowskiStencilFit

namespace KumarNivat

-- finite inward slopes place every late generating window, and its generated endpoint turns far seeds into a whole regional row.
theorem generated_regional_row_from_far_seeds {A I : Type*} (c x y : Site → A)
    (hx : LanguageContained x c) (hy : LanguageContained y c)
    (R S : Finset Site) (hgen : GeneratingPolygon c R S) (a : Site)
    (hprimitive : Int.gcd a.1 a.2 = 1) (cut : ℤ) (J : Finset I)
    (μ : I → Site →+ ℤ) (z : I → ℤ) (hμa : ∀ i ∈ J, 0 < μ i a)
    (p : ℕ) (hp : 0 < p)
    (hxper : RegionalPeriod x {g | latticeEmbedding g ∈ inwardLayerRegion (directionNormal a) cut J μ z} ((p : ℤ) • a))
    (hyper : RegionalPeriod y {g | latticeEmbedding g ∈ inwardLayerRegion (directionNormal a) cut J μ z} ((p : ℤ) • a))
    (η : Site →+ ℤ) (hη : η ≠ 0) (m k : ℤ) (hηa : η a = 0)
    (hmin : ∀ u ∈ S, m ≤ η u) (r : ℕ) (hcard : (lowerLatticeFace S η m).card = r + 1)
    (hfacelevel : ∀ u ∈ lowerLatticeFace S η m, directionNormal a u = k)
    (j : ℤ) (hlevels : ∀ u ∈ S, cut ≤ j - k + directionNormal a u)
    (hband : ∀ u ∈ S \ lowerLatticeFace S η m, ∀ g : Site,
      latticeEmbedding g ∈ inwardLayerRegion (directionNormal a) cut J μ z →
      directionNormal a g = j - k + directionNormal a u → x g = y g)
    (F : Site) (hF : directionNormal a F = j)
    (hseeds : ∀ N : ℤ, ∃ n : ℤ, N ≤ n ∧ ∀ i : Fin r,
      x (F + (n + (i.val : ℤ)) • a) = y (F + (n + (i.val : ℤ)) • a)) :
    ∀ g : Site, latticeEmbedding g ∈ inwardLayerRegion (directionNormal a) cut J μ z →
      directionNormal a g = j → x g = y g := by
  have hnormalA : directionNormal a a = 0 := by simp [directionNormal, determinant, mul_comm]
  have hface : (lowerLatticeFace S η m).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨q₀, t, hq₀, hfirst, hlast, _hblock, hpoints, hcard', _hgenfirst, hgenlast⟩ :=
    exists_generating_polygon_face_block c R S hgen η hη m hmin hface a hηa hprimitive
  have ht : t = r := by omega
  subst t
  have hq₀normal : directionNormal a q₀ = k :=
    hfacelevel q₀ (Finset.mem_filter.mpr ⟨hfirst, hq₀⟩)
  let E := F - q₀
  have hE : directionNormal a E = j - k := by dsimp [E]; rw [map_sub, hF, hq₀normal]
  obtain ⟨N, _hN, hfixed⟩ := eventually_translated_window_in_fixed_halfplanes J μ z S E a hμa
  have hlevel (n : ℤ) (u : Site) : directionNormal a (E + n • a + u) = j - k + directionNormal a u := by
    rw [map_add, map_add, map_zsmul, hE, hnormalA, smul_zero, add_zero]
  have hfit (n : ℤ) (hn : N ≤ n) (u : Site) (hu : u ∈ S) :
      latticeEmbedding (E + n • a + u) ∈ inwardLayerRegion (directionNormal a) cut J μ z := by
    apply (mem_inwardLayerRegion_lattice (directionNormal a) cut J μ z _).mpr
    exact ⟨by rw [hlevel]; exact hlevels u hu, hfixed n hn u hu⟩
  obtain ⟨n₀, hn₀, hseed⟩ := hseeds N
  have hinterior (n : ℤ) (hn : n₀ ≤ n) (u : Site) (hu : u ∈ S \ lowerLatticeFace S η m) :
      x (E + n • a + u) = y (E + n • a + u) :=
    hband u hu _ (hfit n (hn₀.trans hn) u (Finset.mem_sdiff.mp hu).1) (hlevel n u)
  have hseed' (i : Fin r) : x (E + q₀ + (n₀ + (i.val : ℤ)) • a) =
      y (E + q₀ + (n₀ + (i.val : ℤ)) • a) := by
    simpa only [E, sub_add_cancel] using hseed i
  have htail := generated_endpoint_agreement_tail c x y hx hy S (lowerLatticeFace S η m)
    q₀ a E r hlast hgenlast hpoints n₀ hinterior hseed'
  have htailF : ∀ n : ℤ, n₀ ≤ n → x (F + n • a) = y (F + n • a) := by
    intro n hn
    simpa only [E, sub_add_cancel] using htail n hn
  have hforward := inwardLayerRegion_forward_stable (directionNormal a) cut J μ z a hnormalA
    (fun i hi => le_of_lt (hμa i hi))
  have hstable : ∀ g ∈ {g | latticeEmbedding g ∈ inwardLayerRegion (directionNormal a) cut J μ z},
      g + (p : ℤ) • a ∈ {g | latticeEmbedding g ∈ inwardLayerRegion (directionNormal a) cut J μ z} := by
    intro g hg
    change latticeEmbedding (g + (p : ℤ) • a) ∈ inwardLayerRegion (directionNormal a) cut J μ z
    rw [latticeEmbedding_add, latticeEmbedding_zsmul, Int.cast_natCast]
    exact hforward _ hg (p : ℝ) (Nat.cast_nonneg p)
  have hrow := regional_row_agreement_of_periodic_tail x y
    {g | latticeEmbedding g ∈ inwardLayerRegion (directionNormal a) cut J μ z}
      a hprimitive p hp hstable hxper hyper F n₀ htailF
  intro g hg hgj
  exact hrow g hg (hgj.trans hF.symm)

end KumarNivat
