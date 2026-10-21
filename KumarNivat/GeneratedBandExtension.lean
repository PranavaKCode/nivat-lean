module

public import KumarNivat.GeneratedEdgeAgreement
public import KumarNivat.ExposedPolygonFaces
public import KumarNivat.PolygonNormalBands
public import KumarNivat.ShiftedConfigurations

@[expose] public section

namespace KumarNivat

-- a repeated full window seeds the new row, and its generated endpoints extend the old band period.
theorem generated_band_extension_of_full_pattern_repeat {A : Type*} (c x : Site → A)
    (hx : LanguageContained x c) (R S : Finset Site) (hgen : GeneratingPolygon c R S)
    (p : Site) (hprimitive : Int.gcd p.1 p.2 = 1) (m M : ℤ)
    (hbounds : ∀ u ∈ S, m ≤ directionNormal p u ∧ directionNormal p u ≤ M)
    (hface : (lowerLatticeFace S (directionNormal p) m).Nonempty) (q : ℕ)
    (hperiod : RegionalPeriod x (normalBand (directionNormal p) (m + 1) M) ((q : ℤ) • p))
    (n₀ : ℤ)
    (hrepeat : ∀ u ∈ S, x ((n₀ • p + u) + (q : ℤ) • p) = x (n₀ • p + u)) :
    RegionalPeriod x (normalBand (directionNormal p) m M) ((q : ℤ) • p) := by
  have hpne : p ≠ 0 := by rintro rfl; simp at hprimitive
  have hν := directionNormal_ne_zero p hpne
  have hp : directionNormal p p = 0 := by simp [directionNormal, determinant, mul_comm]
  have hqp : directionNormal p ((q : ℤ) • p) = 0 := by rw [map_zsmul, hp, smul_zero]
  obtain ⟨q₀, t, hq₀, hfirst, hlast, hblock, hpoints, _hcard, hgenfirst, hgenlast⟩ :=
    exists_generating_polygon_face_block c R S hgen (directionNormal p) hν m
      (fun u hu => (hbounds u hu).1) hface p hp hprimitive
  have hinterior (n : ℤ) (u : Site) (hu : u ∈ S \ lowerLatticeFace S (directionNormal p) m) :
      shift ((q : ℤ) • p) x (0 + n • p + u) = x (0 + n • p + u) := by
    obtain ⟨hus, huf⟩ := Finset.mem_sdiff.mp hu
    have hun : directionNormal p u ≠ m := by
      intro he
      exact huf (Finset.mem_filter.mpr ⟨hus, he⟩)
    have hb := hbounds u hus
    have hg : 0 + n • p + u ∈ normalBand (directionNormal p) (m + 1) M := by
      change m + 1 ≤ directionNormal p (0 + n • p + u) ∧
        directionNormal p (0 + n • p + u) ≤ M
      simp only [map_add, map_zsmul, hp, smul_zero, zero_add]
      omega
    have hfit : 0 + n • p + u + (q : ℤ) • p ∈ normalBand (directionNormal p) (m + 1) M := by
      change m + 1 ≤ directionNormal p (0 + n • p + u + (q : ℤ) • p) ∧
        directionNormal p (0 + n • p + u + (q : ℤ) • p) ≤ M
      rw [map_add, hqp, add_zero]
      exact hg
    exact hperiod _ hg hfit
  have hseed (i : Fin t) : shift ((q : ℤ) • p) x (0 + q₀ + (n₀ + (i.val : ℤ)) • p) =
      x (0 + q₀ + (n₀ + (i.val : ℤ)) • p) := by
    have hu := hblock ⟨i.val, by omega⟩
    have he := hrepeat (q₀ + (i.val : ℤ) • p) hu
    have hsite : n₀ • p + (q₀ + (i.val : ℤ) • p) = q₀ + (n₀ + (i.val : ℤ)) • p := by
      rw [add_smul]
      abel
    simpa only [shift, zero_add, hsite] using he
  have hline := generated_edge_agreement_of_block c (shift ((q : ℤ) • p) x) x
    (hx.shift _) hx S (lowerLatticeFace S (directionNormal p) m) q₀ p 0 t
    hfirst hlast hgenfirst hgenlast hpoints n₀ hinterior hseed
  obtain ⟨τ, _hτ, hker⟩ := primitive_direction_coordinate p hprimitive
  intro g hg hfit
  by_cases hlevel : directionNormal p g = m
  · have hd : g - q₀ = τ (g - q₀) • p := hker _ (by rw [map_sub, hlevel, hq₀, sub_self])
    have hsite : q₀ + τ (g - q₀) • p = g := by rw [← hd]; abel
    simpa only [shift, zero_add, hsite] using hline (τ (g - q₀))
  · have hg' : g ∈ normalBand (directionNormal p) (m + 1) M := by
      have hb := hg.1
      exact ⟨by omega, hg.2⟩
    have hfit' : g + (q : ℤ) • p ∈ normalBand (directionNormal p) (m + 1) M := by
      change m + 1 ≤ directionNormal p (g + (q : ℤ) • p) ∧
        directionNormal p (g + (q : ℤ) • p) ≤ M
      rw [map_add, hqp, add_zero]
      exact hg'
    exact hperiod g hg' hfit'

end KumarNivat
