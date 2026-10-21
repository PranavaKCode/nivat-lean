module

public import KumarNivat.MinimalDiscrepancy
public import KumarNivat.NoncollinearSites

@[expose] public section

namespace KumarNivat

-- the polygon has actual hull vertices and the edge budget on every nonempty supporting lattice face.
def GeneratingPolygon {A : Type*} (c : Site → A) (R S : Finset Site) : Prop :=
  S ⊆ R ∧ LatticeConvex S ∧ NoncollinearSites S ∧
    (∀ v : Site, IsLatticeVertex S v → GeneratedSite c S v) ∧
    ∀ ν : Site →+ ℤ, ν ≠ 0 → ∀ m : ℤ, (∀ u ∈ S, m ≤ ν u) →
      (lowerLatticeFace S ν m).Nonempty →
        complexity c S - complexity c (S \ lowerLatticeFace S ν m) ≤
          (lowerLatticeFace S ν m).card - 1

-- discrepancy extremality forces zero pattern loss when a generated vertex is removed.
theorem minimal_discrepancy_vertex_generated {A : Type*} (c : Site → A)
    (hc : (Set.range c).Finite) (R S : Finset Site) (hmin : MinimalDiscrepancyWindow c R S)
    (hdim : NoncollinearSites S) (v : Site) (hv : IsLatticeVertex S v) : GeneratedSite c S v := by
  obtain ⟨_hSR, _hSne, hSconv, _hδ, hstrict⟩ := hmin
  have hvm := latticeVertex_mem S v hv
  have hdel := hstrict (S.erase v) (Finset.erase_ssubset hvm)
    (hdim.erase_nonempty v) (hSconv.erase_vertex v hv)
  have hcard := Finset.card_erase_add_one hvm
  have hmono := complexity_mono_window c hc S (S.erase v) (Finset.erase_subset v S)
  have hequal : complexity c (S.erase v) = complexity c S := by
    unfold discrepancy at hdel
    omega
  exact extensionUnique_of_equal_complexity c hc S (S.erase v) (Finset.erase_subset v S) hequal

-- a supporting face of a two-dimensional polygon leaves some lattice sites behind.
theorem NoncollinearSites.sdiff_lower_face_nonempty {S : Finset Site} (hdim : NoncollinearSites S)
    (ν : Site →+ ℤ) (hν : ν ≠ 0) (m : ℤ) : (S \ lowerLatticeFace S ν m).Nonempty := by
  classical
  by_contra hn
  apply hdim.normal_not_constant ν hν m
  intro u hu
  by_contra hlevel
  apply hn
  refine ⟨u, Finset.mem_sdiff.mpr ⟨hu, ?_⟩⟩
  simpa only [lowerLatticeFace, Finset.mem_filter, hu, true_and] using hlevel

-- strict discrepancy comparison supplies the manuscript's exact edge ambiguity budget.
theorem minimal_discrepancy_lower_face_budget {A : Type*} (c : Site → A)
    (hc : (Set.range c).Finite) (R S : Finset Site) (hmin : MinimalDiscrepancyWindow c R S)
    (hdim : NoncollinearSites S) (ν : Site →+ ℤ) (hν : ν ≠ 0)
    (m : ℤ) (hlevel : ∀ u ∈ S, m ≤ ν u) (hface : (lowerLatticeFace S ν m).Nonempty) :
    complexity c S - complexity c (S \ lowerLatticeFace S ν m) ≤
      (lowerLatticeFace S ν m).card - 1 := by
  classical
  obtain ⟨_hSR, _hSne, hSconv, _hδ, hstrict⟩ := hmin
  have hproper : S \ lowerLatticeFace S ν m ⊂ S := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.sdiff_subset, ?_⟩
    intro he
    obtain ⟨v, hv⟩ := hface
    have hvm : v ∈ S := (Finset.mem_filter.mp hv).1
    have hvdel : v ∈ S \ lowerLatticeFace S ν m := by rw [he]; exact hvm
    exact (Finset.mem_sdiff.mp hvdel).2 hv
  have hdel := hstrict (S \ lowerLatticeFace S ν m) hproper
    (hdim.sdiff_lower_face_nonempty ν hν m) (hSconv.sdiff_lower_face ν m hlevel)
  have hsubset : lowerLatticeFace S ν m ⊆ S := Finset.filter_subset _ S
  have hcard := Finset.card_sdiff_add_card_eq_card hsubset
  have hmono := complexity_mono_window c hc S (S \ lowerLatticeFace S ν m) Finset.sdiff_subset
  have hfacepos := Finset.card_pos.mpr hface
  unfold discrepancy at hdel
  omega

-- lemma 5.1 constructs the full generating polygon from the original rectangle bound.
theorem exists_generating_polygon_of_low_complexity {K : Type*} [Field K]
    (c : Site → K) (hc : (Set.range c).Finite)
    (hnot : ¬ ∃ v : Site, v ≠ 0 ∧ IsPeriod c v) (k n : ℕ) (hk : 0 < k) (hn : 0 < n)
    (hlow : complexity c (rectangle k n) ≤ k * n) :
    ∃ S : Finset Site, MinimalDiscrepancyWindow c (rectangle k n) S ∧
      GeneratingPolygon c (rectangle k n) S := by
  have hkZ : (0 : ℤ) < k := by exact_mod_cast hk
  have hnZ : (0 : ℤ) < n := by exact_mod_cast hn
  have hR : (rectangle k n).Nonempty := ⟨(0, 0),
    (mem_rectangle_iff (0, 0) k n).mpr ⟨le_rfl, hkZ, le_rfl, hnZ⟩⟩
  obtain ⟨S, hmin⟩ := exists_minimal_discrepancy_window c (rectangle k n) hR
    (latticeConvex_rectangle k n) (by simpa only [card_rectangle] using hlow)
  have hdata := hmin
  obtain ⟨hSR, hSne, hSconv, hδ, _hstrict⟩ := hdata
  have hslow : complexity c S ≤ S.card := by unfold discrepancy at hδ; omega
  have hdim := noncollinear_of_nonperiodic_low_complexity c hc hnot S hSne hslow
  exact ⟨S, hmin, hSR, hSconv, hdim, minimal_discrepancy_vertex_generated c hc _ S hmin hdim,
    minimal_discrepancy_lower_face_budget c hc _ S hmin hdim⟩

-- the rational encoding preserves the integer configuration's vertices and exact pattern budgets.
theorem exists_integer_generating_polygon (c : Site → ℤ) (hc : (Set.range c).Finite)
    (hnot : ¬ ∃ v : Site, v ≠ 0 ∧ IsPeriod c v) (k n : ℕ) (hk : 0 < k) (hn : 0 < n)
    (hlow : complexity c (rectangle k n) ≤ k * n) :
    ∃ S : Finset Site, GeneratingPolygon c (rectangle k n) S := by
  let d : Site → ℚ := fun g => (c g : ℚ)
  have hd : (Set.range d).Finite := (hc.image (fun z : ℤ => (z : ℚ))).subset (by
    rintro y ⟨g, rfl⟩
    exact ⟨c g, ⟨g, rfl⟩, rfl⟩)
  have hcounts (D : Finset Site) : complexity d D = complexity c D :=
    complexity_map_injective c (fun z : ℤ => (z : ℚ)) Int.cast_injective D
  have hdnot : ¬ ∃ v : Site, v ≠ 0 ∧ IsPeriod d v := by
    rintro ⟨v, hv, hp⟩
    exact hnot ⟨v, hv,
      (isPeriod_map_injective c (fun z : ℤ => (z : ℚ)) Int.cast_injective v).mp hp⟩
  obtain ⟨S, _hmin, hSR, hconv, hdim, hvertices, hfaces⟩ :=
    exists_generating_polygon_of_low_complexity d hd hdnot k n hk hn (by rw [hcounts]; exact hlow)
  refine ⟨S, hSR, hconv, hdim, ?_, ?_⟩
  · intro v hv
    exact (extensionUnique_map_injective c (fun z : ℤ => (z : ℚ)) Int.cast_injective _ _).mp
      (hvertices v hv)
  · intro ν hν m hlevel hface
    simpa only [hcounts] using hfaces ν hν m hlevel hface

end KumarNivat
