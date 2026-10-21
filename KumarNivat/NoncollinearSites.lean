module

public import KumarNivat.ThinRectangles
public import KumarNivat.PrimitiveDirections

@[expose] public section

namespace KumarNivat

-- three sites with nonzero signed area give the polygon's two-dimensional affine span.
def NoncollinearSites (S : Finset Site) : Prop :=
  ∃ u ∈ S, ∃ v ∈ S, ∃ w ∈ S, determinant (v - u) (w - u) ≠ 0

-- a nonempty collinear lattice set lies on an affine primitive integer line.
theorem exists_affine_lattice_line_of_not_noncollinear (S : Finset Site)
    (hne : S.Nonempty) (hcol : ¬ NoncollinearSites S) :
    ∃ p : Site, p ≠ 0 ∧ ∃ E : Site,
      (S : Set Site) ⊆ Set.range (fun n : ℤ => E + n • p) := by
  classical
  obtain ⟨E, hE⟩ := hne
  by_cases hex : ∃ v ∈ S, v ≠ E
  · obtain ⟨v, hv, hvE⟩ := hex
    have hd : v - E ≠ 0 := sub_ne_zero.mpr hvE
    obtain ⟨p, a, ha, he, hp, τ, _ht, hker⟩ := exists_primitive_direction_coordinate (v - E) hd
    have haZ : (a : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt ha
    refine ⟨p, hp, E, ?_⟩
    intro w hw
    have hdet : determinant (v - E) (w - E) = 0 := by
      by_contra hn
      exact hcol ⟨E, hE, v, hv, w, hw, hn⟩
    have hid : determinant ((a : ℤ) • p) (w - E) = (a : ℤ) * determinant p (w - E) := by
      simpa only [one_smul, mul_one] using determinant_zsmul p (w - E) (a : ℤ) 1
    rw [he, hid] at hdet
    have hnormal : directionNormal p (w - E) = 0 :=
      (mul_eq_zero.mp hdet).resolve_left haZ
    have hpoint := hker (w - E) hnormal
    refine ⟨τ (w - E), ?_⟩
    change E + τ (w - E) • p = w
    rw [← hpoint]
    abel_nf
  · refine ⟨(1, 0), by decide, E, ?_⟩
    intro w hw
    have hwE : w = E := by
      by_contra hn
      exact hex ⟨w, hw, hn⟩
    exact ⟨0, by simp [hwE]⟩

-- a nonperiodic configuration's low-complexity window cannot be a segment or singleton.
theorem noncollinear_of_nonperiodic_low_complexity {K : Type*} [Field K]
    (c : Site → K) (hc : (Set.range c).Finite)
    (hnot : ¬ ∃ v : Site, v ≠ 0 ∧ IsPeriod c v)
    (S : Finset Site) (hne : S.Nonempty) (hlow : complexity c S ≤ S.card) : NoncollinearSites S := by
  by_contra hcol
  obtain ⟨p, hp, E, hline⟩ := exists_affine_lattice_line_of_not_noncollinear S hne hcol
  obtain ⟨q, hq, hperiod⟩ := period_of_low_complexity_affine_line_window c hc p hp E S hline hlow
  exact hnot ⟨(q : ℤ) • p, smul_ne_zero (by exact_mod_cast Nat.ne_of_gt hq) hp, hperiod⟩

-- removing one site still leaves a nonempty set when three sites span the plane.
theorem NoncollinearSites.erase_nonempty {S : Finset Site} (hS : NoncollinearSites S)
    (v : Site) : (S.erase v).Nonempty := by
  by_contra hn
  have hall (u : Site) (hu : u ∈ S) : u = v := by
    by_contra hne
    exact hn ⟨u, Finset.mem_erase.mpr ⟨hne, hu⟩⟩
  obtain ⟨x, hx, y, hy, z, hz, hdet⟩ := hS
  apply hdet
  simp [hall x hx, hall y hy, hall z hz, determinant]

-- a nonzero normal cannot be constant on a set whose affine span is the entire plane.
theorem NoncollinearSites.normal_not_constant {S : Finset Site} (hS : NoncollinearSites S)
    (ν : Site →+ ℤ) (hν : ν ≠ 0) (m : ℤ) : ¬ ∀ u ∈ S, ν u = m := by
  intro hall
  obtain ⟨u, hu, v, hv, w, hw, hdet⟩ := hS
  have hvu : ν (v - u) = 0 := by rw [map_sub, hall v hv, hall u hu, sub_self]
  have hwu : ν (w - u) = 0 := by rw [map_sub, hall w hw, hall u hu, sub_self]
  have hex : ∃ g : Site, ν g ≠ 0 := by
    by_contra hn
    apply hν
    ext g
    by_contra hg
    exact hn ⟨g, hg⟩
  obtain ⟨g, hg⟩ := hex
  have he := normal_cramer_identity ν (v - u) (w - u) g
  rw [hvu, hwu, mul_zero, mul_zero, add_zero] at he
  exact mul_ne_zero hdet hg he

end KumarNivat
