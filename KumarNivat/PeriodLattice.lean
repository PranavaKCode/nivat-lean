module

public import KumarNivat.RetainedDisagreement
public import KumarNivat.FilteredPeriods

@[expose] public section

namespace KumarNivat

-- the integer determinant tests independence of two lattice directions.
def determinant (u v : Site) : ℤ := u.1 * v.2 - u.2 * v.1

-- full periodicity has two independent global periods, as in the manuscript.
def FullyPeriodic {A : Type*} (c : Site → A) : Prop :=
  ∃ u v : Site, determinant u v ≠ 0 ∧ IsPeriod c u ∧ IsPeriod c v

-- applying a laurent filter preserves both periods of a fully periodic background.
theorem FullyPeriodic.filtered {K : Type*} [CommRing K] {c : Site → K}
    (hc : FullyPeriodic c) (f : Laurent K) : FullyPeriodic (laurentAct f c) := by
  obtain ⟨u, v, hdet, hu, hv⟩ := hc
  exact ⟨u, v, hdet, hu.filtered f.coeff, hv.filtered f.coeff⟩

-- cramer's identity expresses an integer multiple of any direction in the period lattice.
theorem determinant_smul_identity (u v h : Site) :
    determinant u v • h = determinant h v • u + determinant u h • v := by
  ext <;> simp [determinant] <;> ring

-- the same identity transports any integer lattice normal to the chosen basis.
theorem normal_cramer_identity (ν : Site →+ ℤ) (u v h : Site) :
    determinant u v * ν h = determinant h v * ν u + determinant u h * ν v := by
  have he := congrArg ν (determinant_smul_identity u v h)
  change ν (determinant u v • h) = ν (determinant h v • u + determinant u h • v) at he
  rw [map_add, map_zsmul, map_zsmul, map_zsmul] at he
  simpa using he

-- independent periods generate the corresponding determinant multiple.
theorem period_determinant_multiple {A : Type*} (c : Site → A) (u v h : Site)
    (hu : IsPeriod c u) (hv : IsPeriod c v) : IsPeriod c (determinant u v • h) := by
  rw [determinant_smul_identity]
  exact (hu.zsmul (determinant h v)).add (hv.zsmul (determinant u h))

-- every lattice direction has a positive multiple that fixes a fully periodic array.
theorem FullyPeriodic.exists_period_multiple {A : Type*} {c : Site → A}
    (hc : FullyPeriodic c) (h : Site) : ∃ q : ℕ, 0 < q ∧ IsPeriod c ((q : ℤ) • h) := by
  obtain ⟨u, v, hdet, hu, hv⟩ := hc
  refine ⟨(determinant u v).natAbs, Int.natAbs_pos.mpr hdet, ?_⟩
  exact IsPeriod.natAbs_coefficient (determinant u v) (period_determinant_multiple c u v h hu hv)

-- a finite family of periodic backgrounds can use one common multiple in each chosen direction.
theorem exists_common_period_multiple {A I : Type*} [Finite I] (B : I → Site → A)
    (hB : ∀ i, FullyPeriodic (B i)) (h : Site) :
    ∃ q : ℕ, 0 < q ∧ ∀ i, IsPeriod (B i) ((q : ℤ) • h) := by
  classical
  let : Fintype I := Fintype.ofFinite I
  have hex (s : Finset I) : ∃ q : ℕ, 0 < q ∧ ∀ i ∈ s, IsPeriod (B i) ((q : ℤ) • h) := by
    induction s using Finset.induction with
    | empty => exact ⟨1, by omega, by simp⟩
    | @insert i s hi ih =>
      obtain ⟨q, hq, hp⟩ := ih
      obtain ⟨r, hr, hri⟩ := (hB i).exists_period_multiple h
      refine ⟨r * q, Nat.mul_pos hr hq, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · convert hri.zsmul (q : ℤ) using 1
        ext <;> simp <;> ring
      · convert (hp j hj).zsmul (r : ℤ) using 1
        ext <;> simp <;> ring
  obtain ⟨q, hq, hp⟩ := hex Finset.univ
  exact ⟨q, hq, fun i => hp i (Finset.mem_univ i)⟩

end KumarNivat
