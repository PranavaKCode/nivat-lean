module

public import KumarNivat.PairedStructureWords
public import KumarNivat.OrientedPairedData
public import KumarNivat.PeriodBinomials

@[expose] public section

namespace KumarNivat

-- each letter records one complete tangent period on a fixed normal level.
def periodicRowWord {A : Type*} (c : Site → A) (a v : Site) (L : ℕ) : ℤ → (Fin L → A) :=
  fun n j => c ((n : ℤ) • v + (j.val : ℤ) • a)

-- the row alphabet remains finite even though the normal coordinate is unbounded.
theorem periodicRowWord_range_finite {A : Type*} (c : Site → A)
    (hc : (Set.range c).Finite) (a v : Site) (L : ℕ) :
    (Set.range (periodicRowWord c a v L)).Finite := by
  apply (Set.Finite.pi' (fun _ : Fin L => hc)).subset
  rintro _ ⟨n, rfl⟩ j
  exact ⟨n • v + (j.val : ℤ) • a, rfl⟩

-- reduction of the tangent coefficient recovers every site from its complete row tuple.
def periodicRowIndex (L : ℕ) (hL : 0 < L) (m : ℤ) : Fin L :=
  ⟨(m % (L : ℤ)).toNat, by
    have h₀ := Int.emod_nonneg m (by omega : (L : ℤ) ≠ 0)
    have hlt := Int.emod_lt_of_pos m (by omega : (0 : ℤ) < L)
    omega⟩

-- the same residue index works on every normal level.
theorem periodic_row_value {A : Type*} (c : Site → A) (a v : Site) (L : ℕ)
    (hL : 0 < L) (hp : IsPeriod c ((L : ℤ) • a)) (m n : ℤ) :
    c (m • a + n • v) = periodicRowWord c a v L n (periodicRowIndex L hL m) := by
  let r : ℤ := m % (L : ℤ)
  let q : ℤ := m / (L : ℤ)
  have hr₀ : 0 ≤ r := Int.emod_nonneg _ (by omega : (L : ℤ) ≠ 0)
  have hj : ((periodicRowIndex L hL m).val : ℤ) = r := by
    change ((r.toNat : ℕ) : ℤ) = r
    omega
  have hm : r + q * (L : ℤ) = m := by
    exact Int.emod_add_ediv_mul m (L : ℤ)
  have hsite : (n • v + r • a) + q • ((L : ℤ) • a) = m • a + n • v := by
    rw [smul_smul]
    calc
      n • v + r • a + (q * (L : ℤ)) • a = (r + q * (L : ℤ)) • a + n • v := by
        rw [add_smul]
        abel
      _ = m • a + n • v := by rw [hm]
  change c (m • a + n • v) = c (n • v + ((periodicRowIndex L hL m).val : ℤ) • a)
  rw [hj, ← hsite]
  exact hp.zsmul q (n • v + r • a)

-- equal row tuples compare arbitrary tangent coefficients using the same residue index.
theorem equal_periodic_rows_compare_all_tangent_sites {A : Type*} (c : Site → A)
    (a v : Site) (L : ℕ) (hL : 0 < L) (hp : IsPeriod c ((L : ℤ) • a))
    (m n t : ℤ) (he : periodicRowWord c a v L n = periodicRowWord c a v L t) :
    c (m • a + n • v) = c (m • a + t • v) := by
  calc
    c (m • a + n • v) = periodicRowWord c a v L n (periodicRowIndex L hL m) :=
      periodic_row_value c a v L hL hp m n
    _ = periodicRowWord c a v L t (periodicRowIndex L hL m) :=
      congrFun he (periodicRowIndex L hL m)
    _ = c (m • a + t • v) := (periodic_row_value c a v L hL hp m t).symm

-- a positive period of the tuple sequence supplies the second independent global lattice period.
theorem fullyPeriodic_of_periodic_row_word {A : Type*} (c : Site → A)
    (a v : Site) (hav : determinant a v = 1) (L : ℕ) (hL : 0 < L)
    (hp : IsPeriod c ((L : ℤ) • a)) (p : ℕ) (hp₀ : 0 < p)
    (hrow : Function.Periodic (periodicRowWord c a v L) (p : ℤ)) : FullyPeriodic c := by
  have hsecond : IsPeriod c ((p : ℤ) • v) := by
    intro g
    let m : ℤ := determinant g v
    let n : ℤ := determinant a g
    have hrep : g = m • a + n • v := by
      simpa only [hav, one_smul] using determinant_smul_identity a v g
    have hsite : g + (p : ℤ) • v = m • a + (n + (p : ℤ)) • v := by
      rw [hrep, add_smul]
      abel
    rw [hsite, hrep]
    exact equal_periodic_rows_compare_all_tangent_sites c a v L hL hp m _ _ (hrow n)
  refine ⟨(L : ℤ) • a, (p : ℤ) • v, ?_, hp, hsecond⟩
  rw [determinant_zsmul, hav, mul_one]
  exact mul_ne_zero (by exact_mod_cast Nat.ne_of_gt hL) (by exact_mod_cast Nat.ne_of_gt hp₀)

-- a periodic configuration which is not fully periodic has a genuinely nonperiodic tuple word.
theorem periodic_row_word_has_no_positive_period {A : Type*} (c : Site → A)
    (a v : Site) (hav : determinant a v = 1) (L : ℕ) (hL : 0 < L)
    (hp : IsPeriod c ((L : ℤ) • a)) (hnot : ¬ FullyPeriodic c) :
    ¬ ∃ p : ℕ, 0 < p ∧ Function.Periodic (periodicRowWord c a v L) (p : ℤ) := by
  rintro ⟨p, hp₀, hrow⟩
  exact hnot (fullyPeriodic_of_periodic_row_word c a v hav L hL hp p hp₀ hrow)

end KumarNivat
