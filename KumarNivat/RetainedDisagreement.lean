module

public import KumarNivat.Operators
public import Mathlib.Data.Int.AbsoluteValue
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace KumarNivat

-- eventual transport is the geometric property in lemma 8.2(iii).
def BackwardCofinal (R H : Set Site) (a : Site) : Prop :=
  ∀ g ∈ H, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → g - (n : ℤ) • a ∈ R

-- a regional period only compares pairs of sites that lie in the region.
def RegionalPeriod {A : Type*} (w : Site → A) (H : Set Site) (p : Site) : Prop :=
  ∀ g ∈ H, g + p ∈ H → w (g + p) = w g

-- a hypothetical limit period transfers to the fixed reference half-plane.
theorem transfer_period_to_reference {A : Type*} (theta w : Site → A)
    (R H : Set Site) (a p : Site) (l : ℕ) (hl : 0 < l)
    (hw : IsPeriod w ((l : ℤ) • a)) (hp : IsPeriod theta p)
    (hagree : ∀ g ∈ R, theta g = w g) (htravel : BackwardCofinal R H a) :
    RegionalPeriod w H p := by
  intro g hg hgp
  obtain ⟨N, hN⟩ := htravel g hg
  obtain ⟨M, hM⟩ := htravel (g + p) hgp
  let n : ℕ := l * (N + M + 1)
  have hNn : N ≤ n := by dsimp [n]; nlinarith
  have hMn : M ≤ n := by dsimp [n]; nlinarith
  have hRg := hN n hNn
  have hRgp := hM n hMn
  have hwback : IsPeriod w (-((n : ℤ) • a)) := by
    convert hw.zsmul (-((N + M + 1 : ℕ) : ℤ)) using 1
    ext <;> simp [n] <;> ring
  calc
    w (g + p) = w ((g + p) - (n : ℤ) • a) := (hwback (g + p)).symm
    _ = theta ((g + p) - (n : ℤ) • a) := (hagree _ hRgp).symm
    _ = theta (g - (n : ℤ) • a) := by
      rw [show (g + p) - (n : ℤ) • a = (g - (n : ℤ) • a) + p by abel, hp]
    _ = w (g - (n : ℤ) • a) := hagree _ hRg
    _ = w g := hwback g

-- reverse a negative period so its coefficient can be used as a positive travel length.
theorem IsPeriod.natAbs_coefficient {A : Type*} {c : Site → A} {a : Site} (r : ℤ)
    (hp : IsPeriod c (r • a)) : IsPeriod c ((r.natAbs : ℤ) • a) := by
  cases r with
  | ofNat n => exact hp
  | negSucc n =>
    change IsPeriod c (-((n + 1 : ℕ) : ℤ) • a) at hp
    change IsPeriod c (((n + 1 : ℕ) : ℤ) • a)
    simpa only [neg_zsmul, neg_neg] using hp.neg

-- lemma 8.3: no transverse regional period and one fixed disagreement exclude every limit period.
theorem nonperiodic_of_retained_disagreement {A : Type*} (theta w : Site → A)
    (R H : Set Site) (a : Site) (l : ℕ) (hl : 0 < l)
    (hw : IsPeriod w ((l : ℤ) • a))
    (hagree : ∀ g ∈ R, theta g = w g) (htravel : BackwardCofinal R H a)
    (hparallel : ∀ p : Site, RegionalPeriod w H p → ∃ r : ℤ, p = r • a)
    (hfail : ∃ g ∈ H, theta g ≠ w g) :
    ¬ ∃ p : Site, p ≠ 0 ∧ IsPeriod theta p := by
  rintro ⟨p, hpne, hp⟩
  have hregional := transfer_period_to_reference theta w R H a p l hl hw hp hagree htravel
  obtain ⟨r, hr⟩ := hparallel p hregional
  have hrne : r ≠ 0 := by intro hz; apply hpne; simp [hr, hz]
  have hrpos : 0 < r.natAbs := Int.natAbs_pos.mpr hrne
  have hpa : IsPeriod theta ((r.natAbs : ℤ) • a) :=
    IsPeriod.natAbs_coefficient r (hr ▸ hp)
  let q : ℕ := l * r.natAbs
  have hq : 0 < q := Nat.mul_pos hl hrpos
  have hwt : IsPeriod w ((q : ℤ) • a) := by
    convert hw.zsmul (r.natAbs : ℤ) using 1
    simp only [smul_smul, q, Nat.cast_mul]
    rw [mul_comm]
  have htt : IsPeriod theta ((q : ℤ) • a) := by
    convert hpa.zsmul (l : ℤ) using 1
    simp only [smul_smul, q, Nat.cast_mul]
  obtain ⟨g, hg, hgf⟩ := hfail
  obtain ⟨N, hN⟩ := htravel g hg
  have hlarge : N ≤ q * (N + 1) := by nlinarith
  have hR := hN (q * (N + 1)) hlarge
  have hwback := hwt.zsmul (-((N + 1 : ℕ) : ℤ)) g
  have htback := htt.zsmul (-((N + 1 : ℕ) : ℤ)) g
  have hvec : (-((N + 1 : ℕ) : ℤ)) • ((q : ℤ) • a) =
      -((((q * (N + 1) : ℕ) : ℤ)) • a) := by
    ext <;> simp <;> ring
  rw [hvec] at hwback htback
  have heq : theta g = w g := by
    calc
      theta g = theta (g - ((q * (N + 1) : ℕ) : ℤ) • a) := by
        simpa only [sub_eq_add_neg] using htback.symm
      _ = w (g - ((q * (N + 1) : ℕ) : ℤ) • a) := hagree _ hR
      _ = w g := by
        simpa only [sub_eq_add_neg] using hwback
  exact hgf heq

end KumarNivat
