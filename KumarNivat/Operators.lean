module

public import KumarNivat.Statement
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace KumarNivat

-- all shifts use the forward convention from section 2.
def shift {A : Type*} (h : Site) (c : Site → A) : Site → A :=
  fun g => c (g + h)

-- the zero vector is permitted here; the final statement excludes it.
def IsPeriod {A : Type*} (c : Site → A) (h : Site) : Prop :=
  ∀ g, c (g + h) = c g

-- differences act on arrays, not on formal infinite series.
def difference {K : Type*} [Sub K] (h : Site) (c : Site → K) : Site → K :=
  fun g => c (g + h) - c g

-- addition composes periods without a change of origin.
theorem IsPeriod.add {A : Type*} {c : Site → A} {h t : Site}
    (hh : IsPeriod c h) (ht : IsPeriod c t) : IsPeriod c (h + t) := by
  intro g
  rw [← add_assoc, ht, hh]

-- a period can be traversed backwards as well.
theorem IsPeriod.neg {A : Type*} {c : Site → A} {h : Site}
    (hh : IsPeriod c h) : IsPeriod c (-h) := by
  intro g
  have he := hh (g - h)
  simpa [sub_eq_add_neg, add_assoc] using he.symm

-- integer multiples preserve the same array values.
theorem IsPeriod.zsmul {A : Type*} {c : Site → A} {h : Site}
    (hh : IsPeriod c h) (n : ℤ) : IsPeriod c (n • h) := by
  have hn (m : ℕ) : IsPeriod c (m • h) := by
    induction m with
    | zero => intro g; simp
    | succ m ih => simpa only [succ_nsmul] using ih.add hh
  cases n with
  | ofNat m => simpa only [Int.ofNat_eq_natCast, natCast_zsmul] using hn m
  | negSucc m =>
    change IsPeriod c (-((m + 1 : ℕ) : ℤ) • h)
    rw [neg_zsmul, natCast_zsmul]
    exact (hn (m + 1)).neg

-- the product identity in section 3 uses each factor's own period.
theorem mixed_difference_product {K : Type*} [CommRing K]
    (U V : Site → K) (v w : Site)
    (hU : IsPeriod U v) (hV : IsPeriod V w) :
    difference v (difference w (fun g => U g * V g)) =
      fun g => difference w U g * difference v V g := by
  funext g
  have huv : U (g + v + w) = U (g + w) := by
    rw [show g + v + w = g + w + v by abel, hU]
  have vuv : V (g + v + w) = V (g + v) := hV (g + v)
  dsimp only [difference]
  rw [huv, vuv, hU g, hV g]
  ring

-- finite image rules out a nonzero constant increment along a lattice line.
theorem finite_range_constant_increment {K : Type*} [Field K] [CharZero K]
    (c : Site → K) (hc : (Set.range c).Finite) (v : Site)
    (hinc : IsPeriod (difference v c) v) : IsPeriod c v := by
  classical
  intro g
  let d : K := difference v c g
  have hformula (n : ℕ) : c (g + n • v) = c g + (n : K) * d := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hsame : difference v c (g + n • v) = d := by
        simpa only [natCast_zsmul] using hinc.zsmul (n : ℤ) g
      have hstep : c ((g + n • v) + v) = c (g + n • v) + d := by
        dsimp only [difference] at hsame
        have he := congrArg (fun x : K => x + c (g + n • v)) hsame
        simpa [add_comm] using he
      rw [succ_nsmul, ← add_assoc, hstep, ih]
      push_cast
      ring
  let f : ℕ → Set.range c := fun n => ⟨c (g + n • v), ⟨g + n • v, rfl⟩⟩
  let : Finite (Set.range c) := hc.to_subtype
  obtain ⟨m, n, hmn, heq⟩ := Finite.exists_ne_map_eq_of_infinite f
  have he : c g + (m : K) * d = c g + (n : K) * d := by
    rw [← hformula m, ← hformula n]
    exact congrArg Subtype.val heq
  have hd : d = 0 := by
    have hmul : (m : K) * d = (n : K) * d := add_left_cancel he
    have hcast : (m : K) ≠ (n : K) := by exact_mod_cast hmn
    exact (mul_eq_mul_right_iff.mp hmul).resolve_left hcast
  exact sub_eq_zero.mp hd

end KumarNivat
