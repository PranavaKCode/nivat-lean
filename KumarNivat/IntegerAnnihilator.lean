module

public import KumarNivat.Alphabets
public import KumarNivat.LocalAnnihilator
public import Mathlib.Data.Rat.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
-- the ordered product lemma now needs its defining module explicitly.
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

@[expose] public section

namespace KumarNivat

-- one positive denominator clears every coefficient of a finite rational stencil.
theorem exists_integer_multiple (f : Stencil ℚ) :
    ∃ B : ℕ, 0 < B ∧ ∃ F : Stencil ℤ,
      ∀ u : Site, (F u : ℚ) = (B : ℚ) * f u := by
  classical
  let B : ℕ := ∏ u ∈ f.support, (f u).den
  have hB : 0 < B := Finset.prod_pos (fun _ _ => Rat.den_pos _)
  have hex (u : Site) : ∃ z : ℤ, (z : ℚ) = (B : ℚ) * f u := by
    by_cases hu : u ∈ f.support
    · have hdiv : (f u).den ∣ B := Finset.dvd_prod_of_mem (fun v => (f v).den) hu
      obtain ⟨m, hm⟩ := hdiv
      refine ⟨(m : ℤ) * (f u).num, ?_⟩
      calc
        (((m : ℤ) * (f u).num : ℤ) : ℚ) = (m : ℚ) * ((f u).num : ℚ) := by simp
        _ = (m : ℚ) * (f u * ((f u).den : ℚ)) := by rw [Rat.mul_den_eq_num]
        _ = (B : ℚ) * f u := by rw [hm]; push_cast; ring
    · refine ⟨0, ?_⟩
      rw [Finsupp.notMem_support_iff.mp hu]
      simp
  let z : Site → ℤ := fun u => Classical.choose (hex u)
  have hz (u : Site) : (z u : ℚ) = (B : ℚ) * f u := Classical.choose_spec (hex u)
  have hsupport : ∀ u, z u ≠ 0 → u ∈ f.support := by
    intro u hzu
    by_contra hu
    have hzero : (z u : ℚ) = 0 := by rw [hz, Finsupp.notMem_support_iff.mp hu, mul_zero]
    exact hzu (Int.cast_eq_zero.mp hzero)
  exact ⟨B, hB, Finsupp.onFinset f.support z hsupport, hz⟩

-- scaling rational coefficients commutes with the original integer configuration's finite action.
theorem cast_act_integer_multiple (c : Site → ℤ) (f : Stencil ℚ) (F : Stencil ℤ)
    (B : ℕ) (hB : 0 < B) (hscale : ∀ u, (F u : ℚ) = (B : ℚ) * f u) (g : Site) :
    ((act F c g : ℤ) : ℚ) = (B : ℚ) * act f (fun x => (c x : ℚ)) g := by
  classical
  have hBq : (B : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hB
  have hs : F.support = f.support := by
    ext u
    rw [Finsupp.mem_support_iff, Finsupp.mem_support_iff]
    constructor
    · intro hF hf
      have hz : (F u : ℚ) = 0 := by rw [hscale, hf, mul_zero]
      exact hF (Int.cast_eq_zero.mp hz)
    · intro hf hF
      have hz := hscale u
      rw [hF, Int.cast_zero] at hz
      exact hf ((mul_eq_zero.mp hz.symm).resolve_left hBq)
  unfold act Finsupp.sum
  simp only [Int.cast_sum, Int.cast_mul]
  rw [hs]
  simp_rw [hscale]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  ring

-- lemma 2.1 now has the manuscript's actual integer-coefficient conclusion.
theorem exists_integer_annihilator (c : Site → ℤ) (hc : (Set.range c).Finite)
    (D : Finset Site) (hlow : complexity c D ≤ D.card) :
    ∃ F : Stencil ℤ, F ≠ 0 ∧ ∀ g, act F c g = 0 := by
  let d : Site → ℚ := fun g => (c g : ℚ)
  have hd : (Set.range d).Finite := (hc.image (fun x : ℤ => (x : ℚ))).subset (by
    rintro y ⟨g, rfl⟩
    exact ⟨c g, ⟨g, rfl⟩, rfl⟩)
  have hcount : complexity d D = complexity c D :=
    complexity_map_injective c (fun x : ℤ => (x : ℚ)) Int.cast_injective D
  obtain ⟨f, hf, hann⟩ := exists_nonzero_annihilator d hd D (hcount ▸ hlow)
  obtain ⟨B, hB, F, hscale⟩ := exists_integer_multiple f
  have hBq : (B : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hB
  refine ⟨F, ?_, ?_⟩
  · intro hz
    apply hf
    ext u
    have he := hscale u
    rw [hz, Finsupp.zero_apply, Int.cast_zero] at he
    exact (mul_eq_zero.mp he.symm).resolve_left hBq
  · intro g
    have he := cast_act_integer_multiple c f F B hB hscale g
    rw [show act f (fun x => (c x : ℚ)) g = 0 from hann g, mul_zero] at he
    exact Int.cast_eq_zero.mp he

end KumarNivat
