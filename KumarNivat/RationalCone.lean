import KumarNivat.ConeObstruction
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Tactic.FieldSimp

namespace KumarNivat

-- integer normals encode the two nonparallel rational supporting lines.
noncomputable def coneHeight (F : Site →+ Site) (t : ℝ) : Site →+ ℝ where
  toFun g := ((F g).1 : ℝ) + t * ((F g).2 : ℝ)
  map_zero' := by simp
  map_add' g h := by simp [mul_add]; ring

-- an irrational positive combination orders lattice sites without ties.
theorem coneHeight_injective (F : Site →+ Site) (hF : Function.Injective F)
    (t : ℝ) (ht : Irrational t) : Function.Injective (coneHeight F t) := by
  intro g h he
  change ((F g).1 : ℝ) + t * ((F g).2 : ℝ) =
    ((F h).1 : ℝ) + t * ((F h).2 : ℝ) at he
  have hy : (F g).2 = (F h).2 := by
    by_contra hne
    have hden : (((F g).2 - (F h).2 : ℤ) : ℝ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr hne
    apply ht.ne_rational ((F h).1 - (F g).1) ((F g).2 - (F h).2)
    apply (eq_div_iff hden).mpr
    push_cast
    nlinarith
  have hx : (F g).1 = (F h).1 := by
    rw [hy] at he
    exact_mod_cast add_right_cancel he
  exact hF (Prod.ext hx hy)

-- dual-height sublevels are bounded integer boxes, so their preimages are finite.
theorem rational_cone_proper_support {K : Type*} [Zero K] (e : Site → K)
    (F : Site →+ Site) (hF : Function.Injective F) (a b : ℤ)
    (hsupport : ∀ g, e g ≠ 0 → a ≤ (F g).1 ∧ b ≤ (F g).2)
    (t : ℝ) (ht : 0 < t) : ProperSupport e (coneHeight F t) := by
  intro B
  let box : Set Site :=
    (Set.Icc a ⌊B - t * (b : ℝ)⌋) ×ˢ (Set.Icc b ⌊(B - (a : ℝ)) / t⌋)
  have hbox : box.Finite := (Set.finite_Icc a _).prod (Set.finite_Icc b _)
  apply (hbox.preimage hF.injOn).subset
  intro g hg
  obtain ⟨ha, hb⟩ := hsupport g hg.1
  have hheight : ((F g).1 : ℝ) + t * ((F g).2 : ℝ) ≤ B := hg.2
  have haR : (a : ℝ) ≤ ((F g).1 : ℝ) := by exact_mod_cast ha
  have hbR : (b : ℝ) ≤ ((F g).2 : ℝ) := by exact_mod_cast hb
  have hx : ((F g).1 : ℝ) ≤ B - t * (b : ℝ) := by nlinarith
  have hy : ((F g).2 : ℝ) ≤ (B - (a : ℝ)) / t := by
    apply (le_div_iff₀ ht).mpr
    nlinarith
  exact ⟨⟨ha, Int.le_floor.mpr hx⟩, ⟨hb, Int.le_floor.mpr hy⟩⟩

-- lemma 3.1 for the rational cones used by the two filtered defects.
theorem rational_pointed_cone_no_annihilator {K : Type*} [Field K]
    (e : Site → K) (hne : ∃ g, e g ≠ 0)
    (F : Site →+ Site) (hF : Function.Injective F) (a b : ℤ)
    (hsupport : ∀ g, e g ≠ 0 → a ≤ (F g).1 ∧ b ≤ (F g).2) :
    ∀ f : Stencil K, (∀ g, act f e g = 0) → f = 0 := by
  have ht : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  exact no_annihilator_of_proper_support e (coneHeight F (Real.sqrt 2))
    (coneHeight_injective F hF _ irrational_sqrt_two)
    (rational_cone_proper_support e F hF a b hsupport _ ht) hne

end KumarNivat
