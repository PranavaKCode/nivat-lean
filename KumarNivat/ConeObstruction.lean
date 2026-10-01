import KumarNivat.Operators
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

namespace KumarNivat

-- a laurent operator is a finitely supported coefficient function on the lattice.
abbrev Stencil (K : Type*) [Zero K] := Site →₀ K

-- this is the finite sum in equation (2.2).
noncomputable def act {K : Type*} [CommRing K] (f : Stencil K)
    (e : Site → K) (g : Site) : K := f.sum (fun u a => a * e (g + u))

-- finite sublevels are the support property obtained from the cone's dual interior.
def ProperSupport {K : Type*} [Zero K] (e : Site → K) (ell : Site →+ ℝ) : Prop :=
  ∀ B : ℝ, {g : Site | e g ≠ 0 ∧ ell g ≤ B}.Finite

-- proper sublevels give a least support site even when the array has infinite support.
theorem exists_support_minimum {K : Type*} [Zero K] (e : Site → K)
    (ell : Site →+ ℝ) (hproper : ProperSupport e ell) (hne : ∃ g, e g ≠ 0) :
    ∃ g, e g ≠ 0 ∧ ∀ x, e x ≠ 0 → ell g ≤ ell x := by
  obtain ⟨g₀, hg₀⟩ := hne
  let s : Set Site := {g | e g ≠ 0 ∧ ell g ≤ ell g₀}
  have hs : s.Finite := hproper (ell g₀)
  have hsne : s.Nonempty := ⟨g₀, hg₀, le_rfl⟩
  obtain ⟨g, hg, hmin⟩ := Set.exists_min_image s ell hs hsne
  refine ⟨g, hg.1, ?_⟩
  intro x hx
  by_cases hle : ell x ≤ ell g₀
  · exact hmin x ⟨hx, hle⟩
  · exact hg.2.trans (le_of_lt (lt_of_not_ge hle))

-- lemma 3.1's extremal argument uses a maximum for the operator and a minimum for the array.
theorem act_nonzero_of_proper_support {K : Type*} [Field K] (e : Site → K)
    (ell : Site →+ ℝ) (hinj : Function.Injective ell)
    (hproper : ProperSupport e ell) (hne : ∃ g, e g ≠ 0)
    (f : Stencil K) (hf : f ≠ 0) : ∃ g, act f e g ≠ 0 := by
  classical
  obtain ⟨g, hg, hmin⟩ := exists_support_minimum e ell hproper hne
  have hs : f.support.Nonempty := Finsupp.support_nonempty_iff.mpr hf
  obtain ⟨u, hu, hmax⟩ := f.support.exists_max_image ell hs
  refine ⟨g - u, ?_⟩
  have hzero : ∀ v ∈ f.support, v ≠ u → f v * e ((g - u) + v) = 0 := by
    intro v hv hvu
    have hlt : ell v < ell u := lt_of_le_of_ne (hmax v hv) (fun he => hvu (hinj he))
    have he : e ((g - u) + v) = 0 := by
      by_contra henz
      have hge := hmin ((g - u) + v) henz
      simp only [map_add, map_sub] at hge
      linarith
    rw [he, mul_zero]
  unfold act Finsupp.sum
  rw [Finset.sum_eq_single u hzero (fun h => (h hu).elim), sub_add_cancel]
  exact mul_ne_zero (Finsupp.mem_support_iff.mp hu) hg

-- an annihilator would contradict the explicitly nonzero evaluation above.
theorem no_annihilator_of_proper_support {K : Type*} [Field K] (e : Site → K)
    (ell : Site →+ ℝ) (hinj : Function.Injective ell)
    (hproper : ProperSupport e ell) (hne : ∃ g, e g ≠ 0) :
    ∀ f : Stencil K, (∀ g, act f e g = 0) → f = 0 := by
  intro f hann
  by_contra hf
  obtain ⟨g, hg⟩ := act_nonzero_of_proper_support e ell hinj hproper hne f hf
  exact hg (hann g)

end KumarNivat
