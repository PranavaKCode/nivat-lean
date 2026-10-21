module

public import KumarNivat.WindowRelations
public import KumarNivat.QuadraticOperator

@[expose] public section

namespace KumarNivat

-- a quotient-box translate plus any observable input site fits the original rectangle.
theorem fitting_translate_site (t z : Site) (r s k n : ℕ)
    (ht : t ∈ rectangle (k - r) (n - s)) (hz : z ∈ rectangle (r + 1) (s + 1)) :
    t + z ∈ rectangle k n := by
  rw [mem_rectangle_iff] at ht hz ⊢
  simp only [Prod.fst_add, Prod.snd_add]
  omega

-- shifting a filtered array preserves each of its period vectors.
theorem IsPeriod.shift {A : Type*} {c : Site → A} {v : Site} (hp : IsPeriod c v) (u : Site) :
    IsPeriod (shift u c) v := by
  intro x
  change c (x + v + u) = c (x + u)
  rw [show x + v + u = x + u + v by abel, hp]

-- each observation uses only typed sites within the selected pattern window.
noncomputable def shiftedFilterObservation {K : Type*} [CommRing K] (c : Site → K)
    (D J : Finset Site) (f : Stencil K) (u : Site)
    (hfit : ∀ t : J, ∀ x ∈ f.support, t.val + u + x ∈ D) :
    J → (patterns c D → K) := fun t p =>
      ∑ x : f.support, f x.val * p.val ⟨t.val + u + x.val, hfit t x.val x.property⟩

-- evaluating the local function gives the shifted filter on the global configuration.
theorem shiftedFilterObservation_eval {K : Type*} [CommRing K] (c : Site → K)
    (D J : Finset Site) (f : Stencil K) (u : Site)
    (hfit : ∀ t : J, ∀ x ∈ f.support, t.val + u + x ∈ D) (t : J) :
    evaluatePatterns c D (shiftedFilterObservation c D J f u hfit t) =
      shift t.val (shift u (act f c)) := by
  classical
  funext g
  change (∑ x : f.support, f x.val * c (g + (t.val + u + x.val))) =
    f.sum (fun x a => a * c (((g + t.val) + u) + x))
  have he : ∀ x : Site, g + (t.val + u + x) = ((g + t.val) + u) + x := by
    intro x
    abel
  simp only [he, Finsupp.sum]
  exact Finset.sum_coe_sort f.support (fun x : Site => f x * c (((g + t.val) + u) + x))

-- sections 3 and 4 assemble once the directional filters and their factor-box placement are supplied.
theorem rectangle_bound_of_directional_filters {K : Type*} [Field K]
    (c : Site → K) (hc : (Set.range c).Finite)
    (φ : Laurent K) (hφ : φ ≠ 0) (r s k n : ℕ) (hext : BoxExtrema φ r s)
    (hdiv : ∀ q : Laurent K, (∃ κ : K, laurentAct q c = fun _ => κ) → φ ∣ q)
    (f g : Stencil K) (u₁ u₂ : Site)
    (hfit₁ : ∀ x ∈ f.support, u₁ + x ∈ rectangle (r + 1) (s + 1))
    (hfit₂ : ∀ x ∈ g.support, u₂ + x ∈ rectangle (r + 1) (s + 1))
    (v w : Site) (hv : v ≠ 0) (hw : w ≠ 0)
    (hperiod₁ : IsPeriod (act f c) v) (hperiod₂ : IsPeriod (act g c) w)
    (Q₀ : Laurent K) (hQ₀ : Q₀ ≠ 0) (hann : laurentAct Q₀ c = 0)
    (F : Site →+ Site) (hF : Function.Injective F) (a b : ℤ)
    (hsupport : ∀ x,
      difference w (shift u₁ (act f c)) x * difference v (shift u₂ (act g c)) x ≠ 0 →
        a ≤ (F x).1 ∧ b ≤ (F x).2)
    (hne : ∃ x,
      difference w (shift u₁ (act f c)) x * difference v (shift u₂ (act g c)) x ≠ 0) :
    k * n + 1 ≤ complexity c (rectangle k n) := by
  let D := rectangle k n
  let J := rectangle (k - r) (n - s)
  let U := shift u₁ (act f c)
  let V := shift u₂ (act g c)
  have hfitF (t : J) (x : Site) (hx : x ∈ f.support) : t.val + u₁ + x ∈ D := by
    have he := fitting_translate_site t.val (u₁ + x) r s k n t.property (hfit₁ x hx)
    simpa only [add_assoc] using he
  have hfitG (t : J) (x : Site) (hx : x ∈ g.support) : t.val + u₂ + x ∈ D := by
    have he := fitting_translate_site t.val (u₂ + x) r s k n t.property (hfit₂ x hx)
    simpa only [add_assoc] using he
  let obsF := shiftedFilterObservation c D J f u₁ hfitF
  let obsG := shiftedFilterObservation c D J g u₂ hfitG
  let obs : J → (patterns c D → K) := fun t p => obsF t p * obsG t p
  let d : Site → K := fun x => U x * V x
  have hlocal (t : J) : evaluatePatterns c D (obs t) = shift t.val d := by
    funext x
    have heF := congrFun (shiftedFilterObservation_eval c D J f u₁ hfitF t) x
    have heG := congrFun (shiftedFilterObservation_eval c D J g u₂ hfitG t) x
    change evaluatePatterns c D (obsF t) x * evaluatePatterns c D (obsG t) x =
      U (x + t.val) * V (x + t.val)
    exact congrArg₂ (fun a b : K => a * b) heF heG
  obtain ⟨Q, _hQ, hQc, hQconstant, hfree⟩ := exists_quadratic_operator_of_halfplanes
    c U V v w hv hw (hperiod₁.shift u₁) (hperiod₂.shift u₂)
    Q₀ hQ₀ hann F hF a b hsupport hne
  have hrelations : Module.finrank K (LinearMap.ker (affineMap c D)) ≤ J.card := by
    rw [show J.card = (k - r) * (n - s) from card_rectangle _ _]
    exact affine_kernel_bound_of_common_divisor c φ hφ r s k n hext hdiv
  have hb := observable_pattern_bound c hc D J obs d hlocal Q hQc hQconstant hfree hrelations
  simpa only [D, card_rectangle] using hb

end KumarNivat
