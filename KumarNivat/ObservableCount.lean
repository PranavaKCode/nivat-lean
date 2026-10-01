import KumarNivat.LocalAnnihilator
import KumarNivat.DimensionCount

namespace KumarNivat

-- a finite stencil acts linearly on arrays, including the affine test identities.
noncomputable def actLinear {K : Type*} [CommRing K] (f : Stencil K) :
    (Site → K) →ₗ[K] (Site → K) where
  toFun c := act f c
  map_add' c d := by
    funext g
    simp [act, mul_add, Finsupp.sum_add]
  map_smul' t c := by
    funext g
    simp [act, Finsupp.sum, Finset.mul_sum, mul_assoc, mul_comm]

-- finite operators commute because their lattice shifts and scalar coefficients commute.
theorem act_commute {K : Type*} [CommRing K] (f h : Stencil K) (c : Site → K) :
    act f (act h c) = act h (act f c) := by
  classical
  funext g
  unfold act Finsupp.sum
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro u hu
  rw [show g + u + v = g + v + u by abel]
  ring

-- operators commute with observation shifts without enlarging the defining pattern window.
theorem act_shift {K : Type*} [CommRing K] (f : Stencil K) (c : Site → K) (t : Site) :
    act f (shift t c) = shift t (act f c) := by
  funext g
  unfold act shift
  congr 1
  funext u a
  congr 2
  abel

-- evaluate a function on occurring patterns at every lattice translate.
noncomputable def evaluatePatterns {K : Type*} [CommRing K] (c : Site → K)
    (D : Finset Site) : (patterns c D → K) →ₗ[K] (Site → K) where
  toFun v g := v ⟨fun u => c (g + u.val), ⟨g, rfl⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

-- include the constant coordinate in the affine coefficient map from section 4.
noncomputable def affineMap {K : Type*} [CommRing K] (c : Site → K)
    (D : Finset Site) : (Option D → K) →ₗ[K] (patterns c D → K) where
  toFun a p := a none + ∑ u : D, a (some u) * p.val u
  map_add' a b := by
    funext p
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    ring
  map_smul' t a := by
    funext p
    simp [Finset.mul_sum, mul_add, mul_assoc]

-- this is the final counting argument of section 4, with its remaining inputs exposed.
theorem observable_pattern_bound {K : Type*} [Field K] (c : Site → K)
    (hc : (Set.range c).Finite) (D J : Finset Site)
    (obs : J → (patterns c D → K)) (d : Site → K)
    (hlocal : ∀ t : J, evaluatePatterns c D (obs t) = shift t.val d)
    (Q : Stencil K) (hQc : ∀ g, act Q c g = 0)
    (hQconstant : ∀ κ : K, act Q (fun _ => κ) = 0)
    (hfree : ∀ f : Stencil K, (∀ g, act f (act Q d) g = 0) → f = 0)
    (hrelations : Module.finrank K (LinearMap.ker (affineMap c D)) ≤ J.card) :
    D.card + 1 ≤ complexity c D := by
  classical
  let : Fintype (patterns c D) := (patterns_finite_of_range c hc D).fintype
  let H : (J → K) →ₗ[K] (patterns c D → K) :=
    { toFun a := ∑ t : J, a t • obs t
      map_add' a b := by simp [add_smul, Finset.sum_add_distrib]
      map_smul' t a := by simp [Finset.smul_sum, mul_smul] }
  let L := (actLinear Q).comp (evaluatePatterns c D)
  have hEval (a : J → K) : evaluatePatterns c D (H a) =
      fun g => ∑ t : J, a t * d (g + t.val) := by
    change evaluatePatterns c D (∑ t : J, a t • obs t) = _
    rw [map_sum]
    simp only [map_smul, hlocal]
    funext g
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, shift]
  have hQH (a : J → K) : L (H a) = act (localStencil J a) (act Q d) := by
    change act Q (evaluatePatterns c D (H a)) = _
    rw [hEval]
    have he : (fun g => ∑ t : J, a t * d (g + t.val)) = act (localStencil J a) d := by
      funext g
      exact (act_localStencil J a d g).symm
    rw [he, act_commute]
  have hobs : Function.Injective (L.comp H) := by
    intro a b hab
    have hz : L (H (a - b)) = 0 := by
      rw [map_sub, map_sub]
      exact sub_eq_zero.mpr hab
    rw [hQH] at hz
    have hf := hfree (localStencil J (a - b)) (fun g => congrFun hz g)
    have hcoeff : a - b = 0 := by
      funext t
      have he := congrArg (fun f : Stencil K => f t.val) hf
      simpa only [localStencil_coeff, Finsupp.zero_apply, Pi.zero_apply] using he
    exact sub_eq_zero.mp hcoeff
  have hkill : L.comp (affineMap c D) = 0 := by
    apply LinearMap.ext
    intro a
    funext g
    let f := localStencil D (fun u => a (some u))
    have he : evaluatePatterns c D (affineMap c D a) =
        (fun _ => a none) + act f c := by
      funext x
      simp only [evaluatePatterns, affineMap, LinearMap.coe_mk, AddHom.coe_mk,
        Pi.add_apply, f, act_localStencil]
    change act Q (evaluatePatterns c D (affineMap c D a)) g = 0
    rw [he]
    change actLinear Q ((fun _ => a none) + act f c) g = 0
    rw [map_add]
    change (act Q (fun _ => a none)) g + act Q (act f c) g = 0
    rw [hQconstant, Pi.zero_apply, zero_add, act_commute]
    have hc0 : act Q c = 0 := funext hQc
    rw [hc0]
    simp [act]
  have hcard : Fintype.card (patterns c D) = complexity c D := by
    simp only [complexity, Set.ncard_eq_toFinset_card', Set.toFinset_card]
  have hb := dimension_count (affineMap c D) H L hkill hobs
    (by simpa only [Fintype.card_coe] using hrelations)
  simpa only [Fintype.card_option, Fintype.card_coe, hcard] using hb

end KumarNivat
