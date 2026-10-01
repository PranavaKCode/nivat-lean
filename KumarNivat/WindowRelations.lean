import KumarNivat.RectangleQuotient

namespace KumarNivat

-- finite window coefficients embed linearly into the laurent algebra.
noncomputable def windowLaurentMap {K : Type*} [CommRing K] (D : Finset Site) :
    (D → K) →ₗ[K] Laurent K where
  toFun a := AddMonoidAlgebra.ofCoeff (localStencil D a)
  map_add' a b := by
    apply AddMonoidAlgebra.coeff_injective
    simp [localStencil, Finsupp.single_add, Finset.sum_add_distrib]
  map_smul' t a := by
    apply AddMonoidAlgebra.coeff_injective
    simp [localStencil, Finset.smul_sum]

-- restriction recovers each coefficient on the window.
theorem windowLaurent_coeff {K : Type*} [CommRing K] (D : Finset Site) (a : D → K) (u : D) :
    (windowLaurentMap D a).coeff u.val = a u := localStencil_coeff D a u

-- the constructed polynomial has no exponent outside its defining window.
theorem windowLaurent_support {K : Type*} [CommRing K] (D : Finset Site) (a : D → K) :
    (windowLaurentMap D a).coeff.support ⊆ D := by
  classical
  intro x hx
  by_contra hxD
  have hneq : ∀ u : D, u.val ≠ x := by
    intro u hu
    exact hxD (hu ▸ u.property)
  have hz : (windowLaurentMap D a).coeff x = 0 := by
    simp [windowLaurentMap, localStencil, hneq]
  exact (Finsupp.mem_support_iff.mp hx) hz

-- a polynomial supported in the window is reconstructed by its restricted coefficients.
theorem windowLaurent_reconstruct {K : Type*} [CommRing K] (D : Finset Site) (f : Laurent K)
    (hfit : f.coeff.support ⊆ D) :
    windowLaurentMap D (fun u => f.coeff u.val) = f := by
  classical
  apply AddMonoidAlgebra.coeff_injective
  ext x
  by_cases hx : x ∈ D
  · exact windowLaurent_coeff D _ ⟨x, hx⟩
  · rw [Finsupp.notMem_support_iff.mp (fun h => hx (windowLaurent_support D _ h)),
      Finsupp.notMem_support_iff.mp (fun h => hx (hfit h))]

-- discard only the constant coordinate when forming an affine relation polynomial.
def someProjection {K : Type*} [CommRing K] (D : Finset Site) :
    (Option D → K) →ₗ[K] (D → K) where
  toFun a u := a (some u)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

-- equation (4.1): the actual affine relation kernel is bounded by the quotient box area.
theorem affine_kernel_bound_of_common_divisor {K : Type*} [Field K] (c : Site → K)
    (φ : Laurent K) (hφ : φ ≠ 0) (r s k n : ℕ) (hext : BoxExtrema φ r s)
    (hdiv : ∀ f : Laurent K, (∃ κ : K, laurentAct f c = fun _ => κ) → φ ∣ f) :
    Module.finrank K (LinearMap.ker (affineMap c (rectangle k n))) ≤ (k - r) * (n - s) := by
  classical
  let D := rectangle k n
  let J := rectangle (k - r) (n - s)
  let R := LinearMap.ker (affineMap c D)
  let W : R →ₗ[K] Laurent K :=
    ((windowLaurentMap D).comp (someProjection D)).comp R.subtype
  have hWfit (a : R) : (W a).coeff.support ⊆ D :=
    windowLaurent_support D (fun u => a.val (some u))
  have hWconstant (a : R) : ∃ κ : K, laurentAct (W a) c = fun _ => κ := by
    refine ⟨-a.val none, ?_⟩
    funext g
    have he := congrFun (LinearMap.mem_ker.mp a.property)
      ⟨fun u => c (g + u.val), ⟨g, rfl⟩⟩
    change a.val none + ∑ u : D, a.val (some u) * c (g + u.val) = 0 at he
    change act (localStencil D (fun u => a.val (some u))) c g = -a.val none
    rw [act_localStencil]
    exact eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using he)
  have hWinj : Function.Injective W := by
    intro a b hab
    have hsome (u : D) : a.val (some u) = b.val (some u) := by
      have he := congrArg (fun f : Laurent K => f.coeff u.val) hab
      change localStencil D (fun u => a.val (some u)) u.val =
        localStencil D (fun u => b.val (some u)) u.val at he
      simpa only [localStencil_coeff] using he
    have ha := congrFun (LinearMap.mem_ker.mp a.property)
      ⟨fun u => c (0 + u.val), ⟨0, rfl⟩⟩
    have hb := congrFun (LinearMap.mem_ker.mp b.property)
      ⟨fun u => c (0 + u.val), ⟨0, rfl⟩⟩
    change a.val none + ∑ u : D, a.val (some u) * c (0 + u.val) = 0 at ha
    change b.val none + ∑ u : D, b.val (some u) * c (0 + u.val) = 0 at hb
    simp_rw [hsome] at ha
    have hnone : a.val none = b.val none := add_right_cancel (ha.trans hb.symm)
    apply Subtype.ext
    funext o
    cases o with
    | none => exact hnone
    | some u => exact hsome u
  let M : (J → K) →ₗ[K] Laurent K :=
    (LinearMap.mulLeft K φ).comp (windowLaurentMap J)
  have hWrange (a : R) : W a ∈ LinearMap.range M := by
    obtain ⟨q, hq⟩ := hdiv (W a) (hWconstant a)
    have hqJ : q.coeff.support ⊆ J := quotient_support_rectangle φ q hφ r s k n hext (by
      rw [← hq]
      exact hWfit a)
    refine ⟨fun u : J => q.coeff u.val, ?_⟩
    change φ * windowLaurentMap J (fun u => q.coeff u.val) = W a
    rw [windowLaurent_reconstruct J q hqJ]
    exact hq.symm
  let W' := W.codRestrict (LinearMap.range M) hWrange
  have hW'inj : Function.Injective W' := by
    intro a b hab
    exact hWinj (congrArg Subtype.val hab)
  have hdim := LinearMap.finrank_le_finrank_of_injective hW'inj
  have hrange := M.finrank_range_le
  have hbound : Module.finrank K (LinearMap.range M) ≤ (k - r) * (n - s) := by
    simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe, J, card_rectangle]
      using hrange
  exact hdim.trans hbound

end KumarNivat
