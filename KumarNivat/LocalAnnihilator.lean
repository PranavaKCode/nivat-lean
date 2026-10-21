module

public import KumarNivat.AffineDependence
public import KumarNivat.ConeObstruction

@[expose] public section

namespace KumarNivat

-- evaluation is additive in the finite operator coefficients.
noncomputable def actAt {K : Type*} [CommRing K] (c : Site → K) (g : Site) :
    Stencil K →+ K where
  toFun f := act f c g
  map_zero' := by simp [act]
  map_add' f h := by
    exact Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)

-- coefficients on a finite window give an actual finitely supported operator.
noncomputable def localStencil {K : Type*} [CommRing K] (D : Finset Site)
    (a : D → K) : Stencil K := ∑ u : D, Finsupp.single u.val (a u)

-- each window coefficient can be recovered, so the representation is injective.
theorem localStencil_coeff {K : Type*} [CommRing K] (D : Finset Site)
    (a : D → K) (u : D) : localStencil D a u.val = a u := by
  classical
  simp [localStencil, Finsupp.single_apply]

-- the operator samples precisely the same translated window as the affine relation.
theorem act_localStencil {K : Type*} [CommRing K] (D : Finset Site)
    (a : D → K) (c : Site → K) (g : Site) :
    act (localStencil D a) c g = ∑ u : D, a u * c (g + u.val) := by
  classical
  change actAt c g (∑ u : D, Finsupp.single u.val (a u)) = _
  rw [map_sum]
  simp [actAt, act]

-- translating exponents composes evaluation with a forward lattice shift.
theorem act_translateStencil {K : Type*} [CommRing K] (f : Stencil K)
    (w : Site) (c : Site → K) (g : Site) :
    act (f.mapDomain (fun u => u + w)) c g = act f c (g + w) := by
  unfold act
  rw [Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
  congr 1
  funext u a
  congr 2
  abel

-- differences of coefficient functions become differences of evaluated operators.
theorem act_sub {K : Type*} [CommRing K] (f h : Stencil K) (c : Site → K) (g : Site) :
    act (f - h) c g = act f c g - act h c g := (actAt c g).map_sub f h

-- a finite nonzero stencil cannot be invariant under one horizontal exponent shift.
theorem horizontal_stencil_difference_nonzero {K : Type*} [CommRing K]
    (f : Stencil K) (hf : f ≠ 0) :
    f.mapDomain (fun u => u + (1, 0)) - f ≠ 0 := by
  classical
  obtain ⟨u, hu, hmax⟩ := f.support.exists_max_image Prod.fst
    (Finsupp.support_nonempty_iff.mpr hf)
  have hshift : f (u + (1, 0)) = 0 := by
    by_contra hne
    have hh := hmax (u + (1, 0)) (Finsupp.mem_support_iff.mpr hne)
    simp only [Prod.fst_add] at hh
    omega
  intro hz
  have hval := congrArg (fun s : Stencil K => s (u + (1, 0))) hz
  have hinj : Function.Injective (fun v : Site => v + (1, 0)) :=
    fun _ _ h => add_right_cancel h
  simp only [Finsupp.sub_apply, Finsupp.mapDomain_apply_of_injective hinj,
    hshift, sub_zero, Finsupp.zero_apply] at hval
  exact (Finsupp.mem_support_iff.mp hu) hval

-- lemma 2.1's affine relation produces a nonzero annihilator over the coefficient field.
theorem exists_nonzero_annihilator {K : Type*} [Field K] (c : Site → K)
    (hc : (Set.range c).Finite) (D : Finset Site) (hlow : complexity c D ≤ D.card) :
    ∃ f : Stencil K, f ≠ 0 ∧ ∀ g, act f c g = 0 := by
  obtain ⟨a, ha, κ, hconstant⟩ := exists_constant_local_combination c hc D hlow
  let f := localStencil D a
  have hf : f ≠ 0 := by
    intro hz
    apply ha
    funext u
    have he := congrArg (fun s : Stencil K => s u.val) hz
    simpa only [f, localStencil_coeff, Finsupp.zero_apply, Pi.zero_apply] using he
  refine ⟨f.mapDomain (fun u => u + (1, 0)) - f,
    horizontal_stencil_difference_nonzero f hf, ?_⟩
  intro g
  rw [act_sub, act_translateStencil]
  simp only [f, act_localStencil, hconstant, sub_self]

end KumarNivat
