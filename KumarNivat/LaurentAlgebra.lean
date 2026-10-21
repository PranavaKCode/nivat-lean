module

public import KumarNivat.ObservableCount
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors

@[expose] public section

namespace KumarNivat

-- use convolution multiplication for finite operators, separately from pointwise array products.
abbrev Laurent (K : Type*) [CommRing K] := AddMonoidAlgebra K Site

-- the coefficient action agrees with the finite stencil action already checked.
noncomputable def laurentAct {K : Type*} [CommRing K] (f : Laurent K)
    (c : Site → K) : Site → K := act f.coeff c

-- evaluation at a fixed site is additive in the laurent operator.
noncomputable def laurentActAt {K : Type*} [CommRing K] (c : Site → K) (g : Site) :
    Laurent K →+ K := (actAt c g).comp AddMonoidAlgebra.coeffAddEquiv.toAddMonoidHom

-- a single monomial samples one site with its scalar coefficient.
theorem laurentAct_single {K : Type*} [CommRing K] (u : Site) (a : K) (c : Site → K) :
    laurentAct (AddMonoidAlgebra.single u a) c = fun g => a * c (g + u) := by
  funext g
  simp [laurentAct, act]

-- the identity and zero operators have the usual actions.
@[simp] theorem laurentAct_one {K : Type*} [CommRing K] (c : Site → K) :
    laurentAct 1 c = c := by
  funext g
  simp [laurentAct, act, AddMonoidAlgebra.one_def]

@[simp] theorem laurentAct_zero {K : Type*} [CommRing K] (c : Site → K) :
    laurentAct 0 c = 0 := by
  funext g
  simp [laurentAct, act]

-- a zero array stays zero under every finite operator.
@[simp] theorem laurentAct_config_zero {K : Type*} [CommRing K] (f : Laurent K) :
    laurentAct f (0 : Site → K) = 0 := by
  funext g
  simp [laurentAct, act]

-- laurent multiplication composes operators, as required in equation (2.2).
theorem laurentAct_mul {K : Type*} [CommRing K] (f h : Laurent K) (c : Site → K) :
    laurentAct (f * h) c = laurentAct f (laurentAct h c) := by
  classical
  funext g
  change laurentActAt c g (f * h) = _
  rw [AddMonoidAlgebra.mul_def, map_finsuppSum]
  simp_rw [map_finsuppSum]
  change f.coeff.sum (fun u a => h.coeff.sum (fun v b =>
    laurentAct (AddMonoidAlgebra.single (u + v) (a * b)) c g)) = _
  simp_rw [laurentAct_single]
  simp [laurentAct, act, Finsupp.sum, Finset.mul_sum,
    mul_assoc, add_assoc]

-- subtracting finite operators subtracts their actions.
theorem laurentAct_sub {K : Type*} [CommRing K] (f h : Laurent K) (c : Site → K) :
    laurentAct (f - h) c = laurentAct f c - laurentAct h c := by
  funext g
  exact (laurentActAt c g).map_sub f h

-- the lattice algebra is an integral domain over a field.
theorem laurent_mul_ne_zero {K : Type*} [Field K] (f h : Laurent K)
    (hf : f ≠ 0) (hh : h ≠ 0) : f * h ≠ 0 := mul_ne_zero hf hh

-- a directional period binomial uses the same forward convention as the manuscript.
noncomputable def binomial {K : Type*} [CommRing K] (v : Site) : Laurent K :=
  AddMonoidAlgebra.single v 1 - 1

-- binomial action is precisely the directional difference.
theorem laurentAct_binomial {K : Type*} [CommRing K] (v : Site) (c : Site → K) :
    laurentAct (binomial v) c = difference v c := by
  rw [binomial, laurentAct_sub, laurentAct_single, laurentAct_one]
  funext g
  simp [difference]

-- a nonzero direction gives a nonzero polynomial over a nontrivial ring.
theorem binomial_ne_zero {K : Type*} [CommRing K] [Nontrivial K] (v : Site) (hv : v ≠ 0) :
    (binomial v : Laurent K) ≠ 0 := by
  intro hz
  have he := congrArg (fun f : Laurent K => f.coeff v) hz
  simp [binomial, AddMonoidAlgebra.one_def, hv] at he

-- annihilator-freeness survives a nonzero laurent filter, as used after equation (3.3).
theorem annihilator_free_filtered {K : Type*} [Field K] (e : Site → K)
    (hfree : ∀ f : Stencil K, (∀ g, act f e g = 0) → f = 0)
    (Q : Laurent K) (hQ : Q ≠ 0) :
    ∀ f : Stencil K, (∀ g, act f (laurentAct Q e) g = 0) → f = 0 := by
  intro f hann
  let H : Laurent K := AddMonoidAlgebra.ofCoeff f
  have hprod : laurentAct (H * Q) e = 0 := by
    rw [laurentAct_mul]
    exact funext hann
  have hz := hfree (H * Q).coeff (fun g => congrFun hprod g)
  have hring : H * Q = 0 := AddMonoidAlgebra.coeff_injective hz
  have hH : H = 0 := (mul_eq_zero.mp hring).resolve_right hQ
  exact congrArg AddMonoidAlgebra.coeff hH

end KumarNivat
