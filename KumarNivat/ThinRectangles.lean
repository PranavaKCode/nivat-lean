module

public import KumarNivat.AxisOperators
public import KumarNivat.Alphabets
public import KumarNivat.LocalAnnihilator
public import KumarNivat.LineFactorCoefficients
public import KumarNivat.LaurentNormalization

@[expose] public section

namespace KumarNivat

-- a local coefficient stencil has no exponent outside its observation window.
theorem localStencil_support_subset {K : Type*} [CommRing K]
    (D : Finset Site) (a : D → K) : (localStencil D a).support ⊆ D := by
  classical
  intro u hu
  by_contra hout
  have hz : localStencil D a u = 0 := by
    simp only [localStencil, Finsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro v _hv
    apply Finsupp.single_eq_of_ne
    intro he
    exact hout (he ▸ v.property)
  exact Finsupp.mem_support_iff.mp hu hz

-- the affine relation on a line yields a directional recurrence and hence a common global period.
theorem period_of_low_complexity_affine_line_window {K : Type*} [Field K]
    (c : Site → K) (hc : (Set.range c).Finite) (p : Site) (hp : p ≠ 0)
    (E : Site) (D : Finset Site) (hline : (D : Set Site) ⊆ Set.range (fun n : ℤ => E + n • p))
    (hlow : complexity c D ≤ D.card) :
    ∃ q : ℕ, 0 < q ∧ IsPeriod c ((q : ℤ) • p) := by
  classical
  obtain ⟨a, ha, κ, hconstant⟩ := exists_constant_local_combination c hc D hlow
  let f : Laurent K := AddMonoidAlgebra.ofCoeff (localStencil D a)
  have hf : f ≠ 0 := by
    intro hz
    apply ha
    funext u
    have he := congrArg (fun q : Laurent K => q.coeff u.val) hz
    simpa only [f, AddMonoidAlgebra.coeff_ofCoeff, localStencil_coeff,
      AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, Pi.zero_apply] using he
  let f₀ := AddMonoidAlgebra.single (-E) (1 : K) * f
  have hf₀ : f₀ ≠ 0 := mul_ne_zero (by simp) hf
  have hsupp : (f₀.coeff.support : Set Site) ⊆ Set.range (directionLine p) := by
    intro u hu
    have hu' := (monomial_translate_mem_support (-E) f u).mp hu
    obtain ⟨n, hn⟩ := hline (localStencil_support_subset D a hu')
    refine ⟨n, ?_⟩
    change n • p = u
    have he : E + n • p = E + u := by simpa only [sub_neg_eq_add, add_comm] using hn
    exact add_left_cancel he
  let d := AddMonoidAlgebra.comapDomain (directionLine p)
    (integer_direction_multiple_injective p hp) f₀
  have hdaxis : axisOperator p d = f₀ :=
    AddMonoidAlgebra.mapDomain_comapDomain hsupp (integer_direction_multiple_injective p hp)
  let e : LaurentPolynomial K := (AddMonoidAlgebra.single 1 1 - 1) * d
  have heaxis : axisOperator p e = binomial p * f₀ := by
    simp only [e, map_mul, map_sub, map_one, axisOperator_single, one_smul, hdaxis, binomial]
  have he : e ≠ 0 := by
    intro hz
    have hzero : axisOperator p e = 0 := by rw [hz, map_zero]
    rw [heaxis] at hzero
    exact mul_ne_zero (binomial_ne_zero p hp) hf₀ hzero
  have hfconstant : laurentAct f c = fun _ => κ := by
    funext g
    exact (act_localStencil D a c g).trans (hconstant g)
  have hf₀constant : laurentAct f₀ c = fun _ => κ := by
    rw [laurentAct_mul, hfconstant]
    funext g
    rw [laurentAct_single]
    exact one_mul κ
  have hann : laurentAct (axisOperator p e) c = 0 := by
    rw [heaxis, laurentAct_mul, hf₀constant, laurentAct_binomial]
    funext g
    exact sub_self κ
  exact period_multiple_of_axis_annihilator c hc p e he hann

-- the through-origin version is the special case used by the thin rectangle arguments.
theorem period_of_low_complexity_line_window {K : Type*} [Field K]
    (c : Site → K) (hc : (Set.range c).Finite) (p : Site) (hp : p ≠ 0)
    (D : Finset Site) (hline : (D : Set Site) ⊆ Set.range (directionLine p))
    (hlow : complexity c D ≤ D.card) :
    ∃ q : ℕ, 0 < q ∧ IsPeriod c ((q : ℤ) • p) := by
  apply period_of_low_complexity_affine_line_window c hc p hp 0 D _ hlow
  simpa only [directionLine, AddMonoidHom.coe_mk, ZeroHom.coe_mk, zero_add] using hline

-- a one-cell-high rectangle observes only the horizontal lattice line.
theorem horizontal_period_of_one_cell_height {K : Type*} [Field K]
    (c : Site → K) (hc : (Set.range c).Finite) (k : ℕ)
    (hlow : complexity c (rectangle k 1) ≤ k) :
    ∃ q : ℕ, 0 < q ∧ IsPeriod c ((q : ℤ) • (1, 0)) := by
  apply period_of_low_complexity_line_window c hc (1, 0) (by decide) (rectangle k 1)
  · intro u hu
    have hb := (mem_rectangle_iff u k 1).mp hu
    have hy : u.2 = 0 := by omega
    refine ⟨u.1, ?_⟩
    ext <;> simp [directionLine, hy]
  · simpa only [card_rectangle, mul_one] using hlow

-- a one-cell-wide rectangle gives the same construction along the vertical line.
theorem vertical_period_of_one_cell_width {K : Type*} [Field K]
    (c : Site → K) (hc : (Set.range c).Finite) (n : ℕ)
    (hlow : complexity c (rectangle 1 n) ≤ n) :
    ∃ q : ℕ, 0 < q ∧ IsPeriod c ((q : ℤ) • (0, 1)) := by
  apply period_of_low_complexity_line_window c hc (0, 1) (by decide) (rectangle 1 n)
  · intro u hu
    have hb := (mem_rectangle_iff u 1 n).mp hu
    have hx : u.1 = 0 := by omega
    refine ⟨u.2, ?_⟩
    ext <;> simp [directionLine, hx]
  · simpa only [card_rectangle, one_mul] using hlow

end KumarNivat
