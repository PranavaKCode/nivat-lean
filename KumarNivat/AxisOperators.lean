import KumarNivat.LaurentBlocks
import KumarNivat.LineAnnihilatorPeriods

namespace KumarNivat

-- an integer exponent samples along the chosen lattice direction.
def directionLine (p : Site) : ℤ →+ Site where
  toFun n := n • p
  map_zero' := zero_smul ℤ p
  map_add' m n := add_smul m n p

-- insert one-variable laurent coefficients along that lattice direction.
noncomputable def axisOperator {K : Type*} [CommRing K] (p : Site) :
    LaurentPolynomial K →+* Laurent K := AddMonoidAlgebra.mapDomainRingHom K (directionLine p)

-- a one-variable monomial becomes the corresponding directional stencil monomial.
theorem axisOperator_single {K : Type*} [CommRing K] (p : Site) (n : ℤ) (a : K) :
    axisOperator p (AddMonoidAlgebra.single n a) = AddMonoidAlgebra.single (n • p) a := by
  simp only [axisOperator, AddMonoidAlgebra.mapDomainRingHom_apply,
    AddMonoidAlgebra.mapDomain_single, directionLine, AddMonoidHom.coe_mk, ZeroHom.coe_mk]

-- the trimmed laurent block is exactly the line recurrence operator already verified.
theorem axisOperator_block {K : Type*} [CommRing K] (p : Site) (m : ℤ) (t : ℕ)
    (α : Fin (t + 1) → K) :
    axisOperator p (laurentBlock m t α) = lineOperator (m • p) p t α := by
  rw [laurentBlock, map_sum]
  simp only [axisOperator_single, add_smul, lineOperator]

-- every nonzero directional eliminant yields a positive common period on all parallel lines.
theorem period_multiple_of_axis_annihilator {K : Type*} [Field K]
    (c : Site → K) (hc : (Set.range c).Finite) (p : Site) (d : LaurentPolynomial K)
    (hd : d ≠ 0) (hann : laurentAct (axisOperator p d) c = 0) :
    ∃ q : ℕ, 0 < q ∧ IsPeriod c ((q : ℤ) • p) := by
  obtain ⟨m, t, α, hfirst, hlast, he⟩ := exists_reversible_laurent_block d hd
  rw [he, axisOperator_block] at hann
  exact ⟨((Set.range c).ncard ^ t).factorial, Nat.factorial_pos _,
    line_annihilator_period c hc (m • p) p t α hfirst hlast hann⟩

-- constants in the outer laurent variable correspond to the original vertical coordinate.
theorem nestedLaurent_C {K : Type*} [CommRing K] (d : LaurentPolynomial K) :
    (nestedLaurentEquiv (K := K)).symm (LaurentPolynomial.C d) = axisOperator (0, 1) d := by
  induction d using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add d e hd he => simp only [map_add, hd, he]
  | single n a =>
    change AddMonoidAlgebra.curryRingEquiv.symm (AddMonoidAlgebra.single 0
      (AddMonoidAlgebra.single n a)) = _
    rw [AddMonoidAlgebra.curryRingEquiv_symm_single, axisOperator_single]
    congr 1
    ext <;> simp

end KumarNivat
