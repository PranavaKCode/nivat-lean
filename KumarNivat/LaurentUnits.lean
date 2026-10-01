import KumarNivat.BinomialCoprime
import KumarNivat.LineFactorCoefficients

namespace KumarNivat

-- a laurent unit has zero width in both coordinate normals, so it is one nonzero monomial.
theorem laurent_unit_is_single {K : Type*} [Field K]
    (f : Laurent K) (hunit : IsUnit f) :
    ∃ u : Site, ∃ a : K, a ≠ 0 ∧ f = AddMonoidAlgebra.single u a := by
  classical
  obtain ⟨g, he⟩ := isUnit_iff_exists_inv.mp hunit
  have hfg : f * g ≠ 0 := by rw [he]; exact one_ne_zero
  have hf : f ≠ 0 := left_ne_zero_of_mul hfg
  have hg : g ≠ 0 := right_ne_zero_of_mul hfg
  let ν := AddMonoidHom.fst ℤ ℤ
  let μ := AddMonoidHom.snd ℤ ℤ
  have hinj : Function.Injective (ν.prod μ) := by
    intro x y hxy
    exact Prod.ext (congrArg Prod.fst hxy) (congrArg Prod.snd hxy)
  have hinj' : Function.Injective (μ.prod ν) := by
    intro x y hxy
    exact Prod.ext (congrArg Prod.snd hxy) (congrArg Prod.fst hxy)
  have hflat (ell : Site →+ ℤ) : ∀ u ∈ (f * g).coeff.support, ell u = 0 := by
    intro u hu
    rw [he] at hu
    have hu₀ : u = 0 := by simpa [AddMonoidAlgebra.one_def] using hu
    rw [hu₀, map_zero]
  obtain ⟨a, ha⟩ := factor_support_normal_fiber f g hf hg ν μ hinj (hflat ν)
  obtain ⟨b, hb⟩ := factor_support_normal_fiber f g hf hg μ ν hinj' (hflat μ)
  have hsupport : f.coeff.support.Nonempty := Finsupp.support_nonempty_iff.mpr
    (fun hz => hf (AddMonoidAlgebra.coeff_injective hz))
  obtain ⟨u, hu⟩ := hsupport
  have hsingle : f.coeff.support ⊆ {u} := by
    intro v hv
    apply Finset.mem_singleton.mpr
    apply hinj
    exact Prod.ext ((ha v hv).trans (ha u hu).symm) ((hb v hv).trans (hb u hu).symm)
  refine ⟨u, f.coeff u, Finsupp.mem_support_iff.mp hu, ?_⟩
  apply AddMonoidAlgebra.coeff_injective
  exact Finsupp.eq_single_iff.mpr ⟨hsingle, rfl⟩

-- positive factor degree and nonzero endpoints exclude a monomial unit.
theorem lineOperator_not_isUnit {K : Type*} [Field K]
    (E p : Site) (hp : p ≠ 0) (t : ℕ) (ht : 0 < t) (α : Fin (t + 1) → K)
    (hfirst : α 0 ≠ 0) (hlast : α (Fin.last t) ≠ 0) :
    ¬ IsUnit (lineOperator E p t α) := by
  intro hunit
  obtain ⟨u, a, _ha, he⟩ := laurent_unit_is_single (lineOperator E p t α) hunit
  have hsupport : (lineOperator E p t α).coeff.support ⊆ {u} := by
    rw [he]
    exact Finsupp.support_single_subset
  have hend := lineOperator_endpoints_mem E p hp t α hfirst hlast
  have hE : E = u := Finset.mem_singleton.mp (hsupport hend.1)
  have hlastE : E + (t : ℤ) • p = u := Finset.mem_singleton.mp (hsupport hend.2)
  have hzero : (t : ℤ) • p = 0 := add_left_cancel
    (show E + (t : ℤ) • p = E + 0 by simpa only [add_zero, hE] using hlastE)
  exact (smul_ne_zero (by exact_mod_cast Nat.ne_of_gt ht) hp) hzero

end KumarNivat
