import KumarNivat.LaurentAlgebra
import KumarNivat.RationalCone

namespace KumarNivat

-- section 3's quadratic product supplies the operator needed by the pattern count.
theorem exists_quadratic_operator {K : Type*} [Field K]
    (c U V : Site → K) (v w : Site) (hv : v ≠ 0) (hw : w ≠ 0)
    (hU : IsPeriod U v) (hV : IsPeriod V w)
    (Q₀ : Laurent K) (hQ₀ : Q₀ ≠ 0) (hann : laurentAct Q₀ c = 0)
    (hfree : ∀ f : Stencil K,
      (∀ g, act f (fun x => difference w U x * difference v V x) g = 0) → f = 0) :
    ∃ Q : Stencil K, Q ≠ 0 ∧ (∀ g, act Q c g = 0) ∧
      (∀ κ : K, act Q (fun _ => κ) = 0) ∧
      ∀ f : Stencil K,
        (∀ g, act f (act Q (fun x => U x * V x)) g = 0) → f = 0 := by
  let Q : Laurent K := (binomial v * binomial w) * Q₀
  have hQ : Q ≠ 0 := laurent_mul_ne_zero _ _
    (laurent_mul_ne_zero _ _ (binomial_ne_zero v hv) (binomial_ne_zero w hw)) hQ₀
  have hswap : Q = Q₀ * (binomial v * binomial w) := mul_comm _ _
  have hQc : laurentAct Q c = 0 := by
    change laurentAct ((binomial v * binomial w) * Q₀) c = 0
    rw [laurentAct_mul, hann, laurentAct_config_zero]
  have hconstant (κ : K) : laurentAct Q (fun _ => κ) = 0 := by
    rw [hswap, laurentAct_mul, laurentAct_mul, laurentAct_binomial w]
    have hz : difference w (fun _ : Site => κ) = 0 := by funext g; simp [difference]
    rw [hz, laurentAct_config_zero, laurentAct_config_zero]
  have hproduct : laurentAct Q (fun x => U x * V x) =
      laurentAct Q₀ (fun x => difference w U x * difference v V x) := by
    rw [hswap, laurentAct_mul, laurentAct_mul, laurentAct_binomial,
      laurentAct_binomial, mixed_difference_product U V v w hU hV]
  refine ⟨Q.coeff, ?_, fun g => congrFun hQc g, hconstant, ?_⟩
  · intro hz
    exact hQ (AddMonoidAlgebra.coeff_injective hz)
  · intro f hf
    change ∀ g, act f (laurentAct Q (fun x => U x * V x)) g = 0 at hf
    rw [hproduct] at hf
    exact annihilator_free_filtered _ hfree Q₀ hQ₀ f hf

-- independent integer half-plane normals make the shifted defect product a pointed-cone array.
theorem exists_quadratic_operator_of_halfplanes {K : Type*} [Field K]
    (c U V : Site → K) (v w : Site) (hv : v ≠ 0) (hw : w ≠ 0)
    (hU : IsPeriod U v) (hV : IsPeriod V w)
    (Q₀ : Laurent K) (hQ₀ : Q₀ ≠ 0) (hann : laurentAct Q₀ c = 0)
    (F : Site →+ Site) (hF : Function.Injective F) (a b : ℤ)
    (hsupport : ∀ g, difference w U g * difference v V g ≠ 0 →
      a ≤ (F g).1 ∧ b ≤ (F g).2)
    (hne : ∃ g, difference w U g * difference v V g ≠ 0) :
    ∃ Q : Stencil K, Q ≠ 0 ∧ (∀ g, act Q c g = 0) ∧
      (∀ κ : K, act Q (fun _ => κ) = 0) ∧
      ∀ f : Stencil K,
        (∀ g, act f (act Q (fun x => U x * V x)) g = 0) → f = 0 := by
  exact exists_quadratic_operator c U V v w hv hw hU hV Q₀ hQ₀ hann
    (rational_pointed_cone_no_annihilator _ hne F hF a b hsupport)

end KumarNivat
