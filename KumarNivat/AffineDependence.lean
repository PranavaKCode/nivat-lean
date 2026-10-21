module

public import KumarNivat.Statement
public import KumarNivat.DimensionCount
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Tactic.Ring

@[expose] public section

namespace KumarNivat

-- finite image suffices even when the ambient numeric alphabet is infinite.
theorem patterns_finite_of_range {A : Type*} (c : Site → A)
    (hc : (Set.range c).Finite) (D : Finset Site) : (patterns c D).Finite := by
  apply (Set.Finite.pi' (fun _ : D => hc)).subset
  rintro p ⟨g, rfl⟩ u
  exact ⟨g + u.val, rfl⟩

-- lemma 2.1 starts with a nonzero affine relation, including equality at the pattern threshold.
theorem exists_constant_local_combination {K : Type*} [Field K] (c : Site → K)
    (hc : (Set.range c).Finite) (D : Finset Site) (hlow : complexity c D ≤ D.card) :
    ∃ a : D → K, a ≠ 0 ∧ ∃ κ : K, ∀ g : Site,
      ∑ u : D, a u * c (g + u.val) = κ := by
  classical
  let P := patterns c D
  let : Fintype P := (patterns_finite_of_range c hc D).fintype
  let F : (K × (D → K)) →ₗ[K] (P → K) :=
    { toFun := fun v p => v.1 + ∑ u : D, v.2 u * p.val u
      map_add' := by
        intro v w
        funext p
        simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]
        ring
      map_smul' := by
        intro t v
        funext p
        simp [Finset.mul_sum, mul_add, mul_assoc] }
  have hcard : Fintype.card P = complexity c D := by
    simp only [P, complexity, Set.ncard_eq_toFinset_card', Set.toFinset_card]
  have hdim : Module.finrank K (P → K) < Module.finrank K (K × (D → K)) := by
    simp only [Module.finrank_prod, Module.finrank_fintype_fun_eq_card,
      Module.finrank_self, Fintype.card_coe, hcard]
    omega
  have hker : LinearMap.ker F ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt hdim
  obtain ⟨v, hv, hvne⟩ := (LinearMap.ker F).ne_bot_iff.mp hker
  have hrel (g : Site) : v.1 + ∑ u : D, v.2 u * c (g + u.val) = 0 := by
    exact congrFun (LinearMap.mem_ker.mp hv) ⟨_, ⟨g, rfl⟩⟩
  have ha : v.2 ≠ 0 := by
    intro ha
    have hfirst : v.1 = 0 := by simpa [ha] using hrel 0
    exact hvne (Prod.ext hfirst ha)
  refine ⟨v.2, ha, -v.1, ?_⟩
  intro g
  exact eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using hrel g)

end KumarNivat
