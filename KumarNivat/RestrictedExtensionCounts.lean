import KumarNivat.PatternExtensions
import KumarNivat.TuplePatternPeriods
import KumarNivat.FiniteWordDynamics

namespace KumarNivat

open scoped Classical

-- summing the exact fibers counts only the full patterns over the selected legal bases.
theorem card_extensions_over_bases {A : Type*} (c : Site → A)
    (S T : Finset Site) (hTS : T ⊆ S) [Fintype (patterns c S)]
    (B : Finset (patterns c T)) :
    (Finset.univ.filter (fun q => legalPatternRestriction c S T hTS q ∈ B)).card =
      ∑ b ∈ B, extensionCount c S T hTS b := by
  classical
  simp_rw [extensionCount_eq_card_fiber]
  exact (Finset.sum_card_fiberwise_eq_card_filter Finset.univ B
    (legalPatternRestriction c S T hTS)).symm

-- every selected base contributes one pattern plus its share of the actual extension budget.
theorem card_extensions_over_bases_le {A : Type*} (c : Site → A)
    (hc : (Set.range c).Finite) (S T : Finset Site) (hTS : T ⊆ S)
    [Fintype (patterns c S)] [Fintype (patterns c T)] (B : Finset (patterns c T)) :
    (Finset.univ.filter (fun q => legalPatternRestriction c S T hTS q ∈ B)).card ≤
      (complexity c S - complexity c T) + B.card := by
  classical
  rw [card_extensions_over_bases]
  have hsplit : (∑ b ∈ B, extensionCount c S T hTS b) =
      (∑ b ∈ B, (extensionCount c S T hTS b - 1)) + B.card := by
    calc
      _ = ∑ b ∈ B, ((extensionCount c S T hTS b - 1) + 1) := by
        apply Finset.sum_congr rfl
        intro b _hb
        have hpos := extensionCount_pos c hc S T hTS b
        omega
      _ = _ := by rw [Finset.sum_add_distrib]; simp
  rw [hsplit]
  have hsum : (∑ b ∈ B, (extensionCount c S T hTS b - 1)) ≤
      ∑ b : patterns c T, (extensionCount c S T hTS b - 1) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ B)
      (fun _b _hb _hnot => Nat.zero_le _)
  rw [extra_extensions_eq_pattern_loss c hc S T hTS] at hsum
  omega

-- the observed-base bound produces an actual repeated full window within the paper's two-r bound.
theorem short_full_pattern_collision_over_bases {A : Type*} (c x : Site → A)
    (hc : (Set.range c).Finite) (hx : LanguageContained x c)
    (S T : Finset Site) (hTS : T ⊆ S) [Fintype (patterns c T)]
    (B : Finset (patterns c T)) (r : ℕ)
    (hbudget : complexity c S - complexity c T ≤ r) (hcount : B.card ≤ r)
    (E p : Site)
    (hbase : ∀ n : ℤ, legalTranslatedPattern c x hx T (E + n • p) ∈ B) :
    ∃ i j : ℕ, i < j ∧ j ≤ 2 * r ∧ ∀ u ∈ S,
      x (E + (j : ℤ) • p + u) = x (E + (i : ℤ) • p + u) := by
  classical
  let : Fintype (patterns c S) := (patterns_finite_of_range c hc S).fintype
  let Q : Finset (patterns c S) := Finset.univ.filter
    (fun q => legalPatternRestriction c S T hTS q ∈ B)
  have hQ : Q.card ≤ 2 * r := by
    have hb := card_extensions_over_bases_le c hc S T hTS B
    change Q.card ≤ (complexity c S - complexity c T) + B.card at hb
    omega
  let s : ℕ → patterns c S := fun n => legalTranslatedPattern c x hx S (E + (n : ℤ) • p)
  have hmem (n : ℕ) : s n ∈ (Q : Set (patterns c S)) := by
    have hrestrict : legalPatternRestriction c S T hTS (s n) =
        legalTranslatedPattern c x hx T (E + (n : ℤ) • p) := by
      apply Subtype.ext
      rfl
    change s n ∈ Q
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrestrict ▸ hbase (n : ℤ)⟩
  obtain ⟨i, j, hij, hj, he⟩ := finite_state_short_collision s (Q : Set (patterns c S))
    Q.finite_toSet hmem
  have hj' : j ≤ Q.card := by simpa only [Set.ncard_coe_finset] using hj
  refine ⟨i, j, hij, hj'.trans hQ, ?_⟩
  intro u hu
  exact congrFun (congrArg Subtype.val he.symm) ⟨u, hu⟩

end KumarNivat
