module

public import KumarNivat.GeneratingSets
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

namespace KumarNivat

open scoped Classical

-- an occurring larger pattern restricts to an occurring smaller pattern in the same language.
def legalPatternRestriction {A : Type*} (c : Site → A) (S T : Finset Site) (hTS : T ⊆ S) :
    patterns c S → patterns c T := fun p =>
  ⟨restrictPattern S T hTS p.val, by
    rw [patterns_restriction_image c S T hTS]
    exact ⟨p.val, p.property, rfl⟩⟩

-- every occurring base has at least one occurring extension, using the same translation.
theorem legalPatternRestriction_surjective {A : Type*} (c : Site → A)
    (S T : Finset Site) (hTS : T ⊆ S) :
    Function.Surjective (legalPatternRestriction c S T hTS) := by
  intro p
  obtain ⟨g, hg⟩ := p.property
  refine ⟨⟨fun u => c (g + u.val), ⟨g, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  exact hg

-- the fiber counts all distinct legal extensions of one actual occurring base pattern.
noncomputable def extensionCount {A : Type*} (c : Site → A)
    (S T : Finset Site) (hTS : T ⊆ S) (p : patterns c T) : ℕ :=
  {q : patterns c S | legalPatternRestriction c S T hTS q = p}.ncard

-- finite enumeration computes that exact set cardinality without choosing extension witnesses.
theorem extensionCount_eq_card_fiber {A : Type*} (c : Site → A)
    (S T : Finset Site) (hTS : T ⊆ S) [Fintype (patterns c S)] (p : patterns c T) :
    extensionCount c S T hTS p =
      (Finset.univ.filter (fun q => legalPatternRestriction c S T hTS q = p)).card := by
  classical
  have he : {q : patterns c S | legalPatternRestriction c S T hTS q = p} =
      (Finset.univ.filter (fun q => legalPatternRestriction c S T hTS q = p) : Set (patterns c S)) := by
    ext q
    simp
  rw [extensionCount, he, Set.ncard_coe_finset]

-- surjectivity makes the subtraction of one extension per base legitimate.
theorem extensionCount_pos {A : Type*} (c : Site → A) (hc : (Set.range c).Finite)
    (S T : Finset Site) (hTS : T ⊆ S) (p : patterns c T) : 0 < extensionCount c S T hTS p := by
  classical
  let : Fintype (patterns c S) := (patterns_finite_of_range c hc S).fintype
  obtain ⟨q, hq⟩ := legalPatternRestriction_surjective c S T hTS p
  rw [extensionCount_eq_card_fiber]
  exact Finset.card_pos.mpr ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ q, hq⟩⟩

-- enumerating legal patterns agrees with the original translated-window cardinality.
theorem card_legal_patterns {A : Type*} (c : Site → A) (S : Finset Site)
    [Fintype (patterns c S)] : Fintype.card (patterns c S) = complexity c S := by
  simp only [complexity, Set.ncard_eq_toFinset_card', Set.toFinset_card]

-- restriction fibers partition the full occurring-pattern set.
theorem sum_extensionCount {A : Type*} (c : Site → A) (hc : (Set.range c).Finite)
    (S T : Finset Site) (hTS : T ⊆ S) [Fintype (patterns c T)] :
    (∑ p : patterns c T, extensionCount c S T hTS p) = complexity c S := by
  classical
  let : Fintype (patterns c S) := (patterns_finite_of_range c hc S).fintype
  simp_rw [extensionCount_eq_card_fiber]
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  simp only [Finset.mem_univ, Finset.filter_true, Finset.card_univ, card_legal_patterns]

-- the paper's ambiguity identity counts the extra extensions beyond one per occurring base.
theorem extra_extensions_eq_pattern_loss {A : Type*} (c : Site → A)
    (hc : (Set.range c).Finite) (S T : Finset Site) (hTS : T ⊆ S) [Fintype (patterns c T)] :
    (∑ p : patterns c T, (extensionCount c S T hTS p - 1)) =
      complexity c S - complexity c T := by
  classical
  rw [Finset.sum_tsub_distrib _ (fun p _hp => by have hpos := extensionCount_pos c hc S T hTS p; omega)]
  rw [sum_extensionCount c hc S T hTS]
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, card_legal_patterns]

-- every ambiguous base spends at least one unit of the extra-extension budget.
theorem ambiguous_pattern_count_le_pattern_loss {A : Type*} (c : Site → A)
    (hc : (Set.range c).Finite) (S T : Finset Site) (hTS : T ⊆ S) [Fintype (patterns c T)] :
    (Finset.univ.filter (fun p => 2 ≤ extensionCount c S T hTS p)).card ≤
      complexity c S - complexity c T := by
  classical
  let E := Finset.univ.filter (fun p => 2 ≤ extensionCount c S T hTS p)
  calc
    E.card = ∑ _p ∈ E, 1 := by simp
    _ ≤ ∑ p ∈ E, (extensionCount c S T hTS p - 1) := by
      apply Finset.sum_le_sum
      intro p hp
      have htwo := (Finset.mem_filter.mp hp).2
      omega
    _ ≤ ∑ p : patterns c T, (extensionCount c S T hTS p - 1) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _p _hp _hnot => Nat.zero_le _)
    _ = complexity c S - complexity c T := extra_extensions_eq_pattern_loss c hc S T hTS

-- a generated polygon's edge bound controls actual ambiguous bases on that edge's complement.
theorem generating_polygon_ambiguity_budget {A : Type*} (c : Site → A)
    (hc : (Set.range c).Finite) (R S : Finset Site) (hgen : GeneratingPolygon c R S)
    (ν : Site →+ ℤ) (hν : ν ≠ 0) (m : ℤ) (hmin : ∀ u ∈ S, m ≤ ν u)
    (hface : (lowerLatticeFace S ν m).Nonempty)
    [Fintype (patterns c (S \ lowerLatticeFace S ν m))] :
    (Finset.univ.filter (fun p => 2 ≤ extensionCount c S (S \ lowerLatticeFace S ν m)
      Finset.sdiff_subset p)).card ≤ (lowerLatticeFace S ν m).card - 1 := by
  have hbudget := hgen.2.2.2.2 ν hν m hmin hface
  exact (ambiguous_pattern_count_le_pattern_loss c hc S _ Finset.sdiff_subset).trans hbudget

end KumarNivat
