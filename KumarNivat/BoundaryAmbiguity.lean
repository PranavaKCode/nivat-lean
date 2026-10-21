module

public import KumarNivat.BoundaryEdgeAgreement

@[expose] public section

namespace KumarNivat

-- a failed agreement tail rules out a singleton generated supporting face.
theorem positive_edge_degree_of_no_agreement_tail {A : Type*} (c x y : Site → A)
    (hx : LanguageContained x c) (hy : LanguageContained y c)
    (S F : Finset Site) (q₀ p E : Site) (t : ℕ)
    (hendpoint : q₀ + (t : ℤ) • p ∈ S)
    (hgen : GeneratedSite c S (q₀ + (t : ℤ) • p))
    (hface : ∀ u ∈ F, ∃ i : Fin (t + 1), u = q₀ + (i.val : ℤ) • p)
    (N : ℤ)
    (hinterior : ∀ n : ℤ, N ≤ n → ∀ u ∈ S \ F, x (E + n • p + u) = y (E + n • p + u))
    (hnotail : ¬ ∃ b : ℤ, N ≤ b ∧ ∀ n : ℤ, b ≤ n →
      x (E + q₀ + n • p) = y (E + q₀ + n • p)) : 0 < t := by
  by_contra ht
  have ht' : t = 0 := by omega
  subst t
  apply hnotail
  refine ⟨N, le_rfl, ?_⟩
  exact generated_endpoint_agreement_tail c x y hx hy S F q₀ p E 0 hendpoint hgen hface N hinterior
    (fun i => Fin.elim0 i)

-- any uniquely extending base would seed a generated equality tail, contradicting failed continuation.
theorem all_forward_bases_ambiguous_of_no_agreement_tail {A : Type*} (c x y : Site → A)
    (hc : (Set.range c).Finite) (hx : LanguageContained x c) (hy : LanguageContained y c)
    (S F : Finset Site) (q₀ p E : Site) (t : ℕ)
    (hendpoint : q₀ + (t : ℤ) • p ∈ S)
    (hgen : GeneratedSite c S (q₀ + (t : ℤ) • p))
    (hface : ∀ u ∈ F, ∃ i : Fin (t + 1), u = q₀ + (i.val : ℤ) • p)
    (hblock : ∀ i : Fin t, q₀ + (i.val : ℤ) • p ∈ S)
    (N : ℤ)
    (hinterior : ∀ n : ℤ, N ≤ n → ∀ u ∈ S \ F, x (E + n • p + u) = y (E + n • p + u))
    (hnotail : ¬ ∃ b : ℤ, N ≤ b ∧ ∀ n : ℤ, b ≤ n →
      x (E + q₀ + n • p) = y (E + q₀ + n • p)) :
    ∀ n : ℤ, N ≤ n → 2 ≤ extensionCount c S (S \ F) Finset.sdiff_subset
      (legalTranslatedPattern c x hx (S \ F) (E + n • p)) := by
  intro n hn
  by_contra htwo
  have hpos := extensionCount_pos c hc S (S \ F) Finset.sdiff_subset
    (legalTranslatedPattern c x hx (S \ F) (E + n • p))
  have hone : extensionCount c S (S \ F) Finset.sdiff_subset
      (legalTranslatedPattern c x hx (S \ F) (E + n • p)) = 1 := by omega
  have hfull := agreement_of_unique_observed_extension c x y hx hy S (S \ F) Finset.sdiff_subset
    (E + n • p) (hinterior n hn) hone
  have hseed (i : Fin t) : x (E + q₀ + (n + (i.val : ℤ)) • p) =
      y (E + q₀ + (n + (i.val : ℤ)) • p) := by
    have he := hfull (q₀ + (i.val : ℤ) • p) (hblock i)
    have hsite : E + n • p + (q₀ + (i.val : ℤ) • p) = E + q₀ + (n + (i.val : ℤ)) • p := by
      rw [add_smul n (i.val : ℤ) p]
      abel
    simpa only [hsite] using he
  apply hnotail
  refine ⟨n, hn, ?_⟩
  exact generated_endpoint_agreement_tail c x y hx hy S F q₀ p E t hendpoint hgen hface n
    (fun j hj => hinterior j (hn.trans hj)) hseed

end KumarNivat
