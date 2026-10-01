import KumarNivat.BoundaryEdgeAgreement

namespace KumarNivat

-- the two generated endpoints propagate a consecutive edge seed in both directions.
theorem generated_edge_agreement_of_block {A : Type*} (c x y : Site → A)
    (hx : LanguageContained x c) (hy : LanguageContained y c)
    (S F : Finset Site) (q₀ p E : Site) (t : ℕ)
    (hfirst : q₀ ∈ S) (hlast : q₀ + (t : ℤ) • p ∈ S)
    (hgenfirst : GeneratedSite c S q₀) (hgenlast : GeneratedSite c S (q₀ + (t : ℤ) • p))
    (hface : ∀ u ∈ F, ∃ i : Fin (t + 1), u = q₀ + (i.val : ℤ) • p)
    (n₀ : ℤ)
    (hinterior : ∀ n : ℤ, ∀ u ∈ S \ F, x (E + n • p + u) = y (E + n • p + u))
    (hseed : ∀ i : Fin t, x (E + q₀ + (n₀ + (i.val : ℤ)) • p) =
      y (E + q₀ + (n₀ + (i.val : ℤ)) • p)) :
    ∀ n : ℤ, x (E + q₀ + n • p) = y (E + q₀ + n • p) := by
  have hforward := generated_endpoint_agreement_tail c x y hx hy S F q₀ p E t
    hlast hgenlast hface n₀ (fun n _ => hinterior n) hseed
  let q₁ := q₀ + (t : ℤ) • p
  have hreverse_site (n : ℤ) : E + q₁ + n • (-p) = E + q₀ + ((t : ℤ) - n) • p := by
    dsimp [q₁]
    simp only [smul_neg, sub_smul]
    abel
  have hreverse_endpoint : q₁ + (t : ℤ) • (-p) = q₀ := by
    dsimp [q₁]
    simp only [smul_neg]
    abel
  have hreverse_face : ∀ u ∈ F, ∃ i : Fin (t + 1), u = q₁ + (i.val : ℤ) • (-p) := by
    intro u hu
    obtain ⟨i, hi⟩ := hface u hu
    let j : Fin (t + 1) := ⟨t - i.val, by omega⟩
    have hj : (j.val : ℤ) = (t : ℤ) - (i.val : ℤ) := by dsimp [j]; omega
    refine ⟨j, ?_⟩
    rw [hi, hj]
    dsimp [q₁]
    simp only [smul_neg, sub_smul]
    abel
  have hreverse_seed (i : Fin t) : x (E + q₁ + (1 - n₀ + (i.val : ℤ)) • (-p)) =
      y (E + q₁ + (1 - n₀ + (i.val : ℤ)) • (-p)) := by
    let j : Fin t := ⟨t - 1 - i.val, by omega⟩
    have hj : (t : ℤ) - (1 - n₀ + (i.val : ℤ)) = n₀ + (j.val : ℤ) := by
      dsimp [j]
      omega
    simpa only [hreverse_site, hj] using hseed j
  have hreverse_interior (n : ℤ) (_hn : 1 - n₀ ≤ n) :
      ∀ u ∈ S \ F, x (E + n • (-p) + u) = y (E + n • (-p) + u) := by
    simpa only [smul_neg, neg_smul] using hinterior (-n)
  have hbackward := generated_endpoint_agreement_tail c x y hx hy S F q₁ (-p) E t
    (by simpa only [hreverse_endpoint] using hfirst)
    (by simpa only [hreverse_endpoint] using hgenfirst)
    hreverse_face (1 - n₀) hreverse_interior hreverse_seed
  intro n
  by_cases hn : n₀ ≤ n
  · exact hforward n hn
  · have hn' : 1 - n₀ ≤ (t : ℤ) - n := by omega
    have he := hbackward ((t : ℤ) - n) hn'
    simpa only [hreverse_site, sub_sub_cancel] using he

end KumarNivat
