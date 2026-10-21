module

public import KumarNivat.LocalRowSelection
public import KumarNivat.HalfStripTuplePeriods
public import KumarNivat.ShiftedConfigurations

@[expose] public section

namespace KumarNivat

-- the actual local row runs and observed ambiguity give one transverse period on a half-strip inside the working region.
theorem local_parallelogram_half_strip_period {A : Type*} (c x : Site → A)
    (hc : (Set.range c).Finite) (hx : LanguageContained x c)
    (R S : Finset Site) (hgen : GeneratingPolygon c R S) (q₀ a b : Site) (r t : ℕ) (ht : 0 < t)
    (hsub : latticeParallelogram q₀ a b r t ⊆ latticeHull S)
    (μ : Site →+ ℤ) (hμ : μ ≠ 0) (m : ℤ) (hmin : ∀ u ∈ S, m ≤ μ u) (hb : μ b = 0)
    (hcard : (lowerLatticeFace S μ m).card = t + 1) (E₀ : Site) (N : ℤ)
    (hamb : ∀ n : ℤ, N ≤ n → 2 ≤ extensionCount c S (S \ lowerLatticeFace S μ m) Finset.sdiff_subset
      (legalTranslatedPattern c x hx (S \ lowerLatticeFace S μ m) (E₀ + n • b)))
    (P : Set RealPlane)
    (hplace : ∀ n : ℤ, N ≤ n → ∀ u ∈ S \ lowerLatticeFace S μ m,
      latticeEmbedding (E₀ + n • b + u) ∈ P) :
    ∃ E : localParallelogramSites S q₀ a b r t μ m → Site,
      (∀ u, E u ∈ S \ lowerLatticeFace S μ m) ∧
      (∀ u, ∃ d : ℤ, u.val = E u + d • b) ∧
      ∃ k q : ℕ, k < t ∧ 0 < q ∧ q ≤ t ∧
        RegionalPeriod x {g | g - E₀ ∈ sampledHalfStrip E b (N + (k : ℤ))} ((q : ℤ) • b) ∧
        ∀ g : Site, g - E₀ ∈ sampledHalfStrip E b (N + (k : ℤ)) → latticeEmbedding g ∈ P := by
  classical
  obtain ⟨E, hmem, hcover, hfit⟩ := exists_local_parallelogram_row_selector S hgen.2.1 q₀ a b r t ht hsub μ m hb
  have hxE := hx.shift E₀
  have hambE (n : ℕ) : 2 ≤ extensionCount c S (S \ lowerLatticeFace S μ m) Finset.sdiff_subset
      (legalTranslatedPattern c (shift E₀ x) hxE (S \ lowerLatticeFace S μ m) ((N + (n : ℤ)) • b)) := by
    have he : legalTranslatedPattern c (shift E₀ x) hxE (S \ lowerLatticeFace S μ m) ((N + (n : ℤ)) • b) =
        legalTranslatedPattern c x hx (S \ lowerLatticeFace S μ m) (E₀ + (N + (n : ℤ)) • b) := by
      apply Subtype.ext
      funext u
      simp only [legalTranslatedPattern, shift, add_comm, add_left_comm]
    rw [he]
    exact hamb (N + (n : ℤ)) (by omega)
  have hbudget : complexity c S - complexity c (S \ lowerLatticeFace S μ m) ≤ t := by
    have hface : (lowerLatticeFace S μ m).Nonempty := Finset.card_pos.mp (by omega)
    have hh := hgen.2.2.2.2 μ hμ m hmin hface
    rw [hcard] at hh
    omega
  obtain ⟨k, q, hk, hq, hqt, hperiod⟩ := half_strip_period_of_ambiguous_bases c (shift E₀ x) hc hxE
    S (S \ lowerLatticeFace S μ m) Finset.sdiff_subset E b N t hfit hbudget hambE
  refine ⟨E, hmem, hcover, k, q, hk, hq, hqt,
    regional_period_of_shifted_region x (sampledHalfStrip E b (N + (k : ℤ))) E₀ ((q : ℤ) • b) hperiod, ?_⟩
  intro g hg
  obtain ⟨⟨u, n⟩, he⟩ := hg
  change E u + (N + (k : ℤ) + (n : ℤ)) • b = g - E₀ at he
  have hsite : g = E₀ + (N + (k : ℤ) + (n : ℤ)) • b + E u := by
    rw [← sub_add_cancel g E₀, ← he]
    abel
  rw [hsite]
  exact hplace _ (by omega) (E u) (hmem u)

end KumarNivat
