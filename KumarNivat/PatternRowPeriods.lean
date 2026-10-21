module

public import KumarNivat.PolygonStripPeriods
public import KumarNivat.PeriodicBlocks

@[expose] public section

namespace KumarNivat

-- a strip period also repeats every actual legal base placed along its tangent.
theorem legal_pattern_sequence_period_of_strip_period {A : Type*} (c x : Site → A)
    (hx : LanguageContained x c) (T : Finset Site) (p : Site) (q : ℕ)
    (hperiod : RegionalPeriod x (bilateralTranslateStrip T p) ((q : ℤ) • p)) :
    Function.Periodic (fun n : ℤ => legalTranslatedPattern c x hx T (n • p)) (q : ℤ) := by
  intro n
  apply Subtype.ext
  funext u
  have hg : n • p + u.val ∈ bilateralTranslateStrip T p :=
    ⟨(u, n), by simp only [add_comm]⟩
  have hfit : n • p + u.val + (q : ℤ) • p ∈ bilateralTranslateStrip T p := by
    refine ⟨(u, n + (q : ℤ)), ?_⟩
    change u.val + (n + (q : ℤ)) • p = n • p + u.val + (q : ℤ) • p
    rw [add_smul]
    abel
  have he := hperiod _ hg hfit
  simpa only [legalTranslatedPattern, add_smul, add_comm, add_left_comm, add_assoc] using he

-- the observed bases have at most as many members as the positive strip period.
theorem exists_observed_bases_le_strip_period {A : Type*} (c x : Site → A)
    (hx : LanguageContained x c) (T : Finset Site) (p : Site) (q : ℕ) (hq : 0 < q)
    (hperiod : RegionalPeriod x (bilateralTranslateStrip T p) ((q : ℤ) • p)) :
    ∃ B : Finset (patterns c T), B.card ≤ q ∧
      ∀ n : ℤ, legalTranslatedPattern c x hx T (n • p) ∈ B := by
  classical
  let a : ℤ → patterns c T := fun n => legalTranslatedPattern c x hx T (n • p)
  obtain ⟨hfinite, hcount⟩ := periodic_integer_word_range_finite_card_le a q hq
    (legal_pattern_sequence_period_of_strip_period c x hx T p q hperiod)
  refine ⟨hfinite.toFinset, ?_, ?_⟩
  · simpa only [Set.ncard_eq_toFinset_card _ hfinite] using hcount
  · intro n
    exact hfinite.mem_toFinset.mpr ⟨n, rfl⟩

-- a full-window repeat gives an entire strip period once each old row already has a short period.
theorem sampled_strip_period_of_full_pattern_repeat {A I : Type*} (x : Site → A)
    (S : Finset Site) (E : I → Site) (p : Site) (r s q : ℕ)
    (hs : 0 < s) (hsr : s ≤ r)
    (hperiod : RegionalPeriod x (sampledStrip E p) ((s : ℤ) • p))
    (hfit : ∀ i : I, ∀ j : Fin r, E i + (j.val : ℤ) • p ∈ S)
    (b : ℤ)
    (hrepeat : ∀ u ∈ S, x ((b • p + u) + (q : ℤ) • p) = x (b • p + u)) :
    RegionalPeriod x (sampledStrip E p) ((q : ℤ) • p) := by
  have htuple : Function.Periodic (stripTuple x E p) (s : ℤ) := by
    intro n
    funext i
    have hg : E i + n • p ∈ sampledStrip E p := ⟨(i, n), rfl⟩
    have hfit' : E i + n • p + (s : ℤ) • p ∈ sampledStrip E p := by
      refine ⟨(i, n + (s : ℤ)), ?_⟩
      change E i + (n + (s : ℤ)) • p = E i + n • p + (s : ℤ) • p
      rw [add_smul, add_assoc]
    simpa only [stripTuple, add_smul, add_assoc] using hperiod _ hg hfit'
  have hblock (j : Fin r) : stripTuple x E p (b + (j.val : ℤ) + (q : ℤ)) =
      stripTuple x E p (b + (j.val : ℤ)) := by
    funext i
    have he := hrepeat (E i + (j.val : ℤ) • p) (hfit i j)
    simpa only [stripTuple, add_smul, add_comm, add_left_comm, add_assoc] using he
  exact regional_period_of_stripTuple_period x E p q
    (period_of_equal_block_in_short_periodic_word (stripTuple x E p) s r hs hsr htuple b (q : ℤ) hblock)

end KumarNivat
