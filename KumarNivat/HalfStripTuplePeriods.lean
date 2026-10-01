import KumarNivat.TuplePatternPeriods

namespace KumarNivat

-- a one-sided tuple sequence starts at the actual integer translation threshold.
def halfStripTuple {A I : Type*} (x : Site → A) (E : I → Site) (p : Site) (N : ℤ) (n : ℕ) : I → A :=
  stripTuple x E p (N + (n : ℤ))

-- the sampled half-strip retains every nonnegative primitive translate of its row sites.
def sampledHalfStrip {I : Type*} (E : I → Site) (p : Site) (N : ℤ) : Set Site :=
  Set.range (fun z : I × ℕ => E z.1 + (N + (z.2 : ℤ)) • p)

-- every nonnegative multiple of the sampled direction stays in the same half-strip.
theorem sampled_half_strip_forward_nat_step {I : Type*} (E : I → Site) (b : Site) (N : ℤ) (q : ℕ) :
    ∀ g ∈ sampledHalfStrip E b N, g + (q : ℤ) • b ∈ sampledHalfStrip E b N := by
  intro g hg
  obtain ⟨⟨u, n⟩, rfl⟩ := hg
  refine ⟨(u, n + q), ?_⟩
  change E u + (N + ((n + q : ℕ) : ℤ)) • b = E u + (N + (n : ℤ)) • b + (q : ℤ) • b
  rw [Nat.cast_add]
  simp only [add_smul, add_assoc]

-- restricting the bilateral tuple alphabet preserves finiteness.
theorem halfStripTuple_range_finite {A I : Type*} [Finite I]
    (x : Site → A) (hx : (Set.range x).Finite) (E : I → Site) (p : Site) (N : ℤ) :
    (Set.range (halfStripTuple x E p N)).Finite := by
  apply (stripTuple_range_finite x hx E p).subset
  rintro _ ⟨n, rfl⟩
  exact ⟨N + (n : ℤ), rfl⟩

-- each word on the forward sequence is read from one of its actual observed base patterns.
theorem halfStripTuple_wordCount_le_base_family {A I : Type*}
    (x : Site → A) (E : I → Site) (p : Site) (N : ℤ) (T : Finset Site) (r : ℕ)
    (hfit : ∀ i : I, ∀ j : Fin r, E i + (j.val : ℤ) • p ∈ T)
    (B : Set (T → A)) (hB : B.Finite)
    (hbase : ∀ n : ℕ, (fun u : T => x ((N + (n : ℤ)) • p + u.val)) ∈ B) :
    wordCount (halfStripTuple x E p N) r ≤ B.ncard := by
  let read : (T → A) → (Fin r → I → A) :=
    fun w j i => w ⟨E i + (j.val : ℤ) • p, hfit i j⟩
  have hsub : Set.range (sequenceWord (halfStripTuple x E p N) r) ⊆ read '' B := by
    rintro _ ⟨n, rfl⟩
    refine ⟨(fun u : T => x ((N + (n : ℤ)) • p + u.val)), hbase n, ?_⟩
    funext j i
    change x ((N + (n : ℤ)) • p + (E i + (j.val : ℤ) • p)) =
      x (E i + (N + ((n + j.val : ℕ) : ℤ)) • p)
    congr 1
    rw [Nat.cast_add]
    simp only [add_smul]
    abel
  exact (Set.ncard_le_ncard hsub (hB.image read)).trans (Set.ncard_image_le hB)

-- a periodic tuple tail gives the same regional period on every sampled forward row.
theorem regional_period_of_halfStripTuple_tail {A I : Type*}
    (x : Site → A) (E : I → Site) (p : Site) (N : ℤ) (b q : ℕ)
    (hperiod : ∀ n : ℕ, b ≤ n → halfStripTuple x E p N (n + q) = halfStripTuple x E p N n) :
    RegionalPeriod x (sampledHalfStrip E p (N + (b : ℤ))) ((q : ℤ) • p) := by
  intro g hg _hfit
  obtain ⟨⟨i, n⟩, rfl⟩ := hg
  have he := congrFun (hperiod (b + n) (by omega)) i
  simpa only [halfStripTuple, stripTuple, Nat.cast_add, add_smul, add_assoc] using he

-- the small base family bounds both the discarded initial segment and the common forward period.
theorem half_strip_period_of_small_base_family {A I : Type*} [Finite I]
    (x : Site → A) (hx : (Set.range x).Finite) (E : I → Site) (p : Site) (N : ℤ)
    (T : Finset Site) (r : ℕ) (hfit : ∀ i : I, ∀ j : Fin r, E i + (j.val : ℤ) • p ∈ T)
    (B : Set (T → A)) (hB : B.Finite) (hcount : B.ncard ≤ r)
    (hbase : ∀ n : ℕ, (fun u : T => x ((N + (n : ℤ)) • p + u.val)) ∈ B) :
    ∃ b q : ℕ, b < r ∧ 0 < q ∧ q ≤ r ∧
      RegionalPeriod x (sampledHalfStrip E p (N + (b : ℤ))) ((q : ℤ) • p) := by
  have hwords := (halfStripTuple_wordCount_le_base_family x E p N T r hfit B hB hbase).trans hcount
  obtain ⟨b, q, hb, hq, hqr, hperiod⟩ := morse_hedlund_one_sided (halfStripTuple x E p N)
    (halfStripTuple_range_finite x hx E p N) r hwords
  exact ⟨b, q, hb, hq, hqr, regional_period_of_halfStripTuple_tail x E p N b q hperiod⟩

-- eventual ambiguity of actual legal bases yields the forward half-strip period used in section 7.
theorem half_strip_period_of_ambiguous_bases {A I : Type*} [Finite I]
    (c x : Site → A) (hc : (Set.range c).Finite) (hlang : LanguageContained x c)
    (S T : Finset Site) (hTS : T ⊆ S) (E : I → Site) (p : Site) (N : ℤ) (r : ℕ)
    (hfit : ∀ i : I, ∀ j : Fin r, E i + (j.val : ℤ) • p ∈ T)
    (hbudget : complexity c S - complexity c T ≤ r)
    (hambiguous : ∀ n : ℕ, 2 ≤ extensionCount c S T hTS
      (legalTranslatedPattern c x hlang T ((N + (n : ℤ)) • p))) :
    ∃ b q : ℕ, b < r ∧ 0 < q ∧ q ≤ r ∧
      RegionalPeriod x (sampledHalfStrip E p (N + (b : ℤ))) ((q : ℤ) • p) := by
  have hbase (n : ℕ) : (fun u : T => x ((N + (n : ℤ)) • p + u.val)) ∈
      ambiguousBaseFamily c S T hTS :=
    ⟨legalTranslatedPattern c x hlang T ((N + (n : ℤ)) • p), hambiguous n, rfl⟩
  exact half_strip_period_of_small_base_family x (finite_range_of_language x c hc hlang) E p N T r hfit
    (ambiguousBaseFamily c S T hTS) (ambiguousBaseFamily_finite c hc S T hTS)
    ((ambiguousBaseFamily_count_le c hc S T hTS).trans hbudget) hbase

end KumarNivat
