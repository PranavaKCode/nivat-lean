module

public import KumarNivat.WordComplexity
public import KumarNivat.PatternExtensions
public import KumarNivat.OrbitLanguage
public import KumarNivat.RetainedDisagreement

@[expose] public section

namespace KumarNivat

-- one letter of the strip sequence records the chosen initial site on each row.
def stripTuple {A I : Type*} (x : Site → A) (E : I → Site) (p : Site) (n : ℤ) : I → A :=
  fun i => x (E i + n • p)

-- the sampled strip contains the whole lattice line through every chosen row site.
def sampledStrip {I : Type*} (E : I → Site) (p : Site) : Set Site :=
  Set.range (fun z : I × ℤ => E z.1 + z.2 • p)

-- finitely many rows over finite image give a finite tuple alphabet.
theorem stripTuple_range_finite {A I : Type*} [Finite I]
    (x : Site → A) (hx : (Set.range x).Finite) (E : I → Site) (p : Site) :
    (Set.range (stripTuple x E p)).Finite := by
  apply (Set.Finite.pi' (fun _i : I => hx)).subset
  rintro _ ⟨n, rfl⟩ i
  exact ⟨E i + n • p, rfl⟩

-- a tuple-sequence period preserves the configuration on every sampled row.
theorem regional_period_of_stripTuple_period {A I : Type*}
    (x : Site → A) (E : I → Site) (p : Site) (q : ℕ)
    (hperiod : Function.Periodic (stripTuple x E p) (q : ℤ)) :
    RegionalPeriod x (sampledStrip E p) ((q : ℤ) • p) := by
  intro g hg _hfit
  obtain ⟨⟨i, n⟩, rfl⟩ := hg
  have he := congrFun (hperiod n) i
  simpa only [stripTuple, add_smul, add_assoc] using he

-- each tuple word is a restriction of its observed translated base pattern.
theorem stripTuple_wordCount_le_base_family {A I : Type*}
    (x : Site → A) (E : I → Site) (p : Site) (T : Finset Site) (r : ℕ)
    (hfit : ∀ i : I, ∀ j : Fin r, E i + (j.val : ℤ) • p ∈ T)
    (B : Set (T → A)) (hB : B.Finite)
    (hbase : ∀ n : ℤ, (fun u : T => x (n • p + u.val)) ∈ B) :
    wordCount (stripTuple x E p) r ≤ B.ncard := by
  let read : (T → A) → (Fin r → I → A) :=
    fun w j i => w ⟨E i + (j.val : ℤ) • p, hfit i j⟩
  have hsub : Set.range (sequenceWord (stripTuple x E p) r) ⊆ read '' B := by
    rintro _ ⟨n, rfl⟩
    refine ⟨(fun u : T => x (n • p + u.val)), hbase n, ?_⟩
    funext j i
    change x (n • p + (E i + (j.val : ℤ) • p)) = x (E i + (n + (j.val : ℤ)) • p)
    congr 1
    rw [add_smul]
    abel
  exact (Set.ncard_le_ncard hsub (hB.image read)).trans (Set.ncard_image_le hB)

-- the actual base-family count yields the sharp common period on all sampled rows.
theorem strip_period_of_small_base_family {A I : Type*} [Finite I]
    (x : Site → A) (hx : (Set.range x).Finite) (E : I → Site) (p : Site)
    (T : Finset Site) (r : ℕ) (hfit : ∀ i : I, ∀ j : Fin r, E i + (j.val : ℤ) • p ∈ T)
    (B : Set (T → A)) (hB : B.Finite) (hcount : B.ncard ≤ r)
    (hbase : ∀ n : ℤ, (fun u : T => x (n • p + u.val)) ∈ B) :
    ∃ q : ℕ, 0 < q ∧ q ≤ r ∧ RegionalPeriod x (sampledStrip E p) ((q : ℤ) • p) := by
  have hwords := (stripTuple_wordCount_le_base_family x E p T r hfit B hB hbase).trans hcount
  obtain ⟨q, hq, hqr, hperiod⟩ := morse_hedlund_bilateral (stripTuple x E p)
    (stripTuple_range_finite x hx E p) r hwords
  exact ⟨q, hq, hqr, regional_period_of_stripTuple_period x E p q hperiod⟩

-- inherited language makes the observed base an actual legal pattern of the original array.
def legalTranslatedPattern {A : Type*} (c x : Site → A) (hlang : LanguageContained x c)
    (T : Finset Site) (g : Site) : patterns c T :=
  ⟨fun u => x (g + u.val), patterns_subset_of_language x c hlang T ⟨g, rfl⟩⟩

-- this family contains precisely the underlying functions of actual ambiguous legal bases.
def ambiguousBaseFamily {A : Type*} (c : Site → A) (S T : Finset Site) (hTS : T ⊆ S) : Set (T → A) :=
  Subtype.val '' {w : patterns c T | 2 ≤ extensionCount c S T hTS w}

-- finitary language bounds the ambiguous family without enumerating the ambient alphabet.
theorem ambiguousBaseFamily_finite {A : Type*} (c : Site → A) (hc : (Set.range c).Finite)
    (S T : Finset Site) (hTS : T ⊆ S) : (ambiguousBaseFamily c S T hTS).Finite := by
  let : Fintype (patterns c T) := (patterns_finite_of_range c hc T).fintype
  exact (Set.toFinite _).image Subtype.val

-- forgetting the subtype proof preserves the exact ambiguity count and its extension budget.
theorem ambiguousBaseFamily_count_le {A : Type*} (c : Site → A) (hc : (Set.range c).Finite)
    (S T : Finset Site) (hTS : T ⊆ S) :
    (ambiguousBaseFamily c S T hTS).ncard ≤ complexity c S - complexity c T := by
  classical
  let : Fintype (patterns c T) := (patterns_finite_of_range c hc T).fintype
  let B : Finset (patterns c T) := Finset.univ.filter (fun w => 2 ≤ extensionCount c S T hTS w)
  have hset : {w : patterns c T | 2 ≤ extensionCount c S T hTS w} = (B : Set (patterns c T)) := by
    ext w
    simp only [B, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
  rw [ambiguousBaseFamily, Set.ncard_image_of_injective _ Subtype.val_injective, hset,
    Set.ncard_coe_finset]
  exact ambiguous_pattern_count_le_pattern_loss c hc S T hTS

-- ambiguous observed bases spend the verified extension budget and force the paper's strip period.
theorem strip_period_of_ambiguous_bases {A I : Type*} [Finite I]
    (c x : Site → A) (hc : (Set.range c).Finite) (hlang : LanguageContained x c)
    (S T : Finset Site) (hTS : T ⊆ S) (E : I → Site) (p : Site) (r : ℕ)
    (hfit : ∀ i : I, ∀ j : Fin r, E i + (j.val : ℤ) • p ∈ T)
    (hbudget : complexity c S - complexity c T ≤ r)
    (hambiguous : ∀ n : ℤ, 2 ≤ extensionCount c S T hTS
      (legalTranslatedPattern c x hlang T (n • p))) :
    ∃ q : ℕ, 0 < q ∧ q ≤ r ∧ RegionalPeriod x (sampledStrip E p) ((q : ℤ) • p) := by
  have hbase (n : ℤ) : (fun u : T => x (n • p + u.val)) ∈ ambiguousBaseFamily c S T hTS :=
    ⟨legalTranslatedPattern c x hlang T (n • p), hambiguous n, rfl⟩
  exact strip_period_of_small_base_family x (finite_range_of_language x c hc hlang) E p T r hfit
    (ambiguousBaseFamily c S T hTS) (ambiguousBaseFamily_finite c hc S T hTS)
    ((ambiguousBaseFamily_count_le c hc S T hTS).trans hbudget) hbase

end KumarNivat
