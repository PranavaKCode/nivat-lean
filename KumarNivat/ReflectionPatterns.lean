module

public import KumarNivat.ReflectionBasics
public import KumarNivat.PatternExtensions
public import KumarNivat.TuplePatternPeriods

@[expose] public section

namespace KumarNivat

-- change only the finite window coordinates, keeping every symbol unchanged.
def reflectionPatternEquiv {A : Type*} (S : Finset Site) : (S → A) ≃ (reflectedWindow S → A) where
  toFun p u := p ((reflectionWindowEquiv S).symm u)
  invFun p u := p (reflectionWindowEquiv S u)
  left_inv p := by funext u; simp
  right_inv p := by funext u; simp

-- the transformed pattern occurs at exactly the reflected translation of its original occurrence.
theorem mem_patterns_reflection_iff {A : Type*} (c : Site → A) (S : Finset Site) (p : S → A) :
    reflectionPatternEquiv S p ∈ patterns (reflectedConfig c) (reflectedWindow S) ↔ p ∈ patterns c S := by
  constructor
  · rintro ⟨g, he⟩
    refine ⟨siteReflection g, ?_⟩
    funext u
    have h := congrFun he (reflectionWindowEquiv S u)
    change c (siteReflection (g + siteReflection u.val)) =
      p ((reflectionWindowEquiv S).symm (reflectionWindowEquiv S u)) at h
    simpa only [map_add, siteReflection_twice, Equiv.symm_apply_apply] using h
  · rintro ⟨g, rfl⟩
    refine ⟨siteReflection g, ?_⟩
    funext u
    change c (siteReflection (siteReflection g + u.val)) = c (g + siteReflection u.val)
    rw [map_add, siteReflection_twice]

-- this is a bijection of actual legal patterns, rather than of a larger ambient alphabet.
def reflectionLegalPatternEquiv {A : Type*} (c : Site → A) (S : Finset Site) :
    patterns c S ≃ patterns (reflectedConfig c) (reflectedWindow S) where
  toFun p := ⟨reflectionPatternEquiv S p.val, (mem_patterns_reflection_iff c S p.val).mpr p.property⟩
  invFun p := ⟨(reflectionPatternEquiv S).symm p.val, (mem_patterns_reflection_iff c S _).mp
    (by simpa only [Equiv.apply_symm_apply] using p.property)⟩
  left_inv p := Subtype.ext ((reflectionPatternEquiv S).left_inv p.val)
  right_inv p := Subtype.ext ((reflectionPatternEquiv S).right_inv p.val)

-- reflection preserves the exact observed count for every original finite window.
theorem complexity_reflection {A : Type*} (c : Site → A) (S : Finset Site) :
    complexity (reflectedConfig c) (reflectedWindow S) = complexity c S := by
  have hset : patterns (reflectedConfig c) (reflectedWindow S) =
      reflectionPatternEquiv S '' patterns c S := by
    ext p
    constructor
    · intro hp
      refine ⟨(reflectionPatternEquiv S).symm p, ?_, Equiv.apply_symm_apply _ p⟩
      apply (mem_patterns_reflection_iff c S _).mp
      simpa only [Equiv.apply_symm_apply] using hp
    · rintro ⟨q, hq, rfl⟩
      exact (mem_patterns_reflection_iff c S q).mpr hq
  unfold complexity
  rw [hset]
  exact Set.ncard_image_of_injective _ (reflectionPatternEquiv S).injective

-- the reflection has no effect on the original finite symbol range.
theorem reflectedConfig_range {A : Type*} (c : Site → A) : Set.range (reflectedConfig c) = Set.range c := by
  ext v
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨siteReflection g, rfl⟩
  · rintro ⟨g, rfl⟩
    exact ⟨siteReflection g, by change c (siteReflection (siteReflection g)) = c g; rw [siteReflection_twice]⟩

-- every transformed observation inherits the same original language after its window and translation are reflected.
theorem LanguageContained.reflection {A : Type*} {x c : Site → A} (hx : LanguageContained x c) :
    LanguageContained (reflectedConfig x) (reflectedConfig c) := by
  intro D g
  obtain ⟨t, ht⟩ := hx (reflectedWindow D) (siteReflection g)
  refine ⟨siteReflection t, ?_⟩
  intro u hu
  have he := ht (siteReflection u) ((mem_reflectedWindow D _).mpr (by rwa [siteReflection_twice]))
  simpa only [reflectedConfig, map_add, siteReflection_twice] using he

-- finite pattern restrictions commute with the actual legal-pattern bijections.
theorem legalPatternRestriction_reflection {A : Type*} (c : Site → A) (S T : Finset Site)
    (hTS : T ⊆ S) (hRTS : reflectedWindow T ⊆ reflectedWindow S) (p : patterns c S) :
    legalPatternRestriction (reflectedConfig c) (reflectedWindow S) (reflectedWindow T) hRTS
      (reflectionLegalPatternEquiv c S p) =
        reflectionLegalPatternEquiv c T (legalPatternRestriction c S T hTS p) := by
  apply Subtype.ext
  funext u
  rfl

-- restriction fibers have the same cardinality under the orientation change.
theorem extensionCount_reflection {A : Type*} (c : Site → A) (S T : Finset Site)
    (hTS : T ⊆ S) (hRTS : reflectedWindow T ⊆ reflectedWindow S) (p : patterns c T) :
    extensionCount (reflectedConfig c) (reflectedWindow S) (reflectedWindow T) hRTS
      (reflectionLegalPatternEquiv c T p) = extensionCount c S T hTS p := by
  have hfiber : reflectionLegalPatternEquiv c S ''
      {q : patterns c S | legalPatternRestriction c S T hTS q = p} =
      {q : patterns (reflectedConfig c) (reflectedWindow S) |
        legalPatternRestriction (reflectedConfig c) (reflectedWindow S) (reflectedWindow T) hRTS q =
          reflectionLegalPatternEquiv c T p} := by
    ext q
    constructor
    · rintro ⟨u, hu, rfl⟩
      change legalPatternRestriction c S T hTS u = p at hu
      change legalPatternRestriction (reflectedConfig c) (reflectedWindow S) (reflectedWindow T) hRTS
        (reflectionLegalPatternEquiv c S u) = reflectionLegalPatternEquiv c T p
      rw [legalPatternRestriction_reflection c S T hTS hRTS u, hu]
    · intro hq
      change legalPatternRestriction (reflectedConfig c) (reflectedWindow S) (reflectedWindow T) hRTS q =
        reflectionLegalPatternEquiv c T p at hq
      refine ⟨(reflectionLegalPatternEquiv c S).symm q, ?_, Equiv.apply_symm_apply _ q⟩
      change legalPatternRestriction c S T hTS ((reflectionLegalPatternEquiv c S).symm q) = p
      apply (reflectionLegalPatternEquiv c T).injective
      rw [← legalPatternRestriction_reflection c S T hTS hRTS ((reflectionLegalPatternEquiv c S).symm q),
        Equiv.apply_symm_apply]
      exact hq
  unfold extensionCount
  rw [← hfiber]
  exact Set.ncard_image_of_injective _ (reflectionLegalPatternEquiv c S).injective

-- transformed translated patterns use the same values at the same original sites.
theorem legalTranslatedPattern_reflection {A : Type*} (c x : Site → A) (hx : LanguageContained x c)
    (S : Finset Site) (g : Site) :
    reflectionLegalPatternEquiv c S (legalTranslatedPattern c x hx S g) =
      legalTranslatedPattern (reflectedConfig c) (reflectedConfig x) hx.reflection
        (reflectedWindow S) (siteReflection g) := by
  apply Subtype.ext
  funext u
  change x (g + siteReflection u.val) = x (siteReflection (siteReflection g + u.val))
  rw [map_add, siteReflection_twice]

-- equal observed base windows have equal extension counts, including their dependent membership proofs.
theorem observed_extension_count_base_congr {A : Type*} (c x : Site → A) (hx : LanguageContained x c)
    (S T U : Finset Site) (hT : T ⊆ S) (hU : U ⊆ S) (he : T = U) (g : Site) :
    extensionCount c S T hT (legalTranslatedPattern c x hx T g) =
      extensionCount c S U hU (legalTranslatedPattern c x hx U g) := by
  subst U
  rfl

end KumarNivat
