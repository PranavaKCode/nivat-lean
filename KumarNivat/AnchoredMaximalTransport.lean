module

public import KumarNivat.AnchoredEnvelopeTranslation

@[expose] public section

namespace KumarNivat

-- choose one actual polygon witness, then carry that same witness through every anchor translation.
theorem anchored_maximal_cyclic_polygons_at_common_boundary {A : Type*} {n : ℕ} [NeZero n]
    (c w : Site → A) (e : ZMod n → Site) (horder : CyclicEdgeOrder e) (Z : Set RealPlane)
    (F M : ℕ → Finset Site) (u : ℕ → Site) (G : Site) (cut : ℤ)
    (hprimitive : Int.gcd (e 0).1 (e 0).2 = 1) (hcut : directionNormal (e 0) G = cut)
    (hG : ∀ N, G ∈ M N) (hhalf : ∀ N, ∀ g ∈ M N, cut ≤ directionNormal (e 0) g)
    (hM : ∀ N, AnchoredCyclicAgreement (shift (u N) c) w (F N) (e 0) e Z (M N))
    (hmax : ∀ N, ∀ T : Finset Site,
      AnchoredCyclicAgreement (shift (u N) c) w (F N) (e 0) e Z T → M N ⊆ T → T = M N) :
    ∃ P : ∀ N, OrderedCyclicLatticePolygon e (M N), ∃ k : ℕ → ℤ,
      ∃ Q : ∀ N, OrderedCyclicLatticePolygon e ((M N).image (fun g => -k N • e 0 + g)),
      (∀ N, (Q N).vertex 1 = G ∧ (∀ i, (Q N).edgeLength i = (P N).edgeLength i) ∧
        LatticeConvex ((M N).image (fun g => -k N • e 0 + g)) ∧
        (∀ i, directionNormal (e 0) ((Q N).vertex i) = directionNormal (e 0) ((P N).vertex i))) ∧
      (∀ N, AnchoredCyclicAgreement (shift (u N + k N • e 0) c) (shift (k N • e 0) w)
        ((F N).image (fun g => -k N • e 0 + g)) (e 0) e Z
          ((M N).image (fun g => -k N • e 0 + g))) ∧
      ∀ N, ∀ T : Finset Site,
        AnchoredCyclicAgreement (shift (u N + k N • e 0) c) (shift (k N • e 0) w)
          ((F N).image (fun g => -k N • e 0 + g)) (e 0) e Z T →
        (M N).image (fun g => -k N • e 0 + g) ⊆ T →
          T = (M N).image (fun g => -k N • e 0 + g) := by
  classical
  let P := fun N => Classical.choice (hM N).1.1
  have hshift (N : ℕ) : ∃ k : ℤ, (P N).vertex 1 = G + k • e 0 :=
    ordered_cyclic_tangent_anchor_shift e horder (M N) (P N) G (hG N) cut hprimitive hcut (hhalf N)
  choose k hk using hshift
  let Q := fun N => orderedCyclicPolygonTranslation e (M N) (P N) (hM N).2.1 (-k N • e 0)
  have hsource (N : ℕ) : shift (-(-k N • e 0)) (shift (u N) c) = shift (u N + k N • e 0) c := by
    funext g
    change c ((g + -(-k N • e 0)) + u N) = c (g + (u N + k N • e 0))
    rw [neg_smul, neg_neg]
    congr 1
    abel
  have hreference (N : ℕ) : shift (-(-k N • e 0)) w = shift (k N • e 0) w := by
    rw [neg_smul, neg_neg]
  refine ⟨P, k, Q, ?_, ?_, ?_⟩
  · intro N
    refine ⟨?_, ?_, latticeConvex_integer_translation (M N) (hM N).2.1 (-k N • e 0), ?_⟩
    · change -k N • e 0 + (1 : ℤ) • (P N).vertex 1 = G
      rw [one_smul, hk N, neg_smul]
      abel
    · intro i
      change 1 * (P N).edgeLength i = (P N).edgeLength i
      exact one_mul _
    · intro i
      change directionNormal (e 0) (-k N • e 0 + (1 : ℤ) • (P N).vertex i) = _
      rw [one_smul, map_add, map_zsmul, directionNormal_self, smul_zero, zero_add]
  · intro N
    have h := (hM N).translation (-k N • e 0)
    rw [hsource N, hreference N] at h
    exact h
  · intro N
    have h := anchored_cyclic_maximality_translation (shift (u N) c) w (F N) (M N)
      (e 0) e Z (hmax N) (-k N • e 0)
    rw [hsource N, hreference N] at h
    exact h

end KumarNivat
