module

public import KumarNivat.AnchoredCyclicBases

@[expose] public section

namespace KumarNivat

-- the finite half-plane windows use the original lattice coordinates and contain their boundary anchor.
noncomputable def anchoredHalfplaneWindow (ν : Site →+ ℤ) (cut : ℤ) (G : Site) (N : ℕ) : Finset Site :=
  (((Finset.Icc (-(N : ℤ)) N).product (Finset.Icc (-(N : ℤ)) N)).filter (fun g => cut ≤ ν g)) ∪ {G}

-- each actual window stays in the prescribed half-plane.
theorem anchored_halfplane_window_in_halfplane (ν : Site →+ ℤ) (cut : ℤ) (G : Site)
    (hG : ν G = cut) (N : ℕ) :
    ∀ g ∈ anchoredHalfplaneWindow ν cut G N, cut ≤ ν g := by
  classical
  intro g hg
  rcases Finset.mem_union.mp hg with hg | hg
  · exact (Finset.mem_filter.mp hg).2
  · have he := Finset.mem_singleton.mp hg
    rw [he, hG]

-- every original lattice site of the half-plane belongs to all sufficiently large windows.
theorem anchored_halfplane_windows_exhaust (ν : Site →+ ℤ) (cut : ℤ) (G g : Site)
    (hg : cut ≤ ν g) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → g ∈ anchoredHalfplaneWindow ν cut G n := by
  classical
  refine ⟨g.1.natAbs + g.2.natAbs, ?_⟩
  intro n hn
  apply Finset.mem_union_left
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, hg⟩
  · apply Finset.mem_Icc.mpr
    have hbound : |g.1| ≤ (n : ℤ) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast (by omega : g.1.natAbs ≤ n)
    exact abs_le.mp hbound
  · apply Finset.mem_Icc.mpr
    have hbound : |g.2| ≤ (n : ℤ) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast (by omega : g.2.natAbs ≤ n)
    exact abs_le.mp hbound

-- one step records the chosen actual base, matching translate, and inclusion-maximal polygon.
structure AnchoredMaximalPolygonStep {A : Type*} {n : ℕ} [NeZero n]
    (c w : Site → A) (e : ZMod n → Site) (Z : Set RealPlane) (cut : ℤ) (S : Finset Site) where
  base : Finset Site
  polygon : Finset Site
  shiftVector : Site
  base_convex : LatticeConvex base
  contains : S ⊆ base
  base_halfplane : ∀ g ∈ base, cut ≤ directionNormal (e 0) g
  base_envelope : AnchoredCyclicEnvelope e Z base
  agreement : AnchoredCyclicAgreement (shift shiftVector c) w base (e 0) e Z polygon
  polygon_halfplane : ∀ g ∈ polygon, cut ≤ directionNormal (e 0) g
  maximal : ∀ Q : Finset Site,
    AnchoredCyclicAgreement (shift shiftVector c) w base (e 0) e Z Q → polygon ⊆ Q → Q = polygon

-- dependent choice makes the actual maximal polygons nested before any anchor translation is applied.
theorem anchored_maximal_polygon_exhaustion {A : Type*} {n : ℕ} [NeZero n]
    (c w : Site → A) (e : ZMod n → Site) (Z : Set RealPlane) (cut : ℤ) (G : Site)
    (hG : directionNormal (e 0) G = cut)
    (hStep : ∀ S : Finset Site, (∀ g ∈ S, cut ≤ directionNormal (e 0) g) →
      Nonempty (AnchoredMaximalPolygonStep c w e Z cut S)) :
    ∃ F M : ℕ → Finset Site, ∃ u : ℕ → Site, Monotone M ∧
      (∀ N, anchoredHalfplaneWindow (directionNormal (e 0)) cut G N ⊆ F N) ∧
      (∀ N, LatticeConvex (F N) ∧ (∀ g ∈ F N, cut ≤ directionNormal (e 0) g) ∧
        AnchoredCyclicEnvelope e Z (F N) ∧
        AnchoredCyclicAgreement (shift (u N) c) w (F N) (e 0) e Z (M N) ∧
        (∀ g ∈ M N, cut ≤ directionNormal (e 0) g) ∧
        ∀ Q : Finset Site, AnchoredCyclicAgreement (shift (u N) c) w (F N) (e 0) e Z Q →
          M N ⊆ Q → Q = M N) ∧
      ∀ g : Site, cut ≤ directionNormal (e 0) g → ∃ N : ℕ, ∀ m : ℕ, N ≤ m → g ∈ M m := by
  classical
  let H := {M : Finset Site // ∀ g ∈ M, cut ≤ directionNormal (e 0) g}
  let grow (N : ℕ) (old : H) : AnchoredMaximalPolygonStep c w e Z cut
      (old.val ∪ anchoredHalfplaneWindow (directionNormal (e 0)) cut G N) :=
    Classical.choice (hStep _ (by
      intro g hg
      rcases Finset.mem_union.mp hg with hg | hg
      · exact old.property g hg
      · exact anchored_halfplane_window_in_halfplane (directionNormal (e 0)) cut G hG N g hg))
  let state : ℕ → H := Nat.rec ⟨∅, by simp⟩ (fun N old =>
    ⟨(grow N old).polygon, (grow N old).polygon_halfplane⟩)
  let F := fun N => (grow N (state N)).base
  let M := fun N => (grow N (state N)).polygon
  let u := fun N => (grow N (state N)).shiftVector
  have hFM (N : ℕ) : F N ⊆ M N := (grow N (state N)).agreement.2.2.1
  have hwindow (N : ℕ) : anchoredHalfplaneWindow (directionNormal (e 0)) cut G N ⊆ F N :=
    fun _g hg => (grow N (state N)).contains (Finset.mem_union_right _ hg)
  have hprevious (N : ℕ) : (state N).val ⊆ F N :=
    fun _g hg => (grow N (state N)).contains (Finset.mem_union_left _ hg)
  have hstate (N : ℕ) : (state (N + 1)).val = M N := rfl
  have hmono : Monotone M := by
    apply monotone_nat_of_le_succ
    intro N
    exact (hstate N ▸ hprevious (N + 1)).trans (hFM (N + 1))
  refine ⟨F, M, u, hmono, hwindow, ?_, ?_⟩
  · intro N
    exact ⟨(grow N (state N)).base_convex, (grow N (state N)).base_halfplane,
      (grow N (state N)).base_envelope, (grow N (state N)).agreement, (grow N (state N)).polygon_halfplane,
      (grow N (state N)).maximal⟩
  · intro g hg
    obtain ⟨N, hN⟩ := anchored_halfplane_windows_exhaust (directionNormal (e 0)) cut G g hg
    exact ⟨N, fun m hm => hFM m (hwindow m (hN m hm))⟩

-- the actual newton base construction discharges every step of the maximal half-plane exhaustion.
theorem actual_newton_maximal_polygon_exhaustion {K : Type*} [CommRing K] [Nontrivial K]
    [NoZeroDivisors K] [TopologicalSpace K] [DiscreteTopology K] {n : ℕ} [NeZero n]
    (c w : Site → K) (hw : w ∈ orbitClosure c)
    (hs : List Site) (hlen : 2 ≤ hs.length) (hdirs : ∀ h ∈ hs, h ≠ 0)
    (hpairs : hs.Pairwise (fun p q => determinant p q ≠ 0))
    (e : ZMod n → Site) (horder : CyclicEdgeOrder e)
    (P : OrderedCyclicLatticePolygon e (differenceProduct (K := K) hs).coeff.support)
    (hprimitive : Int.gcd (e 0).1 (e 0).2 = 1) (p : Site) (hpmem : p ∈ hs)
    (hparallel : determinant (e 0) p = 0) (cut : ℤ) (G : Site)
    (hG : directionNormal (e 0) G = cut)
    (hnoHalfStrip : ∀ F : Finset Site,
      AnchoredCyclicEnvelope e (latticeHull (differenceProduct (K := K) hs).coeff.support) F →
      LatticeConvex F → (∀ g ∈ F, cut ≤ directionNormal (e 0) g) →
      ∀ u : Site, ¬ ∀ g ∈ polygonHalfStrip F (e 0), shift u c g = w g) :
    ∃ F M : ℕ → Finset Site, ∃ u : ℕ → Site, Monotone M ∧
      (∀ N, anchoredHalfplaneWindow (directionNormal (e 0)) cut G N ⊆ F N) ∧
      (∀ N, LatticeConvex (F N) ∧ (∀ g ∈ F N, cut ≤ directionNormal (e 0) g) ∧
        AnchoredCyclicEnvelope e (latticeHull (differenceProduct (K := K) hs).coeff.support) (F N) ∧
        AnchoredCyclicAgreement (shift (u N) c) w (F N) (e 0) e
          (latticeHull (differenceProduct (K := K) hs).coeff.support) (M N) ∧
        (∀ g ∈ M N, cut ≤ directionNormal (e 0) g) ∧
        ∀ Q : Finset Site, AnchoredCyclicAgreement (shift (u N) c) w (F N) (e 0) e
          (latticeHull (differenceProduct (K := K) hs).coeff.support) Q → M N ⊆ Q → Q = M N) ∧
      ∀ g : Site, cut ≤ directionNormal (e 0) g → ∃ N : ℕ, ∀ m : ℕ, N ≤ m → g ∈ M m := by
  apply anchored_maximal_polygon_exhaustion c w e
    (latticeHull (differenceProduct (K := K) hs).coeff.support) cut G hG
  intro S hS
  obtain ⟨F, M, u, hF, hSF, hhalf, hEnvelope, hM, hhalfM, hmax⟩ :=
    exists_maximal_cyclic_polygon_containing_halfplane_data c w hw hs hlen hdirs hpairs e horder
      P hprimitive p hpmem hparallel cut S hS hnoHalfStrip
  exact ⟨⟨F, M, u, hF, hSF, hhalf, hEnvelope, hM, hhalfM, hmax⟩⟩

end KumarNivat
