import KumarNivat.AnchoredCyclicSeedFailures
import KumarNivat.AnchoredIntegerExpansionFailures
import KumarNivat.BoundaryLineRecurrences
import KumarNivat.ShiftedConfigurations

namespace KumarNivat

-- actual maximality failures and shared annihilation give one fixed finite disagreement set for the anchored sequence.
theorem anchored_maximal_sequence_has_fixed_facet_failures {K : Type*}
    [CommRing K] [Nontrivial K] [NoZeroDivisors K] {q : ℕ} [NeZero q]
    (hs : List Site) (hdirs : ∀ p ∈ hs, p ≠ 0)
    (hpairs : hs.Pairwise (fun p r => determinant p r ≠ 0))
    (e : ZMod (2 * q) → Site) (hfan : AnchoredChainFanOrder e) (c w : Site → K) (G : Site)
    (seq : AnchoredCyclicMaximalSequence c w e (latticeHull (differenceProduct (K := K) hs).coeff.support) G)
    (Q : OrderedCyclicLatticePolygon e (differenceProduct (K := K) hs).coeff.support)
    (hprimitive₀ : Int.gcd (e 0).1 (e 0).2 = 1) (p : Site) (hpmem : p ∈ hs)
    (hparallel : determinant (e 0) p = 0) (b : ℕ) (hb₀ : 0 < b) (hbq : b < q)
    (hprimitive : Int.gcd (e (b : ZMod (2 * q))).1 (e (b : ZMod (2 * q))).2 = 1)
    (B : Site) (hfixed : ∀ N, (seq.cyclic N).vertex (b : ZMod (2 * q)) = B)
    (hbuffer : ∀ N, Q.edgeLength (b : ZMod (2 * q)) +
      |determinant (e ((b : ZMod (2 * q)) - 1)) (e ((b : ZMod (2 * q)) + 1))| + 1 ≤
        (seq.cyclic N).edgeLength (b : ZMod (2 * q)))
    (hcann : laurentAct (differenceProduct hs) c = 0)
    (hwann : laurentAct (differenceProduct hs) w = 0) :
    ∃ E : Finset Site,
      (∀ N, ∃ g ∈ E, shift (seq.sourceShift N) c g ≠ w g) ∧
      (∀ g ∈ E, ∃ j : ℕ, 1 ≤ j ∧ j ≤ (cyclicFacetRelaxationScale e (b : ZMod (2 * q))).toNat ∧
        directionNormal (e (b : ZMod (2 * q))) g = directionNormal (e (b : ZMod (2 * q))) B - (j : ℤ)) ∧
      ∀ N, ∀ g ∈ E, ∃ j : ℕ, 1 ≤ j ∧
        j ≤ (cyclicFacetRelaxationScale e (b : ZMod (2 * q))).toNat ∧
        latticeEmbedding g ∈ normalFace
          (cyclicFacetRelaxedRegion e (seq.polygon N) (seq.cyclic N) (b : ZMod (2 * q)) (j : ℤ))
          (latticeNormal (directionNormal (e (b : ZMod (2 * q)))))
          ((directionNormal (e (b : ZMod (2 * q))) B - (j : ℤ) : ℤ) : ℝ) := by
  let δ := fun N => shift (seq.sourceShift N) c - w
  have hann : ∀ N, laurentAct (differenceProduct hs) (δ N) = 0 := by
    intro N
    dsimp [δ]
    rw [laurentAct_config_sub, laurentAct_shift, hcann, hwann]
    have hzero : shift (seq.sourceShift N) (0 : Site → K) = 0 := by funext g; rfl
    rw [hzero, sub_self]
  have hlen : ∀ N k, Q.edgeLength k ≤ (seq.cyclic N).edgeLength k := by
    intro N
    exact anchored_cyclic_envelope_edge_lengths e hfan.order (differenceProduct (K := K) hs).coeff.support
      (seq.polygon N) Q (seq.cyclic N) (seq.agreement N).1
  have hzero : ∀ N g, latticeEmbedding g ∈ latticeHull (seq.polygon N) → δ N g = 0 := by
    intro N g hg
    change shift (seq.sourceShift N) c g - w g = 0
    exact sub_eq_zero.mpr ((seq.agreement N).2.2.2.2 g (seq.convex N g hg))
  have hfailure : ∀ N, ∃ g : Site, latticeEmbedding g ∈
      cyclicFacetRelaxedRegion e (seq.polygon N) (seq.cyclic N) (b : ZMod (2 * q))
        (cyclicFacetRelaxationScale e (b : ZMod (2 * q))) ∧ δ N g ≠ 0 := by
    intro N
    obtain ⟨W, _hW, _hEnvelope, hHull, _hPW, _hstrict, g, hg, hneq⟩ :=
      anchored_maximal_sequence_integer_facet_expansion_failure hs hdirs hpairs e hfan c w G seq Q
        hprimitive₀ p hpmem hparallel b hb₀ hbq N (hbuffer N)
    refine ⟨g, ?_, ?_⟩
    · rw [← hHull]
      exact subset_convexHull ℝ _ ⟨g, hg, rfl⟩
    · change shift (seq.sourceShift N) c g - w g ≠ 0
      exact sub_ne_zero.mpr hneq
  obtain ⟨E, hEfail, hElevels, hEplaced⟩ := actual_cyclic_relaxation_failures_fixed_seeds
    (differenceProduct hs) e hfan.order Q (b : ZMod (2 * q)) hprimitive
    seq.polygon seq.cyclic B hfixed hlen hbuffer δ hann hzero hfailure
  refine ⟨E, ?_, hElevels, hEplaced⟩
  intro N
  obtain ⟨g, hg, hneq⟩ := hEfail N
  refine ⟨g, hg, ?_⟩
  change shift (seq.sourceShift N) c g - w g ≠ 0 at hneq
  exact sub_ne_zero.mp hneq

end KumarNivat
