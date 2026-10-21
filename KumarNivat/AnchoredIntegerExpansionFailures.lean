module

public import KumarNivat.AnchoredIntegerExpansionHalfStrips
public import KumarNivat.AnchoredIntegerExpansionLayers
public import KumarNivat.AnchoredExpansionFailures

@[expose] public section

namespace KumarNivat

-- the constructed strict integer envelope forces an actual disagreement by the source's maximality.
theorem anchored_maximal_sequence_integer_facet_expansion_failure {K A : Type*}
    [CommRing K] [Nontrivial K] [NoZeroDivisors K] {q : ℕ} [NeZero q]
    (hs : List Site) (hdirs : ∀ h ∈ hs, h ≠ 0)
    (hpairs : hs.Pairwise (fun p r => determinant p r ≠ 0))
    (e : ZMod (2 * q) → Site) (hfan : AnchoredChainFanOrder e) (c w : Site → A) (G : Site)
    (seq : AnchoredCyclicMaximalSequence c w e (latticeHull (differenceProduct (K := K) hs).coeff.support) G)
    (Q : OrderedCyclicLatticePolygon e (differenceProduct (K := K) hs).coeff.support)
    (hprimitive : Int.gcd (e 0).1 (e 0).2 = 1) (p : Site) (hpmem : p ∈ hs)
    (hparallel : determinant (e 0) p = 0) (b : ℕ) (hb₀ : 0 < b) (hbq : b < q) (N : ℕ)
    (hbuffer : Q.edgeLength (b : ZMod (2 * q)) +
      |determinant (e ((b : ZMod (2 * q)) - 1)) (e ((b : ZMod (2 * q)) + 1))| + 1 ≤
        (seq.cyclic N).edgeLength (b : ZMod (2 * q))) :
    ∃ W : Finset Site, LatticeConvex W ∧
      AnchoredCyclicEnvelope e (latticeHull (differenceProduct (K := K) hs).coeff.support) W ∧
      latticeHull W = cyclicFacetRelaxedRegion e (seq.polygon N) (seq.cyclic N) (b : ZMod (2 * q))
        (cyclicFacetRelaxationScale e (b : ZMod (2 * q))) ∧
      seq.polygon N ⊆ W ∧ seq.polygon N ≠ W ∧
      ∃ g ∈ W, shift (seq.sourceShift N) c g ≠ w g := by
  have hlen := anchored_cyclic_envelope_edge_lengths e hfan.order
    (differenceProduct (K := K) hs).coeff.support (seq.polygon N) Q (seq.cyclic N) (seq.agreement N).1
  obtain ⟨W, hW, R, hv, _hr, hHullW, hdom, hPW⟩ := exists_actual_integer_facet_expansion e hfan.order
    (differenceProduct (K := K) hs).coeff.support (seq.polygon N) Q (seq.cyclic N) hlen
    (b : ZMod (2 * q)) hbuffer
  obtain ⟨C, _hCformula, hCconvex, hCcompact, hCnonempty, hsum⟩ :=
    ordered_cyclic_edge_envelope_minkowski e hfan.order (differenceProduct (K := K) hs).coeff.support W Q R hdom
  have hEnvelopeW : AnchoredCyclicEnvelope e (latticeHull (differenceProduct (K := K) hs).coeff.support) W :=
    ⟨⟨R⟩, C, hCconvex, hCcompact, hCnonempty, hsum⟩
  have hstrict := integer_facet_expansion_strict e hfan.order (seq.polygon N) W (seq.cyclic N) R
    (b : ZMod (2 * q)) hv
  have hstripW := anchored_integer_facet_expansion_lattice_halfstrip (K := K)
    hs hdirs hpairs e hfan hprimitive p hpmem hparallel (seq.base N) (seq.polygon N) W
    (seq.base_convex N) (seq.base_envelope N) (seq.cyclic N) (seq.agreement N).2.2.1
    (seq.agreement N).2.2.2.1 b hb₀ hbq hHullW
  exact ⟨W, hW, hEnvelopeW, hHullW, hPW, hstrict,
    seq.failure_on_strict_expansion N W hEnvelopeW hW hPW hstrict hstripW⟩

end KumarNivat
