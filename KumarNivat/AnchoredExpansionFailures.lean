module

public import KumarNivat.AnchoredActualSequences

@[expose] public section

namespace KumarNivat

-- a genuine strict envelope expansion inside the same allowed half-strip must contain an actual disagreement.
theorem AnchoredCyclicMaximalSequence.failure_on_strict_expansion {A : Type*}
    {q : ℕ} [NeZero (2 * q)] {c w : Site → A} {e : ZMod (2 * q) → Site}
    {Z : Set RealPlane} {G : Site} (seq : AnchoredCyclicMaximalSequence c w e Z G)
    (N : ℕ) (W : Finset Site) (hEnvelope : AnchoredCyclicEnvelope e Z W)
    (hW : LatticeConvex W) (hPW : seq.polygon N ⊆ W) (hstrict : seq.polygon N ≠ W)
    (hstrip : ∀ g ∈ W, g ∈ polygonHalfStrip (seq.base N) (e 0)) :
    ∃ g ∈ W, shift (seq.sourceShift N) c g ≠ w g := by
  classical
  by_contra hnot
  have hagree : ∀ g ∈ W, shift (seq.sourceShift N) c g = w g := by
    simpa only [not_exists, not_and, not_not] using hnot
  have hcandidate : AnchoredCyclicAgreement (shift (seq.sourceShift N) c) w
      (seq.base N) (e 0) e Z W :=
    ⟨hEnvelope, hW, (seq.agreement N).2.2.1.trans hPW, hstrip, hagree⟩
  exact hstrict (seq.maximal N W hcandidate hPW).symm

end KumarNivat
