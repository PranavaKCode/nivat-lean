import KumarNivat.AnchoredMaximalTransport
import KumarNivat.AnchoredCyclicPhases
import KumarNivat.AnchoredExhaustionWidths
import KumarNivat.AnchoredChainUnion

open Filter Topology

namespace KumarNivat

-- these are the actual maximal polygons after anchoring and fixing one reference phase.
structure AnchoredCyclicMaximalSequence {A : Type*} {q : ℕ} [NeZero (2 * q)]
    (c w : Site → A) (e : ZMod (2 * q) → Site) (Z : Set RealPlane) (G : Site) where
  base : ℕ → Finset Site
  polygon : ℕ → Finset Site
  sourceShift : ℕ → Site
  cyclic : ∀ N, OrderedCyclicLatticePolygon e (polygon N)
  anchor : ∀ N, (cyclic N).vertex 1 = G
  convex : ∀ N, LatticeConvex (polygon N)
  base_convex : ∀ N, LatticeConvex (base N)
  base_envelope : ∀ N, AnchoredCyclicEnvelope e Z (base N)
  agreement : ∀ N, AnchoredCyclicAgreement (shift (sourceShift N) c) w (base N) (e 0) e Z (polygon N)
  maximal : ∀ N, ∀ T : Finset Site,
    AnchoredCyclicAgreement (shift (sourceShift N) c) w (base N) (e 0) e Z T →
      polygon N ⊆ T → T = polygon N
  lengths_monotone : Monotone (fun N => (cyclic N).edgeLength)
  polygons_monotone : Monotone polygon
  tangent_diverges : Tendsto (fun N => ((cyclic N).edgeLength 0).toNat) atTop atTop
  width_diverges : Tendsto (fun N => ((directionNormal (e 0) ((cyclic N).vertex (q : ZMod (2 * q))) -
    directionNormal (e 0) G : ℤ) : ℝ)) atTop atTop

-- original half-plane exhaustion constructs the anchored sequence and both growth conditions internally.
theorem exists_actual_anchored_maximal_sequence {K : Type*} [CommRing K] [Nontrivial K]
    [NoZeroDivisors K] [TopologicalSpace K] [DiscreteTopology K] {q : ℕ} [NeZero (2 * q)]
    (c w : Site → K) (hw : w ∈ orbitClosure c)
    (hs : List Site) (hlen : 2 ≤ hs.length) (hdirs : ∀ h ∈ hs, h ≠ 0)
    (hpairs : hs.Pairwise (fun p r => determinant p r ≠ 0))
    (e : ZMod (2 * q) → Site) (hfan : AnchoredChainFanOrder e)
    (P₀ : OrderedCyclicLatticePolygon e (differenceProduct (K := K) hs).coeff.support)
    (hprimitive : Int.gcd (e 0).1 (e 0).2 = 1) (p : Site) (hpmem : p ∈ hs)
    (hparallel : determinant (e 0) p = 0) (cut : ℤ) (G : Site)
    (hGcut : directionNormal (e 0) G = cut)
    (l : ℕ) (hl : 0 < l) (hperiod : IsPeriod w ((l : ℤ) • e 0))
    (hnoHalfStrip : ∀ F : Finset Site,
      AnchoredCyclicEnvelope e (latticeHull (differenceProduct (K := K) hs).coeff.support) F →
      LatticeConvex F → (∀ g ∈ F, cut ≤ directionNormal (e 0) g) →
      ∀ u : Site, ¬ ∀ g ∈ polygonHalfStrip F (e 0), shift u c g = w g) :
    ∃ r : ℤ, 0 ≤ r ∧ r < (l : ℤ) ∧
      Nonempty (AnchoredCyclicMaximalSequence c (shift (r • e 0) w) e
        (latticeHull (differenceProduct (K := K) hs).coeff.support) G) := by
  classical
  let Z := latticeHull (differenceProduct (K := K) hs).coeff.support
  obtain ⟨F, M, u, _hmonoM, hwindow, hdata, hexhaust⟩ := actual_newton_maximal_polygon_exhaustion
    c w hw hs hlen hdirs hpairs e hfan.order P₀ hprimitive p hpmem hparallel cut G hGcut hnoHalfStrip
  have hM (N : ℕ) : AnchoredCyclicAgreement (shift (u N) c) w (F N) (e 0) e Z (M N) :=
    (hdata N).2.2.2.1
  have hhalf (N : ℕ) : ∀ g ∈ M N, cut ≤ directionNormal (e 0) g := (hdata N).2.2.2.2.1
  have hG (N : ℕ) : G ∈ M N := by
    apply (hM N).2.2.1
    apply hwindow N
    exact Finset.mem_union_right _ (Finset.mem_singleton_self G)
  obtain ⟨P, k, Q, hQ, hagreeQ, hmaxQ⟩ := anchored_maximal_cyclic_polygons_at_common_boundary
    c w e hfan.order Z F M u G cut hprimitive hGcut hG hhalf hM (fun N => (hdata N).2.2.2.2.2)
  let T := fun N => (M N).image (fun g => -k N • e 0 + g)
  have hanchorQ : ∀ N, (Q N).vertex 1 = G := fun N => (hQ N).1
  have hconvexQ : ∀ N, LatticeConvex (T N) := fun N => (hQ N).2.2.1
  have haP := exhaustive_cyclic_tangent_lengths_diverge e hfan.order M P G cut hprimitive hGcut hG hhalf hexhaust
  have hwP := exhaustive_cyclic_transverse_width_diverges e hfan M P G cut hprimitive hGcut hexhaust
  have haQ : Tendsto (fun N => ((Q N).edgeLength 0).toNat) atTop atTop := by
    convert haP using 1
    funext N
    rw [(hQ N).2.1 0]
  have hwQ : Tendsto (fun N => ((directionNormal (e 0) ((Q N).vertex (q : ZMod (2 * q))) -
      directionNormal (e 0) G : ℤ) : ℝ)) atTop atTop := by
    convert hwP using 1
    funext N
    rw [(hQ N).2.2.2 (q : ZMod (2 * q))]
  obtain ⟨r, hr₀, hr₁, ρ, hρ, hphase, hlengths, _hhulls, hpolygons⟩ :=
    anchored_cyclic_constant_phase_monotone_subsequence w (e 0) l hl hperiod k e hfan.order T Q hconvexQ G hanchorQ
  refine ⟨r, hr₀, hr₁, ⟨{
    base := fun N => (F (ρ N)).image (fun g => -k (ρ N) • e 0 + g)
    polygon := T ∘ ρ
    sourceShift := fun N => u (ρ N) + k (ρ N) • e 0
    cyclic := fun N => Q (ρ N)
    anchor := fun N => hanchorQ (ρ N)
    convex := fun N => hconvexQ (ρ N)
    base_convex := fun N => latticeConvex_integer_translation (F (ρ N)) (hdata (ρ N)).1 (-k (ρ N) • e 0)
    base_envelope := fun N => ((hdata (ρ N)).2.2.1).translation (hdata (ρ N)).1 (-k (ρ N) • e 0)
    agreement := ?_
    maximal := ?_
    lengths_monotone := hlengths
    polygons_monotone := hpolygons
    tangent_diverges := haQ.comp hρ.tendsto_atTop
    width_diverges := hwQ.comp hρ.tendsto_atTop
  }⟩⟩
  · intro N
    have h := hagreeQ (ρ N)
    rw [hphase N] at h
    exact h
  · intro N S hS hTS
    apply hmaxQ (ρ N) S _ hTS
    rw [hphase N]
    exact hS

-- the constructed maximal sequence supplies the finite-chain union with no assumed growth or stable-support data.
theorem AnchoredCyclicMaximalSequence.actual_chain_union {A : Type*} {q : ℕ} [NeZero (2 * q)]
    {c w : Site → A} {e : ZMod (2 * q) → Site} {Z : Set RealPlane} {G : Site}
    (seq : AnchoredCyclicMaximalSequence c w e Z G) (hfan : AnchoredChainFanOrder e) :
    ∃ b : ℕ, 0 < b ∧ b < q ∧
      Tendsto (fun N => ((seq.cyclic N).edgeLength (b : ZMod (2 * q))).toNat) atTop atTop ∧
      ∃ B : Site, (∀ᶠ N in atTop, (seq.cyclic N).vertex (b : ZMod (2 * q)) = B) ∧
      ∃ fixed : ℕ → ℤ, fixed 0 = directionNormal (e 0) G ∧
        (∀ i : ℕ, i ≤ b → ∀ᶠ N in atTop, anchoredCyclicSupport e (seq.polygon N) (seq.cyclic N) i = fixed i) ∧
        (⋃ N, latticeHull (seq.polygon N)) = finiteInwardRegion (Finset.range (b + 1))
          (fun i => directionNormal (e (i : ZMod (2 * q)))) fixed :=
  anchored_actual_chain_union e hfan seq.polygon seq.cyclic G seq.anchor
    (fun _N _M hNM i => seq.lengths_monotone hNM i) seq.tangent_diverges seq.width_diverges

end KumarNivat
