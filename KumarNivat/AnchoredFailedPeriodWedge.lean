import KumarNivat.AnchoredChainFan
import KumarNivat.FailedFacetWedgeNegative
import KumarNivat.OrientedPairedData
import KumarNivat.SquarefreeProducts

namespace KumarNivat

open scoped Pointwise

-- the first retained normal is the outer half-plane and the last normal is the adjoined moving facet.
theorem retained_chain_as_adjoined_facets
    (μ : ℕ → Site →+ ℤ) (fixed : ℕ → ℤ) (b : ℕ) (hb₀ : 0 < b) (β : ℤ) :
    inwardLayerRegion (μ b) β (Finset.range b) μ fixed =
      inwardLayerRegion (μ 0) (fixed 0) (facetIndexSet (Finset.Icc 1 (b - 1)))
        (facetNormals (μ b) μ) (facetLevels β fixed) := by
  ext x
  rw [mem_inward_region_adjoined_facet]
  constructor
  · intro hx
    refine ⟨hx.2 0 (Finset.mem_range.mpr hb₀), hx.1, ?_⟩
    intro i hi
    obtain ⟨_hi₀, hib⟩ := Finset.mem_Icc.mp hi
    exact hx.2 i (Finset.mem_range.mpr (by omega))
  · intro hx
    refine ⟨hx.2.1, ?_⟩
    intro i hi
    have hib := Finset.mem_range.mp hi
    by_cases he : i = 0
    · subst i
      exact hx.1
    · exact hx.2.2 i (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)

-- the actual failed moving facet constructs a fully periodic background wedge for the same limit configuration.
theorem anchored_failed_period_background_wedge {K : Type*}
    [CommRing K] [Nontrivial K] [NoZeroDivisors K] {q : ℕ} [NeZero (2 * q)]
    (c θ : Site → K) (hc : (Set.range c).Finite) (hθ : LanguageContained θ c)
    (hs : List Site) (hdirs : ∀ p ∈ hs, p ≠ 0)
    (hann : laurentAct (differenceProduct hs) θ = 0)
    (R S : Finset Site) (hgen : GeneratingPolygon c R S)
    (e : ZMod (2 * q) → Site) (hfan : AnchoredChainFanOrder e)
    (b : ℕ) (hb₀ : 0 < b) (hbq : b < q)
    (hprimitiveA : Int.gcd (e 0).1 (e 0).2 = 1)
    (hprimitiveB : Int.gcd (e (b : ZMod (2 * q))).1 (e (b : ZMod (2 * q))).2 = 1)
    (m M : ℤ) (hbounds : ∀ u ∈ S, m ≤ directionNormal (e 0) u ∧ directionNormal (e 0) u ≤ M)
    (hlower : 2 ≤ (lowerLatticeFace S (directionNormal (e 0)) m).card)
    (hupper : 2 ≤ (lowerLatticeFace S (-directionNormal (e 0)) (-M)).card)
    (fixed : ℕ → ℤ) (β : ℤ) (C : Set RealPlane)
    (hsum : inwardLayerRegion (directionNormal (e (b : ZMod (2 * q)))) β (Finset.range b)
      (fun i => directionNormal (e (i : ZMod (2 * q)))) fixed =
        latticeHull (differenceProduct (K := K) hs).coeff.support + C)
    (l : ℕ) (hl : 0 < l)
    (hagree : ∀ g : Site, latticeEmbedding g ∈
      inwardLayerRegion (directionNormal (e (b : ZMod (2 * q)))) (β + 1) (Finset.range b)
        (fun i => directionNormal (e (i : ZMod (2 * q)))) fixed →
      θ g = shift ((l : ℤ) • (-e 0)) θ g)
    (hfailure : ∃ g : Site, latticeEmbedding g ∈
      inwardLayerRegion (directionNormal (e (b : ZMod (2 * q)))) β (Finset.range b)
        (fun i => directionNormal (e (i : ZMod (2 * q)))) fixed ∧
      θ g ≠ shift ((l : ℤ) • (-e 0)) θ g) :
    Function.Injective ((directionNormal (e 0)).prod (directionNormal (e (b : ZMod (2 * q))))) ∧
      ∃ E : Site, ∃ B : Site → K, FullyPeriodic B ∧
        AgreesOnWedge (directionNormal (e 0)) (directionNormal (e (b : ZMod (2 * q))))
          (directionNormal (e 0) E) (directionNormal (e (b : ZMod (2 * q))) E) θ B ∧
        Set.range B ⊆ Set.range θ := by
  let μ := fun i : ℕ => directionNormal (e (i : ZMod (2 * q)))
  let η := directionNormal (e (b : ZMod (2 * q)))
  let J := Finset.Icc 1 (b - 1)
  have hregion (r : ℤ) :
      inwardLayerRegion η r (Finset.range b) μ fixed =
        inwardLayerRegion (directionNormal (e 0)) (fixed 0) (facetIndexSet J)
          (facetNormals η μ) (facetLevels r fixed) := by
    simpa only [μ, η, J, Nat.cast_zero] using retained_chain_as_adjoined_facets μ fixed b hb₀ r
  have hnormal : -directionNormal (-e 0) = directionNormal (e 0) := by
    rw [directionNormal_neg, neg_neg]
  have hprimitiveNeg : Int.gcd (-e 0).1 (-e 0).2 = 1 := by
    simpa only [Prod.fst_neg, Prod.snd_neg, Int.gcd, Int.natAbs_neg] using hprimitiveA
  have hpositive : 0 < determinant (e 0) (e (b : ZMod (2 * q))) := by
    simpa only [Nat.cast_zero] using anchored_chain_first_half_pair_positive e hfan 0 b hb₀ hbq
  have hdet : determinant (-e 0) (e (b : ZMod (2 * q))) < 0 := by
    have he : determinant (-e 0) (e (b : ZMod (2 * q))) =
        -determinant (e 0) (e (b : ZMod (2 * q))) := by
      simp only [determinant, Prod.fst_neg, Prod.snd_neg]
      ring
    rw [he]
    omega
  have hμa : ∀ i ∈ J, 0 < μ i (-e 0) := by
    intro i hi
    obtain ⟨hi₀, hib⟩ := Finset.mem_Icc.mp hi
    exact (anchored_chain_surviving_normal_signs e hfan b hb₀ hbq i (by omega)).2.2 (by omega)
  have hμb : ∀ i ∈ J, 0 < μ i (e (b : ZMod (2 * q))) := by
    intro i hi
    obtain ⟨_hi₀, hib⟩ := Finset.mem_Icc.mp hi
    exact anchored_chain_first_half_pair_positive e hfan i b (by omega) hbq
  have hηa : 0 < η (-e 0) :=
    (anchored_chain_surviving_normal_signs e hfan b hb₀ hbq b le_rfl).2.2 hb₀
  have hη : η ≠ 0 := by
    intro he
    rw [he] at hηa
    norm_num at hηa
  have hηb : η (e (b : ZMod (2 * q))) = 0 := directionNormal_self _
  have hf := differenceProduct_ne_zero (K := K) hs hdirs
  have hout := background_wedge_from_failed_facet_negative_orientation c θ hc hθ
    (differenceProduct hs) hf hann R S hgen (-e 0) (e (b : ZMod (2 * q)))
    hprimitiveNeg hprimitiveB hdet m M (fixed 0)
    (by rwa [hnormal]) (by rwa [hnormal]) (by rwa [directionNormal_neg])
    J μ fixed hμa hμb η hη hηa hηb l hl β C
    (by rw [hnormal, ← hregion β]; exact hsum)
    (by rw [hnormal, ← hregion (β + 1)]; exact hagree)
    (by rw [hnormal, ← hregion β]; exact hfailure)
  simpa only [hnormal] using hout

end KumarNivat
