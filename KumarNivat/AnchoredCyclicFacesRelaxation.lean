import KumarNivat.AnchoredEnvelopeLengths

open Filter Topology

namespace KumarNivat

-- one fixed positive scale clears both neighboring intersection denominators.
def cyclicFacetRelaxationScale {n : ℕ} [NeZero n] (e : ZMod n → Site) (i : ZMod n) : ℤ :=
  determinant (e (i - 1)) (e i) * determinant (e i) (e (i + 1))

-- scaling each rational intermediate layer gives actual integer endpoint displacements.
def scaledFacetRelaxationVertex {n : ℕ} [NeZero n] (e : ZMod n → Site)
    (F : Finset Site) (P : OrderedCyclicLatticePolygon e F) (i : ZMod n) (j : ℤ) (k : ZMod n) : Site :=
  if k = i then cyclicFacetRelaxationScale e i • P.vertex k +
    (j * determinant (e i) (e (i + 1))) • e (i - 1)
  else if k = i + 1 then cyclicFacetRelaxationScale e i • P.vertex k -
    (j * determinant (e (i - 1)) (e i)) • e (i + 1)
  else cyclicFacetRelaxationScale e i • P.vertex k

-- only the moving edge and its two neighbors change their primitive lengths.
def scaledFacetRelaxationLength {n : ℕ} [NeZero n] (e : ZMod n → Site)
    (F : Finset Site) (P : OrderedCyclicLatticePolygon e F) (i : ZMod n) (j : ℤ) (k : ZMod n) : ℤ :=
  if k = i - 1 then cyclicFacetRelaxationScale e i * P.edgeLength k +
    j * determinant (e i) (e (i + 1))
  else if k = i then cyclicFacetRelaxationScale e i * P.edgeLength k -
    j * determinant (e (i - 1)) (e (i + 1))
  else if k = i + 1 then cyclicFacetRelaxationScale e i * P.edgeLength k +
    j * determinant (e (i - 1)) (e i)
  else cyclicFacetRelaxationScale e i * P.edgeLength k

-- positive adjacent turns make the three modified cyclic indices distinct.
theorem cyclic_facet_neighbors_distinct {n : ℕ} [NeZero n]
    (e : ZMod n → Site) (horder : CyclicEdgeOrder e) (i : ZMod n) :
    i - 1 ≠ i ∧ i ≠ i + 1 ∧ i - 1 ≠ i + 1 := by
  have hleft := horder.adjacent_pos i
  have hright := horder.adjacent_pos (i + 1)
  simp only [add_sub_cancel_right] at hright
  refine ⟨?_, ?_, ?_⟩
  · intro he
    rw [he] at hleft
    simp [determinant, mul_comm] at hleft
  · intro he
    rw [← he] at hright
    simp [determinant, mul_comm] at hright
  · intro he
    rw [he] at hleft
    have hreverse : determinant (e (i + 1)) (e i) = -determinant (e i) (e (i + 1)) := by
      simp only [determinant]
      ring
    rw [hreverse] at hleft
    omega

-- adjacent positive turns also make the denominator-clearing scale strictly positive.
theorem cyclic_facet_relaxation_scale_positive {n : ℕ} [NeZero n]
    (e : ZMod n → Site) (horder : CyclicEdgeOrder e) (i : ZMod n) :
    0 < cyclicFacetRelaxationScale e i := by
  have hright := horder.adjacent_pos (i + 1)
  simp only [add_sub_cancel_right] at hright
  exact mul_pos (horder.adjacent_pos i) hright

-- the three neighboring directions satisfy the exact integer identity needed for the moving edge.
theorem cyclic_facet_neighbor_vector_identity {n : ℕ} [NeZero n]
    (e : ZMod n → Site) (i : ZMod n) :
    determinant (e (i - 1)) (e (i + 1)) • e i =
      determinant (e (i - 1)) (e i) • e (i + 1) +
        determinant (e i) (e (i + 1)) • e (i - 1) := by
  have he := determinant_smul_identity (e (i - 1)) (e i) (e (i + 1))
  have hreverse : determinant (e (i + 1)) (e i) = -determinant (e i) (e (i + 1)) := by
    simp only [determinant]
    ring
  rw [hreverse, neg_smul] at he
  rw [he]
  abel

-- every scaled intermediate layer is an actual closed integer walk in the same fixed fan.
theorem scaled_facet_relaxation_edge_equations {n : ℕ} [NeZero n]
    (e : ZMod n → Site) (horder : CyclicEdgeOrder e) (F : Finset Site)
    (P : OrderedCyclicLatticePolygon e F) (i : ZMod n) (j : ℤ) :
    ∀ k, scaledFacetRelaxationVertex e F P i j (k + 1) =
      scaledFacetRelaxationVertex e F P i j k + scaledFacetRelaxationLength e F P i j k • e k := by
  obtain ⟨hpc, hcn, hpn⟩ := cyclic_facet_neighbors_distinct e horder i
  intro k
  by_cases hkprev : k = i - 1
  · subst k
    have he := P.edge_eq (i - 1)
    simp only [sub_add_cancel] at he
    simp only [scaledFacetRelaxationVertex, scaledFacetRelaxationLength, sub_add_cancel,
      ite_true, ite_eq_right hpc, ite_eq_right hpn]
    rw [he, smul_add, add_smul, smul_smul]
    abel
  · by_cases hkcur : k = i
    · subst k
      have hvector := congrArg (fun z : Site => j • z) (cyclic_facet_neighbor_vector_identity e i)
      simp only [smul_add, smul_smul] at hvector
      simp only [scaledFacetRelaxationVertex, scaledFacetRelaxationLength,
        ite_true, ite_eq_right hcn.symm, ite_eq_right hpc.symm]
      rw [P.edge_eq, smul_add, sub_smul, smul_smul, hvector]
      abel
    · by_cases hknext : k = i + 1
      · subst k
        have hfarcur : i + 1 + 1 ≠ i := by
          intro he
          apply hpn
          calc
            i - 1 = (i + 1 + 1) - 1 := by rw [he]
            _ = i + 1 := by abel
        have hfarnext : i + 1 + 1 ≠ i + 1 := by
          intro he
          have hzero : (1 : ZMod n) = 0 := add_left_cancel (show (i + 1) + 1 = (i + 1) + 0 by simpa using he)
          exact hcn (by rw [hzero, add_zero])
        simp only [scaledFacetRelaxationVertex, scaledFacetRelaxationLength,
          ite_eq_right hfarcur, ite_eq_right hfarnext, ite_eq_right hcn.symm,
          ite_eq_right hpn.symm, ite_true]
        rw [P.edge_eq, smul_add, add_smul, smul_smul]
        abel
      · have hnextcur : k + 1 ≠ i := by
          intro he
          apply hkprev
          calc
            k = (k + 1) - 1 := by abel
            _ = i - 1 := by rw [he]
        have hnextnext : k + 1 ≠ i + 1 := fun he => hkcur (add_right_cancel he)
        simp only [scaledFacetRelaxationVertex, scaledFacetRelaxationLength,
          ite_eq_right hkprev, ite_eq_right hkcur, ite_eq_right hknext,
          ite_eq_right hnextcur, ite_eq_right hnextnext]
        rw [P.edge_eq, smul_add, smul_smul]

-- a fixed moving-edge buffer preserves the full original newton edge lengths at every cleared intermediate layer.
theorem scaled_facet_relaxation_lengths_dominate {n : ℕ} [NeZero n]
    (e : ZMod n → Site) (horder : CyclicEdgeOrder e) (Z F : Finset Site)
    (Q : OrderedCyclicLatticePolygon e Z) (P : OrderedCyclicLatticePolygon e F)
    (hlen : ∀ k, Q.edgeLength k ≤ P.edgeLength k) (i : ZMod n) (j : ℤ)
    (hj₀ : 0 ≤ j) (hjm : j ≤ cyclicFacetRelaxationScale e i)
    (hbuffer : Q.edgeLength i + |determinant (e (i - 1)) (e (i + 1))| + 1 ≤ P.edgeLength i) :
    ∀ k, cyclicFacetRelaxationScale e i * Q.edgeLength k ≤ scaledFacetRelaxationLength e F P i j k := by
  intro k
  have hM := cyclic_facet_relaxation_scale_positive e horder i
  have hleft := horder.adjacent_pos i
  have hright := horder.adjacent_pos (i + 1)
  simp only [add_sub_cancel_right] at hright
  have hbase := mul_le_mul_of_nonneg_left (hlen k) hM.le
  dsimp [scaledFacetRelaxationLength]
  split_ifs with hprev hcur hnext
  · exact hbase.trans (le_add_of_nonneg_right (mul_nonneg hj₀ hright.le))
  · subst k
    have hscaled := mul_le_mul_of_nonneg_left hbuffer hM.le
    have hspan : j * determinant (e (i - 1)) (e (i + 1)) ≤
        cyclicFacetRelaxationScale e i * |determinant (e (i - 1)) (e (i + 1))| := by
      calc
        j * determinant (e (i - 1)) (e (i + 1)) ≤ j * |determinant (e (i - 1)) (e (i + 1))| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) hj₀
        _ ≤ _ := mul_le_mul_of_nonneg_right hjm (abs_nonneg _)
    nlinarith
  · exact hbase.trans (le_add_of_nonneg_right (mul_nonneg hj₀ hleft.le))
  · exact hbase

-- the first unbounded primitive edge eventually supplies this finite relaxation buffer.
theorem unbounded_facet_length_eventually_has_buffer {n : ℕ} [NeZero n]
    (e : ZMod n → Site) (Z : Finset Site) (Q : OrderedCyclicLatticePolygon e Z)
    (F : ℕ → Finset Site) (P : ∀ N, OrderedCyclicLatticePolygon e (F N)) (i : ZMod n)
    (hdiv : Tendsto (fun N => ((P N).edgeLength i).toNat) atTop atTop) :
    ∀ᶠ N in atTop,
      Q.edgeLength i + |determinant (e (i - 1)) (e (i + 1))| + 1 ≤ (P N).edgeLength i := by
  let bound := Q.edgeLength i + |determinant (e (i - 1)) (e (i + 1))| + 1
  have hlarge := (tendsto_atTop.mp hdiv) bound.toNat
  exact hlarge.mono (fun N hN => by have hpos := (P N).length_pos i; dsimp [bound] at *; omega)

end KumarNivat
