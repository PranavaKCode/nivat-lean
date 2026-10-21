module

public import KumarNivat.NewtonCyclicOrder

@[expose] public section

namespace KumarNivat

-- the actual factor fan carries antipodal pairs and no repeated unoriented line.
structure AnchoredChainFanOrder {q : ℕ} [NeZero (2 * q)] (e : ZMod (2 * q) → Site) : Prop where
  order : CyclicEdgeOrder e
  opposite : ∀ i, e (i + (q : ZMod (2 * q))) = -e i
  nonparallel : ∀ i (d : ℕ), 0 < d → d < q → determinant (e i) (e (i + (d : ZMod (2 * q)))) ≠ 0

-- antipodality rules out a prematurely negative determinant before a half turn.
theorem anchored_chain_half_turn_positive {q : ℕ} [NeZero (2 * q)]
    (e : ZMod (2 * q) → Site) (hfan : AnchoredChainFanOrder e)
    (i : ZMod (2 * q)) (d : ℕ) (hd₀ : 0 < d) (hdq : d < q) :
    0 < determinant (e i) (e (i + (d : ZMod (2 * q)))) := by
  obtain ⟨k, _hkn, hpositive, hnegative⟩ := hfan.order.normal_turn i
  have hne := hfan.nonparallel i d hd₀ hdq
  by_cases hdk : d < k
  · have hn := hpositive d hdk
    omega
  · have hfirst := hnegative d (by omega) (by omega)
    have hsecond := hnegative (q + d) (by omega) (by omega)
    have hindex : i + ((q + d : ℕ) : ZMod (2 * q)) =
        (i + (d : ZMod (2 * q))) + (q : ZMod (2 * q)) := by
      rw [Nat.cast_add]
      ring
    rw [hindex, hfan.opposite] at hsecond
    have hneg : determinant (e i) (-e (i + (d : ZMod (2 * q)))) =
        -determinant (e i) (e (i + (d : ZMod (2 * q)))) := by
      simp only [determinant, Prod.fst_neg, Prod.snd_neg]
      ring
    rw [hneg] at hsecond
    omega

-- natural offsets agree with the actual cyclic index while they stay in the named half turn.
theorem anchored_chain_nat_index {q : ℕ} [NeZero (2 * q)] (i j : ℕ) (hij : i ≤ j) :
    (i : ZMod (2 * q)) + ((j - i : ℕ) : ZMod (2 * q)) = (j : ZMod (2 * q)) := by
  rw [← Nat.cast_add]
  congr 1
  omega

-- two increasing first-half edges have strictly positive determinant in the actual fixed fan.
theorem anchored_chain_first_half_pair_positive {q : ℕ} [NeZero (2 * q)]
    (e : ZMod (2 * q) → Site) (hfan : AnchoredChainFanOrder e)
    (i j : ℕ) (hij : i < j) (hjq : j < q) :
    0 < determinant (e (i : ZMod (2 * q))) (e (j : ZMod (2 * q))) := by
  have h := anchored_chain_half_turn_positive e hfan (i : ZMod (2 * q))
    (j - i) (by omega) (by omega)
  rwa [anchored_chain_nat_index i j hij.le] at h

-- the first finite chain has the actual inward signs of its two recession rays.
theorem anchored_chain_surviving_normal_signs {q : ℕ} [NeZero (2 * q)]
    (e : ZMod (2 * q) → Site) (hfan : AnchoredChainFanOrder e)
    (b : ℕ) (_hb₀ : 0 < b) (hbq : b < q) :
    ∀ i : ℕ, i ≤ b →
      0 ≤ directionNormal (e (i : ZMod (2 * q))) (-e 0) ∧
      0 ≤ directionNormal (e (i : ZMod (2 * q))) (e (b : ZMod (2 * q))) ∧
      (0 < i → 0 < directionNormal (e (i : ZMod (2 * q))) (-e 0)) := by
  intro i hib
  have hminus : directionNormal (e (i : ZMod (2 * q))) (-e 0) =
      determinant (e 0) (e (i : ZMod (2 * q))) := by
    change determinant (e (i : ZMod (2 * q))) (-e 0) = determinant (e 0) (e (i : ZMod (2 * q)))
    simp only [determinant, Prod.fst_neg, Prod.snd_neg]
    ring
  have hfirst : 0 ≤ determinant (e 0) (e (i : ZMod (2 * q))) := by
    by_cases hi : i = 0
    · subst i
      simp [determinant, mul_comm]
    · simpa only [Nat.cast_zero] using le_of_lt
        (anchored_chain_first_half_pair_positive e hfan 0 i (by omega) (by omega))
  refine ⟨by rwa [hminus], ?_, ?_⟩
  · by_cases hi : i = b
    · subst i
      simp [directionNormal, determinant, mul_comm]
    · exact le_of_lt (anchored_chain_first_half_pair_positive e hfan i b (by omega) hbq)
  · intro hi
    rw [hminus]
    simpa only [Nat.cast_zero] using anchored_chain_first_half_pair_positive e hfan 0 i hi (by omega)

-- every normal outside the surviving chain is negative on one of the two actual rays.
theorem anchored_chain_removed_normal_signs {q : ℕ} [NeZero (2 * q)]
    (e : ZMod (2 * q) → Site) (hfan : AnchoredChainFanOrder e)
    (b : ℕ) (hb₀ : 0 < b) (hbq : b < q) :
    ∀ i : ℕ, b < i → i < 2 * q →
      directionNormal (e (i : ZMod (2 * q))) (-e 0) < 0 ∨
      directionNormal (e (i : ZMod (2 * q))) (e (b : ZMod (2 * q))) < 0 := by
  intro i hbi hiq
  by_cases hi : i < q
  · right
    have hpos := anchored_chain_first_half_pair_positive e hfan b i hbi hi
    change determinant (e (i : ZMod (2 * q))) (e (b : ZMod (2 * q))) < 0
    have hreverse : determinant (e (i : ZMod (2 * q))) (e (b : ZMod (2 * q))) =
        -determinant (e (b : ZMod (2 * q))) (e (i : ZMod (2 * q))) := by
      simp only [determinant]
      ring
    rw [hreverse]
    omega
  · have hindex : e (i : ZMod (2 * q)) = -e ((i - q : ℕ) : ZMod (2 * q)) := by
      have he : ((i - q : ℕ) : ZMod (2 * q)) + (q : ZMod (2 * q)) =
          (i : ZMod (2 * q)) := by
        rw [← Nat.cast_add]
        congr 1
        omega
      rw [← he, hfan.opposite]
    by_cases hieq : i = q
    · right
      subst i
      rw [hindex]
      simp only [Nat.sub_self, Nat.cast_zero]
      have hpos : 0 < determinant (e 0) (e (b : ZMod (2 * q))) := by
        simpa only [Nat.cast_zero] using anchored_chain_first_half_pair_positive e hfan 0 b hb₀ hbq
      have hneg : directionNormal (-e 0) (e (b : ZMod (2 * q))) =
          -determinant (e 0) (e (b : ZMod (2 * q))) := by
        change determinant (-e 0) (e (b : ZMod (2 * q))) = -determinant (e 0) (e (b : ZMod (2 * q)))
        simp only [determinant, Prod.fst_neg, Prod.snd_neg]
        ring
      rw [hneg]
      omega
    · left
      rw [hindex]
      have hpos : 0 < determinant (e 0) (e ((i - q : ℕ) : ZMod (2 * q))) := by
        simpa only [Nat.cast_zero] using
          anchored_chain_first_half_pair_positive e hfan 0 (i - q) (by omega) (by omega)
      have hneg : directionNormal (-e ((i - q : ℕ) : ZMod (2 * q))) (-e 0) =
          -determinant (e 0) (e ((i - q : ℕ) : ZMod (2 * q))) := by
        change determinant (-e ((i - q : ℕ) : ZMod (2 * q))) (-e 0) =
          -determinant (e 0) (e ((i - q : ℕ) : ZMod (2 * q)))
        simp only [determinant, Prod.fst_neg, Prod.snd_neg]
        ring
      rw [hneg]
      omega

end KumarNivat
