import KumarNivat.ColleAnchoredPreparationSource

namespace KumarNivat

-- one retained geometric facet endpoint now supplies the full general paired-direction conclusion of the quoted structural theorem.
theorem paired_direction_of_integer_annihilator_not_fullyPeriodic_of_anchored_selection
    (c : Site → ℤ) (hc : (Set.range c).Finite) (f : Laurent ℤ) (hf : f ≠ 0)
    (hann : laurentAct f c = 0) (hnotfull : ¬ FullyPeriodic c)
    (hretained : ∀ (hs : List Site) {q : ℕ} [NeZero q] (e : ZMod (2 * q) → Site)
      (D : ColleAnchoredSourceData c hs e), Nonempty (ColleAnchoredRetainedFacet c hs e D.reference)) :
    HasPairedOneSidedDirection c := by
  classical
  by_contra hnopair
  obtain ⟨hs, q, hq, e, ⟨D⟩⟩ := exists_colle_anchored_source_data_of_integer_annihilator_no_pair
    c hc f hf hann hnotfull hnopair
  let _ : NeZero q := ⟨by omega⟩
  exact hnopair (paired_direction_of_colle_retained_facet c hs e D (Classical.choice (hretained hs e D)))

-- the same precise retained endpoint also gives the contrapositive full-periodicity form used in the source proof.
theorem fullyPeriodic_of_integer_annihilator_no_pair_of_anchored_selection
    (c : Site → ℤ) (hc : (Set.range c).Finite) (f : Laurent ℤ) (hf : f ≠ 0)
    (hann : laurentAct f c = 0) (hnopair : ¬ HasPairedOneSidedDirection c)
    (hretained : ∀ (hs : List Site) {q : ℕ} [NeZero q] (e : ZMod (2 * q) → Site)
      (D : ColleAnchoredSourceData c hs e), Nonempty (ColleAnchoredRetainedFacet c hs e D.reference)) :
    FullyPeriodic c := by
  by_contra hnotfull
  exact hnopair (paired_direction_of_integer_annihilator_not_fullyPeriodic_of_anchored_selection
    c hc f hf hann hnotfull hretained)

end KumarNivat
