module

public import KumarNivat.ColleAnchoredPreparationEndpoint
public import KumarNivat.ColleAnchoredRetainedFacet

@[expose] public section

namespace KumarNivat

-- the original integer annihilator and failure of full periodicity now give paired directions unconditionally.
theorem paired_direction_of_integer_annihilator_not_fullyPeriodic
    (c : Site → ℤ) (hc : (Set.range c).Finite) (f : Laurent ℤ) (hf : f ≠ 0)
    (hann : laurentAct f c = 0) (hnotfull : ¬ FullyPeriodic c) :
    HasPairedOneSidedDirection c :=
  paired_direction_of_integer_annihilator_not_fullyPeriodic_of_anchored_selection c hc f hf hann hnotfull
    (by
      intro hs q _inst e D
      exact exists_colle_anchored_retained_facet c hs e D)

-- its contrapositive is the source structural statement used before choosing the periodic reference.
theorem fullyPeriodic_of_integer_annihilator_no_pair
    (c : Site → ℤ) (hc : (Set.range c).Finite) (f : Laurent ℤ) (hf : f ≠ 0)
    (hann : laurentAct f c = 0) (hnopair : ¬ HasPairedOneSidedDirection c) :
    FullyPeriodic c :=
  fullyPeriodic_of_integer_annihilator_no_pair_of_anchored_selection c hc f hf hann hnopair
    (by
      intro hs q _inst e D
      exact exists_colle_anchored_retained_facet c hs e D)

end KumarNivat
