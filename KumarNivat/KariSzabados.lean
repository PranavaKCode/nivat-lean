module

public import KumarNivat.IntegerProductAnnihilator
public import KumarNivat.DistinctDirectionProducts

@[expose] public section

namespace KumarNivat

-- the kari-szabados input is proved from the integer annihilator with distinct directions.
theorem integer_annihilator_distinct_difference_product (c : Site → ℤ)
    (hc : (Set.range c).Finite) (f : Laurent ℤ) (hf : f ≠ 0)
    (hann : laurentAct f c = 0) :
    ∃ hs : List Site, hs ≠ [] ∧ hs.Pairwise (fun p q => determinant p q ≠ 0) ∧
      (∀ h ∈ hs, h ≠ 0) ∧ laurentAct (differenceProduct hs) c = 0 := by
  by_cases hc₀ : c = 0
  · refine ⟨[(1, 0)], by simp, by simp, ?_, ?_⟩
    · intro h hh
      have he : h = (1, 0) := List.mem_singleton.mp hh
      rw [he]
      decide
    · rw [hc₀, laurentAct_config_zero]
  · obtain ⟨hs, hdirs, hprod⟩ := exists_integer_difference_product c hc f hf hann
    let d : Site → ℚ := fun g => (c g : ℚ)
    have hd : (Set.range d).Finite := (hc.image (fun n : ℤ => (n : ℚ))).subset (by
      rintro y ⟨g, rfl⟩
      exact ⟨c g, ⟨g, rfl⟩, rfl⟩)
    have hcast : laurentAct (differenceProduct hs) d = 0 := cast_integer_difference_product c hs hprod
    obtain ⟨ts, hpairs, hnonzero, hts⟩ := normalize_difference_directions hs hdirs d hd hcast
    have hint : laurentAct (differenceProduct ts) c = 0 :=
      integer_difference_product_of_cast_zero (K := ℚ) c ts hts
    refine ⟨ts, ?_, hpairs, hnonzero, hint⟩
    intro hnil
    rw [hnil, differenceProduct_nil, laurentAct_one] at hint
    exact hc₀ hint

-- low pattern complexity supplies exactly the nonempty distinct-direction product used by the paper.
theorem low_complexity_distinct_difference_product (c : Site → ℤ)
    (hc : (Set.range c).Finite) (D : Finset Site) (hlow : complexity c D ≤ D.card) :
    ∃ hs : List Site, hs ≠ [] ∧ hs.Pairwise (fun p q => determinant p q ≠ 0) ∧
      (∀ h ∈ hs, h ≠ 0) ∧ laurentAct (differenceProduct hs) c = 0 := by
  obtain ⟨F, hF, hann⟩ := exists_integer_annihilator c hc D hlow
  apply integer_annihilator_distinct_difference_product c hc (AddMonoidAlgebra.ofCoeff F)
  · intro hz
    exact hF (congrArg AddMonoidAlgebra.coeff hz)
  · exact funext hann

end KumarNivat
