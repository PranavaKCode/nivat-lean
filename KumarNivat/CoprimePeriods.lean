module

public import KumarNivat.CoordinateEliminants
public import KumarNivat.LaurentMaps

@[expose] public section

namespace KumarNivat

-- lemma 2.3: two coprime laurent annihilators give independent global periods for a finite-image array.
theorem fullyPeriodic_of_coprime_annihilators {K : Type*} [Field K]
    (c : Site → K) (hc : (Set.range c).Finite) (f g : Laurent K) (hf : f ≠ 0)
    (hcop : IsRelPrime f g) (hfc : laurentAct f c = 0) (hgc : laurentAct g c = 0) :
    FullyPeriodic c := by
  obtain ⟨d₁, d₂, hd₁, hd₂, a₁, b₁, a₂, b₂, he₁, he₂⟩ :=
    exists_coordinate_eliminants f g hf hcop
  have haxis₁ : laurentAct (axisOperator (1, 0) d₁) c = 0 := by
    rw [← he₁, laurentAct_add, laurentAct_mul, laurentAct_mul, hfc, hgc,
      laurentAct_config_zero, laurentAct_config_zero, add_zero]
  have haxis₂ : laurentAct (axisOperator (0, 1) d₂) c = 0 := by
    rw [← he₂, laurentAct_add, laurentAct_mul, laurentAct_mul, hfc, hgc,
      laurentAct_config_zero, laurentAct_config_zero, add_zero]
  obtain ⟨q, hq, hp₁⟩ := period_multiple_of_axis_annihilator c hc (1, 0) d₁ hd₁ haxis₁
  obtain ⟨r, hr, hp₂⟩ := period_multiple_of_axis_annihilator c hc (0, 1) d₂ hd₂ haxis₂
  refine ⟨(q : ℤ) • ((1, 0) : Site), (r : ℤ) • ((0, 1) : Site), ?_, hp₁, hp₂⟩
  rw [determinant_zsmul]
  have hbasis : determinant ((1, 0) : Site) (0, 1) = 1 := by decide
  rw [hbasis, mul_one]
  exact mul_ne_zero (by exact_mod_cast Nat.ne_of_gt hq) (by exact_mod_cast Nat.ne_of_gt hr)

end KumarNivat
