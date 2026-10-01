import KumarNivat.LineRecurrence
import KumarNivat.LaurentAlgebra

namespace KumarNivat

-- a directional factor is written along its integer exponent segment.
noncomputable def lineOperator {K : Type*} [CommRing K] (E p : Site)
    (t : ℕ) (α : Fin (t + 1) → K) : Laurent K :=
  ∑ i : Fin (t + 1), AddMonoidAlgebra.single (E + (i.val : ℤ) • p) (α i)

-- applying the factor samples precisely the sites along that segment.
theorem laurentAct_lineOperator {K : Type*} [CommRing K] (E p : Site)
    (t : ℕ) (α : Fin (t + 1) → K) (b : Site → K) (g : Site) :
    laurentAct (lineOperator E p t α) b g =
      ∑ i : Fin (t + 1), α i * b (g + E + (i.val : ℤ) • p) := by
  classical
  change laurentActAt b g (lineOperator E p t α) = _
  rw [lineOperator, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  change laurentAct (AddMonoidAlgebra.single (E + (i.val : ℤ) • p) (α i)) b g = _
  rw [laurentAct_single]
  simp only [add_assoc]

-- translating away the factor's initial exponent yields the short line recurrence.
theorem lineRecurrence_of_lineOperator {K : Type*} [CommRing K]
    (E p : Site) (t : ℕ) (α : Fin (t + 1) → K) (b : Site → K)
    (hann : laurentAct (lineOperator E p t α) b = 0) (k : Site) :
    LineRecurrence t α (fun n : ℤ => b (k + n • p)) := by
  intro n
  have he := congrFun hann (k + n • p - E)
  rw [laurentAct_lineOperator] at he
  change (∑ i : Fin (t + 1), α i * b ((k + n • p - E) + E + (i.val : ℤ) • p)) = 0 at he
  have hsite (i : Fin (t + 1)) :
      (k + n • p - E) + E + (i.val : ℤ) • p = k + (n + (i.val : ℤ)) • p := by
    rw [add_smul]
    abel
  simpa only [hsite] using he

end KumarNivat
