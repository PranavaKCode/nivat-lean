module

public import KumarNivat.DistinctDirectionProducts

@[expose] public section

namespace KumarNivat

-- removing an actual distinct-direction factor retains the exact product and all remaining directions.
theorem differenceProduct_delete_factor {K : Type*} [CommRing K] (hs : List Site)
    (hpairs : hs.Pairwise (fun p q => determinant p q ≠ 0)) (p : Site) (hp : p ∈ hs) :
    ∃ rest : List Site, rest.length + 1 = hs.length ∧ (∀ q ∈ rest, q ∈ hs) ∧
      rest.Pairwise (fun a b => determinant a b ≠ 0) ∧
      differenceProduct (K := K) hs = binomial p * differenceProduct rest ∧
      (∀ q ∈ rest, determinant p q ≠ 0) ∧ ∀ q ∈ hs, q = p ∨ q ∈ rest := by
  obtain ⟨xs, ys, hsplit⟩ := List.mem_iff_append.mp hp
  let rest := xs ++ ys
  have hparts := List.pairwise_append.mp (hsplit ▸ hpairs)
  have hpys := List.pairwise_cons.mp hparts.2.1
  refine ⟨rest, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [rest]
    rw [hsplit]
    simp only [List.length_append, List.length_cons]
    omega
  · intro q hq
    rw [hsplit]
    rcases List.mem_append.mp hq with hqx | hqy
    · exact List.mem_append_left (p :: ys) hqx
    · exact List.mem_append_right xs (List.mem_cons_of_mem p hqy)
  · exact List.pairwise_append.mpr ⟨hparts.1, hpys.2,
      fun a ha b hb => hparts.2.2 a ha b (List.mem_cons_of_mem p hb)⟩
  · rw [hsplit, differenceProduct_append, differenceProduct_cons]
    dsimp [rest]
    rw [differenceProduct_append]
    ring
  · intro q hq
    rcases List.mem_append.mp hq with hqx | hqy
    · have he := hparts.2.2 q hqx p List.mem_cons_self
      have hswap : determinant p q = -determinant q p := by simp [determinant]; ring
      rw [hswap]
      exact neg_ne_zero.mpr he
    · exact hpys.1 q hqy
  · intro q hq
    rw [hsplit] at hq
    rcases List.mem_append.mp hq with hqx | hqy
    · exact Or.inr (List.mem_append_left ys hqx)
    · rcases List.mem_cons.mp hqy with hqp | hqys
      · exact Or.inl hqp
      · exact Or.inr (List.mem_append_right xs hqys)

-- divisibility of the enlarged period binomial cancels the original factor in the actual difference recurrence.
theorem difference_annihilator_of_binomial_factor {K : Type*} [CommRing K]
    (z : Site → K) (f : Laurent K) (p : Site) (m : ℤ)
    (hann : laurentAct (binomial p * f) z = 0) :
    laurentAct f (difference (m • p) z) = 0 := by
  obtain ⟨A, hA⟩ := binomial_dvd_integer_multiple (K := K) p m
  rw [← laurentAct_binomial, ← laurentAct_mul]
  have he : f * binomial (m • p) = A * (binomial p * f) := by rw [hA]; ring
  rw [he, laurentAct_mul, hann, laurentAct_config_zero]

end KumarNivat
