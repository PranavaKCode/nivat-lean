module

public import KumarNivat.LaurentAlgebra

@[expose] public section

namespace KumarNivat

-- finite convolution is additive in the operator.
theorem laurentAct_add {K : Type*} [CommRing K] (f h : Laurent K) (c : Site → K) :
    laurentAct (f + h) c = laurentAct f c + laurentAct h c := by
  funext g
  exact (laurentActAt c g).map_add f h

-- a finite operator sum acts term by term.
theorem laurentAct_sum {K I : Type*} [CommRing K] (S : Finset I)
    (f : I → Laurent K) (c : Site → K) :
    laurentAct (∑ i ∈ S, f i) c = ∑ i ∈ S, laurentAct (f i) c := by
  classical
  funext g
  change laurentActAt c g (∑ i ∈ S, f i) = _
  rw [map_sum]
  exact (Finset.sum_apply g S (fun i => laurentAct (f i) c)).symm

-- coefficient-ring maps commute with the action, including reduction modulo a prime.
theorem laurentAct_mapRing {K L : Type*} [CommRing K] [CommRing L]
    (ρ : K →+* L) (f : Laurent K) (c : Site → K) :
    laurentAct (AddMonoidAlgebra.mapRingHom Site ρ f) (ρ ∘ c) = ρ ∘ laurentAct f c := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => funext g; simp
  | add f h hf hh =>
    funext g
    simpa only [map_add, laurentAct_add, Pi.add_apply, Function.comp_apply]
      using congrArg₂ (fun x y : L => x + y) (congrFun hf g) (congrFun hh g)
  | single u a =>
    funext g
    simp [laurentAct_single, Function.comp_apply]

-- a positive power of an annihilator remains an annihilator.
theorem laurentAct_pow_zero {K : Type*} [CommRing K] (f : Laurent K) (c : Site → K)
    (hann : laurentAct f c = 0) (n : ℕ) (hn : 0 < n) : laurentAct (f ^ n) c = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [pow_succ, laurentAct_mul, hann, laurentAct_config_zero]

end KumarNivat
