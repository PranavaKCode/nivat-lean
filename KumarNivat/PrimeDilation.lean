module

public import KumarNivat.LaurentDilation
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Nat.Factorization.Induction

@[expose] public section

namespace KumarNivat

-- frobenius dilates exponents because every coefficient of the prime field is fixed.
theorem prime_power_dilation (p : ℕ) [Fact p.Prime] (f : Laurent (ZMod p)) :
    f ^ p = dilate p f := by
  let : CharP (Laurent (ZMod p)) p := charP_of_injective_algebraMap' (ZMod p) p
  change frobenius (Laurent (ZMod p)) p f = dilate p f
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f h hf hh => simp only [map_add, hf, hh]
  | single u a =>
    rw [frobenius_def, AddMonoidAlgebra.single_pow, ZMod.pow_card, dilate_single]

-- the prime-divisibility and absolute-value bound force the next dilated output to vanish.
theorem annihilator_dilate_by_large_prime (f : Laurent ℤ) (c : Site → ℤ)
    (B m p : ℕ) (hp : p.Prime) (hlarge : B < p)
    (hbound : ∀ n g, (laurentAct (dilate n f) c g).natAbs ≤ B)
    (hann : laurentAct (dilate m f) c = 0) :
    laurentAct (dilate (m * p) f) c = 0 := by
  let : Fact p.Prime := ⟨hp⟩
  let red : ℤ →+* ZMod p := Int.castRingHom (ZMod p)
  let reduced := AddMonoidAlgebra.mapRingHom Site red (dilate m f)
  have hred : laurentAct reduced (red ∘ c) = 0 := by
    rw [laurentAct_mapRing, hann]
    funext g
    exact map_zero red
  have hpower := laurentAct_pow_zero reduced (red ∘ c) hred p hp.pos
  have hfilter : AddMonoidAlgebra.mapRingHom Site red (dilate (m * p) f) = reduced ^ p := by
    rw [prime_power_dilation]
    dsimp only [reduced]
    rw [dilate_mapRing, dilate_comp, Nat.mul_comm p m]
  have hmod : laurentAct (AddMonoidAlgebra.mapRingHom Site red (dilate (m * p) f))
      (red ∘ c) = 0 := hfilter ▸ hpower
  rw [laurentAct_mapRing] at hmod
  funext g
  have hdiv : (p : ℤ) ∣ laurentAct (dilate (m * p) f) c g := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    exact congrFun hmod g
  apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdiv
  simpa only [Int.natAbs_natCast] using (hbound (m * p) g).trans_lt hlarge

-- a prime divisor of an exponent coprime to the factorial bound must exceed that bound.
theorem prime_factor_above_factorial_bound (B n p : ℕ)
    (hp : p.Prime) (hpn : p ∣ n) (hcop : n.Coprime B.factorial) : B < p := by
  by_contra hn
  have hpB : p ∣ B.factorial := Nat.dvd_factorial hp.pos (by omega)
  have hcop' := hcop.of_dvd_left hpn
  exact (hp.coprime_iff_not_dvd.mp hcop') hpB

-- prime induction gives every positive dilation coprime to the uniform factorial bound.
theorem annihilator_dilate_coprime_factorial (f : Laurent ℤ) (c : Site → ℤ)
    (B : ℕ) (hbound : ∀ n g, (laurentAct (dilate n f) c g).natAbs ≤ B)
    (hann : laurentAct f c = 0) :
    ∀ n : ℕ, 0 < n → n.Coprime B.factorial → laurentAct (dilate n f) c = 0 := by
  apply induction_on_primes
  · intro hpos hcop
    omega
  · intro hpos hcop
    simpa only [dilate_one] using hann
  · intro p n hp ih hpos hcop
    have hn : 0 < n := by nlinarith
    have hcopn : n.Coprime B.factorial := hcop.of_dvd_left (Nat.dvd_mul_left n p)
    have hlarge := prime_factor_above_factorial_bound B (p * n) p hp
      (Nat.dvd_mul_right p n) hcop
    rw [Nat.mul_comm p n]
    exact annihilator_dilate_by_large_prime f c B n p hp hlarge hbound (ih hn hcopn)

-- the arithmetic progression used for interpolation consists entirely of annihilating dilations.
theorem annihilator_dilate_progression (f : Laurent ℤ) (c : Site → ℤ)
    (B : ℕ) (hbound : ∀ n g, (laurentAct (dilate n f) c g).natAbs ≤ B)
    (hann : laurentAct f c = 0) (j : ℕ) :
    laurentAct (dilate (1 + j * B.factorial) f) c = 0 := by
  apply annihilator_dilate_coprime_factorial f c B hbound hann
  · omega
  · simp

end KumarNivat
