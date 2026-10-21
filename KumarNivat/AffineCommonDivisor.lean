module

public import KumarNivat.SquarefreeProducts

@[expose] public section

namespace KumarNivat

-- a sufficiently steep integer slope avoids every direction in the finite factor list.
theorem exists_transverse_integer_direction (hs : List Site) (hdirs : ∀ h ∈ hs, h ≠ 0) :
    ∃ w : Site, w ≠ 0 ∧ ∀ h ∈ hs, determinant w h ≠ 0 := by
  classical
  let N := hs.toFinset.sup (fun h => h.2.natAbs) + 1
  have hN : (0 : ℤ) < N := by dsimp [N]; positivity
  refine ⟨(1, (N : ℤ)), ?_, ?_⟩
  · intro hz
    have he := congrArg Prod.fst hz
    norm_num at he
  · intro h hh
    have hsup := Finset.le_sup (f := fun h : Site => h.2.natAbs) (List.mem_toFinset.mpr hh)
    have hbound : (h.2.natAbs : ℤ) < (N : ℤ) := by
      exact_mod_cast (show h.2.natAbs < N by dsimp [N]; omega)
    have hhi : h.2 ≤ (h.2.natAbs : ℤ) := Int.le_natAbs
    have hlo : -h.2 ≤ (h.2.natAbs : ℤ) := by
      have he : -h.2 ≤ ((-h.2).natAbs : ℤ) := Int.le_natAbs
      simpa only [Int.natAbs_neg] using he
    change (1 : ℤ) * h.2 - (N : ℤ) * h.1 ≠ 0
    rw [one_mul]
    by_cases hh₁ : h.1 = 0
    · have hh₂ : h.2 ≠ 0 := by intro hz; exact hdirs h hh (Prod.ext hh₁ hz)
      simpa only [hh₁, mul_zero, sub_zero] using hh₂
    · intro he
      by_cases hpos : 0 < h.1
      · have hge : 1 ≤ h.1 := by omega
        nlinarith
      · have hle : h.1 ≤ -1 := by omega
        nlinarith

-- the common divisor of annihilators also divides every operator with constant output.
theorem common_divisor_divides_constant_output {K : Type*} [Field K]
    (c : Site → K) (φ : Laurent K) (hs : List Site) (hdirs : ∀ h ∈ hs, h ≠ 0)
    (hφprod : φ ∣ differenceProduct hs)
    (hcommon : ∀ f : Laurent K, laurentAct f c = 0 → φ ∣ f) :
    ∀ f : Laurent K, (∃ κ : K, laurentAct f c = fun _ => κ) → φ ∣ f := by
  obtain ⟨w, _hw, hind⟩ := exists_transverse_integer_direction hs hdirs
  have hrel : IsRelPrime φ (binomial w) :=
    (binomial_relPrime_differenceProduct (K := K) w hs hind).symm.of_dvd_left hφprod
  intro f hf
  obtain ⟨κ, hconstant⟩ := hf
  have hann : laurentAct (binomial w * f) c = 0 := by
    rw [laurentAct_mul, hconstant, laurentAct_binomial]
    funext g
    exact sub_self κ
  exact hrel.dvd_of_dvd_mul_left (hcommon (binomial w * f) hann)

end KumarNivat
