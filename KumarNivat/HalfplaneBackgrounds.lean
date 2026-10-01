import KumarNivat.RegionalBackground
import KumarNivat.PrimitiveRetention
import KumarNivat.TangentNormals
import KumarNivat.HalfplaneRecurrence

namespace KumarNivat

-- reversing a regional period uses the same equality at the other end of each fitting pair.
theorem regional_period_neg {A : Type*} (x : Site → A) (R : Set Site) (p : Site)
    (hp : RegionalPeriod x R p) : RegionalPeriod x R (-p) := by
  intro g hg hfit
  have hback : g + -p + p = g := by abel
  have he := hp (g + -p) hfit (by simpa only [hback] using hg)
  simpa only [hback] using he.symm

-- positive normal slope transports every lattice site into the closed half-plane.
theorem halfplane_forward_cofinal (ν : Site →+ ℤ) (b : ℤ) (t : Site) (ht : 0 < ν t) :
    ForwardCofinal {g | b ≤ ν g} t := by
  intro g
  let N := (b - ν g).toNat
  refine ⟨N, ?_⟩
  intro n hn
  have hbound : b - ν g ≤ (n : ℤ) := by dsimp [N] at hn; omega
  have hn₀ : (0 : ℤ) ≤ n := Int.natCast_nonneg n
  change b ≤ ν (g + (n : ℤ) • t)
  rw [map_add, map_zsmul, smul_eq_mul]
  nlinarith

-- a globally tangent-periodic array with two independent regional periods has a fully periodic half-plane extension.
theorem halfplane_background_of_tangent_and_regional_periods {A : Type*} (x : Site → A)
    (p : Site) (hprimitive : Int.gcd p.1 p.2 = 1) (l : ℕ) (hl : 0 < l)
    (hglobal : IsPeriod x ((l : ℤ) • p)) (b : ℤ)
    (hfull : FullyRegionallyPeriodic x {g | b ≤ directionNormal p g}) :
    ∃ B : Site → A, FullyPeriodic B ∧
      (∀ g : Site, b ≤ directionNormal p g → B g = x g) ∧ Set.range B ⊆ Set.range x := by
  have hpne : p ≠ 0 := by rintro rfl; simp at hprimitive
  have hν := directionNormal_ne_zero p hpne
  have hp : directionNormal p p = 0 := by simp [directionNormal, determinant, mul_comm]
  obtain ⟨u, v, huv, hu, hv⟩ := hfull
  have hex : ∃ w : Site, directionNormal p w ≠ 0 ∧
      RegionalPeriod x {g | b ≤ directionNormal p g} w := by
    by_cases hun : directionNormal p u = 0
    · have hvn : directionNormal p v ≠ 0 := by
        intro hvn
        exact huv (nonzero_normal_kernel_parallel (directionNormal p) hν u v hun hvn)
      exact ⟨v, hvn, hv⟩
    · exact ⟨u, hun, hu⟩
  obtain ⟨v₀, hv₀, hregional⟩ := hex
  have hexpos : ∃ w : Site, 0 < directionNormal p w ∧
      RegionalPeriod x {g | b ≤ directionNormal p g} w := by
    by_cases hpos : 0 < directionNormal p v₀
    · exact ⟨v₀, hpos, hregional⟩
    · refine ⟨-v₀, ?_, regional_period_neg x _ v₀ hregional⟩
      rw [map_neg]
      omega
  obtain ⟨w, hw, hwp⟩ := hexpos
  let P := (l : ℤ) • p
  have hP : directionNormal p P = 0 := by dsimp [P]; rw [map_zsmul, hp, smul_zero]
  have hdet : determinant P w ≠ 0 := by
    have he : determinant P w = (l : ℤ) * directionNormal p w := by
      change determinant ((l : ℤ) • p) w = (l : ℤ) * determinant p w
      simpa only [one_smul, mul_one] using determinant_zsmul p w (l : ℤ) 1
    rw [he]
    exact mul_ne_zero (by exact_mod_cast Nat.ne_of_gt hl) (ne_of_gt hw)
  have hstableP : ∀ g ∈ {g | b ≤ directionNormal p g}, g + P ∈ {g | b ≤ directionNormal p g} := by
    intro g hg
    change b ≤ directionNormal p (g + P)
    rw [map_add, hP, add_zero]
    exact hg
  have hstablew : ∀ g ∈ {g | b ≤ directionNormal p g}, g + w ∈ {g | b ≤ directionNormal p g} := by
    intro g hg
    change b ≤ directionNormal p g at hg
    change b ≤ directionNormal p (g + w)
    rw [map_add]
    omega
  have hcofinal : ForwardCofinal {g | b ≤ directionNormal p g} (P + w) :=
    halfplane_forward_cofinal (directionNormal p) b (P + w) (by rw [map_add, hP, zero_add]; exact hw)
  exact exists_background_of_regional_periods x {g | b ≤ directionNormal p g} P w hdet
    hstableP hstablew (fun g _hg _hfit => hglobal g) hwp hcofinal

-- two fully periodic backgrounds agreeing inward must agree everywhere by a shared inward period.
theorem fully_periodic_halfplane_agreement {A : Type*} (B C : Site → A)
    (hB : FullyPeriodic B) (hC : FullyPeriodic C) (ν : Site →+ ℤ) (b : ℤ)
    (v : Site) (hv : 0 < ν v) (hagree : ∀ g : Site, b ≤ ν g → B g = C g) : B = C := by
  obtain ⟨a, ha, hBa⟩ := hB.exists_period_multiple v
  obtain ⟨d, hd, hCd⟩ := hC.exists_period_multiple v
  let t := ((a * d : ℕ) : ℤ) • v
  have hBt : IsPeriod B t := by
    simpa only [t, Nat.cast_mul, smul_smul, mul_comm] using hBa.zsmul (d : ℤ)
  have hCt : IsPeriod C t := by
    simpa only [t, Nat.cast_mul, smul_smul] using hCd.zsmul (a : ℤ)
  have ht : 0 < ν t := by
    dsimp [t]
    rw [map_zsmul, smul_eq_mul]
    exact mul_pos (by exact_mod_cast Nat.mul_pos ha hd) hv
  have hcofinal := halfplane_forward_cofinal ν b t ht
  funext g
  obtain ⟨N, hN⟩ := hcofinal g
  have hfit : b ≤ ν (g + (N : ℤ) • t) := hN N le_rfl
  exact (hBt.zsmul (N : ℤ) g).symm.trans ((hagree _ hfit).trans (hCt.zsmul (N : ℤ) g))

end KumarNivat
