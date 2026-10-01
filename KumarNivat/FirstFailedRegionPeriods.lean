import KumarNivat.TangentPeriods
import Mathlib.Data.Nat.Find

namespace KumarNivat

-- the shared product recurrence prevents a nonperiodic array's tangent period from reaching the final half-plane.
theorem nonperiodic_no_tangent_halfplane_period {K : Type*} [CommRing K] [Nontrivial K] [NoZeroDivisors K]
    (x : Site → K) (hs : List Site) (hdirs : ∀ h ∈ hs, h ≠ 0)
    (hpairs : hs.Pairwise (fun p q => determinant p q ≠ 0))
    (hann : laurentAct (differenceProduct hs) x = 0)
    (hnot : ¬ ∃ v : Site, v ≠ 0 ∧ IsPeriod x v)
    (a : Site) (hprimitive : Int.gcd a.1 a.2 = 1) (cut : ℤ) (p : ℕ) (hp : 0 < p) :
    ¬ RegionalPeriod x {g | cut ≤ directionNormal a g} ((p : ℤ) • a) := by
  intro hperiod
  have hane : a ≠ 0 := by rintro rfl; simp at hprimitive
  have hnormal := directionNormal_ne_zero a hane
  have hpne : (p : ℤ) • a ≠ 0 := smul_ne_zero (by exact_mod_cast Nat.ne_of_gt hp) hane
  have htangent : directionNormal a ((p : ℤ) • a) = 0 := by
    rw [map_zsmul]
    have ha : directionNormal a a = 0 := by simp [directionNormal, determinant, mul_comm]
    rw [ha, smul_zero]
  obtain ⟨H, hH, _hparallel, hglobal⟩ := global_period_of_tangent_regional_period x hs hdirs hpairs
    hann (directionNormal a) hnormal cut ((p : ℤ) • a) hpne htangent hperiod
  exact hnot ⟨H, hH, hglobal⟩

-- a finite ray-enlargement chain has an actual first failed period, with the same period retained at every preceding stage.
theorem first_failed_region_period {A : Type*} (x : Site → A) (P : ℕ → Set Site) (h : Site) (q : ℕ)
    (hstart : RegionalPeriod x (P 0) h) (hfinal : ¬ RegionalPeriod x (P q) h) :
    ∃ i : ℕ, i < q ∧ (∀ j : ℕ, j ≤ i → RegionalPeriod x (P j) h) ∧
      ¬ RegionalPeriod x (P (i + 1)) h := by
  classical
  let F : ℕ → Prop := fun n => n ≤ q ∧ ¬ RegionalPeriod x (P n) h
  have hex : ∃ n : ℕ, F n := ⟨q, le_rfl, hfinal⟩
  let n := Nat.find hex
  have hspec := Nat.find_spec hex
  have hnq : n ≤ q := hspec.1
  have hn : 0 < n := by
    by_contra hnot
    have hn0 : n = 0 := by omega
    have hbad : ¬ RegionalPeriod x (P n) h := hspec.2
    rw [hn0] at hbad
    exact hbad hstart
  refine ⟨n - 1, by omega, ?_, ?_⟩
  · intro j hj
    by_contra hbad
    exact Nat.find_min hex (by omega : j < n) ⟨by omega, hbad⟩
  · have he : n - 1 + 1 = n := by omega
    rw [he]
    exact hspec.2

end KumarNivat
