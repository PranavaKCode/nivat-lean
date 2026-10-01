import KumarNivat.OrbitLanguage
import Mathlib.Data.Nat.Find

namespace KumarNivat

-- the first outer disagreement exists because its distance from the agreement half-plane is an integer.
theorem first_integer_disagreement_level {A : Type*} (x y : Site → A) (ν : Site →+ ℤ)
    (hxy : x ≠ y) (hhalf : ∀ g : Site, 0 ≤ ν g → x g = y g) :
    ∃ β : ℤ, ∃ E : Site, β < 0 ∧ ν E = β ∧ x E ≠ y E ∧
      ∀ g : Site, β + 1 ≤ ν g → x g = y g := by
  classical
  let P : ℕ → Prop := fun n => ∃ g : Site, ν g = -((n : ℤ) + 1) ∧ x g ≠ y g
  have hfailure : ∃ n : ℕ, P n := by
    obtain ⟨g, hneq⟩ := Function.ne_iff.mp hxy
    have hneg : ν g < 0 := by
      by_contra hn
      exact hneq (hhalf g (by omega))
    let n := (-ν g - 1).toNat
    exact ⟨n, g, by dsimp [n]; omega, hneq⟩
  let n := Nat.find hfailure
  obtain ⟨E, hE, hneq⟩ := Nat.find_spec hfailure
  refine ⟨-((n : ℤ) + 1), E, by omega, hE, hneq, ?_⟩
  intro g hg
  by_cases hpos : 0 ≤ ν g
  · exact hhalf g hpos
  · by_contra hne
    let k := (-ν g - 1).toNat
    have hlevel : ν g = -((k : ℤ) + 1) := by dsimp [k]; omega
    have hkn : k < n := by omega
    exact Nat.find_min hfailure hkn ⟨g, hlevel, hne⟩

end KumarNivat
