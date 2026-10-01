import KumarNivat.BinomialCoprime
import Mathlib.Data.Int.GCD

namespace KumarNivat

-- bezout coefficients recover every integer point on a primitive lattice line.
theorem primitive_direction_coordinate (p : Site) (hgcd : Int.gcd p.1 p.2 = 1) :
    ∃ τ : Site →+ ℤ, τ p = 1 ∧
      ∀ g : Site, directionNormal p g = 0 → g = τ g • p := by
  let A := Int.gcdA p.1 p.2
  let B := Int.gcdB p.1 p.2
  let τ : Site →+ ℤ :=
    { toFun := fun g => A * g.1 + B * g.2
      map_zero' := by simp
      map_add' := by intro g l; simp; ring }
  have ht : τ p = 1 := by
    have hb := Int.gcd_eq_gcd_ab p.1 p.2
    rw [hgcd, Nat.cast_one] at hb
    dsimp [τ, A, B]
    nlinarith [hb]
  let q : Site := (-B, A)
  have hdet : determinant p q = 1 := by
    change p.1 * A - p.2 * (-B) = 1
    change A * p.1 + B * p.2 = 1 at ht
    nlinarith [ht]
  refine ⟨τ, ht, ?_⟩
  intro g hg
  have hi := determinant_smul_identity p q g
  have hcoord : determinant g q = τ g := by
    simp only [determinant, q, τ, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    ring
  change determinant p g = 0 at hg
  simpa only [hdet, one_smul, hcoord, hg, zero_smul, add_zero] using hi

-- remove the coordinate gcd to construct the primitive direction of any nonzero vector.
theorem exists_primitive_direction_coordinate (h : Site) (hh : h ≠ 0) :
    ∃ p : Site, ∃ a : ℕ, 0 < a ∧ h = (a : ℤ) • p ∧ p ≠ 0 ∧
      ∃ τ : Site →+ ℤ, τ p = 1 ∧
        ∀ g : Site, directionNormal p g = 0 → g = τ g • p := by
  have hgcd : 0 < Int.gcd h.1 h.2 := by
    by_contra hn
    have hz : Int.gcd h.1 h.2 = 0 := by omega
    have hx := Int.gcd_dvd_left h.1 h.2
    have hy := Int.gcd_dvd_right h.1 h.2
    rw [hz, Nat.cast_zero] at hx hy
    exact hh (Prod.ext (zero_dvd_iff.mp hx) (zero_dvd_iff.mp hy))
  obtain ⟨x, y, hxy, hx, hy⟩ := Int.exists_gcd_one hgcd
  let p : Site := (x, y)
  let a := Int.gcd h.1 h.2
  have he : h = (a : ℤ) • p := by
    ext <;> simp only [p, a, zsmul_eq_mul]
    · exact hx.trans (mul_comm _ _)
    · exact hy.trans (mul_comm _ _)
  have hp : p ≠ 0 := by
    intro hz
    exact hh (by rw [he, hz, smul_zero])
  obtain ⟨τ, ht, hker⟩ := primitive_direction_coordinate p hxy
  exact ⟨p, a, hgcd, he, hp, τ, ht, hker⟩

-- normal and primitive line coordinate together distinguish every lattice site.
theorem normal_line_coordinate_injective (p : Site) (τ : Site →+ ℤ)
    (hker : ∀ g : Site, directionNormal p g = 0 → g = τ g • p) :
    Function.Injective ((directionNormal p).prod τ) := by
  intro x y he
  have hn : directionNormal p x = directionNormal p y := congrArg Prod.fst he
  have ht : τ x = τ y := congrArg Prod.snd he
  have hdiff := hker (x - y) (by rw [map_sub, hn, sub_self])
  have hz : x - y = 0 := by
    rw [map_sub, ht, sub_self, zero_smul] at hdiff
    exact hdiff
  exact sub_eq_zero.mp hz

end KumarNivat
