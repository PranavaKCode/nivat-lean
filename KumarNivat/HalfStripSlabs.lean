module

public import KumarNivat.PolygonHalfStrips
public import KumarNivat.PolygonNormalBands
public import KumarNivat.HighHalfStripRows

@[expose] public section

namespace KumarNivat

open scoped Pointwise

-- complete primitive rows and finitely many actual polygon bases give one common forward slab.
theorem polygon_half_strip_contains_initial_slab (F : Finset Site) (hF : LatticeConvex F)
    (a : Site) (hprimitive : Int.gcd a.1 a.2 = 1) (τ : Site →+ ℤ) (hτ : τ a = 1)
    (hker : ∀ g : Site, directionNormal a g = 0 → g = τ g • a)
    (C : Set RealPlane) (hsum : latticeHull F = lineInterval 0 (latticeEmbedding a) 0 1 + C)
    (u₀ u₁ : Site) (hu₀ : u₀ ∈ F) (hu₁ : u₁ ∈ F)
    (s : ℤ) (d : ℕ) (h₀ : (-directionNormal a) u₀ = s)
    (hwidth : s + (d : ℤ) - 1 ≤ (-directionNormal a) u₁) :
    ∃ M : ℤ, ∀ g : Site, s ≤ (-directionNormal a) g →
      (-directionNormal a) g ≤ s + (d : ℤ) - 1 → M ≤ τ g → g ∈ polygonHalfStrip F a := by
  classical
  obtain ⟨v, hv⟩ := primitive_basis_of_line_coordinate a τ hτ
  have hva : directionNormal a v = 1 := hv
  have haa : directionNormal a a = 0 := by simp [directionNormal, determinant, mul_comm]
  have hrows (i : Fin d) : ∃ E : Site, E ∈ F ∧ (-directionNormal a) E = s + (i.val : ℤ) := by
    let g := (-(s + (i.val : ℤ))) • v
    have hg : directionNormal a g = -(s + (i.val : ℤ)) := by
      simp only [g, map_zsmul, hva, smul_eq_mul, mul_one]
    have hband : g ∈ normalBand (directionNormal a) (directionNormal a u₁) (directionNormal a u₀) := by
      change -directionNormal a u₀ = s at h₀
      change s + (d : ℤ) - 1 ≤ -directionNormal a u₁ at hwidth
      change directionNormal a u₁ ≤ directionNormal a g ∧ directionNormal a g ≤ directionNormal a u₀
      rw [hg]
      have hi := i.isLt
      omega
    obtain ⟨E, n, he, hE, _hrun⟩ := lattice_row_run_on_intermediate_primitive_level F hF a hprimitive
      1 (by omega) C (by simpa only [Nat.cast_one] using hsum)
      (directionNormal a u₁) (directionNormal a u₀) u₁ u₀ hu₁ hu₀ rfl rfl g hband
    refine ⟨E, hE, ?_⟩
    have hlevel : directionNormal a E = directionNormal a g := by
      rw [he, map_add, map_zsmul, haa, smul_zero, add_zero]
    change -directionNormal a E = s + (i.val : ℤ)
    rw [hlevel, hg, neg_neg]
  choose E hmem hlevel using hrows
  let M : ℤ := ∑ i : Fin d, |τ (E i)|
  refine ⟨M, ?_⟩
  intro g hlow hhigh htail
  change s ≤ -directionNormal a g at hlow
  change -directionNormal a g ≤ s + (d : ℤ) - 1 at hhigh
  let i : Fin d := ⟨(-directionNormal a g - s).toNat, by omega⟩
  have hi : (i.val : ℤ) = -directionNormal a g - s := by dsimp [i]; omega
  have hsamerow : directionNormal a (g - E i) = 0 := by
    have hEi := hlevel i
    change -directionNormal a (E i) = s + (i.val : ℤ) at hEi
    rw [map_sub]
    omega
  have hbound : τ (E i) ≤ M := (le_abs_self _).trans (Finset.single_le_sum
    (fun j (_hj : j ∈ Finset.univ) => abs_nonneg (τ (E j))) (Finset.mem_univ i))
  let n := τ (g - E i)
  have hn : 0 ≤ n := by dsimp [n]; rw [map_sub]; omega
  have hncast : (n.toNat : ℤ) = n := by omega
  refine ⟨(⟨E i, hmem i⟩, n.toNat), ?_⟩
  change E i + (0 + (n.toNat : ℤ)) • a = g
  rw [zero_add, hncast, ← hker (g - E i) hsamerow]
  abel

end KumarNivat
