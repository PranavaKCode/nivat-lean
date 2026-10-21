module

public import KumarNivat.HalfStripSlabs
public import KumarNivat.ExtremalSlopeFactors
public import KumarNivat.WedgeSlabPropagation

@[expose] public section

namespace KumarNivat

open scoped Pointwise

-- clearing the slope denominator gives one integer cutoff that places the whole seed slab in the known row tails.
theorem sloping_normal_initial_slab_cutoff (ν τ : Site →+ ℤ) (p : Site) (hp : 0 < ν p)
    (s M : ℤ) (d : ℕ) :
    ∃ A : ℤ, ∀ g : Site, s ≤ ν g → ν g ≤ s + (d : ℤ) - 1 →
      A ≤ slopingNormal ν τ p g → M ≤ τ g := by
  classical
  let C : ℤ := ∑ i : Fin d, |τ p * (s + (i.val : ℤ))|
  refine ⟨ν p * M + C, ?_⟩
  intro g hlow hhigh hslope
  let i : Fin d := ⟨(ν g - s).toNat, by omega⟩
  have hi : s + (i.val : ℤ) = ν g := by dsimp [i]; omega
  have hbound : -τ p * ν g ≤ C := by
    have hterm : |τ p * (s + (i.val : ℤ))| ≤ C := Finset.single_le_sum
      (fun j (_hj : j ∈ Finset.univ) => abs_nonneg (τ p * (s + (j.val : ℤ)))) (Finset.mem_univ i)
    rw [hi] at hterm
    have hneg : -τ p * ν g ≤ |τ p * ν g| := by simpa only [neg_mul] using neg_le_abs (τ p * ν g)
    exact hneg.trans hterm
  change ν p * M + C ≤ ν p * τ g - τ p * ν g at hslope
  nlinarith

-- the actual finite polygon supplies the seed and the actual laurent recurrence propagates it through the downward wedge.
theorem wedge_zero_from_polygon_half_strip {K : Type*} [CommRing K] [NoZeroDivisors K]
    (δ : Site → K) (f : Laurent K) (hann : laurentAct f δ = 0) (hconst : f.coeff 0 ≠ 0)
    (F : Finset Site) (hF : LatticeConvex F) (a : Site) (hprimitive : Int.gcd a.1 a.2 = 1)
    (τ : Site →+ ℤ) (hτ : τ a = 1)
    (hker : ∀ g : Site, directionNormal a g = 0 → g = τ g • a)
    (C : Set RealPlane) (hsum : latticeHull F = lineInterval 0 (latticeEmbedding a) 0 1 + C)
    (u₀ u₁ : Site) (hu₀ : u₀ ∈ F) (hu₁ : u₁ ∈ F) (s : ℤ) (d : ℕ)
    (h₀ : (-directionNormal a) u₀ = s)
    (hwidth : s + (d : ℤ) - 1 ≤ (-directionNormal a) u₁)
    (p : Site) (hp : 0 < (-directionNormal a) p)
    (hsteps : ∀ u ∈ f.coeff.support, u ≠ 0 →
      1 ≤ (-directionNormal a) u ∧ (-directionNormal a) u ≤ (d : ℤ))
    (hslope : ∀ u ∈ f.coeff.support, 0 ≤ slopingNormal (-directionNormal a) τ p u)
    (hzero : ∀ g ∈ polygonHalfStrip F a, δ g = 0) :
    ∃ A : ℤ, ∀ g : Site, (-directionNormal a) g ≤ s + (d : ℤ) - 1 →
      A ≤ slopingNormal (-directionNormal a) τ p g → δ g = 0 := by
  obtain ⟨M, hslab⟩ := polygon_half_strip_contains_initial_slab F hF a hprimitive τ hτ hker
    C hsum u₀ u₁ hu₀ hu₁ s d h₀ hwidth
  obtain ⟨A, hcut⟩ := sloping_normal_initial_slab_cutoff (-directionNormal a) τ p hp s M d
  refine ⟨A, zero_on_wedge_of_initial_slab δ f hann hconst (-directionNormal a)
    (slopingNormal (-directionNormal a) τ p) d hsteps hslope (s + (d : ℤ) - 1) A ?_⟩
  intro g hlow hhigh hs
  have hg : s ≤ (-directionNormal a) g := by omega
  exact hzero g (hslab g hg hhigh (hcut g hg hhigh hs))

end KumarNivat
