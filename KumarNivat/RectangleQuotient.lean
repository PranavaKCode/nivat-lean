module

public import KumarNivat.SupportExtrema

@[expose] public section

namespace KumarNivat

-- rectangle membership keeps both coordinate bounds in the original basis.
theorem mem_rectangle_iff (u : Site) (k n : ℕ) : u ∈ rectangle k n ↔
    0 ≤ u.1 ∧ u.1 < (k : ℤ) ∧ 0 ≤ u.2 ∧ u.2 < (n : ℤ) := by
  simp [rectangle, and_assoc]

-- the cardinality is exactly the area, including empty quotient rectangles.
theorem card_rectangle (k n : ℕ) : (rectangle k n).card = k * n := by
  simp [rectangle, Finset.card_product]

-- swap coordinates only to test the second bound; observation windows are unchanged.
def swapCoordinates : Site →+ Site where
  toFun u := (u.2, u.1)
  map_zero' := rfl
  map_add' _ _ := rfl

-- the coordinate swap loses no lattice information.
theorem swapCoordinates_injective : Function.Injective swapCoordinates := by
  intro u v h
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  exact Prod.ext h₂ h₁

-- these four attained extrema describe the normalized divisor's coordinate widths.
def BoxExtrema {K : Type*} [CommRing K] (φ : Laurent K) (r s : ℕ) : Prop :=
  (∃ u ∈ φ.coeff.support, u.1 = 0) ∧
  (∃ u ∈ φ.coeff.support, u.1 = (r : ℤ)) ∧
  (∃ u ∈ φ.coeff.support, u.2 = 0) ∧
  (∃ u ∈ φ.coeff.support, u.2 = (s : ℤ))

-- section 4's divisor quotient fits the box with both widths subtracted.
theorem quotient_support_rectangle {K : Type*} [Field K]
    (φ q : Laurent K) (hφ : φ ≠ 0) (r s k n : ℕ)
    (hext : BoxExtrema φ r s) (hfit : (φ * q).coeff.support ⊆ rectangle k n) :
    q.coeff.support ⊆ rectangle (k - r) (n - s) := by
  intro v hv
  have hq : q ≠ 0 := by
    intro hz
    have hzero : q.coeff v = 0 := by simp [hz]
    exact (Finsupp.mem_support_iff.mp hv) hzero
  obtain ⟨⟨xl, hxl, hxl0⟩, ⟨xu, hxu, hxur⟩, ⟨yl, hyl, hyl0⟩, ⟨yu, hyu, hyus⟩⟩ := hext
  have hcoords (w : Site) (hw : w ∈ (φ * q).coeff.support) :
      0 ≤ w.1 ∧ w.1 < (k : ℤ) ∧ 0 ≤ w.2 ∧ w.2 < (n : ℤ) :=
    (mem_rectangle_iff w k n).mp (hfit hw)
  have hxu' := coordinate_sum_bound φ q hφ hq (AddMonoidHom.id Site)
    Function.injective_id ((k : ℤ) - 1) (by
      intro w hw
      change w.1 ≤ (k : ℤ) - 1
      have hc := hcoords w hw
      omega) xu hxu v hv
  have hxl' := coordinate_sum_bound φ q hφ hq
    (AddEquiv.neg Site).toAddMonoidHom (AddEquiv.neg Site).injective 0 (by
      intro w hw
      change -w.1 ≤ 0
      have hc := hcoords w hw
      omega) xl hxl v hv
  have hyu' := coordinate_sum_bound φ q hφ hq swapCoordinates swapCoordinates_injective
    ((n : ℤ) - 1) (by
      intro w hw
      change w.2 ≤ (n : ℤ) - 1
      have hc := hcoords w hw
      omega) yu hyu v hv
  let negSwap := (AddEquiv.neg Site).toAddMonoidHom.comp swapCoordinates
  have hyl' := coordinate_sum_bound φ q hφ hq negSwap
    ((AddEquiv.neg Site).injective.comp swapCoordinates_injective) 0 (by
      intro w hw
      change -w.2 ≤ 0
      have hc := hcoords w hw
      omega) yl hyl v hv
  change xu.1 + v.1 ≤ (k : ℤ) - 1 at hxu'
  change -(xl.1 + v.1) ≤ 0 at hxl'
  change yu.2 + v.2 ≤ (n : ℤ) - 1 at hyu'
  change -(yl.2 + v.2) ≤ 0 at hyl'
  rw [hxl0] at hxl'
  rw [hxur] at hxu'
  rw [hyl0] at hyl'
  rw [hyus] at hyu'
  apply (mem_rectangle_iff v (k - r) (n - s)).mpr
  have hrk : r ≤ k := by omega
  have hsn : s ≤ n := by omega
  rw [Nat.cast_sub hrk, Nat.cast_sub hsn]
  omega

end KumarNivat
