module

public import KumarNivat.RegionalBackground
public import KumarNivat.PrimitiveDirections

@[expose] public section

namespace KumarNivat

-- a common forward regional period carries any point of the row into an agreement tail.
theorem regional_row_agreement_of_periodic_tail {A : Type*} (x y : Site → A)
    (R : Set Site) (a : Site) (hprimitive : Int.gcd a.1 a.2 = 1) (p : ℕ) (hp : 0 < p)
    (hstable : ∀ g ∈ R, g + (p : ℤ) • a ∈ R)
    (hxper : RegionalPeriod x R ((p : ℤ) • a)) (hyper : RegionalPeriod y R ((p : ℤ) • a))
    (E : Site) (N : ℤ) (htail : ∀ n : ℤ, N ≤ n → x (E + n • a) = y (E + n • a)) :
    ∀ g ∈ R, directionNormal a g = directionNormal a E → x g = y g := by
  obtain ⟨τ, _hτ, hker⟩ := primitive_direction_coordinate a hprimitive
  intro g hg hnormal
  have hdiff := hker (g - E) (by rw [map_sub, hnormal, sub_self])
  let k := τ (g - E)
  have hgsite : g = E + k • a := by dsimp [k]; rw [← hdiff]; abel
  let M := (N - k).toNat
  have hM : N - k ≤ (M : ℤ) := by dsimp [M]; omega
  have hM₀ : (0 : ℤ) ≤ M := Int.natCast_nonneg M
  have hp₁ : (1 : ℤ) ≤ p := by exact_mod_cast hp
  have hindex : N ≤ k + (M : ℤ) * (p : ℤ) := by nlinarith
  have hsite : g + (M : ℤ) • ((p : ℤ) • a) = E + (k + (M : ℤ) * (p : ℤ)) • a := by
    rw [hgsite, smul_smul, add_smul]
    abel
  have he : x (g + (M : ℤ) • ((p : ℤ) • a)) = y (g + (M : ℤ) • ((p : ℤ) • a)) := by
    rw [hsite]
    exact htail _ hindex
  have hx := (regional_period_forward_multiples x R ((p : ℤ) • a) hstable hxper M g hg).2
  have hy := (regional_period_forward_multiples y R ((p : ℤ) • a) hstable hyper M g hg).2
  exact hx.symm.trans (he.trans hy)

-- a full period's worth of equal sites starts the tail and therefore determines the entire regional row.
theorem regional_row_agreement_of_periodic_block {A : Type*} (x y : Site → A)
    (R : Set Site) (a : Site) (hprimitive : Int.gcd a.1 a.2 = 1) (p : ℕ) (hp : 0 < p)
    (hstable : ∀ g ∈ R, g + (p : ℤ) • a ∈ R)
    (hxper : RegionalPeriod x R ((p : ℤ) • a)) (hyper : RegionalPeriod y R ((p : ℤ) • a))
    (E : Site) (b : ℤ) (hfit : ∀ i : Fin p, E + (b + (i.val : ℤ)) • a ∈ R)
    (hseed : ∀ i : Fin p, x (E + (b + (i.val : ℤ)) • a) = y (E + (b + (i.val : ℤ)) • a)) :
    ∀ g ∈ R, directionNormal a g = directionNormal a E → x g = y g := by
  apply regional_row_agreement_of_periodic_tail x y R a hprimitive p hp hstable hxper hyper E b
  intro n hn
  let q := (n - b).toNat
  let i : Fin p := ⟨q % p, Nat.mod_lt q hp⟩
  let d := q / p
  have hq : (q : ℤ) = n - b := by dsimp [q]; omega
  have hi : (i.val : ℤ) + (p : ℤ) * (d : ℤ) = (q : ℤ) := by
    dsimp [i, d]
    exact_mod_cast Nat.mod_add_div q p
  have hrep : n = b + (i.val : ℤ) + (d : ℤ) * (p : ℤ) := by
    rw [mul_comm] at hi
    omega
  have hsite : E + n • a = (E + (b + (i.val : ℤ)) • a) + (d : ℤ) • ((p : ℤ) • a) := by
    rw [hrep, add_smul, smul_smul, add_assoc]
  rw [hsite]
  have hx := (regional_period_forward_multiples x R ((p : ℤ) • a) hstable hxper d
    (E + (b + (i.val : ℤ)) • a) (hfit i)).2
  have hy := (regional_period_forward_multiples y R ((p : ℤ) • a) hstable hyper d
    (E + (b + (i.val : ℤ)) • a) (hfit i)).2
  exact hx.trans ((hseed i).trans hy.symm)

end KumarNivat
