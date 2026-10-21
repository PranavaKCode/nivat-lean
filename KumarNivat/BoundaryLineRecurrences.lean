module

public import KumarNivat.ExposedOperators
public import KumarNivat.FacetRecurrences

@[expose] public section

namespace KumarNivat

-- a complete line recurrence extends a zero tail to every integer index.
theorem zero_of_bilateral_recurrence_tail {K : Type*} [CommRing K] [NoZeroDivisors K]
    (t : ℕ) (α : Fin (t + 1) → K) (a : ℤ → K) (hfirst : α 0 ≠ 0)
    (hrec : LineRecurrence t α a) (N : ℤ) (htail : ∀ n : ℤ, N ≤ n → a n = 0) :
    ∀ n : ℤ, a n = 0 := by
  intro n
  exact zero_of_ray_recurrence_tail t α a n N hfirst (fun k _hk => hrec k) htail n le_rfl

-- the same finite operator acts linearly on differences of two configurations.
theorem laurentAct_config_sub {K : Type*} [CommRing K]
    (f : Laurent K) (x y : Site → K) : laurentAct f (x - y) = laurentAct f x - laurentAct f y :=
  (actLinear f.coeff).map_sub x y

-- the actual exposed coefficients turn a boundary tail into zero on the full lattice line.
theorem zero_on_boundary_of_halfplane_and_line_tail {K : Type*} [CommRing K] [NoZeroDivisors K]
    (δ : Site → K) (f : Laurent K) (hf : f ≠ 0) (hann : laurentAct f δ = 0)
    (ν : Site →+ ℤ) (hν : ν ≠ 0) (p : Site) (hp : ν p = 0)
    (hprimitive : Int.gcd p.1 p.2 = 1) (β : ℤ) (E : Site) (hE : ν E = β)
    (hhalf : ∀ g : Site, β + 1 ≤ ν g → δ g = 0)
    (N : ℤ) (htail : ∀ n : ℤ, N ≤ n → δ (E + n • p) = 0) :
    ∀ g : Site, ν g = β → δ g = 0 := by
  classical
  have hpne : p ≠ 0 := by rintro rfl; simp at hprimitive
  have hsupp : f.coeff.support.Nonempty := Finsupp.support_nonempty_iff.mpr
    (fun hz => hf (AddMonoidAlgebra.coeff_injective hz))
  obtain ⟨v, hv, hmin⟩ := f.coeff.support.exists_min_image ν hsupp
  obtain ⟨q₀, t, α, hfirst, _hlast, hq₀, hdecomp, hstrict⟩ :=
    exposed_line_decomposition_of_supporting_level f ν hν (ν v) hmin v p hpne hprimitive hp hv rfl
  have hrec : LineRecurrence t α (fun n => δ (E + n • p)) := by
    intro n
    apply exposed_line_recurrence_at δ f (f - exposedOperator f ν (ν v)) q₀ p E t α hdecomp hann n
    intro u hu
    have hi := hstrict u hu
    have hbound : β + 1 ≤ ν ((E + n • p - q₀) + u) := by
      rw [map_add, map_sub, map_add, map_zsmul, hE, hp, smul_zero, add_zero, hq₀]
      omega
    exact hhalf _ hbound
  have hzero := zero_of_bilateral_recurrence_tail t α (fun n => δ (E + n • p)) hfirst hrec N htail
  obtain ⟨τ, _hτ, hker⟩ := primitive_direction_coordinate p hprimitive
  intro g hg
  have hflat : ν (g - E) = 0 := by rw [map_sub, hg, hE, sub_self]
  have he := hker (g - E) (nonzero_normal_kernel_parallel ν hν p (g - E) hp hflat)
  have hsite : g = E + τ (g - E) • p := by rw [← he]; abel
  rw [hsite]
  exact hzero (τ (g - E))

-- shared annihilation and inward agreement make a boundary equality tail determine the entire line.
theorem boundary_agreement_of_inward_halfplane_and_tail {K : Type*} [CommRing K] [NoZeroDivisors K]
    (x y : Site → K) (f : Laurent K) (hf : f ≠ 0)
    (hx : laurentAct f x = 0) (hy : laurentAct f y = 0)
    (ν : Site →+ ℤ) (hν : ν ≠ 0) (p : Site) (hp : ν p = 0)
    (hprimitive : Int.gcd p.1 p.2 = 1) (β : ℤ) (E : Site) (hE : ν E = β)
    (hhalf : ∀ g : Site, β + 1 ≤ ν g → x g = y g)
    (N : ℤ) (htail : ∀ n : ℤ, N ≤ n → x (E + n • p) = y (E + n • p)) :
    ∀ g : Site, ν g = β → x g = y g := by
  have hann : laurentAct f (x - y) = 0 := by rw [laurentAct_config_sub, hx, hy, sub_self]
  have hz := zero_on_boundary_of_halfplane_and_line_tail (x - y) f hf hann ν hν p hp hprimitive β E hE
    (fun g hg => sub_eq_zero.mpr (hhalf g hg)) N (fun n hn => sub_eq_zero.mpr (htail n hn))
  exact fun g hg => sub_eq_zero.mp (hz g hg)

end KumarNivat
