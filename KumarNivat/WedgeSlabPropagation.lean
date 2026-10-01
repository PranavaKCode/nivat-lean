import KumarNivat.HalfplaneRecurrence

namespace KumarNivat

-- bounded positive normal steps propagate the initial finite slab down the actual wedge.
theorem zero_on_wedge_of_initial_slab {K : Type*} [CommRing K] [NoZeroDivisors K]
    (δ : Site → K) (f : Laurent K) (hann : laurentAct f δ = 0) (hconst : f.coeff 0 ≠ 0)
    (ν μ : Site →+ ℤ) (d : ℕ)
    (hsteps : ∀ u ∈ f.coeff.support, u ≠ 0 → 1 ≤ ν u ∧ ν u ≤ (d : ℤ))
    (hslope : ∀ u ∈ f.coeff.support, 0 ≤ μ u) (top A : ℤ)
    (hseed : ∀ g : Site, top - (d : ℤ) + 1 ≤ ν g → ν g ≤ top → A ≤ μ g → δ g = 0) :
    ∀ g : Site, ν g ≤ top → A ≤ μ g → δ g = 0 := by
  classical
  have hlevels (n : ℕ) : ∀ g : Site, ν g = top - (n : ℤ) → A ≤ μ g → δ g = 0 := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro g hg hμg
      by_cases hnd : n < d
      · exact hseed g (by omega) (by omega) hμg
      · have hdn : d ≤ n := by omega
        have heval : laurentAct f δ g = f.coeff 0 * δ g := by
          unfold laurentAct act Finsupp.sum
          have he : (∑ u ∈ f.coeff.support, f.coeff u * δ (g + u)) = f.coeff 0 * δ (g + 0) := by
            apply Finset.sum_eq_single 0
            · intro u hu hune
              have hνu := hsteps u hu hune
              have hμu := hslope u hu
              let k := ((n : ℤ) - ν u).toNat
              have hkn : k < n := by dsimp [k]; omega
              have hkcast : (k : ℤ) = (n : ℤ) - ν u := by dsimp [k]; omega
              have hpoint : ν (g + u) = top - (k : ℤ) := by rw [map_add, hg, hkcast]; omega
              have hμpoint : A ≤ μ (g + u) := by rw [map_add]; omega
              rw [ih k hkn (g + u) hpoint hμpoint, mul_zero]
            · intro hn
              exact (hn (Finsupp.mem_support_iff.mpr hconst)).elim
          simpa only [add_zero] using he
        have hz := congrFun hann g
        rw [heval] at hz
        exact (mul_eq_zero.mp hz).resolve_left hconst
  intro g hg hμg
  exact hlevels (top - ν g).toNat g (by omega) hμg

end KumarNivat

