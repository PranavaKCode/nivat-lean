module

public import KumarNivat.TransportedSeedEqualities

@[expose] public section

namespace KumarNivat

-- every half-strip seed can be moved past any tangent threshold while preserving the same transverse multiple.
theorem far_seed_blocks_from_transported_half_strip {A : Type*} (x : Site → A) (R H : Set Site)
    (a h : Site) (p : ℕ) (hp : 0 < p) (hHR : H ⊆ R)
    (hstableR : ∀ g ∈ R, g + (p : ℤ) • a ∈ R) (hstableH : ∀ g ∈ H, g + h ∈ H)
    (hperiodR : RegionalPeriod x R ((p : ℤ) • a)) (hperiodH : RegionalPeriod x H h)
    (F : Site) (r : ℕ) (hfit : ∀ i : Fin r, F + (i.val : ℤ) • a ∈ H) (D : ℕ) :
    ∀ N : ℤ, ∃ n : ℤ, N ≤ n ∧ ∀ i : Fin r,
      x ((F + (n + (i.val : ℤ)) • a) + (D : ℤ) • h) = x (F + (n + (i.val : ℤ)) • a) := by
  intro N
  let M := N.toNat
  let n : ℤ := (M : ℤ) * (p : ℤ)
  have hM : N ≤ (M : ℤ) := by dsimp [M]; omega
  have hM₀ : (0 : ℤ) ≤ M := Int.natCast_nonneg M
  have hp₁ : (1 : ℤ) ≤ p := by exact_mod_cast hp
  refine ⟨n, by dsimp [n]; nlinarith, ?_⟩
  intro i
  have he := transported_half_strip_multiple_equalities x R H ((p : ℤ) • a) h hHR hstableR hstableH
    hperiodR hperiodH D M (F + (i.val : ℤ) • a) (hfit i)
  have hsite : (F + (i.val : ℤ) • a) + (M : ℤ) • ((p : ℤ) • a) = F + (n + (i.val : ℤ)) • a := by
    dsimp [n]
    rw [smul_smul, add_smul]
    abel
  simpa only [hsite] using he

end KumarNivat
