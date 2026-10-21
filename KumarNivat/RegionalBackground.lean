module

public import KumarNivat.WedgeSaturation

@[expose] public section

namespace KumarNivat

-- every lattice site eventually enters the region along this forward direction.
def ForwardCofinal (R : Set Site) (t : Site) : Prop :=
  ∀ g, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → g + (n : ℤ) • t ∈ R

-- a forward-stable region allows repeated use of a regional period.
theorem regional_period_forward_multiples {A : Type*} (x : Site → A) (R : Set Site)
    (t : Site) (hstable : ∀ g ∈ R, g + t ∈ R) (hp : RegionalPeriod x R t) :
    ∀ n : ℕ, ∀ g ∈ R, g + (n : ℤ) • t ∈ R ∧ x (g + (n : ℤ) • t) = x g := by
  intro n
  induction n with
  | zero => intro g hg; simpa using (show g ∈ R ∧ x g = x g from ⟨hg, rfl⟩)
  | succ n ih =>
    intro g hg
    obtain ⟨hn, he⟩ := ih g hg
    have hnext := hstable _ hn
    have hperiod := hp _ hn hnext
    have hsite : g + ((n + 1 : ℕ) : ℤ) • t = (g + (n : ℤ) • t) + t := by
      simp [add_smul, add_assoc]
    rw [hsite]
    exact ⟨hnext, hperiod.trans he⟩

-- stabilized values along an interior recession direction define the global background.
theorem exists_background_of_regional_periods {A : Type*} (x : Site → A) (R : Set Site)
    (h₁ h₂ : Site) (hdet : determinant h₁ h₂ ≠ 0)
    (hstable₁ : ∀ g ∈ R, g + h₁ ∈ R) (hstable₂ : ∀ g ∈ R, g + h₂ ∈ R)
    (hp₁ : RegionalPeriod x R h₁) (hp₂ : RegionalPeriod x R h₂)
    (hcofinal : ForwardCofinal R (h₁ + h₂)) :
    ∃ B : Site → A, FullyPeriodic B ∧ (∀ g ∈ R, B g = x g) ∧
      Set.range B ⊆ Set.range x := by
  classical
  let t := h₁ + h₂
  have hstable : ∀ g ∈ R, g + t ∈ R := by
    intro g hg
    simpa only [t, ← add_assoc] using hstable₂ (g + h₁) (hstable₁ g hg)
  have hpt : RegionalPeriod x R t := by
    intro g hg hgt
    have hfirst := hstable₁ g hg
    have hsecond := hstable₂ _ hfirst
    change x (g + (h₁ + h₂)) = x g
    rw [← add_assoc, hp₂ _ hfirst hsecond, hp₁ _ hg hfirst]
  let N (g : Site) : ℕ := Classical.choose (hcofinal g)
  have hN (g : Site) (n : ℕ) (hn : N g ≤ n) : g + (n : ℤ) • t ∈ R :=
    Classical.choose_spec (hcofinal g) n hn
  let B (g : Site) : A := x (g + (N g : ℤ) • t)
  have hvalue (g : Site) (n : ℕ) (hn : N g ≤ n) : B g = x (g + (n : ℤ) • t) := by
    have he := (regional_period_forward_multiples x R t hstable hpt
      (n - N g) (g + (N g : ℤ) • t) (hN g (N g) le_rfl)).2
    have hsite : (g + (N g : ℤ) • t) + ((n - N g : ℕ) : ℤ) • t =
        g + (n : ℤ) • t := by
      rw [add_assoc, ← add_smul, Nat.cast_sub hn]
      rw [show (N g : ℤ) + ((n : ℤ) - (N g : ℤ)) = (n : ℤ) by omega]
    rw [hsite] at he
    exact he.symm
  have hperiod (h : Site) (hp : RegionalPeriod x R h) : IsPeriod B h := by
    intro g
    let n := max (N g) (N (g + h))
    have hng : N g ≤ n := le_max_left _ _
    have hngh : N (g + h) ≤ n := le_max_right _ _
    rw [hvalue (g + h) n hngh, hvalue g n hng]
    have hg := hN g n hng
    have hgh := hN (g + h) n hngh
    have hsite : (g + h) + (n : ℤ) • t = (g + (n : ℤ) • t) + h := by abel
    rw [hsite] at hgh ⊢
    exact hp _ hg hgh
  refine ⟨B, ⟨h₁, h₂, hdet, hperiod h₁ hp₁, hperiod h₂ hp₂⟩, ?_, ?_⟩
  · intro g hg
    exact (regional_period_forward_multiples x R t hstable hpt (N g) g hg).2
  · rintro y ⟨g, rfl⟩
    exact ⟨g + (N g : ℤ) • t, rfl⟩

-- positive slopes along both wedge normals give the required forward cofinality.
theorem wedge_forward_cofinal (ell μ : Site →+ ℤ) (a b : ℤ) (t : Site)
    (hell : 0 < ell t) (hμ : 0 < μ t) :
    ForwardCofinal {g | a ≤ ell g ∧ b ≤ μ g} t := by
  intro g
  let N := (a - ell g).natAbs + (b - μ g).natAbs + 1
  refine ⟨N, ?_⟩
  intro n hn
  have hdiff₁ : a - ell g ≤ ((a - ell g).natAbs : ℤ) := Int.le_natAbs
  have hdiff₂ : b - μ g ≤ ((b - μ g).natAbs : ℤ) := Int.le_natAbs
  have hN₁ : (a - ell g).natAbs ≤ n := by dsimp [N] at hn; omega
  have hN₂ : (b - μ g).natAbs ≤ n := by dsimp [N] at hn; omega
  have hbound₁ : a - ell g ≤ (n : ℤ) := hdiff₁.trans (by exact_mod_cast hN₁)
  have hbound₂ : b - μ g ≤ (n : ℤ) := hdiff₂.trans (by exact_mod_cast hN₂)
  have hn₀ : (0 : ℤ) ≤ n := by positivity
  change a ≤ ell (g + (n : ℤ) • t) ∧ b ≤ μ (g + (n : ℤ) • t)
  rw [map_add, map_zsmul, map_add, map_zsmul]
  simp only [zsmul_eq_mul, Int.cast_id]
  constructor <;> nlinarith

-- the paper's regional periods give an actual fully periodic background on a rational wedge.
theorem exists_background_on_wedge {A : Type*} (x : Site → A)
    (ell μ : Site →+ ℤ) (a b : ℤ) (h₁ h₂ : Site)
    (hdet : determinant h₁ h₂ ≠ 0)
    (hell₁ : 0 ≤ ell h₁) (hell₂ : 0 ≤ ell h₂)
    (hμ₁ : 0 ≤ μ h₁) (hμ₂ : 0 ≤ μ h₂)
    (hell : 0 < ell (h₁ + h₂)) (hμ : 0 < μ (h₁ + h₂))
    (hp₁ : RegionalPeriod x {g | a ≤ ell g ∧ b ≤ μ g} h₁)
    (hp₂ : RegionalPeriod x {g | a ≤ ell g ∧ b ≤ μ g} h₂) :
    ∃ B : Site → A, FullyPeriodic B ∧ AgreesOnWedge ell μ a b x B ∧
      Set.range B ⊆ Set.range x := by
  have hstable (h : Site) (he : 0 ≤ ell h) (hm : 0 ≤ μ h) :
      ∀ g ∈ {g | a ≤ ell g ∧ b ≤ μ g}, g + h ∈ {g | a ≤ ell g ∧ b ≤ μ g} := by
    intro g hg
    change a ≤ ell g ∧ b ≤ μ g at hg
    change a ≤ ell (g + h) ∧ b ≤ μ (g + h)
    rw [map_add, map_add]
    exact ⟨by omega, by omega⟩
  obtain ⟨B, hB, hagree, hrange⟩ := exists_background_of_regional_periods x _ h₁ h₂ hdet
    (hstable h₁ hell₁ hμ₁) (hstable h₂ hell₂ hμ₂) hp₁ hp₂
    (wedge_forward_cofinal ell μ a b (h₁ + h₂) hell hμ)
  exact ⟨B, hB, fun g hg₁ hg₂ => (hagree g ⟨hg₁, hg₂⟩).symm, hrange⟩

end KumarNivat
