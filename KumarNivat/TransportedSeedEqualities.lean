module

public import KumarNivat.StableRegions

@[expose] public section

namespace KumarNivat

-- the existing regional period transports the same transverse equality to every forward period translate.
theorem regional_period_transports_equality {A : Type*} (x : Site → A) (R : Set Site)
    (p h : Site) (hstable : ∀ g ∈ R, g + p ∈ R) (hperiod : RegionalPeriod x R p)
    (g : Site) (hg : g ∈ R) (hgh : g + h ∈ R) (heq : x (g + h) = x g) (M : ℕ) :
    x ((g + (M : ℤ) • p) + h) = x (g + (M : ℤ) • p) := by
  have hleft := (regional_period_forward_multiples x R p hstable hperiod M (g + h) hgh).2
  have hright := (regional_period_forward_multiples x R p hstable hperiod M g hg).2
  have hsite : (g + (M : ℤ) • p) + h = (g + h) + (M : ℤ) • p := by abel
  rw [hsite, hleft, heq, hright]

-- a transverse half-strip period supplies all positive-multiple seed equalities far along the old period direction.
theorem transported_half_strip_multiple_equalities {A : Type*} (x : Site → A) (R H : Set Site)
    (p h : Site) (hHR : H ⊆ R)
    (hstableR : ∀ g ∈ R, g + p ∈ R) (hstableH : ∀ g ∈ H, g + h ∈ H)
    (hperiodR : RegionalPeriod x R p) (hperiodH : RegionalPeriod x H h) (D M : ℕ) :
    ∀ g ∈ H, x ((g + (M : ℤ) • p) + (D : ℤ) • h) = x (g + (M : ℤ) • p) := by
  intro g hg
  have hdata := regional_period_forward_multiples x H h hstableH hperiodH D g hg
  exact regional_period_transports_equality x R p ((D : ℤ) • h) hstableR hperiodR g
    (hHR hg) (hHR hdata.1) hdata.2 M

end KumarNivat
