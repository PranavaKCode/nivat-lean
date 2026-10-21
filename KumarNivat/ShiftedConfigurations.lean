module

public import KumarNivat.OrbitLanguage
public import KumarNivat.RetainedDisagreement

@[expose] public section

namespace KumarNivat

-- a lattice translation preserves the actual finite-pattern language inherited from the original array.
theorem LanguageContained.shift {A : Type*} {x c : Site → A}
    (hx : LanguageContained x c) (h : Site) : LanguageContained (shift h x) c := by
  intro D g
  obtain ⟨t, ht⟩ := hx D (g + h)
  refine ⟨t, ?_⟩
  intro u hu
  change x ((g + u) + h) = c (t + u)
  simpa only [add_assoc, add_comm, add_left_comm] using ht u hu

-- translations act continuously on the same product-topology orbit closure.
theorem orbitClosure_shift_mem {A : Type*} [TopologicalSpace A]
    (c x : Site → A) (hx : x ∈ orbitClosure c) (h : Site) : shift h x ∈ orbitClosure c := by
  have hcont : Continuous (fun y : Site → A => shift h y) :=
    continuous_pi (fun g => continuous_apply (g + h))
  have hmaps : Set.MapsTo (fun y : Site → A => shift h y)
      (Set.range (fun u : Site => shift u c)) (Set.range (fun u : Site => shift u c)) := by
    rintro _ ⟨u, rfl⟩
    refine ⟨u + h, ?_⟩
    funext g
    simp only [shift, add_comm, add_left_comm]
  exact hmaps.closure hcont hx

-- the annihilator identity translates with the selected array.
theorem laurentAct_shift {K : Type*} [CommRing K] (f : Laurent K) (x : Site → K) (h : Site) :
    laurentAct f (shift h x) = shift h (laurentAct f x) := act_shift f.coeff x h

-- a translated working region carries the same regional period back to the original coordinates.
theorem regional_period_of_shifted_region {A : Type*} (x : Site → A) (R : Set Site) (h p : Site)
    (hperiod : RegionalPeriod (shift h x) R p) :
    RegionalPeriod x {g | g - h ∈ R} p := by
  intro g hg hgp
  have hfit : g - h + p ∈ R := by
    change g + p - h ∈ R at hgp
    simpa only [sub_add_eq_add_sub] using hgp
  have he := hperiod (g - h) hg hfit
  simpa only [shift, sub_add_cancel, sub_add_eq_add_sub, add_sub_cancel] using he

-- a regional period passes to translated coordinates when the whole working region is translated with it.
theorem regional_period_shift {A : Type*} (x : Site → A) (R : Set Site) (h p : Site)
    (hperiod : RegionalPeriod x R p) :
    RegionalPeriod (shift h x) {g | g + h ∈ R} p := by
  intro g hg hfit
  have hfit' : (g + h) + p ∈ R := by
    change (g + p) + h ∈ R at hfit
    simpa only [add_assoc, add_comm, add_left_comm] using hfit
  simpa only [shift, add_assoc, add_comm, add_left_comm] using hperiod (g + h) hg hfit'

end KumarNivat
