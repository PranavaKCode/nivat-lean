import KumarNivat.PeriodicWedgeBound
import KumarNivat.ThinRectangles
import KumarNivat.OrbitLanguage
import KumarNivat.KariSzabados
import Mathlib.Topology.Instances.Int

namespace KumarNivat

universe u

-- this records precisely the remaining selection proposition, including the retained nonperiodicity.
def IntegerWedgeSelection : Prop :=
  ∀ (c : Site → ℤ), (Set.range c).Finite →
    (¬ ∃ v : Site, v ≠ 0 ∧ IsPeriod c v) →
    ∀ k n : ℕ, 2 ≤ k → 2 ≤ n → complexity c (rectangle k n) ≤ k * n →
      ∃ θ : Site → ℤ, θ ∈ orbitClosure c ∧
        (¬ ∃ v : Site, v ≠ 0 ∧ IsPeriod θ v) ∧
        ∃ B : Site → ℤ, FullyPeriodic B ∧ ∃ ell μ : Site →+ ℤ, ∃ a b : ℤ,
          Function.Injective (ell.prod μ) ∧ AgreesOnWedge ell μ a b θ B

-- all other ingredients of the paper's final deduction are now proved; selection remains explicit.
theorem fullNivat_of_integer_wedge_selection (hselection : IntegerWedgeSelection) : FullNivat.{u} := by
  intro A _inst c hlow
  obtain ⟨k, n, hk, hn, hcount⟩ := hlow
  obtain ⟨d, hd, hcounts, hperiods⟩ := exists_integer_model c
  have hdcount : complexity d (rectangle k n) ≤ k * n := by rw [hcounts]; exact hcount
  let e : Site → ℚ := fun g => (d g : ℚ)
  have hefinite : (Set.range e).Finite := (hd.image (fun z : ℤ => (z : ℚ))).subset (by
    rintro y ⟨g, rfl⟩
    exact ⟨d g, ⟨g, rfl⟩, rfl⟩)
  have hecount (D : Finset Site) : complexity e D = complexity d D :=
    complexity_map_injective d (fun z : ℤ => (z : ℚ)) Int.cast_injective D
  have heperiod (v : Site) : IsPeriod e v ↔ IsPeriod d v :=
    isPeriod_map_injective d (fun z : ℤ => (z : ℚ)) Int.cast_injective v
  by_cases hn₁ : n = 1
  · subst n
    have hecount' : complexity e (rectangle k 1) ≤ k := by
      rw [hecount]
      simpa only [mul_one] using hdcount
    obtain ⟨q, hq, hp⟩ := horizontal_period_of_one_cell_height e hefinite k hecount'
    refine ⟨(q : ℤ) • (1, 0), ?_, (hperiods _).mp ((heperiod _).mp hp)⟩
    exact smul_ne_zero (by exact_mod_cast Nat.ne_of_gt hq) (by decide)
  by_cases hk₁ : k = 1
  · subst k
    have hecount' : complexity e (rectangle 1 n) ≤ n := by
      rw [hecount]
      simpa only [one_mul] using hdcount
    obtain ⟨q, hq, hp⟩ := vertical_period_of_one_cell_width e hefinite n hecount'
    refine ⟨(q : ℤ) • (0, 1), ?_, (hperiods _).mp ((heperiod _).mp hp)⟩
    exact smul_ne_zero (by exact_mod_cast Nat.ne_of_gt hq) (by decide)
  by_contra hnot
  have hdnot : ¬ ∃ v : Site, v ≠ 0 ∧ IsPeriod d v := by
    rintro ⟨v, hv, hp⟩
    exact hnot ⟨v, hv, (hperiods v).mp hp⟩
  obtain ⟨θ, hθ, hθnot, B, hB, ell, μ, a, b, hinj, hagree⟩ :=
    hselection d hd hdnot k n (by omega) (by omega) hdcount
  have hlang := languageContained_of_mem_orbitClosure d θ hθ
  have hθfinite := finite_range_of_language θ d hd hlang
  obtain ⟨hs, _hnil, hpairs, hdirs, hann⟩ :=
    low_complexity_distinct_difference_product d hd (rectangle k n) (by
      simpa only [card_rectangle] using hdcount)
  have hθann : laurentAct (differenceProduct hs) θ = 0 := funext
    (annihilator_inherited_of_language θ d hlang (differenceProduct hs).coeff (congrFun hann))
  let θQ : Site → ℚ := fun g => (θ g : ℚ)
  let BQ : Site → ℚ := fun g => (B g : ℚ)
  have hθQfinite : (Set.range θQ).Finite := (hθfinite.image (fun z : ℤ => (z : ℚ))).subset (by
    rintro y ⟨g, rfl⟩
    exact ⟨θ g, ⟨g, rfl⟩, rfl⟩)
  have hθQnot : ¬ ∃ v : Site, v ≠ 0 ∧ IsPeriod θQ v := by
    rintro ⟨v, hv, hp⟩
    exact hθnot ⟨v, hv,
      (isPeriod_map_injective θ (fun z : ℤ => (z : ℚ)) Int.cast_injective v).mp hp⟩
  have hBQ : FullyPeriodic BQ := by
    obtain ⟨v, w, hdet, hv, hw⟩ := hB
    exact ⟨v, w, hdet, fun g => congrArg (fun z : ℤ => (z : ℚ)) (hv g),
      fun g => congrArg (fun z : ℤ => (z : ℚ)) (hw g)⟩
  have hagreeQ : AgreesOnWedge ell μ a b θQ BQ := by
    intro g hg₁ hg₂
    exact congrArg (fun z : ℤ => (z : ℚ)) (hagree g hg₁ hg₂)
  have hlower := periodic_wedge_bound θQ BQ hθQfinite hθQnot hBQ ell μ a b hinj hagreeQ
    hs hdirs hpairs (cast_integer_difference_product θ hs hθann) k n
  have hθcounts : complexity θQ (rectangle k n) = complexity θ (rectangle k n) :=
    complexity_map_injective θ (fun z : ℤ => (z : ℚ)) Int.cast_injective _
  rw [hθcounts] at hlower
  have hupper := complexity_le_of_language θ d hd hlang (rectangle k n)
  omega

end KumarNivat
