import KumarNivat.PairedDirections
import KumarNivat.ShiftedConfigurations
import KumarNivat.PeriodLattice

namespace KumarNivat

-- every further orbit limit stays in the original closed shift-invariant set.
theorem orbitClosure_subset_of_mem {A : Type*} [TopologicalSpace A]
    (c x : Site → A) (hx : x ∈ orbitClosure c) : orbitClosure x ⊆ orbitClosure c := by
  apply closure_minimal
  · rintro _ ⟨h, rfl⟩
    exact orbitClosure_shift_mem c x hx h
  · exact isClosed_closure

-- the actual witnesses for a selected orbit point also witness the original direction.
theorem OneSidedNonexpansive.of_mem_orbitClosure {A : Type*} [TopologicalSpace A]
    {c x : Site → A} {ell : Site →+ ℝ} (hx : x ∈ orbitClosure c)
    (hNE : OneSidedNonexpansive x ell) : OneSidedNonexpansive c ell := by
  obtain ⟨hell, y, z, hy, hz, hne, hagree⟩ := hNE
  have hsub := orbitClosure_subset_of_mem c x hx
  exact ⟨hell, y, z, hsub hy, hsub hz, hne, hagree⟩

-- both orientations transfer together without changing their common line.
theorem HasPairedOneSidedDirection.of_mem_orbitClosure {A : Type*} [TopologicalSpace A]
    {c x : Site → A} (hx : x ∈ orbitClosure c) (hpair : HasPairedOneSidedDirection x) :
    HasPairedOneSidedDirection c := by
  obtain ⟨ell, hpos, hneg⟩ := hpair
  exact ⟨ell, hpos.of_mem_orbitClosure hx, hneg.of_mem_orbitClosure hx⟩

-- a global period is a two-site local identity and therefore passes to inherited language.
theorem IsPeriod.of_languageContained {A : Type*} {c x : Site → A} {p : Site}
    (hp : IsPeriod c p) (hx : LanguageContained x c) : IsPeriod x p := by
  classical
  intro g
  obtain ⟨t, ht⟩ := hx {0, p} g
  have hzero := ht 0 (by simp)
  have hstep := ht p (by simp)
  simp only [add_zero] at hzero
  exact hstep.trans ((hp t).trans hzero.symm)

-- the same two independent periods survive every actual orbit-closure selection.
theorem FullyPeriodic.of_mem_orbitClosure {A : Type*} [TopologicalSpace A]
    [DiscreteTopology A] {c x : Site → A} (hc : FullyPeriodic c)
    (hx : x ∈ orbitClosure c) : FullyPeriodic x := by
  obtain ⟨u, v, huv, hu, hv⟩ := hc
  have hlang := languageContained_of_mem_orbitClosure c x hx
  exact ⟨u, v, huv, hu.of_languageContained hlang, hv.of_languageContained hlang⟩

-- one common inward global period transports half-plane agreement to every site.
theorem equal_of_common_period_and_halfplane {A : Type*} (x y : Site → A)
    (ell : Site →+ ℝ) (p : Site) (hp : 0 < ell p)
    (hpx : IsPeriod x p) (hpy : IsPeriod y p)
    (hagree : ∀ g : Site, 0 ≤ ell g → x g = y g) : x = y := by
  funext g
  obtain ⟨n, hn⟩ := exists_nat_gt (-ell g / ell p)
  have hn' := (div_lt_iff₀ hp).mp hn
  have hfit : 0 ≤ ell (g + (n : ℤ) • p) := by
    rw [map_add, map_zsmul, zsmul_eq_mul]
    simp only [Int.cast_natCast]
    linarith
  exact (hpx.zsmul (n : ℤ) g).symm.trans ((hagree _ hfit).trans (hpy.zsmul (n : ℤ) g))

-- full periodicity supplies a shared inward period for every nonzero normal.
theorem FullyPeriodic.not_oneSidedNonexpansive {A : Type*} [TopologicalSpace A]
    [DiscreteTopology A] {c : Site → A} (hc : FullyPeriodic c) (ell : Site →+ ℝ) :
    ¬ OneSidedNonexpansive c ell := by
  rintro ⟨hell, x, y, hx, hy, hne, hagree⟩
  have hsome : ∃ g : Site, ell g ≠ 0 := by
    by_contra! hz
    apply hell
    ext g
    exact hz g
  obtain ⟨g, hg⟩ := hsome
  obtain ⟨p, hp⟩ : ∃ p : Site, 0 < ell p := by
    rcases lt_or_gt_of_ne hg with hneg | hpos
    · exact ⟨-g, by simpa only [map_neg] using neg_pos.mpr hneg⟩
    · exact ⟨g, hpos⟩
  obtain ⟨q, hq, hperiod⟩ := hc.exists_period_multiple p
  have hnormal : 0 < ell ((q : ℤ) • p) := by
    rw [map_zsmul, zsmul_eq_mul]
    exact mul_pos (by exact_mod_cast hq) hp
  have hpx := hperiod.of_languageContained (languageContained_of_mem_orbitClosure c x hx)
  have hpy := hperiod.of_languageContained (languageContained_of_mem_orbitClosure c y hy)
  exact hne (equal_of_common_period_and_halfplane x y ell _ hnormal hpx hpy hagree)

-- paired directions are incompatible with a fully periodic original configuration.
theorem HasPairedOneSidedDirection.not_fullyPeriodic {A : Type*} [TopologicalSpace A]
    [DiscreteTopology A] {c : Site → A} (hpair : HasPairedOneSidedDirection c) :
    ¬ FullyPeriodic c := by
  obtain ⟨ell, hNE, _⟩ := hpair
  intro hc
  exact hc.not_oneSidedNonexpansive ell hNE

-- the symmetry conclusion forces all directions expansive only under the original no-pair hypothesis.
theorem no_oneSidedNonexpansive_of_symmetric_orbit_point {A : Type*} [TopologicalSpace A]
    (c x : Site → A) (hx : x ∈ orbitClosure c) (hnopair : ¬ HasPairedOneSidedDirection c)
    (hsym : ∀ ell : Site →+ ℝ,
      ¬ OneSidedNonexpansive x ell → ¬ OneSidedNonexpansive x (-ell)) :
    ∀ ell : Site →+ ℝ, ¬ OneSidedNonexpansive x ell := by
  intro ell hNE
  have hneg : ¬ OneSidedNonexpansive x (-ell) := by
    intro hNEneg
    exact hnopair ⟨ell, hNE.of_mem_orbitClosure hx, hNEneg.of_mem_orbitClosure hx⟩
  have hdouble := hsym (-ell) hneg
  exact hdouble (by simpa only [neg_neg] using hNE)

-- finitely many lattice translates yield independent horizontal and vertical global periods.
theorem fullyPeriodic_of_finite_shift_orbit {A : Type*} (c : Site → A)
    (hfin : (Set.range (fun h : Site => shift h c)).Finite) : FullyPeriodic c := by
  classical
  let Orbit := Set.range (fun h : Site => shift h c)
  let : Finite Orbit := hfin.to_subtype
  let horizontal : ℕ → Orbit := fun n => ⟨shift ((n : ℤ), 0) c, ⟨((n : ℤ), 0), rfl⟩⟩
  let vertical : ℕ → Orbit := fun n => ⟨shift (0, (n : ℤ)) c, ⟨(0, (n : ℤ)), rfl⟩⟩
  obtain ⟨i, j, hij, hx⟩ := Finite.exists_ne_map_eq_of_infinite horizontal
  obtain ⟨k, l, hkl, hy⟩ := Finite.exists_ne_map_eq_of_infinite vertical
  have hx' : shift ((i : ℤ), 0) c = shift ((j : ℤ), 0) c := congrArg Subtype.val hx
  have hy' : shift (0, (k : ℤ)) c = shift (0, (l : ℤ)) c := congrArg Subtype.val hy
  refine ⟨((i : ℤ) - j, 0), (0, (k : ℤ) - l), ?_, ?_, ?_⟩
  · simp only [determinant, mul_zero, sub_zero]
    exact mul_ne_zero (sub_ne_zero.mpr (by exact_mod_cast hij))
      (sub_ne_zero.mpr (by exact_mod_cast hkl))
  · intro g
    have he := congrFun hx' (g - ((j : ℤ), 0))
    change c ((g - ((j : ℤ), 0)) + ((i : ℤ), 0)) = c ((g - ((j : ℤ), 0)) + ((j : ℤ), 0)) at he
    have hsite : g + ((i : ℤ) - j, 0) = (g - ((j : ℤ), 0)) + ((i : ℤ), 0) := by
      (ext <;> simp); ring
    rw [hsite]
    exact he.trans (congrArg c (sub_add_cancel g ((j : ℤ), 0)))
  · intro g
    have he := congrFun hy' (g - (0, (l : ℤ)))
    change c ((g - (0, (l : ℤ))) + (0, (k : ℤ))) = c ((g - (0, (l : ℤ))) + (0, (l : ℤ))) at he
    have hsite : g + (0, (k : ℤ) - l) = (g - (0, (l : ℤ))) + (0, (k : ℤ)) := by
      (ext <;> simp); ring
    rw [hsite]
    exact he.trans (congrArg c (sub_add_cancel g (0, (l : ℤ))))

end KumarNivat
