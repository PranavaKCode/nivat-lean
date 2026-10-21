module

public import KumarNivat.PairedStructureNormals
public import KumarNivat.AnchoredCompactness

@[expose] public section

open Filter Topology

namespace KumarNivat

-- one inward translation replaces strict half-plane agreement by closed half-plane agreement.
theorem oneSidedNonexpansive_of_open_halfplane_pair {A : Type*} [TopologicalSpace A]
    (c x y : Site → A) (hx : x ∈ orbitClosure c) (hy : y ∈ orbitClosure c) (hne : x ≠ y)
    (ell : Site →+ ℝ) (hell : ell ≠ 0)
    (hagree : ∀ g : Site, 0 < ell g → x g = y g) : OneSidedNonexpansive c ell := by
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
  refine ⟨hell, shift p x, shift p y, orbitClosure_shift_mem c x hx p,
    orbitClosure_shift_mem c y hy p, ?_, ?_⟩
  · intro he
    apply hne
    funext u
    have hu := congrFun he (u - p)
    simpa only [shift, sub_add_cancel] using hu
  · intro u hu
    exact hagree (u + p) (by rw [map_add]; linarith)

-- a finite alphabet with infinitely many orbit points has an actual nonexpansive half-plane.
theorem exists_oneSidedNonexpansive_of_infinite_orbitClosure {A : Type*}
    [TopologicalSpace A] [DiscreteTopology A] (c : Site → A) (hc : (Set.range c).Finite)
    (hinfinite : (orbitClosure c).Infinite) :
    ∃ ell : Site →+ ℝ, OneSidedNonexpansive c ell := by
  classical
  choose x hx y hy g hlarge hfail hagree using
    (fun n : ℕ => infinite_orbitClosure_nearest_disagreement c hc hinfinite n)
  have hcompact := finite_range_orbitClosure_compact c hc
  have hsquare : IsCompact (Set.Icc ((-1, -1) : RealPlane) (1, 1)) := isCompact_Icc
  obtain ⟨⟨θ, w, v⟩, hmem, φ, hφ, hlimit⟩ :=
    (hcompact.prod (hcompact.prod hsquare)).tendsto_subseq
      (fun n => show (x n, y n, inwardUnitNormal (g n)) ∈
        orbitClosure c ×ˢ (orbitClosure c ×ˢ Set.Icc ((-1, -1) : RealPlane) (1, 1)) from
        ⟨hx n, hy n, inwardUnitNormal_mem_square (g n) (by have := hlarge n; omega)⟩)
  have hxlimit : Tendsto (x ∘ φ) atTop (𝓝 θ) := hlimit.fst_nhds
  have hylimit : Tendsto (y ∘ φ) atTop (𝓝 w) := hlimit.snd_nhds.fst_nhds
  have hvlimit : Tendsto (inwardUnitNormal ∘ g ∘ φ) atTop (𝓝 v) := hlimit.snd_nhds.snd_nhds
  have hneq : θ ≠ w := by
    obtain ⟨u, hu, hne⟩ := configuration_limits_retain_finite_disagreement
      (x ∘ φ) (y ∘ φ) θ w {0} hxlimit hylimit
      (Eventually.of_forall (fun n => ⟨0, Finset.mem_singleton_self 0, hfail (φ n)⟩))
    exact fun he => hne (congrFun he u)
  have hell : realDotNormal v ≠ 0 := limiting_unit_normal_ne_zero _ v hvlimit
    (fun n => inwardUnitNormal_unit (g (φ n)) (by have := hlarge (φ n); omega))
  have hopen : ∀ h : Site, 0 < realDotNormal v h → θ h = w h := by
    intro h hh
    have hinside := eventually_inside_nearest_disagreement_ball g hlarge φ hφ v hvlimit h hh
    have hequal : ∀ᶠ n in atTop, (x ∘ φ) n h = (y ∘ φ) n h :=
      hinside.mono (fun n hn => hagree (φ n) h hn)
    obtain ⟨n, ⟨hnx, hny⟩, he⟩ :=
      (((configuration_limit_eventually_eq (x ∘ φ) θ hxlimit h).and
        (configuration_limit_eventually_eq (y ∘ φ) w hylimit h)).and hequal).exists
    exact hnx.symm.trans (he.trans hny)
  exact ⟨realDotNormal v, oneSidedNonexpansive_of_open_halfplane_pair c θ w
    hmem.1 hmem.2.1 hneq (realDotNormal v) hell hopen⟩

-- finitely many orbit points give independent periods, so every other array has a bad direction.
theorem exists_oneSidedNonexpansive_of_not_fullyPeriodic {A : Type*}
    [TopologicalSpace A] [DiscreteTopology A] (c : Site → A) (hc : (Set.range c).Finite)
    (hnot : ¬ FullyPeriodic c) : ∃ ell : Site →+ ℝ, OneSidedNonexpansive c ell := by
  apply exists_oneSidedNonexpansive_of_infinite_orbitClosure c hc
  intro hfinite
  apply hnot
  apply fullyPeriodic_of_finite_shift_orbit c
  exact hfinite.subset (fun _ hg => subset_closure hg)

-- absence of all one-sided nonexpansive directions forces full periodicity.
theorem fullyPeriodic_of_no_oneSidedNonexpansive {A : Type*}
    [TopologicalSpace A] [DiscreteTopology A] (c : Site → A) (hc : (Set.range c).Finite)
    (hnoNE : ∀ ell : Site →+ ℝ, ¬ OneSidedNonexpansive c ell) : FullyPeriodic c := by
  by_contra hnot
  obtain ⟨ell, hNE⟩ := exists_oneSidedNonexpansive_of_not_fullyPeriodic c hc hnot
  exact hnoNE ell hNE

-- a symmetric selected point is fully periodic when the original array has no paired direction.
theorem symmetric_orbit_point_fullyPeriodic_under_no_pair {A : Type*}
    [TopologicalSpace A] [DiscreteTopology A] (c x : Site → A) (hc : (Set.range c).Finite)
    (hx : x ∈ orbitClosure c) (hnopair : ¬ HasPairedOneSidedDirection c)
    (hsym : ∀ ell : Site →+ ℝ,
      ¬ OneSidedNonexpansive x ell → ¬ OneSidedNonexpansive x (-ell)) : FullyPeriodic x := by
  apply fullyPeriodic_of_no_oneSidedNonexpansive x
    (finite_range_of_language x c hc (languageContained_of_mem_orbitClosure c x hx))
  exact no_oneSidedNonexpansive_of_symmetric_orbit_point c x hx hnopair hsym

end KumarNivat
