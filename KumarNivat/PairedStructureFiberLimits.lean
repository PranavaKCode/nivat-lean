module

public import KumarNivat.PairedStructureFiberCard

@[expose] public section

open Filter Topology

namespace KumarNivat

-- all members of a finite fiber family can be translated and selected along one common subsequence.
theorem finite_orbit_family_joint_subsequence {A I : Type*} [Finite I]
    [TopologicalSpace A] [DiscreteTopology A] (c : Site → A) (hc : (Set.range c).Finite)
    (e : I → Site → A) (hmem : ∀ i, e i ∈ orbitClosure c) (u : ℕ → Site) :
    ∃ d : I → Site → A, (∀ i, d i ∈ orbitClosure c) ∧ ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ ∀ i, Tendsto ((fun n => shift (u n) (e i)) ∘ φ) atTop (𝓝 (d i)) := by
  have hcompact : IsCompact {d : I → Site → A | ∀ i, d i ∈ orbitClosure c} :=
    isCompact_pi_infinite (fun _ : I => finite_range_orbitClosure_compact c hc)
  obtain ⟨d, hd, φ, hφ, hlimit⟩ := hcompact.tendsto_subseq
    (fun n => show (fun i => shift (u n) (e i)) ∈ {d : I → Site → A | ∀ i, d i ∈ orbitClosure c}
      from fun i => orbitClosure_shift_mem c (e i) (hmem i) (u n))
  exact ⟨d, hd, φ, hφ, fun i => (continuous_apply i).tendsto d |>.comp hlimit⟩

-- equality of the same finite binomial outputs passes to both selected limits.
theorem difference_outputs_equal_of_limits {K : Type*} [CommRing K]
    [TopologicalSpace K] [DiscreteTopology K] (x y : ℕ → Site → K)
    (d e : Site → K) (p : Site) (hx : Tendsto x atTop (𝓝 d))
    (hy : Tendsto y atTop (𝓝 e)) (he : ∀ n, difference p (x n) = difference p (y n)) :
    difference p d = difference p e := by
  funext g
  obtain ⟨n, ⟨⟨⟨hx₀, hx₁⟩, hy₀⟩, hy₁⟩⟩ :=
    ((((configuration_limit_eventually_eq x d hx g).and
      (configuration_limit_eventually_eq x d hx (g + p))).and
      (configuration_limit_eventually_eq y e hy g)).and
      (configuration_limit_eventually_eq y e hy (g + p))).exists
  have h := congrFun (he n) g
  change x n (g + p) - x n g = y n (g + p) - y n g at h
  simpa only [difference, hx₀, hx₁, hy₀, hy₁] using h

-- an increasing inward translation turns distinct fiber members into limits separated on every translated patch.
theorem exists_uniformly_separated_binomial_fiber_limit {K : Type*} [CommRing K]
    [TopologicalSpace K] [DiscreteTopology K] (c : Site → K) (hc : (Set.range c).Finite)
    (a v : Site) (hav : determinant a v = 1) (L d N : ℕ)
    (e : Fin N → Site → K) (hinj : Function.Injective e) (hmem : ∀ i, e i ∈ orbitClosure c)
    (hfilter : ∀ i j, difference ((L : ℤ) • a) (e i) = difference ((L : ℤ) • a) (e j))
    (hpatch : ∀ x ∈ orbitClosure c, ∀ y ∈ orbitClosure c,
      difference ((L : ℤ) • a) x = difference ((L : ℤ) • a) y →
      (∀ u ∈ rowFrame 0 a v L d, x u = y u) →
      ∀ g : Site, directionNormal a g ≤ (d : ℤ) → x g = y g) :
    ∃ q : Fin N → Site → K, (∀ i, q i ∈ orbitClosure c) ∧
      (∀ i j, difference ((L : ℤ) • a) (q i) = difference ((L : ℤ) • a) (q j)) ∧
      ∀ i j : Fin N, i ≠ j → ∀ t : Site, ∃ u ∈ rowFrame 0 a v L d,
        q i (t + u) ≠ q j (t + u) := by
  classical
  obtain ⟨q, hq, φ, hφ, hlimit⟩ := finite_orbit_family_joint_subsequence c hc e hmem
    (fun n => (n : ℤ) • v)
  have hqfilter (i j : Fin N) : difference ((L : ℤ) • a) (q i) = difference ((L : ℤ) • a) (q j) := by
    apply difference_outputs_equal_of_limits _ _ _ _ _ (hlimit i) (hlimit j)
    intro n
    rw [Function.comp_apply, Function.comp_apply, difference_shift_configuration,
      difference_shift_configuration, hfilter i j]
  refine ⟨q, hq, hqfilter, ?_⟩
  intro i j hij t
  by_contra! hsame
  obtain ⟨g, hg⟩ := Function.ne_iff.mp (show e i ≠ e j from fun he => hij (hinj he))
  have hleft : ∀ᶠ n in atTop, ∀ u ∈ rowFrame 0 a v L d,
      shift ((φ n : ℤ) • v) (e i) (t + u) = q i (t + u) :=
    (rowFrame 0 a v L d).eventually_all.mpr
      (fun u _ => configuration_limit_eventually_eq _ _ (hlimit i) (t + u))
  have hright : ∀ᶠ n in atTop, ∀ u ∈ rowFrame 0 a v L d,
      shift ((φ n : ℤ) • v) (e j) (t + u) = q j (t + u) :=
    (rowFrame 0 a v L d).eventually_all.mpr
      (fun u _ => configuration_limit_eventually_eq _ _ (hlimit j) (t + u))
  let T := (directionNormal a g - (d : ℤ) - directionNormal a t).toNat
  obtain ⟨n, ⟨hl, hr⟩, hn⟩ := ((hleft.and hright).and (eventually_ge_atTop T)).exists
  let s : Site := t + (φ n : ℤ) • v
  have houtput : difference ((L : ℤ) • a) (shift s (e i)) =
      difference ((L : ℤ) • a) (shift s (e j)) := by
    rw [difference_shift_configuration, difference_shift_configuration, hfilter i j]
  have hread : ∀ u ∈ rowFrame 0 a v L d, shift s (e i) u = shift s (e j) u := by
    intro u hu
    have he := (hl u hu).trans ((hsame u hu).trans (hr u hu).symm)
    simpa only [shift, s, add_assoc, add_comm, add_left_comm] using he
  have hhalf := hpatch (shift s (e i)) (orbitClosure_shift_mem c (e i) (hmem i) s)
    (shift s (e j)) (orbitClosure_shift_mem c (e j) (hmem j) s) houtput hread
  have hfit : directionNormal a (g - s) ≤ (d : ℤ) := by
    rw [map_sub]
    dsimp [s]
    rw [map_add, map_zsmul]
    change directionNormal a g - (directionNormal a t + (φ n : ℤ) • determinant a v) ≤ (d : ℤ)
    rw [hav, smul_eq_mul, mul_one]
    have hφn : (n : ℤ) ≤ (φ n : ℤ) := by exact_mod_cast hφ.id_le n
    dsimp [T] at hn
    omega
  exact hg (by simpa only [shift, sub_add_cancel] using hhalf (g - s) hfit)

-- membership in the actual orbit closure gives a prescribed limit of lattice translates.
theorem shifts_tendsto_prescribed_orbit_point {A : Type*} [TopologicalSpace A]
    [DiscreteTopology A] (c x : Site → A) (hx : x ∈ orbitClosure c) :
    ∃ u : ℕ → Site, Tendsto (fun n => shift (u n) c) atTop (𝓝 x) := by
  obtain ⟨z, hz, hlimit⟩ := mem_closure_iff_seq_limit.mp hx
  choose u hu using hz
  refine ⟨u, ?_⟩
  simpa only [hu] using hlimit

end KumarNivat
