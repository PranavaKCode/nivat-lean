module

public import KumarNivat.PairedStructureRows
public import KumarNivat.PairedStructureLimits

@[expose] public section

open Filter Topology

namespace KumarNivat

-- nonperiodic row words give actual orbit witnesses along a chosen global period line.
theorem periodic_configuration_forward_nonexpansive {A : Type*}
    [TopologicalSpace A] [DiscreteTopology A] (c : Site → A) (hc : (Set.range c).Finite)
    (a v : Site) (hav : determinant a v = 1) (L : ℕ) (hL : 0 < L)
    (hp : IsPeriod c ((L : ℤ) • a)) (hnot : ¬ FullyPeriodic c) :
    OneSidedNonexpansive c (integerNormalAsReal (directionNormal a)) := by
  classical
  let row : ℤ → (Fin L → A) := periodicRowWord c a v L
  have hfinite := periodicRowWord_range_finite c hc a v L
  have hnoper := periodic_row_word_has_no_positive_period c a v hav L hL hp hnot
  choose i j hwords hdiff using
    (fun n : ℕ => nonperiodic_word_has_predecessor_branch row hfinite hnoper (n + 1) (by omega))
  let x : ℕ → Site → A := fun n => shift (i n • v) c
  let y : ℕ → Site → A := fun n => shift (j n • v) c
  let E : Finset Site := Finset.univ.image (fun t : Fin L => -v + (t.val : ℤ) • a)
  have hx (n : ℕ) : x n ∈ orbitClosure c := subset_closure ⟨i n • v, rfl⟩
  have hy (n : ℕ) : y n ∈ orbitClosure c := subset_closure ⟨j n • v, rfl⟩
  have hfail (n : ℕ) : ∃ g ∈ E, x n g ≠ y n g := by
    obtain ⟨t, ht⟩ := Function.ne_iff.mp (hdiff n)
    refine ⟨-v + (t.val : ℤ) • a, Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩, ?_⟩
    have hsite (z : ℤ) : (-v + (t.val : ℤ) • a) + z • v = (z - 1) • v + (t.val : ℤ) • a := by
      rw [sub_smul, one_smul]
      abel
    change c ((-v + (t.val : ℤ) • a) + i n • v) ≠
      c ((-v + (t.val : ℤ) • a) + j n • v)
    rw [hsite, hsite]
    exact ht
  have hell : integerNormalAsReal (directionNormal a) ≠ 0 := by
    intro hz
    have he := congrArg (fun ell : Site →+ ℝ => ell v) hz
    change (determinant a v : ℝ) = 0 at he
    rw [hav] at he
    norm_num at he
  apply oneSidedNonexpansive_of_growing_halfplane_pairs c hc _ hell x y hx hy E hfail
  intro g hg
  let k : ℤ := determinant a g
  let m : ℤ := determinant g v
  have hk : 0 ≤ k := by
    change (0 : ℝ) ≤ (determinant a g : ℝ) at hg
    exact_mod_cast hg
  have hkcast : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk
  have hrep : g = m • a + k • v := by
    simpa only [hav, one_smul] using determinant_smul_identity a v g
  have hsite (z : ℤ) : g + z • v = m • a + (k + z) • v := by
    rw [hrep, add_smul]
    abel
  filter_upwards [eventually_ge_atTop k.toNat] with n hn
  have he := congrFun (hwords n) (⟨k.toNat, by omega⟩ : Fin (n + 1))
  simp only [sequenceWord, hkcast] at he
  change c (g + i n • v) = c (g + j n • v)
  rw [hsite, hsite]
  exact equal_periodic_rows_compare_all_tangent_sites c a v L hL hp m _ _
    (by simpa only [row, add_comm] using he)

-- reversing both basis vectors obtains the opposite witnesses on the very same period line.
theorem hasPairedOneSidedDirection_of_periodic_not_fullyPeriodic {A : Type*}
    [TopologicalSpace A] [DiscreteTopology A] (c : Site → A) (hc : (Set.range c).Finite)
    (hperiodic : ∃ p : Site, p ≠ 0 ∧ IsPeriod c p) (hnot : ¬ FullyPeriodic c) :
    HasPairedOneSidedDirection c := by
  obtain ⟨p, hp₀, hp⟩ := hperiodic
  obtain ⟨a, L, hL, hrep, _ha, τ, hτ, _hker⟩ := exists_primitive_direction_coordinate p hp₀
  obtain ⟨v, hav⟩ := primitive_basis_of_line_coordinate a τ hτ
  have hpa : IsPeriod c ((L : ℤ) • a) := hrep ▸ hp
  have hNE := periodic_configuration_forward_nonexpansive c hc a v hav L hL hpa hnot
  have havneg : determinant (-a) (-v) = 1 := by
    simpa only [determinant, Prod.fst_neg, Prod.snd_neg, neg_mul_neg] using hav
  have hpaneg : IsPeriod c ((L : ℤ) • (-a)) := by
    simpa only [smul_neg] using hpa.neg
  have hNEneg := periodic_configuration_forward_nonexpansive c hc (-a) (-v) havneg L hL hpaneg hnot
  rw [integerNormalAsReal_direction_neg] at hNEneg
  exact ⟨integerNormalAsReal (directionNormal a), hNE, hNEneg⟩

-- the original no-pair assumption excludes every global period unless full periodicity already holds.
theorem nonperiodic_of_no_pair_not_fullyPeriodic {A : Type*} [TopologicalSpace A]
    [DiscreteTopology A] (c : Site → A) (hc : (Set.range c).Finite)
    (hnopair : ¬ HasPairedOneSidedDirection c) (hnot : ¬ FullyPeriodic c) :
    ¬ ∃ p : Site, p ≠ 0 ∧ IsPeriod c p := by
  intro hperiodic
  exact hnopair (hasPairedOneSidedDirection_of_periodic_not_fullyPeriodic c hc hperiodic hnot)

end KumarNivat
