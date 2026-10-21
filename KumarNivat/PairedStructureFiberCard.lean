module

public import KumarNivat.PairedStructureFiberLocal
public import KumarNivat.PairedStructureMinimal
public import Mathlib.Data.Nat.Find

@[expose] public section

namespace KumarNivat

-- this is the actual multiplicity of a common binomial output inside the original orbit closure.
def BinomialFiberMultiplicity {K : Type*} [CommRing K] [TopologicalSpace K]
    (c : Site → K) (p : Site) (N : ℕ) : Prop :=
  ∃ e : Fin N → Site → K, Function.Injective e ∧ (∀ i, e i ∈ orbitClosure c) ∧
    ∀ i j, difference p (e i) = difference p (e j)

-- a common translate makes every pairwise disagreement visible to one fixed finite patch.
theorem binomial_fiber_card_le_patch_complexity {K : Type*} [CommRing K]
    [TopologicalSpace K] [DiscreteTopology K] (c : Site → K) (hc : (Set.range c).Finite)
    (a v : Site) (hav : determinant a v = 1) (L : ℕ) (d : ℕ)
    (hpatch : ∀ x ∈ orbitClosure c, ∀ y ∈ orbitClosure c,
      difference ((L : ℤ) • a) x = difference ((L : ℤ) • a) y →
      (∀ u ∈ rowFrame 0 a v L d, x u = y u) →
      ∀ g : Site, directionNormal a g ≤ (d : ℤ) → x g = y g)
    (N : ℕ) (e : Fin N → Site → K) (hinj : Function.Injective e)
    (hmem : ∀ i, e i ∈ orbitClosure c)
    (hfilter : ∀ i j, difference ((L : ℤ) • a) (e i) = difference ((L : ℤ) • a) (e j)) :
    N ≤ complexity c (rowFrame 0 a v L d) := by
  classical
  let ν := directionNormal a
  let B := rowFrame 0 a v L d
  let w (ij : Fin N × Fin N) : Site :=
    if hij : ij.1 ≠ ij.2 then Classical.choose
      (Function.ne_iff.mp (show e ij.1 ≠ e ij.2 from fun he => hij (hinj he))) else 0
  have hw (i j : Fin N) (hij : i ≠ j) : e i (w (i, j)) ≠ e j (w (i, j)) := by
    dsimp only [w]
    rw [dite_eq_left hij]
    exact Classical.choose_spec (Function.ne_iff.mp (show e i ≠ e j from fun he => hij (hinj he)))
  let M : ℤ := ∑ ij : Fin N × Fin N, |ν (w ij)|
  have hbound (i j : Fin N) : ν (w (i, j)) ≤ M := by
    apply (le_abs_self _).trans
    exact Finset.single_le_sum (fun ij _ => abs_nonneg (ν (w ij))) (Finset.mem_univ (i, j))
  let t : Site := M • v
  have ht : ν t = M := by
    dsimp [t]
    rw [map_zsmul, smul_eq_mul]
    change M * determinant a v = M
    rw [hav, mul_one]
  let : Fintype (patterns c B) := (patterns_finite_of_range c hc B).fintype
  have hword (i : Fin N) : (fun u : B => e i (u.val + t)) ∈ patterns c B := by
    obtain ⟨q, hq⟩ := languageContained_of_mem_orbitClosure c (e i) (hmem i) B t
    refine ⟨q, ?_⟩
    funext u
    simpa only [add_comm] using (hq u.val u.property).symm
  let state : Fin N → patterns c B := fun i => ⟨fun u => e i (u.val + t), hword i⟩
  have hstate : Function.Injective state := by
    intro i j he
    by_contra hij
    have hread := congrArg Subtype.val he
    have hsame : ∀ u ∈ B, shift t (e i) u = shift t (e j) u := by
      intro u hu
      exact congrFun hread ⟨u, hu⟩
    have houtput : difference ((L : ℤ) • a) (shift t (e i)) =
        difference ((L : ℤ) • a) (shift t (e j)) := by
      rw [difference_shift_configuration, difference_shift_configuration, hfilter i j]
    have hhalf := hpatch (shift t (e i)) (orbitClosure_shift_mem c (e i) (hmem i) t)
      (shift t (e j)) (orbitClosure_shift_mem c (e j) (hmem j) t) houtput hsame
    have hfit : ν (w (i, j) - t) ≤ (d : ℤ) := by
      rw [map_sub, ht]
      have hb := hbound i j
      have hd : (0 : ℤ) ≤ d := Int.natCast_nonneg d
      omega
    have heq := hhalf (w (i, j) - t) hfit
    exact hw i j hij (by simpa only [shift, sub_add_cancel] using heq)
  have hcard := Fintype.card_le_of_injective state hstate
  simpa only [Fintype.card_fin, Set.fintypeCard_eq_ncard, complexity] using hcard

-- the finite patch bound produces a largest actual fiber family, with positive size.
theorem exists_maximal_binomial_fiber {K : Type*} [CommRing K]
    [TopologicalSpace K] [DiscreteTopology K] (c : Site → K) (hc : (Set.range c).Finite)
    (a v : Site) (hav : determinant a v = 1) (L : ℕ) (hL : 0 < L)
    (hnoNE : ¬ OneSidedNonexpansive c (integerNormalAsReal (directionNormal a))) :
    ∃ d N : ℕ, ∃ e : Fin N → Site → K, 0 < N ∧ Function.Injective e ∧
      (∀ i, e i ∈ orbitClosure c) ∧
      (∀ i j, difference ((L : ℤ) • a) (e i) = difference ((L : ℤ) • a) (e j)) ∧
      (∀ x ∈ orbitClosure c, ∀ y ∈ orbitClosure c,
        difference ((L : ℤ) • a) x = difference ((L : ℤ) • a) y →
        (∀ u ∈ rowFrame 0 a v L d, x u = y u) →
        ∀ g : Site, directionNormal a g ≤ (d : ℤ) → x g = y g) ∧
      ∀ M : ℕ, BinomialFiberMultiplicity c ((L : ℤ) • a) M → M ≤ N := by
  classical
  obtain ⟨d, hpatch⟩ := exists_binomial_fiber_halfplane_patch c hc a v hav L hL hnoNE
  let P := BinomialFiberMultiplicity c ((L : ℤ) • a)
  let bound := complexity c (rowFrame 0 a v L d)
  have hbound (M : ℕ) (hM : P M) : M ≤ bound := by
    obtain ⟨e, hinj, hmem, hfilter⟩ := hM
    exact binomial_fiber_card_le_patch_complexity c hc a v hav L d hpatch M e hinj hmem hfilter
  have hone : P 1 := by
    refine ⟨fun _ => c, fun _ _ _ => Subsingleton.elim _ _, ?_, fun _ _ => rfl⟩
    exact fun _ => mem_own_orbitClosure c
  let N := Nat.findGreatest P bound
  have hN : 0 < N := lt_of_lt_of_le (by omega : (0 : ℕ) < 1)
    (Nat.le_findGreatest (hbound 1 hone) hone)
  obtain ⟨e, hinj, hmem, hfilter⟩ := Nat.findGreatest_spec (hbound 1 hone) hone
  exact ⟨d, N, e, hN, hinj, hmem, hfilter, hpatch,
    fun M hM => Nat.le_findGreatest (hbound M hM) hM⟩

end KumarNivat
