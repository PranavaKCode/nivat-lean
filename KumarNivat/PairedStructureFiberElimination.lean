import KumarNivat.PairedStructureFiberAlgebra
import KumarNivat.PairedStructureFiberLift
import Mathlib.Data.Fin.Tuple.Basic

namespace KumarNivat

-- maximal fiber multiplicity removes the opposite bad direction from an actual selected orbit closure.
theorem remove_opposite_nonexpansive_factor_direction {K : Type*} [CommRing K]
    [Nontrivial K] [NoZeroDivisors K] [TopologicalSpace K] [DiscreteTopology K]
    (c : Site → K) (hc : (Set.range c).Finite) (hs : List Site)
    (hpairs : hs.Pairwise (fun p q => determinant p q ≠ 0))
    (hann : laurentAct (differenceProduct hs) c = 0)
    (a v : Site) (hav : determinant a v = 1) (L : ℕ) (hL : 0 < L)
    (hpmem : (L : ℤ) • a ∈ hs)
    (hnoNE : ¬ OneSidedNonexpansive c (integerNormalAsReal (directionNormal a))) :
    ∃ d ∈ orbitClosure c,
      ¬ OneSidedNonexpansive d (integerNormalAsReal (directionNormal a)) ∧
      ¬ OneSidedNonexpansive d (-integerNormalAsReal (directionNormal a)) := by
  classical
  let p := (L : ℤ) • a
  let ν := directionNormal a
  obtain ⟨width, N, e, hN, hinj, hmem, hfilter, hpatch, hmax⟩ :=
    exists_maximal_binomial_fiber c hc a v hav L hL hnoNE
  obtain ⟨q, hq, hqfilter, hsep⟩ := exists_uniformly_separated_binomial_fiber_limit
    c hc a v hav L width N e hinj hmem hfilter hpatch
  let i₀ : Fin N := ⟨0, hN⟩
  have hν : ν ≠ 0 := by
    intro hz
    have he := congrArg (fun μ : Site →+ ℤ => μ v) hz
    change determinant a v = 0 at he
    rw [hav] at he
    omega
  have hpnormal : ν p = 0 := by simp only [p, ν, map_zsmul, directionNormal_self, smul_zero]
  refine ⟨q i₀, hq i₀, fun hNE => hnoNE (hNE.of_mem_orbitClosure (hq i₀)), ?_⟩
  rintro ⟨_hell, x, y, hx, hy, hxy, hagree⟩
  have hxorig : x ∈ orbitClosure c := orbitClosure_subset_of_mem c (q i₀) (hq i₀) hx
  have hyorig : y ∈ orbitClosure c := orbitClosure_subset_of_mem c (q i₀) (hq i₀) hy
  have hagree' (g : Site) (hg : ν g ≤ 0) : x g = y g := by
    apply hagree
    change (0 : ℝ) ≤ -(ν g : ℝ)
    exact_mod_cast neg_nonneg.mpr hg
  have hxyfilter : difference p x = difference p y := binomial_outputs_equal_of_opposite_halfplane
    c x y hxorig hyorig hs hpairs hann p hpmem ν hν hpnormal 0 hagree'
  obtain ⟨f, hf₀, hfmem, hffilter, hfsep⟩ := exists_binomial_fiber_lift_with_separation
    c hc q hq p hqfilter (rowFrame 0 a v L width) hsep i₀ x hx
  have hfinj : Function.Injective f := by
    intro i j he
    by_contra hij
    obtain ⟨u, _hu, hne⟩ := hfsep i j hij 0
    exact hne (congrFun he (0 + u))
  have hyne (i : Fin N) : y ≠ f i := by
    by_cases hi : i = i₀
    · rw [hi, hf₀]
      exact hxy.symm
    · let t : Site := -((width : ℤ) • v)
      obtain ⟨u, hu, hne⟩ := hfsep i₀ i (Ne.symm hi) t
      have hupp := (rowFrame_normal_bounds 0 a v L width hav u hu).2
      simp only [map_zero, zero_add] at hupp
      change ν u ≤ (width : ℤ) at hupp
      have hfit : ν (t + u) ≤ 0 := by
        rw [map_add]
        dsimp [t]
        rw [map_neg, map_zsmul]
        change -((width : ℤ) • determinant a v) + ν u ≤ 0
        rw [hav, smul_eq_mul, mul_one]
        omega
      intro he
      apply hne
      rw [hf₀, ← he]
      exact hagree' (t + u) hfit
  have hynotin : y ∉ Set.range f := by
    rintro ⟨i, hi⟩
    exact hyne i hi.symm
  have hnewinj : Function.Injective (Fin.cons y f) := Fin.cons_injective_of_injective hynotin hfinj
  have hnewmem (i : Fin (N + 1)) : (Fin.cons y f : Fin (N + 1) → Site → K) i ∈ orbitClosure c := by
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [Fin.cons_zero] using hyorig
    · simpa only [Fin.cons_succ] using hfmem j
  have hfbase (i : Fin N) : difference p (f i) = difference p y := by
    exact (hffilter i i₀).trans (by rw [hf₀]; exact hxyfilter)
  have hnewbase (i : Fin (N + 1)) :
      difference p ((Fin.cons y f : Fin (N + 1) → Site → K) i) = difference p y := by
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [Fin.cons_zero]
    · simpa only [Fin.cons_succ] using hfbase j
  have hcontr := hmax (N + 1) ⟨Fin.cons y f, hnewinj, hnewmem,
    fun i j => (hnewbase i).trans (hnewbase j).symm⟩
  omega

end KumarNivat
