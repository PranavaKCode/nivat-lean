import KumarNivat.PolyhedralFailureLayers
import KumarNivat.AnchoredRelaxedChainUnions

namespace KumarNivat

-- a failed point inside a finite relaxation bounds the first failed integer layer.
theorem first_failed_inward_layer_with_bounded_failure {A I : Type*}
    (x y : Site → A) (ν : Site →+ ℤ) (start : ℤ)
    (J : Finset I) (μ : I → Site →+ ℤ) (fixed : I → ℤ) (M : ℕ)
    (hagree : ∀ g : Site, latticeEmbedding g ∈ inwardLayerRegion ν start J μ fixed → x g = y g)
    (hfailure : ∃ g : Site, latticeEmbedding g ∈ inwardLayerRegion ν (start - (M : ℤ)) J μ fixed ∧
      x g ≠ y g) :
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ M ∧ ∃ g : Site,
      ν g = start - (j : ℤ) ∧
      latticeEmbedding g ∈ inwardLayerRegion ν (start - (j : ℤ)) J μ fixed ∧ x g ≠ y g ∧
      ∀ u : Site, latticeEmbedding u ∈ inwardLayerRegion ν (start - (j : ℤ) + 1) J μ fixed →
        x u = y u := by
  obtain ⟨g₀, hg₀, hneq₀⟩ := hfailure
  have hpoint₀ := (mem_inwardLayerRegion_lattice ν (start - (M : ℤ)) J μ fixed g₀).mp hg₀
  obtain ⟨β, g, hβ, hlevel, hpoint, hneq, hnext⟩ := first_failed_inward_layer x y ν start J μ fixed
    hagree ⟨g₀, hpoint₀.2, hneq₀⟩
  have hbound : start - (M : ℤ) ≤ β := by
    by_contra hn
    apply hneq₀
    apply hnext g₀
    apply (mem_inwardLayerRegion_lattice ν (β + 1) J μ fixed g₀).mpr
    exact ⟨by omega, hpoint₀.2⟩
  let j := (start - β).toNat
  have hj₀ : 1 ≤ j := by dsimp [j]; omega
  have hjM : j ≤ M := by dsimp [j]; omega
  have hβj : β = start - (j : ℤ) := by dsimp [j]; omega
  refine ⟨j, hj₀, hjM, g, ?_, ?_, hneq, ?_⟩
  · rwa [← hβj]
  · rwa [← hβj]
  · rwa [← hβj]

-- a finite natural chain separates its final moving normal from every earlier retained inequality.
theorem finite_chain_last_facet_as_inward_layer
    (μ : ℕ → Site →+ ℤ) (fixed : ℕ → ℤ) (b : ℕ) (j : ℤ) :
    finiteInwardRegion (Finset.range (b + 1)) μ
        (fun i => if i = b then fixed b - j else fixed i) =
      inwardLayerRegion (μ b) (fixed b - j) (Finset.range b) μ fixed := by
  ext x
  constructor
  · intro hx
    refine ⟨?_, ?_⟩
    · have hb := hx b (Finset.mem_range.mpr (by omega))
      simpa only [ite_true] using hb
    · intro i hi
      have hib := Finset.mem_range.mp hi
      have hne : i ≠ b := by omega
      have hb := hx i (Finset.mem_range.mpr (by omega))
      simpa only [ite_eq_right hne] using hb
  · intro hx i hi
    have hib := Finset.mem_range.mp hi
    by_cases he : i = b
    · subst i
      simpa only [ite_true] using hx.1
    · have hi' : i ∈ Finset.range b := Finset.mem_range.mpr (by omega)
      simpa only [ite_eq_right he] using hx.2 i hi'

-- the actual relaxed cyclic chain has that exact distinguished-facet presentation.
theorem anchored_relaxed_chain_as_inward_layer {q : ℕ} [NeZero (2 * q)]
    (e : ZMod (2 * q) → Site) (fixed : ℕ → ℤ) (b : ℕ) (j : ℤ) :
    anchoredRelaxedChainRegion e fixed b j =
      inwardLayerRegion (directionNormal (e (b : ZMod (2 * q)))) (fixed b - j)
        (Finset.range b) (fun i => directionNormal (e (i : ZMod (2 * q)))) fixed := by
  have hcuts : anchoredRelaxedChainCut fixed b j =
      (fun i => if i = b then fixed b - j else fixed i) := by
    funext i
    unfold anchoredRelaxedChainCut
    split_ifs with he
    · rw [he]
    · simp
  rw [anchoredRelaxedChainRegion, hcuts, finite_chain_last_facet_as_inward_layer]

-- a retained failed seed in the final relaxed chain selects the last agreeing actual chain layer.
theorem first_failed_anchored_relaxed_chain {A : Type*} {q : ℕ} [NeZero (2 * q)]
    (x y : Site → A) (e : ZMod (2 * q) → Site) (fixed : ℕ → ℤ) (b M : ℕ)
    (hagree : ∀ g : Site, latticeEmbedding g ∈ anchoredRelaxedChainRegion e fixed b 0 → x g = y g)
    (hfailure : ∃ g : Site, latticeEmbedding g ∈ anchoredRelaxedChainRegion e fixed b (M : ℤ) ∧ x g ≠ y g) :
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ M ∧ ∃ g : Site,
      directionNormal (e (b : ZMod (2 * q))) g = fixed b - (j : ℤ) ∧
      latticeEmbedding g ∈ anchoredRelaxedChainRegion e fixed b (j : ℤ) ∧ x g ≠ y g ∧
      ∀ u : Site, latticeEmbedding u ∈ anchoredRelaxedChainRegion e fixed b ((j : ℤ) - 1) →
        x u = y u := by
  have hagree' : ∀ g : Site, latticeEmbedding g ∈
      inwardLayerRegion (directionNormal (e (b : ZMod (2 * q)))) (fixed b)
        (Finset.range b) (fun i => directionNormal (e (i : ZMod (2 * q)))) fixed → x g = y g := by
    simpa only [anchored_relaxed_chain_as_inward_layer, sub_zero] using hagree
  have hfailure' : ∃ g : Site, latticeEmbedding g ∈
      inwardLayerRegion (directionNormal (e (b : ZMod (2 * q)))) (fixed b - (M : ℤ))
        (Finset.range b) (fun i => directionNormal (e (i : ZMod (2 * q)))) fixed ∧ x g ≠ y g := by
    simpa only [anchored_relaxed_chain_as_inward_layer] using hfailure
  obtain ⟨j, hj₀, hjM, g, hlevel, hpoint, hneq, hnext⟩ :=
    first_failed_inward_layer_with_bounded_failure x y _ (fixed b) (Finset.range b)
      (fun i => directionNormal (e (i : ZMod (2 * q)))) fixed M hagree' hfailure'
  refine ⟨j, hj₀, hjM, g, hlevel, ?_, hneq, ?_⟩
  · rwa [anchored_relaxed_chain_as_inward_layer]
  · intro u hu
    apply hnext u
    rw [anchored_relaxed_chain_as_inward_layer] at hu
    have hcut : fixed b - ((j : ℤ) - 1) = fixed b - (j : ℤ) + 1 := by omega
    rwa [hcut] at hu

end KumarNivat
