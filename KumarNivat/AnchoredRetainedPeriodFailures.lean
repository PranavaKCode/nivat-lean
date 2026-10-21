module

public import KumarNivat.AnchoredSeedFailureLayers
public import KumarNivat.RegionalBackground

@[expose] public section

namespace KumarNivat

-- every relaxed chain is stable under the old backwards period direction.
theorem anchored_relaxed_chain_old_period_forward_stable {q : ℕ} [NeZero (2 * q)]
    (e : ZMod (2 * q) → Site) (hfan : AnchoredChainFanOrder e)
    (fixed : ℕ → ℤ) (b : ℕ) (hb₀ : 0 < b) (hbq : b < q) (j : ℤ) (l : ℕ) :
    ∀ g : Site, latticeEmbedding g ∈ anchoredRelaxedChainRegion e fixed b j →
      latticeEmbedding (g + (l : ℤ) • (-e 0)) ∈ anchoredRelaxedChainRegion e fixed b j := by
  intro g hg i hi
  have hib : i ≤ b := by have h := Finset.mem_range.mp hi; omega
  have hslope := (anchored_chain_surviving_normal_signs e hfan b hb₀ hbq i hib).1
  have hslopeR : (0 : ℝ) ≤ (directionNormal (e (i : ZMod (2 * q))) (-e 0) : ℝ) := by exact_mod_cast hslope
  have hlR : (0 : ℝ) ≤ ((l : ℤ) : ℝ) := by exact_mod_cast Int.natCast_nonneg l
  have hbase := hg i hi
  rw [latticeNormal_embedding] at hbase
  simp only [latticeEmbedding_add, latticeEmbedding_zsmul, map_add, map_smul, latticeNormal_embedding, smul_eq_mul]
  exact hbase.trans (le_add_of_nonneg_right (mul_nonneg hlR hslopeR))

-- a shared old period carries every outer-region point backwards into an actual agreement region.
theorem agreement_of_backward_cofinal_regional_period {A : Type*} (θ w : Site → A)
    (R S H : Set Site) (a : Site) (l : ℕ) (hl : 0 < l)
    (hw : IsPeriod w ((l : ℤ) • a)) (hSH : S ⊆ H)
    (htravel : BackwardCofinal R H a) (hagree : ∀ g ∈ R, θ g = w g)
    (hstable : ∀ g ∈ S, g + (l : ℤ) • (-a) ∈ S)
    (hperiod : RegionalPeriod θ S ((l : ℤ) • (-a))) :
    ∀ g ∈ S, θ g = w g := by
  intro g hg
  obtain ⟨N, hN⟩ := htravel g (hSH hg)
  have hlarge : N ≤ l * (N + 1) := by nlinarith
  have hR := hN (l * (N + 1)) hlarge
  have hsite : g + ((N + 1 : ℕ) : ℤ) • ((l : ℤ) • (-a)) =
      g - (((l * (N + 1) : ℕ) : ℤ) • a) := by
    rw [smul_smul, smul_neg, Nat.cast_mul]
    rw [mul_comm]
    abel
  have hθ := (regional_period_forward_multiples θ S ((l : ℤ) • (-a)) hstable hperiod (N + 1) g hg).2
  have hwback : IsPeriod w (((N + 1 : ℕ) : ℤ) • ((l : ℤ) • (-a))) := by
    have hp : IsPeriod w ((l : ℤ) • (-a)) := by simpa only [smul_neg] using hw.neg
    exact hp.zsmul ((N + 1 : ℕ) : ℤ)
  calc
    θ g = θ (g + ((N + 1 : ℕ) : ℤ) • ((l : ℤ) • (-a))) := hθ.symm
    _ = w (g + ((N + 1 : ℕ) : ℤ) • ((l : ℤ) • (-a))) := hagree _ (hsite.symm ▸ hR)
    _ = w g := hwback g

-- agreement with the periodic reference gives the same configuration its initial old regional period.
theorem anchored_old_regional_period_on_agreement_chain {A : Type*} {q : ℕ} [NeZero (2 * q)]
    (θ w : Site → A) (e : ZMod (2 * q) → Site) (fixed : ℕ → ℤ) (b : ℕ) (l : ℕ)
    (hw : IsPeriod w ((l : ℤ) • e 0))
    (hagree : ∀ g : Site, latticeEmbedding g ∈ anchoredRelaxedChainRegion e fixed b 0 → θ g = w g) :
    RegionalPeriod θ {g : Site | latticeEmbedding g ∈ anchoredRelaxedChainRegion e fixed b 0}
      ((l : ℤ) • (-e 0)) := by
  have hp : IsPeriod w ((l : ℤ) • (-e 0)) := by simpa only [smul_neg] using hw.neg
  intro g hg hgp
  exact (hagree _ hgp).trans ((hp g).trans (hagree g hg).symm)

-- retained disagreement in the finite final chain forces failure against the same array's old period shift.
theorem anchored_retained_disagreement_breaks_old_period {A : Type*} {q : ℕ} [NeZero (2 * q)]
    (θ w : Site → A) (e : ZMod (2 * q) → Site) (hfan : AnchoredChainFanOrder e)
    (fixed : ℕ → ℤ) (b : ℕ) (hb₀ : 0 < b) (hbq : b < q) (l : ℕ) (hl : 0 < l)
    (hw : IsPeriod w ((l : ℤ) • e 0))
    (hagree : ∀ g : Site, latticeEmbedding g ∈ anchoredRelaxedChainRegion e fixed b 0 → θ g = w g)
    (M : ℕ) (hfailure : ∃ g : Site, latticeEmbedding g ∈ anchoredRelaxedChainRegion e fixed b (M : ℤ) ∧ θ g ≠ w g) :
    ¬ RegionalPeriod θ {g : Site | latticeEmbedding g ∈ anchoredRelaxedChainRegion e fixed b (M : ℤ)}
        ((l : ℤ) • (-e 0)) ∧
      ∃ g : Site, latticeEmbedding g ∈ anchoredRelaxedChainRegion e fixed b (M : ℤ) ∧
        θ g ≠ shift ((l : ℤ) • (-e 0)) θ g := by
  classical
  have hnot : ¬ RegionalPeriod θ {g : Site | latticeEmbedding g ∈ anchoredRelaxedChainRegion e fixed b (M : ℤ)}
      ((l : ℤ) • (-e 0)) := by
    intro hperiod
    have hSH : {g : Site | latticeEmbedding g ∈ anchoredRelaxedChainRegion e fixed b (M : ℤ)} ⊆
        {g | fixed 0 ≤ directionNormal (e 0) g} := by
      intro g hg
      have hreal := anchored_relaxed_chain_keeps_reference_halfplane e fixed b hb₀ (M : ℤ) hg
      change (fixed 0 : ℝ) ≤ latticeNormal (directionNormal (e 0)) (latticeEmbedding g) at hreal
      rw [latticeNormal_embedding] at hreal
      change fixed 0 ≤ directionNormal (e 0) g
      exact_mod_cast hreal
    have hall := agreement_of_backward_cofinal_regional_period θ w
      {g : Site | latticeEmbedding g ∈ anchoredRelaxedChainRegion e fixed b 0}
      {g : Site | latticeEmbedding g ∈ anchoredRelaxedChainRegion e fixed b (M : ℤ)}
      {g | fixed 0 ≤ directionNormal (e 0) g} (e 0) l hl hw hSH
      (anchored_relaxed_chain_backward_cofinal e hfan fixed b hb₀ hbq 0) hagree
      (anchored_relaxed_chain_old_period_forward_stable e hfan fixed b hb₀ hbq (M : ℤ) l) hperiod
    obtain ⟨g, hg, hneq⟩ := hfailure
    exact hneq (hall g hg)
  refine ⟨hnot, ?_⟩
  by_contra hno
  have heq : ∀ g : Site, latticeEmbedding g ∈ anchoredRelaxedChainRegion e fixed b (M : ℤ) →
      θ g = shift ((l : ℤ) • (-e 0)) θ g := by
    simpa only [not_exists, not_and, not_not] using hno
  apply hnot
  intro g hg _hgp
  exact (heq g hg).symm

-- the first failed self-shift layer is bounded by the same finite relaxation range already constructed.
theorem anchored_retained_old_period_first_failure {A : Type*} {q : ℕ} [NeZero (2 * q)]
    (θ w : Site → A) (e : ZMod (2 * q) → Site) (hfan : AnchoredChainFanOrder e)
    (fixed : ℕ → ℤ) (b : ℕ) (hb₀ : 0 < b) (hbq : b < q) (l : ℕ) (hl : 0 < l)
    (hw : IsPeriod w ((l : ℤ) • e 0))
    (hagree : ∀ g : Site, latticeEmbedding g ∈ anchoredRelaxedChainRegion e fixed b 0 → θ g = w g)
    (M : ℕ) (hfailure : ∃ g : Site, latticeEmbedding g ∈ anchoredRelaxedChainRegion e fixed b (M : ℤ) ∧ θ g ≠ w g) :
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ M ∧ ∃ g : Site,
      directionNormal (e (b : ZMod (2 * q))) g = fixed b - (j : ℤ) ∧
      latticeEmbedding g ∈ anchoredRelaxedChainRegion e fixed b (j : ℤ) ∧
      θ g ≠ shift ((l : ℤ) • (-e 0)) θ g ∧
      (∀ u : Site, latticeEmbedding u ∈ anchoredRelaxedChainRegion e fixed b ((j : ℤ) - 1) →
        θ u = shift ((l : ℤ) • (-e 0)) θ u) ∧
      RegionalPeriod θ {u : Site | latticeEmbedding u ∈ anchoredRelaxedChainRegion e fixed b ((j : ℤ) - 1)}
        ((l : ℤ) • (-e 0)) := by
  have hinitial := anchored_old_regional_period_on_agreement_chain θ w e fixed b l hw hagree
  have hselfagree : ∀ g : Site, latticeEmbedding g ∈ anchoredRelaxedChainRegion e fixed b 0 →
      θ g = shift ((l : ℤ) • (-e 0)) θ g := by
    intro g hg
    exact (hinitial g hg (anchored_relaxed_chain_old_period_forward_stable e hfan fixed b hb₀ hbq 0 l g hg)).symm
  have hselfFailure := (anchored_retained_disagreement_breaks_old_period θ w e hfan fixed b hb₀ hbq
    l hl hw hagree M hfailure).2
  obtain ⟨j, hj₀, hjM, g, hlevel, hpoint, hneq, hnext⟩ :=
    first_failed_anchored_relaxed_chain θ (shift ((l : ℤ) • (-e 0)) θ) e fixed b M hselfagree hselfFailure
  refine ⟨j, hj₀, hjM, g, hlevel, hpoint, hneq, hnext, ?_⟩
  intro u hu _hup
  exact (hnext u hu).symm

end KumarNivat
