import KumarNivat.GeneratedBandExtension
import KumarNivat.GeneratingBandPeriods
import KumarNivat.PatternRowPeriods
import KumarNivat.RestrictedExtensionCounts

namespace KumarNivat

open scoped Pointwise

-- either a unique base preserves the period, or the actual ambiguity budget supplies a new period at most two-r.
theorem bounded_band_extension {A : Type*} (c x : Site → A)
    (hc : (Set.range c).Finite) (hx : LanguageContained x c)
    (R S : Finset Site) (hgen : GeneratingPolygon c R S) (p : Site)
    (hprimitive : Int.gcd p.1 p.2 = 1) (m M : ℤ)
    (hbounds : ∀ u ∈ S, m ≤ directionNormal p u ∧ directionNormal p u ≤ M)
    (hlower : 2 ≤ (lowerLatticeFace S (directionNormal p) m).card)
    (hshorter : (lowerLatticeFace S (directionNormal p) m).card ≤
      (lowerLatticeFace S (-directionNormal p) (-M)).card)
    (s : ℕ) (hs : 0 < s)
    (hsbound : s ≤ 2 * ((lowerLatticeFace S (directionNormal p) m).card - 1))
    (hperiod : RegionalPeriod x (normalBand (directionNormal p) (m + 1) M) ((s : ℤ) • p)) :
    ∃ q : ℕ, 0 < q ∧ q ≤ 2 * ((lowerLatticeFace S (directionNormal p) m).card - 1) ∧
      RegionalPeriod x (normalBand (directionNormal p) m M) ((q : ℤ) • p) := by
  classical
  let F := lowerLatticeFace S (directionNormal p) m
  let T := S \ F
  let r := F.card - 1
  have hr : 0 < r := by dsimp [r, F]; omega
  have hrcard : r + 1 = F.card := by dsimp [r, F]; omega
  have hpne : p ≠ 0 := by rintro rfl; simp at hprimitive
  have hν := directionNormal_ne_zero p hpne
  have hp : directionNormal p p = 0 := by simp [directionNormal, determinant, mul_comm]
  have hF : F.Nonempty := Finset.card_pos.mp (by dsimp [F]; omega)
  obtain ⟨u₀, hu₀⟩ := hF
  have hupper : (lowerLatticeFace S (-directionNormal p) (-M)).Nonempty :=
    Finset.card_pos.mp (by omega)
  obtain ⟨u₁, hu₁⟩ := hupper
  have hu₁level : directionNormal p u₁ = M := by
    have he := (Finset.mem_filter.mp hu₁).2
    change -directionNormal p u₁ = -M at he
    exact neg_inj.mp he
  obtain ⟨C, _hC, hsum⟩ := segment_summand_of_opposite_face_cardinalities S hgen.2.1 p hprimitive
    m M hbounds r (by rw [hrcard]) (by rw [hrcard]; exact hshorter)
  have hstrip : bilateralTranslateStrip T p = normalBand (directionNormal p) (m + 1) M :=
    off_face_bilateralTranslateStrip_eq_normalBand S hgen.2.1 p hprimitive r hr C hsum m M u₀ u₁
      (Finset.mem_filter.mp hu₀).1 (Finset.mem_filter.mp hu₁).1
      (Finset.mem_filter.mp hu₀).2 hu₁level hbounds
  have hstripperiod : RegionalPeriod x (bilateralTranslateStrip T p) ((s : ℤ) • p) := by
    rw [hstrip]
    exact hperiod
  by_cases hunique : ∃ b : ℤ, extensionCount c S T Finset.sdiff_subset
      (legalTranslatedPattern c x hx T (b • p)) = 1
  · obtain ⟨b, hb⟩ := hunique
    have hy := hx.shift ((s : ℤ) • p)
    have hbaseper := legal_pattern_sequence_period_of_strip_period c x hx T p s hstripperiod
    have hbase (u : Site) (hu : u ∈ T) : x (b • p + u) = shift ((s : ℤ) • p) x (b • p + u) := by
      have he := congrFun (congrArg Subtype.val (hbaseper b)) ⟨u, hu⟩
      simpa only [legalTranslatedPattern, shift, add_smul, add_assoc, add_comm, add_left_comm] using he.symm
    have hfull := agreement_of_unique_observed_extension c x (shift ((s : ℤ) • p) x) hx hy
      S T Finset.sdiff_subset (b • p) hbase hb
    refine ⟨s, hs, hsbound, ?_⟩
    exact generated_band_extension_of_full_pattern_repeat c x hx R S hgen p hprimitive m M
      hbounds ⟨u₀, hu₀⟩ s hperiod b (fun u hu => (hfull u hu).symm)
  · have hamb (n : ℤ) : 2 ≤ extensionCount c S T Finset.sdiff_subset
        (legalTranslatedPattern c x hx T (n • p)) := by
      have hpos := extensionCount_pos c hc S T Finset.sdiff_subset
        (legalTranslatedPattern c x hx T (n • p))
      have hne : extensionCount c S T Finset.sdiff_subset
          (legalTranslatedPattern c x hx T (n • p)) ≠ 1 := fun he => hunique ⟨n, he⟩
      omega
    obtain ⟨s₀, hs₀, hs₀r, hsmall⟩ := band_period_of_shorter_opposite_generating_edges
      c x hc hx R S hgen p hprimitive m M hbounds hlower hshorter hamb
    have hsmallstrip : RegionalPeriod x (bilateralTranslateStrip T p) ((s₀ : ℤ) • p) := by
      rw [hstrip]
      exact hsmall
    obtain ⟨B, hB, hobserved⟩ := exists_observed_bases_le_strip_period c x hx T p s₀ hs₀ hsmallstrip
    let : Fintype (patterns c T) := (patterns_finite_of_range c hc T).fintype
    have hbudget : complexity c S - complexity c T ≤ r :=
      hgen.2.2.2.2 (directionNormal p) hν m (fun u hu => (hbounds u hu).1) ⟨u₀, hu₀⟩
    obtain ⟨i, j, hij, hj, hcollision⟩ := short_full_pattern_collision_over_bases c x hc hx S T
      Finset.sdiff_subset B r hbudget (hB.trans hs₀r) 0 p (by simpa only [zero_add] using hobserved)
    let q := j - i
    have hq : 0 < q := by dsimp [q]; omega
    have hqr : q ≤ 2 * r := by dsimp [q]; omega
    have hrepeat (u : Site) (hu : u ∈ S) :
        x (((i : ℤ) • p + u) + (q : ℤ) • p) = x ((i : ℤ) • p + u) := by
      have hindices : (i : ℤ) + (q : ℤ) = (j : ℤ) := by dsimp [q]; omega
      have hsite : ((i : ℤ) • p + u) + (q : ℤ) • p = (j : ℤ) • p + u := by
        rw [← hindices, add_smul]
        abel
      simpa only [zero_add, hsite] using hcollision u hu
    obtain ⟨E, hmem, hcover, hfit⟩ := exists_off_face_row_run_selector S hgen.2.1 p r hr C hsum
      (directionNormal p) m hp
    have hsample : sampledStrip E p = normalBand (directionNormal p) (m + 1) M :=
      (sampledStrip_eq_bilateralTranslateStrip T p E hmem hcover).trans hstrip
    have hsmall_sample : RegionalPeriod x (sampledStrip E p) ((s₀ : ℤ) • p) := by
      rw [hsample]
      exact hsmall
    have hnew_sample := sampled_strip_period_of_full_pattern_repeat x S E p r s₀ q hs₀ hs₀r
      hsmall_sample (fun u v => (Finset.mem_sdiff.mp (hfit u v)).1) (i : ℤ) hrepeat
    rw [hsample] at hnew_sample
    refine ⟨q, hq, hqr, ?_⟩
    exact generated_band_extension_of_full_pattern_repeat c x hx R S hgen p hprimitive m M
      hbounds ⟨u₀, hu₀⟩ q hnew_sample (i : ℤ) hrepeat

end KumarNivat
