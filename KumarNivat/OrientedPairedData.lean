import KumarNivat.PairedDirections

namespace KumarNivat

-- reversing a primitive tangent reverses its signed integer normal.
theorem directionNormal_neg (p : Site) : directionNormal (-p) = -directionNormal p := by
  ext g
  change (-p.1) * g.2 - (-p.2) * g.1 = -(p.1 * g.2 - p.2 * g.1)
  ring

-- casting the reversed integer normal preserves its opposite real orientation.
theorem integerNormalAsReal_direction_neg (p : Site) :
    integerNormalAsReal (directionNormal (-p)) = -integerNormalAsReal (directionNormal p) := by
  ext g
  change (directionNormal (-p) g : ℝ) = -(directionNormal p g : ℝ)
  have he : directionNormal (-p) g = -directionNormal p g := by rw [directionNormal_neg]; rfl
  rw [he, Int.cast_neg]

-- both paired orientations allow the actual shorter edge to be chosen as the facing edge.
theorem shorter_paired_direction_supporting_data (c : Site → ℤ) (R S : Finset Site)
    (hgen : GeneratingPolygon c R S) (hs : List Site) (hdirs : ∀ h ∈ hs, h ≠ 0)
    (hann : laurentAct (differenceProduct hs) c = 0) (hpair : HasPairedOneSidedDirection c) :
    ∃ p h : Site, p ≠ 0 ∧ Int.gcd p.1 p.2 = 1 ∧ h ∈ hs ∧ h ≠ 0 ∧ determinant p h = 0 ∧
      OneSidedNonexpansive c (integerNormalAsReal (directionNormal p)) ∧
      OneSidedNonexpansive c (-integerNormalAsReal (directionNormal p)) ∧
      ∃ m M : ℤ, (∀ u ∈ S, m ≤ directionNormal p u ∧ directionNormal p u ≤ M) ∧
        2 ≤ (lowerLatticeFace S (directionNormal p) m).card ∧
        2 ≤ (lowerLatticeFace S (-directionNormal p) (-M)).card ∧
        (lowerLatticeFace S (directionNormal p) m).card ≤
          (lowerLatticeFace S (-directionNormal p) (-M)).card := by
  obtain ⟨p, h, hp, hprimitive, hh, hhne, hdet, hNE, hNEneg, m, M, hbounds, hlower, hupper⟩ :=
    paired_direction_supporting_data c R S hgen hs hdirs hann hpair
  by_cases hshort : (lowerLatticeFace S (directionNormal p) m).card ≤
      (lowerLatticeFace S (-directionNormal p) (-M)).card
  · exact ⟨p, h, hp, hprimitive, hh, hhne, hdet, hNE, hNEneg, m, M, hbounds, hlower, hupper, hshort⟩
  · obtain ⟨τ, hτ, _hker⟩ := primitive_direction_coordinate p hprimitive
    have hτneg : (-τ) (-p) = 1 := by simp [hτ]
    have hprimitive' := primitive_gcd_of_line_coordinate (-p) (-τ) hτneg
    have hdet' : determinant (-p) h = 0 := by
      change p.1 * h.2 - p.2 * h.1 = 0 at hdet
      simp only [determinant, Prod.fst_neg, Prod.snd_neg]
      nlinarith
    have hNE' : OneSidedNonexpansive c (integerNormalAsReal (directionNormal (-p))) := by
      rw [integerNormalAsReal_direction_neg]
      exact hNEneg
    have hNEneg' : OneSidedNonexpansive c (-integerNormalAsReal (directionNormal (-p))) := by
      rw [integerNormalAsReal_direction_neg, neg_neg]
      exact hNE
    have hbounds' : ∀ u ∈ S, -M ≤ directionNormal (-p) u ∧ directionNormal (-p) u ≤ -m := by
      intro u hu
      have hb := hbounds u hu
      rw [directionNormal_neg]
      change -M ≤ -directionNormal p u ∧ -directionNormal p u ≤ -m
      omega
    have hface₀ : lowerLatticeFace S (directionNormal (-p)) (-M) =
        lowerLatticeFace S (-directionNormal p) (-M) := by rw [directionNormal_neg]
    have hface₁ : lowerLatticeFace S (-directionNormal (-p)) (-(-m)) =
        lowerLatticeFace S (directionNormal p) m := by simp only [directionNormal_neg, neg_neg]
    refine ⟨-p, h, neg_ne_zero.mpr hp, hprimitive', hh, hhne, hdet', hNE', hNEneg', -M, -m,
      hbounds', ?_, ?_, ?_⟩
    · simpa only [hface₀] using hupper
    · simpa only [hface₁] using hlower
    · rw [hface₀, hface₁]
      omega

end KumarNivat
