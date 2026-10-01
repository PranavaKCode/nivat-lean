import KumarNivat.RegionalBandSweeps
import KumarNivat.FarSeedBlocks
import KumarNivat.InwardPeriodicBands
import KumarNivat.PrimitiveRetention

namespace KumarNivat

-- the verified seed half-strip and fixed-gap bands complete both sweep cases and produce two independent regional periods.
theorem second_period_from_high_seed_half_strip {A I : Type*} (c x : Site → A)
    (hc : (Set.range c).Finite) (hx : LanguageContained x c)
    (R S : Finset Site) (hgen : GeneratingPolygon c R S) (a b : Site)
    (hprimitive : Int.gcd a.1 a.2 = 1) (hdet : 0 < determinant a b) (m M cut : ℤ)
    (hbounds : ∀ u ∈ S, m ≤ directionNormal a u ∧ directionNormal a u ≤ M)
    (J : Finset I) (μ : I → Site →+ ℤ) (z : I → ℤ)
    (hμa : ∀ i ∈ J, 0 < μ i a) (hμb : ∀ i ∈ J, 0 ≤ μ i b)
    (p : ℕ) (hp : 0 < p)
    (hperiod : RegionalPeriod x {g | latticeEmbedding g ∈ inwardLayerRegion (directionNormal a) cut J μ z} ((p : ℤ) • a))
    (r : ℕ)
    (hshort : (lowerLatticeFace S (directionNormal a) m).card = r + 1 ∨
      (lowerLatticeFace S (-directionNormal a) (-M)).card = r + 1)
    (H : Set Site) (l : ℕ) (hl : 0 < l)
    (hHR : H ⊆ {g | latticeEmbedding g ∈ inwardLayerRegion (directionNormal a) cut J μ z})
    (hstableH : ∀ g ∈ H, g + (l : ℤ) • b ∈ H) (hperiodH : RegionalPeriod x H ((l : ℤ) • b))
    (j₀ : ℤ) (hcut : cut ≤ j₀)
    (hhigh : ∀ j : ℤ, j₀ ≤ j → ∃ F : Site, directionNormal a F = j ∧
      ∀ i : Fin r, F + (i.val : ℤ) • a ∈ H) :
    ∃ T : ℤ, ∃ q : ℕ, cut ≤ T ∧ 0 < q ∧
      RegionalPeriod x {g | latticeEmbedding g ∈ inwardLayerRegion (directionNormal a) T J μ z} ((p : ℤ) • a) ∧
      RegionalPeriod x {g | latticeEmbedding g ∈ inwardLayerRegion (directionNormal a) T J μ z} ((q : ℤ) • b) := by
  classical
  have hane : a ≠ 0 := by rintro rfl; simp at hprimitive
  have hnormalA : directionNormal a a = 0 := by simp [directionNormal, determinant, mul_comm]
  have hwidth := hgen.2.2.1.normal_width_pos (directionNormal a) (directionNormal_ne_zero a hane) m M hbounds
  let d := (M - m).toNat
  have hd : (d : ℤ) = M - m := by dsimp [d]; omega
  have hμne : ∀ i ∈ J, μ i ≠ 0 := by
    intro i hi hz
    have hpos := hμa i hi
    rw [hz] at hpos
    simp at hpos
  let P : Set Site := {g | latticeEmbedding g ∈ inwardLayerRegion (directionNormal a) cut J μ z}
  have hstableMotion (v : Site) (hv : 0 ≤ directionNormal a v) (hμv : ∀ i ∈ J, 0 ≤ μ i v) (n : ℕ) :
      ∀ g ∈ P, g + (n : ℤ) • v ∈ P := by
    intro g hg
    change latticeEmbedding (g + (n : ℤ) • v) ∈ inwardLayerRegion (directionNormal a) cut J μ z
    rw [latticeEmbedding_add, latticeEmbedding_zsmul, Int.cast_natCast]
    exact inwardLayerRegion_nonnegative_motion (directionNormal a) cut J μ z v hv hμv _ hg
      (n : ℝ) (Nat.cast_nonneg n)
  have hstableA : ∀ g ∈ P, g + (p : ℤ) • a ∈ P :=
    hstableMotion a (by rw [hnormalA]) (fun i hi => le_of_lt (hμa i hi)) p
  have hstableB : ∀ g ∈ P, g + (l : ℤ) • b ∈ P := hstableMotion b (le_of_lt hdet) hμb l
  obtain ⟨v, E, D, _hav, _hE, hD, _hbound, hbands⟩ := inward_region_fixed_gap_periodic_bands
    c x hc hx a b hprimitive hdet cut J μ z hμne (fun i hi => le_of_lt (hμa i hi)) hμb p hp hperiod l hl d j₀
  let Q := (D : ℤ) • ((l : ℤ) • b)
  let y := shift Q x
  have hy : LanguageContained y c := hx.shift Q
  have hperiodY : RegionalPeriod y P ((p : ℤ) • a) :=
    regional_period_shift_of_forward_stability x P Q ((p : ℤ) • a)
      (forward_stable_nat_multiples P ((l : ℤ) • b) hstableB D) hperiod
  have hseeds : ∀ j : ℤ, j₀ ≤ j → ∃ F : Site, directionNormal a F = j ∧
      ∀ N : ℤ, ∃ n : ℤ, N ≤ n ∧ ∀ i : Fin r,
        x (F + (n + (i.val : ℤ)) • a) = y (F + (n + (i.val : ℤ)) • a) := by
    intro j hj
    obtain ⟨F, hF, hfit⟩ := hhigh j hj
    refine ⟨F, hF, ?_⟩
    intro N
    obtain ⟨n, hn, hseed⟩ := far_seed_blocks_from_transported_half_strip x P H a ((l : ℤ) • b) p hp
      hHR hstableA hstableH hperiod hperiodH F r hfit D N
    exact ⟨n, hn, fun i => (hseed i).symm⟩
  have hbandsXY : ∀ L : ℤ, ∃ B : ℤ, L ≤ B ∧ ∀ g : Site, g ∈ P →
      B ≤ directionNormal a g → directionNormal a g ≤ B + (M - m) → x g = y g := by
    intro L
    obtain ⟨q, hL, hband⟩ := hbands L
    refine ⟨directionNormal a (E + (q : ℤ) • ((l : ℤ) • b)), hL, ?_⟩
    intro g hg hlo hhi
    exact (hband g hg hlo (by rw [hd]; exact hhi)).symm
  have hcovered : ∃ T : ℤ, cut ≤ T ∧ ∀ g ∈ P, T ≤ directionNormal a g → x g = y g := by
    rcases hshort with hlower | hupper
    · refine ⟨j₀, hcut, ?_⟩
      exact agreement_from_arbitrarily_high_regional_bands c x y hx hy R S hgen a hprimitive m M cut
        hbounds J μ z hμa p hp hperiod hperiodY r hlower j₀ hcut hseeds hbandsXY
    · obtain ⟨B, hB, hband⟩ := hbandsXY j₀
      refine ⟨B, hcut.trans hB, ?_⟩
      exact upward_regional_band_sweep c x y hx hy R S hgen a hprimitive m M cut hbounds J μ z hμa
        p hp hperiod hperiodY r hupper j₀ B hcut hB hseeds hband
  obtain ⟨T, hT, hcovered⟩ := hcovered
  let P' : Set Site := {g | latticeEmbedding g ∈ inwardLayerRegion (directionNormal a) T J μ z}
  have hP' : ∀ g ∈ P', g ∈ P ∧ T ≤ directionNormal a g := by
    intro g hg
    have hm := (mem_inwardLayerRegion_lattice (directionNormal a) T J μ z g).mp hg
    exact ⟨(mem_inwardLayerRegion_lattice (directionNormal a) cut J μ z g).mpr ⟨hT.trans hm.1, hm.2⟩, hm.1⟩
  have hperiodA' : RegionalPeriod x P' ((p : ℤ) • a) := by
    intro g hg hfit
    exact hperiod g (hP' g hg).1 (hP' _ hfit).1
  have hperiodQ' : RegionalPeriod x P' Q := by
    intro g hg _hfit
    exact (hcovered g (hP' g hg).1 (hP' g hg).2).symm
  have hQ : Q = ((D * l : ℕ) : ℤ) • b := by dsimp [Q]; rw [smul_smul]
  exact ⟨T, D * l, hT, Nat.mul_pos hD hl, hperiodA', by simpa only [hQ] using hperiodQ'⟩

end KumarNivat
