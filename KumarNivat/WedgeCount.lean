import KumarNivat.FilterCount
import KumarNivat.FilteredWedge
import KumarNivat.FactorBoxPlacement
import KumarNivat.TangentNormals
import KumarNivat.DefectRecurrences

namespace KumarNivat

-- the nonzero determinant also excludes zero period vectors.
theorem determinant_ne_zero_directions (v w : Site) (hdet : determinant v w ≠ 0) :
    v ≠ 0 ∧ w ≠ 0 := by
  constructor
  · intro hz
    apply hdet
    simp [hz, determinant]
  · intro hz
    apply hdet
    simp [hz, determinant]

-- a factor-box shift and a complementary stencil stay within the full gcd box.
theorem complementary_box_shift_fits (u x : Site) (r s r₁ s₁ : ℕ)
    (hr : r₁ ≤ r) (hs : s₁ ≤ s)
    (hu : u ∈ rectangle (r₁ + 1) (s₁ + 1))
    (hx : x ∈ rectangle (r - r₁ + 1) (s - s₁ + 1)) :
    u + x ∈ rectangle (r + 1) (s + 1) := by
  rw [mem_rectangle_iff] at hu hx ⊢
  simp only [Prod.fst_add, Prod.snd_add]
  omega

-- sections 2 through 4 now derive the placed cone obstruction from wedge and factor data.
theorem rectangle_bound_of_wedge_factor_data {K : Type*} [Field K]
    (c B : Site → K) (hc : (Set.range c).Finite) (hB : FullyPeriodic B)
    (ell μ : Site →+ ℤ) (a b : ℤ) (hinj : Function.Injective (ell.prod μ))
    (hwedge : AgreesOnWedge ell μ a b c B)
    (φ : Laurent K) (hφ : φ ≠ 0) (r s k n : ℕ) (hext : BoxExtrema φ r s)
    (hdiv : ∀ f : Laurent K, (∃ κ : K, laurentAct f c = fun _ => κ) → φ ∣ f)
    (f₁ f₂ : Laurent K) (p q E₁ E₂ : Site) (t₁ t₂ r₁ s₁ r₂ s₂ : ℕ)
    (α₁ : Fin (t₁ + 1) → K) (α₂ : Fin (t₂ + 1) → K)
    (hdet : determinant p q ≠ 0)
    (hfirst₁ : α₁ 0 ≠ 0) (hlast₁ : α₁ (Fin.last t₁) ≠ 0)
    (hfirst₂ : α₂ 0 ≠ 0) (hlast₂ : α₂ (Fin.last t₂) ≠ 0)
    (hφ₁ : φ = lineOperator E₁ p t₁ α₁ * f₁)
    (hφ₂ : φ = lineOperator E₂ q t₂ α₂ * f₂)
    (hr₁ : r₁ ≤ r) (hs₁ : s₁ ≤ s) (hr₂ : r₂ ≤ r) (hs₂ : s₂ ≤ s)
    (hE₁ : E₁ ∈ rectangle (r₁ + 1) (s₁ + 1))
    (hend₁ : E₁ + (t₁ : ℤ) • p ∈ rectangle (r₁ + 1) (s₁ + 1))
    (hE₂ : E₂ ∈ rectangle (r₂ + 1) (s₂ + 1))
    (hend₂ : E₂ + (t₂ : ℤ) • q ∈ rectangle (r₂ + 1) (s₂ + 1))
    (hsupp₁ : f₁.coeff.support ⊆ rectangle (r - r₁ + 1) (s - s₁ + 1))
    (hsupp₂ : f₂.coeff.support ⊆ rectangle (r - r₂ + 1) (s - s₂ + 1))
    (v w : Site) (hperioddet : determinant v w ≠ 0)
    (hperiod₁ : IsPeriod (laurentAct f₁ c) v) (hperiod₂ : IsPeriod (laurentAct f₂ c) w)
    (hnot₁ : ¬ FullyPeriodic (laurentAct f₁ c)) (hnot₂ : ¬ FullyPeriodic (laurentAct f₂ c))
    (hBv : IsPeriod B v) (hBw : IsPeriod B w)
    (hρv : IsPeriod (laurentAct φ c) v) (hρw : IsPeriod (laurentAct φ c) w)
    (Q₀ : Laurent K) (hQ₀ : Q₀ ≠ 0) (hann : laurentAct Q₀ c = 0) :
    k * n + 1 ≤ complexity c (rectangle k n) := by
  have hdirs := determinant_ne_zero_directions v w hperioddet
  obtain ⟨ν₁, hν₁, hv, β₁, hagree₁⟩ := filtered_halfplane_agreement c B ell μ a b
    hinj hwedge hB f₁ v hdirs.1 hperiod₁ hBv hnot₁
  obtain ⟨ν₂, hν₂, hw, β₂, hagree₂⟩ := filtered_halfplane_agreement c B ell μ a b
    hinj hwedge hB f₂ w hdirs.2 hperiod₂ hBw hnot₂
  have hann₁ := factor_annihilates_defect c φ (lineOperator E₁ p t₁ α₁) f₁ w hφ₁ hρw
  have hann₂ := factor_annihilates_defect c φ (lineOperator E₂ q t₂ α₂) f₂ v hφ₂ hρv
  have hne₁ := exists_nonzero_transverse_defect (laurentAct f₁ c) v w
    hperioddet hperiod₁ hnot₁
  have hrev : determinant w v ≠ 0 := by
    have he : determinant w v = -determinant v w := by simp [determinant]; ring
    rw [he]
    exact neg_ne_zero.mpr hperioddet
  have hne₂ := exists_nonzero_transverse_defect (laurentAct f₂ c) w v hrev hperiod₂ hnot₂
  obtain ⟨u₁, u₂, hu₁, hu₂, hplaced⟩ := factor_box_placement
    (difference w (laurentAct f₁ c)) (difference v (laurentAct f₂ c))
    p q E₁ E₂ t₁ t₂ r₁ s₁ r₂ s₂ α₁ α₂ hdet hfirst₁ hlast₁ hfirst₂ hlast₂
    hann₁ hann₂ hne₁ hne₂ hE₁ hend₁ hE₂ hend₂
  have hF := independent_negative_normals ν₁ ν₂
    (independent_tangent_normals ν₁ ν₂ v w hν₁ hν₂ hperioddet hv hw)
  have hsupport := shifted_defect_product_support
    (laurentAct f₁ c) (laurentAct f₂ c) (laurentAct f₁ B) (laurentAct f₂ B)
    ν₁ ν₂ β₁ β₂ v w u₁ u₂ hagree₁ hagree₂
    (hBw.filtered f₁.coeff) (hBv.filtered f₂.coeff)
  apply rectangle_bound_of_directional_filters c hc φ hφ r s k n hext hdiv
    f₁.coeff f₂.coeff u₁ u₂
    (fun x hx => complementary_box_shift_fits u₁ x r s r₁ s₁ hr₁ hs₁ hu₁ (hsupp₁ hx))
    (fun x hx => complementary_box_shift_fits u₂ x r s r₂ s₂ hr₂ hs₂ hu₂ (hsupp₂ hx))
    v w hdirs.1 hdirs.2 hperiod₁ hperiod₂ Q₀ hQ₀ hann
    ((-ν₁).prod (-ν₂)) hF
    (ν₁ u₁ - β₁ - max 0 (-ν₁ w) + 1) (ν₂ u₂ - β₂ - max 0 (-ν₂ v) + 1)
  · exact hsupport
  · simpa only [difference_shift, laurentAct] using hplaced

end KumarNivat
