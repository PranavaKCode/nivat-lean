import KumarNivat.FactorBoxGeometry
import KumarNivat.LineOperators

namespace KumarNivat

-- the intersection and short recurrences put two nonzero defects in their own factor boxes.
theorem factor_box_placement_of_recurrences {K : Type*} [Field K]
    (b₁ b₂ : Site → K) (p q E₁ E₂ : Site) (t₁ t₂ r₁ s₁ r₂ s₂ : ℕ)
    (α₁ : Fin (t₁ + 1) → K) (α₂ : Fin (t₂ + 1) → K)
    (hdet : determinant p q ≠ 0)
    (hfirst₁ : α₁ 0 ≠ 0) (hlast₁ : α₁ (Fin.last t₁) ≠ 0)
    (hfirst₂ : α₂ 0 ≠ 0) (hlast₂ : α₂ (Fin.last t₂) ≠ 0)
    (hrec₁ : ∀ k, LineRecurrence t₁ α₁ (fun n : ℤ => b₁ (k + n • p)))
    (hrec₂ : ∀ k, LineRecurrence t₂ α₂ (fun n : ℤ => b₂ (k + n • q)))
    (hne₁ : ∃ k, b₁ k ≠ 0) (hne₂ : ∃ k, b₂ k ≠ 0)
    (hE₁ : E₁ ∈ rectangle (r₁ + 1) (s₁ + 1))
    (hend₁ : E₁ + (t₁ : ℤ) • p ∈ rectangle (r₁ + 1) (s₁ + 1))
    (hE₂ : E₂ ∈ rectangle (r₂ + 1) (s₂ + 1))
    (hend₂ : E₂ + (t₂ : ℤ) • q ∈ rectangle (r₂ + 1) (s₂ + 1)) :
    ∃ u₁ u₂ : Site, u₁ ∈ rectangle (r₁ + 1) (s₁ + 1) ∧
      u₂ ∈ rectangle (r₂ + 1) (s₂ + 1) ∧
      ∃ g, shift u₁ b₁ g * shift u₂ b₂ g ≠ 0 := by
  obtain ⟨k₁, hk₁⟩ := hne₁
  obtain ⟨k₂, hk₂⟩ := hne₂
  obtain ⟨z, τ, σ, hz₁, hz₂⟩ :=
    exists_rational_line_intersection (k₁ - E₁) (k₂ - E₂) p q hdet
  have hn₁ : ∃ n : ℤ, b₁ (k₁ + n • p) ≠ 0 := ⟨0, by simpa using hk₁⟩
  have hn₂ : ∃ n : ℤ, b₂ (k₂ + n • q) ≠ 0 := ⟨0, by simpa using hk₂⟩
  obtain ⟨n₁, hn₁lo, hn₁hi, hb₁⟩ := exists_nonzero_recurrence_segment
    t₁ α₁ (fun n : ℤ => b₁ (k₁ + n • p)) hfirst₁ hlast₁ (hrec₁ k₁) hn₁ τ
  obtain ⟨n₂, hn₂lo, hn₂hi, hb₂⟩ := exists_nonzero_recurrence_segment
    t₂ α₂ (fun n : ℤ => b₂ (k₂ + n • q)) hfirst₂ hlast₂ (hrec₂ k₂) hn₂ σ
  let P₁ := k₁ + n₁ • p
  let P₂ := k₂ + n₂ • q
  let d₁ : ℚ := (n₁ : ℚ) - τ
  let d₂ : ℚ := (n₂ : ℚ) - σ
  have hd₁ : 0 ≤ d₁ := by dsimp [d₁]; linarith
  have hdt₁ : d₁ ≤ (t₁ : ℚ) := by dsimp [d₁]; linarith
  have hd₂ : 0 ≤ d₂ := by dsimp [d₂]; linarith
  have hdt₂ : d₂ ≤ (t₂ : ℚ) := by dsimp [d₂]; linarith
  have hline₁ : rationalSite P₁ - z = rationalSite E₁ + d₁ • rationalSite p := by
    rw [hz₁]
    ext <;> simp [rationalSite, P₁, d₁] <;> ring
  have hline₂ : rationalSite P₂ - z = rationalSite E₂ + d₂ • rationalSite q := by
    rw [hz₂]
    ext <;> simp [rationalSite, P₂, d₂] <;> ring
  have hbox₁ := segment_point_box E₁ (E₁ + (t₁ : ℤ) • p) p t₁ r₁ s₁
    rfl hE₁ hend₁ d₁ hd₁ hdt₁
  have hbox₂ := segment_point_box E₂ (E₂ + (t₂ : ℤ) • q) q t₂ r₂ s₂
    rfl hE₂ hend₂ d₂ hd₂ hdt₂
  have hcoord₁x := congrArg Prod.fst hline₁
  have hcoord₁y := congrArg Prod.snd hline₁
  have hcoord₂x := congrArg Prod.fst hline₂
  have hcoord₂y := congrArg Prod.snd hline₂
  change (P₁.1 : ℚ) - z.1 = (E₁.1 : ℚ) + d₁ * (p.1 : ℚ) at hcoord₁x
  change (P₁.2 : ℚ) - z.2 = (E₁.2 : ℚ) + d₁ * (p.2 : ℚ) at hcoord₁y
  change (P₂.1 : ℚ) - z.1 = (E₂.1 : ℚ) + d₂ * (q.1 : ℚ) at hcoord₂x
  change (P₂.2 : ℚ) - z.2 = (E₂.2 : ℚ) + d₂ * (q.2 : ℚ) at hcoord₂y
  have hfit₁ : P₁ - floorSite z ∈ rectangle (r₁ + 1) (s₁ + 1) := by
    apply floor_anchor_box
    rw [hcoord₁x, hcoord₁y]
    exact hbox₁
  have hfit₂ : P₂ - floorSite z ∈ rectangle (r₂ + 1) (s₂ + 1) := by
    apply floor_anchor_box
    rw [hcoord₂x, hcoord₂y]
    exact hbox₂
  refine ⟨P₁ - floorSite z, P₂ - floorSite z, hfit₁, hfit₂, floorSite z, ?_⟩
  change b₁ (floorSite z + (P₁ - floorSite z)) * b₂ (floorSite z + (P₂ - floorSite z)) ≠ 0
  rw [show floorSite z + (P₁ - floorSite z) = P₁ by abel,
    show floorSite z + (P₂ - floorSite z) = P₂ by abel]
  exact mul_ne_zero hb₁ hb₂

-- lemma 3.2 applies directly to arrays annihilated by the two directional factors.
theorem factor_box_placement {K : Type*} [Field K]
    (b₁ b₂ : Site → K) (p q E₁ E₂ : Site) (t₁ t₂ r₁ s₁ r₂ s₂ : ℕ)
    (α₁ : Fin (t₁ + 1) → K) (α₂ : Fin (t₂ + 1) → K)
    (hdet : determinant p q ≠ 0)
    (hfirst₁ : α₁ 0 ≠ 0) (hlast₁ : α₁ (Fin.last t₁) ≠ 0)
    (hfirst₂ : α₂ 0 ≠ 0) (hlast₂ : α₂ (Fin.last t₂) ≠ 0)
    (hann₁ : laurentAct (lineOperator E₁ p t₁ α₁) b₁ = 0)
    (hann₂ : laurentAct (lineOperator E₂ q t₂ α₂) b₂ = 0)
    (hne₁ : ∃ k, b₁ k ≠ 0) (hne₂ : ∃ k, b₂ k ≠ 0)
    (hE₁ : E₁ ∈ rectangle (r₁ + 1) (s₁ + 1))
    (hend₁ : E₁ + (t₁ : ℤ) • p ∈ rectangle (r₁ + 1) (s₁ + 1))
    (hE₂ : E₂ ∈ rectangle (r₂ + 1) (s₂ + 1))
    (hend₂ : E₂ + (t₂ : ℤ) • q ∈ rectangle (r₂ + 1) (s₂ + 1)) :
    ∃ u₁ u₂ : Site, u₁ ∈ rectangle (r₁ + 1) (s₁ + 1) ∧
      u₂ ∈ rectangle (r₂ + 1) (s₂ + 1) ∧
      ∃ g, shift u₁ b₁ g * shift u₂ b₂ g ≠ 0 := by
  exact factor_box_placement_of_recurrences b₁ b₂ p q E₁ E₂ t₁ t₂ r₁ s₁ r₂ s₂ α₁ α₂
    hdet hfirst₁ hlast₁ hfirst₂ hlast₂
    (lineRecurrence_of_lineOperator E₁ p t₁ α₁ b₁ hann₁)
    (lineRecurrence_of_lineOperator E₂ q t₂ α₂ b₂ hann₂)
    hne₁ hne₂ hE₁ hend₁ hE₂ hend₂

end KumarNivat
