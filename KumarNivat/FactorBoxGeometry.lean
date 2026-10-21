module

public import KumarNivat.LineRecurrence
public import KumarNivat.WedgeSaturation
public import KumarNivat.RectangleQuotient

@[expose] public section

namespace KumarNivat

-- rational coordinates suffice for intersections of integer affine lines.
abbrev RationalSite := ℚ × ℚ

-- embed the integer lattice without changing its coordinates.
def rationalSite (g : Site) : RationalSite := ((g.1 : ℚ), (g.2 : ℚ))

-- the anchor is the coordinatewise floor of the rational intersection.
def floorSite (z : RationalSite) : Site := (⌊z.1⌋, ⌊z.2⌋)

-- choose a nonzero recurrent value within the segment's rational parameter interval.
theorem exists_nonzero_recurrence_segment {K : Type*} [Field K]
    (t : ℕ) (α : Fin (t + 1) → K) (a : ℤ → K)
    (hfirst : α 0 ≠ 0) (hlast : α (Fin.last t) ≠ 0)
    (hrec : LineRecurrence t α a) (hne : ∃ n : ℤ, a n ≠ 0) (τ : ℚ) :
    ∃ n : ℤ, τ ≤ (n : ℚ) ∧ (n : ℚ) ≤ τ + (t : ℚ) ∧ a n ≠ 0 := by
  obtain ⟨i, hi⟩ := exists_nonzero_recurrence_block t α a hfirst hlast hrec hne ⌈τ⌉
  refine ⟨⌈τ⌉ + (i.val : ℤ), ?_, ?_, hi⟩
  · have hceil := Int.le_ceil τ
    have hnonneg : (0 : ℚ) ≤ i.val := by positivity
    push_cast
    linarith
  · have hceil := Int.ceil_lt_add_one τ
    have hlt : (i.val : ℚ) < (t : ℚ) := by exact_mod_cast i.isLt
    have hstep : (i.val : ℚ) + 1 ≤ (t : ℚ) := by exact_mod_cast (show i.val + 1 ≤ t by omega)
    push_cast
    linarith

-- every intermediate point of a bounded line segment obeys the same coordinate bounds.
theorem affine_interval_bounds (e p d t R : ℚ)
    (he : 0 ≤ e ∧ e ≤ R) (hend : 0 ≤ e + t * p ∧ e + t * p ≤ R)
    (hd : 0 ≤ d) (hdt : d ≤ t) : 0 ≤ e + d * p ∧ e + d * p ≤ R := by
  by_cases hp : 0 ≤ p
  · have hmul₀ := mul_nonneg hd hp
    have hmul := mul_le_mul_of_nonneg_right hdt hp
    constructor <;> linarith
  · have hp' : p ≤ 0 := le_of_lt (lt_of_not_ge hp)
    have hmul₀ := mul_nonpos_of_nonneg_of_nonpos hd hp'
    have hmul := mul_le_mul_of_nonpos_right hdt hp'
    constructor <;> linarith

-- a line factor's two endpoints control the entire normalized factor box.
theorem segment_point_box (E E' p : Site) (t r s : ℕ)
    (hend : E' = E + (t : ℤ) • p)
    (hE : E ∈ rectangle (r + 1) (s + 1)) (hE' : E' ∈ rectangle (r + 1) (s + 1))
    (d : ℚ) (hd : 0 ≤ d) (hdt : d ≤ (t : ℚ)) :
    0 ≤ (E.1 : ℚ) + d * (p.1 : ℚ) ∧ (E.1 : ℚ) + d * (p.1 : ℚ) ≤ (r : ℚ) ∧
      0 ≤ (E.2 : ℚ) + d * (p.2 : ℚ) ∧ (E.2 : ℚ) + d * (p.2 : ℚ) ≤ (s : ℚ) := by
  have he := (mem_rectangle_iff E (r + 1) (s + 1)).mp hE
  have he' := (mem_rectangle_iff E' (r + 1) (s + 1)).mp hE'
  have he₁ : (0 : ℚ) ≤ E.1 ∧ (E.1 : ℚ) ≤ (r : ℚ) := by
    exact_mod_cast (show 0 ≤ E.1 ∧ E.1 ≤ (r : ℤ) by omega)
  have he₂ : (0 : ℚ) ≤ E.2 ∧ (E.2 : ℚ) ≤ (s : ℚ) := by
    exact_mod_cast (show 0 ≤ E.2 ∧ E.2 ≤ (s : ℤ) by omega)
  have he'₁ : (0 : ℚ) ≤ E'.1 ∧ (E'.1 : ℚ) ≤ (r : ℚ) := by
    exact_mod_cast (show 0 ≤ E'.1 ∧ E'.1 ≤ (r : ℤ) by omega)
  have he'₂ : (0 : ℚ) ≤ E'.2 ∧ (E'.2 : ℚ) ≤ (s : ℚ) := by
    exact_mod_cast (show 0 ≤ E'.2 ∧ E'.2 ≤ (s : ℤ) by omega)
  have hcoord₁ : (E'.1 : ℚ) = (E.1 : ℚ) + (t : ℚ) * (p.1 : ℚ) := by rw [hend]; simp
  have hcoord₂ : (E'.2 : ℚ) = (E.2 : ℚ) + (t : ℚ) * (p.2 : ℚ) := by rw [hend]; simp
  rw [hcoord₁] at he'₁
  rw [hcoord₂] at he'₂
  have h₁ := affine_interval_bounds _ _ d (t : ℚ) (r : ℚ) he₁ he'₁ hd hdt
  have h₂ := affine_interval_bounds _ _ d (t : ℚ) (s : ℚ) he₂ he'₂ hd hdt
  exact ⟨h₁.1, h₁.2, h₂.1, h₂.2⟩

-- flooring the common anchor preserves each integral coordinate-box bound.
theorem integer_sub_floor_bounds (p : ℤ) (z : ℚ) (r : ℕ)
    (hlo : 0 ≤ (p : ℚ) - z) (hhi : (p : ℚ) - z ≤ (r : ℚ)) :
    0 ≤ p - ⌊z⌋ ∧ p - ⌊z⌋ ≤ (r : ℤ) := by
  have hupperQ : ((⌊z⌋ : ℤ) : ℚ) ≤ (p : ℚ) := (Int.floor_le z).trans (by linarith)
  have hupper : ⌊z⌋ ≤ p := by exact_mod_cast hupperQ
  have hlowerQ : ((p - (r : ℤ) : ℤ) : ℚ) ≤ z := by push_cast; linarith
  have hlower : p - (r : ℤ) ≤ ⌊z⌋ := Int.le_floor.mpr hlowerQ
  constructor <;> omega

-- this is the last rounding step in lemma 3.2.
theorem floor_anchor_box (P : Site) (z : RationalSite) (r s : ℕ)
    (hbox : 0 ≤ (P.1 : ℚ) - z.1 ∧ (P.1 : ℚ) - z.1 ≤ (r : ℚ) ∧
      0 ≤ (P.2 : ℚ) - z.2 ∧ (P.2 : ℚ) - z.2 ≤ (s : ℚ)) :
    P - floorSite z ∈ rectangle (r + 1) (s + 1) := by
  have h₁ := integer_sub_floor_bounds P.1 z.1 r hbox.1 hbox.2.1
  have h₂ := integer_sub_floor_bounds P.2 z.2 s hbox.2.2.1 hbox.2.2.2
  rw [mem_rectangle_iff]
  change 0 ≤ P.1 - ⌊z.1⌋ ∧ P.1 - ⌊z.1⌋ < ((r + 1 : ℕ) : ℤ) ∧
    0 ≤ P.2 - ⌊z.2⌋ ∧ P.2 - ⌊z.2⌋ < ((s + 1 : ℕ) : ℤ)
  omega

-- cramer's rule gives a rational intersection for the two shifted support lines.
theorem exists_rational_line_intersection (a b p q : Site) (hdet : determinant p q ≠ 0) :
    ∃ z : RationalSite, ∃ τ σ : ℚ,
      z = rationalSite a + τ • rationalSite p ∧ z = rationalSite b + σ • rationalSite q := by
  let D : ℚ := (p.1 : ℚ) * (q.2 : ℚ) - (p.2 : ℚ) * (q.1 : ℚ)
  let N₁ : ℚ := ((b.1 : ℚ) - (a.1 : ℚ)) * (q.2 : ℚ) -
    ((b.2 : ℚ) - (a.2 : ℚ)) * (q.1 : ℚ)
  let N₂ : ℚ := ((b.1 : ℚ) - (a.1 : ℚ)) * (p.2 : ℚ) -
    ((b.2 : ℚ) - (a.2 : ℚ)) * (p.1 : ℚ)
  have hD : D ≠ 0 := by
    dsimp [D]
    exact_mod_cast hdet
  refine ⟨rationalSite a + (N₁ / D) • rationalSite p, N₁ / D, N₂ / D, rfl, ?_⟩
  apply Prod.ext
  · change (a.1 : ℚ) + (N₁ / D) * (p.1 : ℚ) = (b.1 : ℚ) + (N₂ / D) * (q.1 : ℚ)
    field_simp [hD]
    dsimp [D, N₁, N₂]
    ring
  · change (a.2 : ℚ) + (N₁ / D) * (p.2 : ℚ) = (b.2 : ℚ) + (N₂ / D) * (q.2 : ℚ)
    field_simp [hD]
    dsimp [D, N₁, N₂]
    ring

end KumarNivat
