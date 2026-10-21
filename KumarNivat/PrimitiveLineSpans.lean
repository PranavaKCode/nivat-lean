module

public import KumarNivat.PrimitiveRealLines
public import KumarNivat.LineFaceGeometry
public import Mathlib.Data.Finset.Max

@[expose] public section

namespace KumarNivat

-- distinct sites on one primitive normal level occupy distinct integer tangent coordinates.
theorem primitive_line_span_of_cardinality (F : Finset Site) (p : Site)
    (hprimitive : Int.gcd p.1 p.2 = 1) (m : ℤ)
    (hlevel : ∀ u ∈ F, directionNormal p u = m) (r : ℕ) (hcard : r + 1 ≤ F.card) :
    ∃ a ∈ F, ∃ b ∈ F, ∃ t : ℤ, (r : ℤ) ≤ t ∧ b = a + t • p := by
  classical
  obtain ⟨τ, _hτ, hker⟩ := primitive_direction_coordinate p hprimitive
  have hF : F.Nonempty := Finset.card_pos.mp (by omega)
  let U := F.image τ
  have hU : U.Nonempty := hF.image τ
  have hinj : Set.InjOn τ (F : Set Site) := by
    intro a ha b hb he
    exact normal_line_coordinate_injective p τ hker
      (Prod.ext ((hlevel a ha).trans (hlevel b hb).symm) he)
  have hUcard : U.card = F.card := Finset.card_image_iff.mpr hinj
  obtain ⟨a, ha, hta⟩ := Finset.mem_image.mp (Finset.min'_mem U hU)
  obtain ⟨b, hb, htb⟩ := Finset.mem_image.mp (Finset.max'_mem U hU)
  have horder : τ a ≤ τ b := by
    rw [hta, htb]
    exact Finset.min'_le_max' U hU
  have hsub : U ⊆ Finset.Icc (τ a) (τ b) := by
    intro j hj
    apply Finset.mem_Icc.mpr
    constructor
    · rw [hta]
      exact Finset.min'_le U j hj
    · rw [htb]
      exact Finset.le_max' U j hj
  have hcount := Finset.card_le_card hsub
  rw [hUcard, Int.card_Icc] at hcount
  have hbound : (r : ℤ) ≤ τ b - τ a := by omega
  have he := hker (b - a) (by rw [map_sub, hlevel b hb, hlevel a ha, sub_self])
  rw [map_sub] at he
  refine ⟨a, ha, b, hb, τ b - τ a, hbound, ?_⟩
  rw [← he]
  abel

-- lattice convexity fills enough of the extreme-site segment to obtain the required integer anchor.
theorem lattice_segment_anchor_of_collinear_cardinality (S F : Finset Site) (hS : LatticeConvex S)
    (hFS : F ⊆ S) (p : Site) (hprimitive : Int.gcd p.1 p.2 = 1) (m : ℤ)
    (hlevel : ∀ u ∈ F, directionNormal p u = m) (r : ℕ) (hcard : r + 1 ≤ F.card) :
    ∃ a : Site, a ∈ F ∧ a + (r : ℤ) • p ∈ S := by
  obtain ⟨a, ha, b, hb, t, hrt, he⟩ := primitive_line_span_of_cardinality F p hprimitive m hlevel r hcard
  have ht : (0 : ℝ) ≤ (t : ℝ) := by
    have ht' : (0 : ℤ) ≤ t := (Int.natCast_nonneg r).trans hrt
    exact_mod_cast ht'
  have hinterval : lineInterval (latticeEmbedding a) (latticeEmbedding p) 0 (t : ℝ) ⊆ latticeHull S := by
    rw [lineInterval_eq_segment _ _ _ _ ht]
    simp only [zero_smul, add_zero]
    apply (convex_convexHull ℝ _).segment_subset
    · exact subset_convexHull ℝ _ ⟨a, hFS ha, rfl⟩
    · have hbm := subset_convexHull ℝ (latticeEmbedding '' (S : Set Site)) ⟨b, hFS hb, rfl⟩
      rw [he, latticeEmbedding_add, latticeEmbedding_zsmul] at hbm
      exact hbm
  refine ⟨a, ha, hS _ (hinterval ?_)⟩
  refine ⟨(r : ℝ), ⟨Nat.cast_nonneg r, by exact_mod_cast hrt⟩, ?_⟩
  simp only [latticeEmbedding_add, latticeEmbedding_zsmul, Int.cast_natCast]

end KumarNivat
