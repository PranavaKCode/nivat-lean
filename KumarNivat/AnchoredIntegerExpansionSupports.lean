import KumarNivat.AnchoredIntegerExpansion
import KumarNivat.AnchoredExhaustionWidths

namespace KumarNivat

-- a polygon between the actual base and its forward translates has the same surviving support levels.
theorem anchored_halfstrip_surviving_supports_equal {n : ℕ} [NeZero n]
    (e : ZMod n → Site) (horder : CyclicEdgeOrder e) (F T : Finset Site)
    (B : OrderedCyclicLatticePolygon e F) (P : OrderedCyclicLatticePolygon e T) (a : Site)
    (hFT : F ⊆ T) (hstrip : ∀ g ∈ T, g ∈ polygonHalfStrip F a) :
    ∀ k, 0 ≤ directionNormal (e k) a →
      directionNormal (e k) (P.vertex k) = directionNormal (e k) (B.vertex k) := by
  intro k hnonnegative
  have hupper := ordered_cyclic_site_normal_minimum e horder T P k (B.vertex k)
    (hFT (B.vertex_mem k))
  obtain ⟨⟨u, s⟩, he⟩ := hstrip (P.vertex k) (P.vertex_mem k)
  change u.val + (0 + (s : ℤ)) • a = P.vertex k at he
  have hbase := ordered_cyclic_site_normal_minimum e horder F B k u.val u.property
  have hlower : directionNormal (e k) (B.vertex k) ≤ directionNormal (e k) (P.vertex k) := by
    rw [← he, map_add, map_zsmul, smul_eq_mul, zero_add]
    exact hbase.trans (le_add_of_nonneg_right (mul_nonneg (Int.natCast_nonneg s) hnonnegative))
  exact le_antisymm hupper hlower

-- the first unbounded edge before the opposite tangent has a strictly decreasing normal on the forward ray.
theorem anchored_integer_expansion_moving_normal_negative {q : ℕ} [NeZero (2 * q)]
    (e : ZMod (2 * q) → Site) (hfan : AnchoredChainFanOrder e) (b : ℕ)
    (hb₀ : 0 < b) (hbq : b < q) :
    directionNormal (e (b : ZMod (2 * q))) (e 0) < 0 := by
  have hpositive : 0 < determinant (e 0) (e (b : ZMod (2 * q))) := by
    simpa only [Nat.cast_zero] using anchored_chain_first_half_pair_positive e hfan 0 b hb₀ hbq
  have hreverse : directionNormal (e (b : ZMod (2 * q))) (e 0) =
      -determinant (e 0) (e (b : ZMod (2 * q))) := by
    change determinant (e (b : ZMod (2 * q))) (e 0) = -determinant (e 0) (e (b : ZMod (2 * q)))
    simp only [determinant]
    ring
  rw [hreverse]
  omega

end KumarNivat
