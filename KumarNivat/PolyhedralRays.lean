import KumarNivat.LatticeConvexity
import KumarNivat.HalfplaneBackgrounds

namespace KumarNivat

-- keep the moving integer facet separate from the finitely many fixed inward inequalities.
def inwardLayerRegion {I : Type*} (ν : Site →+ ℤ) (β : ℤ) (J : Finset I)
    (μ : I → Site →+ ℤ) (a : I → ℤ) : Set RealPlane :=
  {z | (β : ℝ) ≤ latticeNormal ν z ∧ ∀ i ∈ J, (a i : ℝ) ≤ latticeNormal (μ i) z}

-- real half-plane constraints have exactly the original integer inequalities at lattice sites.
@[simp] theorem mem_inwardLayerRegion_lattice {I : Type*} (ν : Site →+ ℤ) (β : ℤ)
    (J : Finset I) (μ : I → Site →+ ℤ) (a : I → ℤ) (g : Site) :
    latticeEmbedding g ∈ inwardLayerRegion ν β J μ a ↔
      β ≤ ν g ∧ ∀ i ∈ J, a i ≤ μ i g := by
  simp only [inwardLayerRegion, Set.mem_ofPred_eq, latticeNormal_embedding, Int.cast_le]

-- nonnegative inward slopes preserve the whole region under nonnegative real motion.
theorem inwardLayerRegion_nonnegative_motion {I : Type*} (ν : Site →+ ℤ) (β : ℤ)
    (J : Finset I) (μ : I → Site →+ ℤ) (a : I → ℤ) (p : Site) (hp : 0 ≤ ν p)
    (hμ : ∀ i ∈ J, 0 ≤ μ i p) :
    ∀ z ∈ inwardLayerRegion ν β J μ a, ∀ s : ℝ, 0 ≤ s →
      z + s • latticeEmbedding p ∈ inwardLayerRegion ν β J μ a := by
  intro z hz s hs
  refine ⟨?_, ?_⟩
  · have hpos : (0 : ℝ) ≤ (ν p : ℝ) := by exact_mod_cast hp
    rw [map_add, map_smul, latticeNormal_embedding, smul_eq_mul]
    exact hz.1.trans (le_add_of_nonneg_right (mul_nonneg hs hpos))
  · intro i hi
    have hpos : (0 : ℝ) ≤ (μ i p : ℝ) := by exact_mod_cast hμ i hi
    rw [map_add, map_smul, latticeNormal_embedding, smul_eq_mul]
    exact (hz.2 i hi).trans (le_add_of_nonneg_right (mul_nonneg hs hpos))

-- the tangent case delegates to the same recession calculation.
theorem inwardLayerRegion_forward_stable {I : Type*} (ν : Site →+ ℤ) (β : ℤ)
    (J : Finset I) (μ : I → Site →+ ℤ) (a : I → ℤ) (p : Site) (hp : ν p = 0)
    (hμ : ∀ i ∈ J, 0 ≤ μ i p) :
    ∀ z ∈ inwardLayerRegion ν β J μ a, ∀ s : ℝ, 0 ≤ s →
      z + s • latticeEmbedding p ∈ inwardLayerRegion ν β J μ a :=
  inwardLayerRegion_nonnegative_motion ν β J μ a p (by rw [hp]) hμ

-- finitely many positive slopes give one threshold for every site of the translated finite window.
theorem eventually_translated_window_in_fixed_halfplanes {I : Type*}
    (J : Finset I) (μ : I → Site →+ ℤ) (a : I → ℤ) (S : Finset Site) (E p : Site)
    (hμ : ∀ i ∈ J, 0 < μ i p) :
    ∃ N : ℤ, 0 ≤ N ∧ ∀ n : ℤ, N ≤ n → ∀ u ∈ S, ∀ i ∈ J,
      a i ≤ μ i (E + n • p + u) := by
  classical
  let D : ℕ := ∑ z ∈ S.product J, (a z.2 - μ z.2 (E + z.1)).natAbs
  refine ⟨(D : ℤ), Int.natCast_nonneg D, ?_⟩
  intro n hn u hu i hi
  have hmember : (u, i) ∈ S.product J := Finset.mem_product.mpr ⟨hu, hi⟩
  have hterm : (a i - μ i (E + u)).natAbs ≤ D := by
    dsimp [D]
    exact Finset.single_le_sum (f := fun z : Site × I => (a z.2 - μ z.2 (E + z.1)).natAbs)
      (fun _z _hz => Nat.zero_le _) hmember
  have hbound : a i - μ i (E + u) ≤ n :=
    (Int.le_natAbs).trans ((by exact_mod_cast hterm :
      ((a i - μ i (E + u)).natAbs : ℤ) ≤ D).trans hn)
  have hn₀ : 0 ≤ n := (Int.natCast_nonneg D).trans hn
  have hslope := hμ i hi
  have hsite : E + n • p + u = E + u + n • p := by abel
  rw [hsite, map_add, map_zsmul, smul_eq_mul]
  nlinarith

end KumarNivat
