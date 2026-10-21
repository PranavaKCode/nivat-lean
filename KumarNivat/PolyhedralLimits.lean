module

public import KumarNivat.PolyhedralRays
public import Mathlib.Order.Filter.AtTopBot.Tendsto
public import Mathlib.Order.Filter.Finite

@[expose] public section

open Filter Topology

namespace KumarNivat

-- the anchored polygons use one fixed finite list of integer inward normals.
def finiteInwardRegion {I : Type*} (J : Finset I) (μ : I → Site →+ ℤ) (z : I → ℤ) : Set RealPlane :=
  {w | ∀ i ∈ J, (z i : ℝ) ≤ latticeNormal (μ i) w}

-- stabilized supports survive the union and every support escaping to minus infinity disappears.
theorem finite_inward_region_union {I : Type*} (J K : Finset I) (hK : K ⊆ J)
    (μ : I → Site →+ ℤ) (z : ℕ → I → ℤ) (fixed : I → ℤ)
    (hlower : ∀ n, ∀ i ∈ K, fixed i ≤ z n i)
    (hfixed : ∀ i ∈ K, ∀ᶠ n in atTop, z n i = fixed i)
    (hescape : ∀ i ∈ J, i ∉ K → Tendsto (fun n => (z n i : ℝ)) atTop atBot) :
    (⋃ n, finiteInwardRegion J μ (z n)) = finiteInwardRegion K μ fixed := by
  ext w
  constructor
  · intro hw
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hw
    intro i hi
    have hb : (fixed i : ℝ) ≤ (z n i : ℝ) := by exact_mod_cast hlower n i hi
    exact hb.trans (hn i (hK hi))
  · intro hw
    have hevent : ∀ i ∈ J, ∀ᶠ n in atTop, (z n i : ℝ) ≤ latticeNormal (μ i) w := by
      intro i hi
      by_cases hk : i ∈ K
      · exact (hfixed i hk).mono (fun n hn => by rw [hn]; exact hw i hk)
      · exact (tendsto_atBot.mp (hescape i hi hk)) (latticeNormal (μ i) w)
    obtain ⟨n, hn⟩ := (J.eventually_all.mpr hevent).exists
    exact Set.mem_iUnion.mpr ⟨n, hn⟩

-- a finite integer half-plane presentation is both closed and convex over the real plane.
theorem finiteInwardRegion_closed_convex {I : Type*} (J : Finset I) (μ : I → Site →+ ℤ) (z : I → ℤ) :
    IsClosed (finiteInwardRegion J μ z) ∧ Convex ℝ (finiteInwardRegion J μ z) := by
  constructor
  · change IsClosed {w : RealPlane | ∀ i ∈ J, (z i : ℝ) ≤ latticeNormal (μ i) w}
    simp only [Set.ofPred_forall]
    exact isClosed_iInter (fun i => isClosed_iInter (fun _hi =>
      isClosed_le continuous_const (by dsimp [latticeNormal]; fun_prop)))
  · intro x hx y hy r s hr hs hrs i hi
    change (z i : ℝ) ≤ latticeNormal (μ i) (r • x + s • y)
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    have hb := add_le_add (mul_le_mul_of_nonneg_left (hx i hi) hr) (mul_le_mul_of_nonneg_left (hy i hi) hs)
    have he : r * (z i : ℝ) + s * (z i : ℝ) = (z i : ℝ) := by rw [← add_mul, hrs, one_mul]
    rwa [he] at hb

-- an actual contained ray segment of unbounded length forces every negatively sloped support to escape.
theorem inward_support_escapes_along_long_ray (μ : Site →+ ℤ) (p : Site) (hp : μ p < 0)
    (B : RealPlane) (lengths : ℕ → ℕ) (hlengths : Tendsto lengths atTop atTop) (z : ℕ → ℤ)
    (hbound : ∀ n, (z n : ℝ) ≤ latticeNormal μ (B + (lengths n : ℝ) • latticeEmbedding p)) :
    Tendsto (fun n => (z n : ℝ)) atTop atBot := by
  apply tendsto_atBot.mpr
  intro t
  obtain ⟨N, hN⟩ := exists_nat_gt (latticeNormal μ B - t)
  have hμ : (μ p : ℝ) ≤ -1 := by exact_mod_cast (by omega : μ p ≤ -1)
  filter_upwards [(tendsto_atTop.mp hlengths) N] with n hn
  have hb := hbound n
  rw [map_add, map_smul, latticeNormal_embedding, smul_eq_mul] at hb
  have hlength : (N : ℝ) ≤ (lengths n : ℝ) := by exact_mod_cast hn
  have hlengthNonnegative : (0 : ℝ) ≤ (lengths n : ℝ) := Nat.cast_nonneg _
  nlinarith

end KumarNivat
