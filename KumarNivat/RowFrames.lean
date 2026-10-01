import KumarNivat.PrimitiveDirections
import Mathlib.Data.Finset.Image

namespace KumarNivat

-- this finite frame observes p consecutive sites on each of d-plus-one consecutive lattice levels.
def rowFrame (E a v : Site) (p d : ℕ) : Finset Site :=
  Finset.univ.image (fun z : Fin p × Fin (d + 1) => E + (z.1.val : ℤ) • a + (z.2.val : ℤ) • v)

-- every displayed row block is part of the actual finite observation window.
theorem rowFrame_mem (E a v : Site) (p d : ℕ) (i : Fin p) (j : Fin (d + 1)) :
    E + (i.val : ℤ) • a + (j.val : ℤ) • v ∈ rowFrame E a v p d :=
  Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩

-- the unit transverse coordinate gives the exact integer normal levels of the frame.
theorem rowFrame_normal_bounds (E a v : Site) (p d : ℕ)
    (hv : directionNormal a v = 1) :
    ∀ g ∈ rowFrame E a v p d,
      directionNormal a E ≤ directionNormal a g ∧ directionNormal a g ≤ directionNormal a E + (d : ℤ) := by
  intro g hg
  obtain ⟨⟨i, j⟩, _hz, rfl⟩ := Finset.mem_image.mp hg
  have ha : directionNormal a a = 0 := by simp [directionNormal, determinant, mul_comm]
  rw [map_add, map_add, map_zsmul, map_zsmul, ha, hv, smul_zero, add_zero, smul_eq_mul, mul_one]
  have hj := j.isLt
  omega

-- every integer level in the frame has a full observed block of the original tangent length.
theorem rowFrame_block_on_level (E a v : Site) (p d : ℕ) (hv : directionNormal a v = 1)
    (j : ℤ) (hj : directionNormal a E ≤ j) (hjd : j ≤ directionNormal a E + (d : ℤ)) :
    ∃ F : Site, directionNormal a F = j ∧ ∀ i : Fin p,
      F + (i.val : ℤ) • a ∈ rowFrame E a v p d := by
  let k : Fin (d + 1) := ⟨(j - directionNormal a E).toNat, by omega⟩
  have hk : (k.val : ℤ) = j - directionNormal a E := by dsimp [k]; omega
  let F := E + (k.val : ℤ) • v
  refine ⟨F, ?_, ?_⟩
  · dsimp [F]
    rw [map_add, map_zsmul, hv, smul_eq_mul, mul_one, hk]
    omega
  · intro i
    have hsite : F + (i.val : ℤ) • a = E + (i.val : ℤ) • a + (k.val : ℤ) • v := by dsimp [F]; abel
    rw [hsite]
    exact rowFrame_mem E a v p d i k

-- translating the base translates the whole frame without altering its row coordinates.
theorem rowFrame_translate (E a v h : Site) (p d : ℕ) :
    rowFrame (E + h) a v p d = (rowFrame E a v p d).image (fun u => u + h) := by
  simp only [rowFrame, Finset.image_image]
  congr 1
  funext z
  change E + h + (z.1.val : ℤ) • a + (z.2.val : ℤ) • v =
    (E + (z.1.val : ℤ) • a + (z.2.val : ℤ) • v) + h
  abel

end KumarNivat
