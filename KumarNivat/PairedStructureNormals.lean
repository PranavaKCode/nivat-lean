module

public import KumarNivat.PairedStructureBalls
public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section

open Filter Topology

namespace KumarNivat

-- these normals point from the nearest disagreement back into its agreement ball.
noncomputable def inwardUnitNormal (g : Site) : RealPlane :=
  (-((g.1 : ℝ) / Real.sqrt (latticeEnergy g)),
    -((g.2 : ℝ) / Real.sqrt (latticeEnergy g)))

-- the real direction acts on the unchanged integer coordinates.
def realDotNormal (v : RealPlane) : Site →+ ℝ :=
  { toFun := fun h => v.1 * (h.1 : ℝ) + v.2 * (h.2 : ℝ)
    map_zero' := by simp
    map_add' := by intro h k; simp only [Prod.fst_add, Prod.snd_add, Int.cast_add]; ring }

-- positive distance makes the normalized inward direction a genuine unit vector.
theorem inwardUnitNormal_unit (g : Site) (hg : 0 < latticeEnergy g) :
    (inwardUnitNormal g).1 ^ 2 + (inwardUnitNormal g).2 ^ 2 = 1 := by
  have hpos : 0 < (latticeEnergy g : ℝ) := by exact_mod_cast hg
  have hr : 0 < Real.sqrt (latticeEnergy g) := Real.sqrt_pos.mpr hpos
  have he := Real.sq_sqrt (le_of_lt hpos)
  simp only [inwardUnitNormal, neg_sq, div_pow]
  rw [← add_div, ← latticeEnergy_cast, he]
  exact div_self (ne_of_gt hpos)

-- unit directions all lie in one fixed compact coordinate square.
theorem inwardUnitNormal_mem_square (g : Site) (hg : 0 < latticeEnergy g) :
    inwardUnitNormal g ∈ Set.Icc ((-1, -1) : RealPlane) (1, 1) := by
  have hunit := inwardUnitNormal_unit g hg
  have hx : |(inwardUnitNormal g).1| ≤ 1 := (sq_le_one_iff_abs_le_one _).mp
    (by nlinarith [sq_nonneg (inwardUnitNormal g).2])
  have hy : |(inwardUnitNormal g).2| ≤ 1 := (sq_le_one_iff_abs_le_one _).mp
    (by nlinarith [sq_nonneg (inwardUnitNormal g).1])
  exact ⟨⟨(abs_le.mp hx).1, (abs_le.mp hy).1⟩, ⟨(abs_le.mp hx).2, (abs_le.mp hy).2⟩⟩

-- convergence preserves the unit equation and therefore excludes the zero normal.
theorem limiting_unit_normal_ne_zero (v : ℕ → RealPlane) (w : RealPlane)
    (hv : Tendsto v atTop (𝓝 w)) (hunit : ∀ n, (v n).1 ^ 2 + (v n).2 ^ 2 = 1) :
    realDotNormal w ≠ 0 := by
  have hs : Tendsto (fun n => (v n).1 ^ 2 + (v n).2 ^ 2) atTop
      (𝓝 (w.1 ^ 2 + w.2 ^ 2)) := (hv.fst_nhds.pow 2).add (hv.snd_nhds.pow 2)
  have hs' : Tendsto (fun n => (v n).1 ^ 2 + (v n).2 ^ 2) atTop (𝓝 (1 : ℝ)) := by
    simpa only [hunit] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  have he : w.1 ^ 2 + w.2 ^ 2 = 1 := tendsto_nhds_unique hs hs'
  intro hz
  have hx := congrArg (fun ell : Site →+ ℝ => ell (1, 0)) hz
  have hy := congrArg (fun ell : Site →+ ℝ => ell (0, 1)) hz
  simp only [realDotNormal, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Int.cast_one, Int.cast_zero,
    mul_one, mul_zero, add_zero, zero_add, AddMonoidHom.zero_apply] at hx hy
  rw [hx, hy] at he
  norm_num at he

-- every site strictly inside the limiting half-plane eventually lies in the growing balls.
theorem eventually_inside_nearest_disagreement_ball (g : ℕ → Site)
    (hlarge : ∀ n, n ^ 2 < latticeEnergy (g n))
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (w : RealPlane)
    (hlimit : Tendsto (inwardUnitNormal ∘ g ∘ φ) atTop (𝓝 w))
    (h : Site) (hpositive : 0 < realDotNormal w h) :
    ∀ᶠ n in atTop, latticeEnergy (g (φ n) + h) < latticeEnergy (g (φ n)) := by
  let a : ℝ := realDotNormal w h
  let b : ℝ := latticeEnergy h
  have ha : 0 < a := hpositive
  have hdots : Tendsto (fun n => realDotNormal (inwardUnitNormal (g (φ n))) h) atTop (𝓝 a) := by
    exact (hlimit.fst_nhds.mul_const (h.1 : ℝ)).add (hlimit.snd_nhds.mul_const (h.2 : ℝ))
  have hdot : ∀ᶠ n in atTop, a / 2 < realDotNormal (inwardUnitNormal (g (φ n))) h :=
    hdots.eventually (Ioi_mem_nhds (by dsimp [a] at ha ⊢; linarith))
  obtain ⟨N, hN⟩ := exists_nat_gt (b / a)
  filter_upwards [hdot, eventually_ge_atTop N] with n hn hnN
  let r : ℝ := Real.sqrt (latticeEnergy (g (φ n)))
  have hrnonneg : 0 ≤ r := Real.sqrt_nonneg _
  have hlarge' : (φ n : ℝ) ^ 2 < (latticeEnergy (g (φ n)) : ℝ) := by
    exact_mod_cast hlarge (φ n)
  have hrsq : r ^ 2 = (latticeEnergy (g (φ n)) : ℝ) :=
    Real.sq_sqrt (by positivity : 0 ≤ (latticeEnergy (g (φ n)) : ℝ))
  have hrφ : (φ n : ℝ) < r := by
    nlinarith [show (0 : ℝ) ≤ (φ n : ℝ) from Nat.cast_nonneg _]
  have hφn : (n : ℝ) ≤ φ n := by exact_mod_cast hφ.id_le n
  have hnN' : (N : ℝ) ≤ n := by exact_mod_cast hnN
  have hr : b / a < r := lt_of_lt_of_le hN (by linarith)
  have hra : b < r * a := (div_lt_iff₀ ha).mp hr
  have hrpos : 0 < r := by
    exact lt_of_le_of_lt (Nat.cast_nonneg (φ n)) hrφ
  have hstep : 2 * r * realDotNormal (inwardUnitNormal (g (φ n))) h > b := by
    nlinarith
  have hfactor : r * realDotNormal (inwardUnitNormal (g (φ n))) h =
      -((g (φ n)).1 : ℝ) * (h.1 : ℝ) - ((g (φ n)).2 : ℝ) * (h.2 : ℝ) := by
    have hrootneq : Real.sqrt (latticeEnergy (g (φ n))) ≠ 0 := ne_of_gt hrpos
    dsimp [realDotNormal, inwardUnitNormal, r]
    field_simp [hrootneq]
    ring
  rw [mul_assoc, hfactor] at hstep
  have he₀ := latticeEnergy_cast (g (φ n))
  have he₁ := latticeEnergy_cast (g (φ n) + h)
  have heh := latticeEnergy_cast h
  simp only [Prod.fst_add, Prod.snd_add, Int.cast_add] at he₁
  have hreal : (latticeEnergy (g (φ n) + h) : ℝ) < (latticeEnergy (g (φ n)) : ℝ) := by
    dsimp [b] at hstep
    nlinarith
  exact_mod_cast hreal

end KumarNivat
