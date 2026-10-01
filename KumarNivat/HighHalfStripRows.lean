import KumarNivat.HalfOpenRayRows
import KumarNivat.LocalRowSelection
import KumarNivat.HalfStripTuplePeriods

namespace KumarNivat

open scoped Pointwise

-- finite row representatives give one normal-height threshold above which the entire semi-open strip is sampled.
theorem high_half_open_strip_subset_sampled_half_strip (S : Finset Site) (hS : LatticeConvex S)
    (q₀ a b : Site) (r t : ℕ) (ht : 0 < t) (hdet : 0 < determinant a b)
    (hsub : latticeParallelogram q₀ a b r t ⊆ latticeHull S)
    (μ : Site →+ ℤ) (m : ℤ) (hq₀ : μ q₀ = m) (ha : 0 < μ a) (hb : μ b = 0)
    (E : localParallelogramSites S q₀ a b r t μ m → Site)
    (hcover : ∀ u, ∃ d : ℤ, u.val = E u + d • b) (N : ℤ) :
    ∃ j₀ : ℤ, directionNormal a q₀ ≤ j₀ ∧ ∀ g : Site,
      latticeEmbedding g ∈ halfOpenRayStrip q₀ a b r → j₀ ≤ directionNormal a g →
        g ∈ sampledHalfStrip E b N := by
  classical
  let d : localParallelogramSites S q₀ a b r t μ m → ℤ := fun u => Classical.choose (hcover u)
  have hd (u : localParallelogramSites S q₀ a b r t μ m) : u.val = E u + d u • b :=
    Classical.choose_spec (hcover u)
  let M : ℕ := ∑ u : localParallelogramSites S q₀ a b r t μ m, (N - d u).natAbs
  let j₀ := directionNormal a q₀ + (M : ℤ) * determinant a b
  have hD : (0 : ℝ) < (determinant a b : ℝ) := by exact_mod_cast hdet
  have hnormalA : directionNormal a a = 0 := by simp [directionNormal, determinant, mul_comm]
  refine ⟨j₀, ?_, ?_⟩
  · dsimp [j₀]
    exact le_add_of_nonneg_right (mul_nonneg (Int.natCast_nonneg M) (le_of_lt hdet))
  · intro g hg hj
    obtain ⟨α, β, hα, hαr, _hβ, he⟩ := hg
    have hheight := congrArg (latticeNormal (directionNormal a)) he
    simp only [map_add, map_smul, latticeNormal_embedding, hnormalA, Int.cast_zero,
      smul_eq_mul, mul_zero, add_zero] at hheight
    change (directionNormal a g : ℝ) = (directionNormal a q₀ : ℝ) + β * (determinant a b : ℝ) at hheight
    have hjR : (directionNormal a q₀ : ℝ) + (M : ℝ) * (determinant a b : ℝ) ≤
        (directionNormal a g : ℝ) := by
      have hh : (j₀ : ℝ) ≤ (directionNormal a g : ℝ) := by exact_mod_cast hj
      simpa only [j₀, Int.cast_add, Int.cast_mul, Int.cast_natCast] using hh
    have hβM : (M : ℝ) ≤ β :=
      (mul_le_mul_iff_of_pos_right hD).mp (by linarith [hheight])
    let k : ℤ := ⌊β⌋
    have hk : (M : ℤ) ≤ k := Int.le_floor.mpr (by simpa only [Int.cast_natCast] using hβM)
    let u := g - k • b
    have huembed : latticeEmbedding u = latticeEmbedding q₀ + α • latticeEmbedding a +
        (β - (k : ℝ)) • latticeEmbedding b := by
      dsimp [u]
      rw [latticeEmbedding_sub, latticeEmbedding_zsmul, he, sub_smul]
      abel
    have hphase₀ : 0 ≤ β - (k : ℝ) := sub_nonneg.mpr (Int.floor_le β)
    have hphase₁ : β - (k : ℝ) ≤ (t : ℝ) := by
      have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
      have hphase : β - (k : ℝ) < 1 := Int.fract_lt_one β
      exact (le_of_lt hphase).trans htR
    have huJ : latticeEmbedding u ∈ latticeParallelogram q₀ a b r t := by
      refine Set.mem_add.mpr ⟨latticeEmbedding q₀ + (β - (k : ℝ)) • latticeEmbedding b,
        ⟨β - (k : ℝ), ⟨hphase₀, hphase₁⟩, rfl⟩, α • latticeEmbedding a,
        ⟨α, ⟨le_of_lt hα, hαr⟩, by simp only [zero_add]⟩, ?_⟩
      rw [huembed]
      abel
    have hum : μ u ≠ m := by
      have huheight := congrArg (latticeNormal μ) huembed
      simp only [map_add, map_smul, latticeNormal_embedding, hq₀, hb, Int.cast_zero,
        smul_eq_mul, mul_zero, add_zero] at huheight
      intro heq
      rw [heq] at huheight
      have hapos : (0 : ℝ) < (μ a : ℝ) := by exact_mod_cast ha
      nlinarith [mul_pos hα hapos]
    have husites : u ∈ localParallelogramSites S q₀ a b r t μ m :=
      Finset.mem_filter.mpr ⟨hS u (hsub huJ), huJ, hum⟩
    let u₀ : localParallelogramSites S q₀ a b r t μ m := ⟨u, husites⟩
    have hterm : (N - d u₀).natAbs ≤ M := by
      dsimp [M]
      exact Finset.single_le_sum (f := fun v : localParallelogramSites S q₀ a b r t μ m => (N - d v).natAbs)
        (fun _v _hv => Nat.zero_le _) (Finset.mem_univ u₀)
    have hgap : N - d u₀ ≤ (M : ℤ) := (Int.le_natAbs).trans (by exact_mod_cast hterm)
    have hn : N ≤ d u₀ + k := by omega
    have hgsite : g = E u₀ + (d u₀ + k) • b := by
      have hu : g = u + k • b := by dsimp [u]; abel
      rw [hu, show u = E u₀ + d u₀ • b from hd u₀, add_smul]
      abel
    refine ⟨(u₀, (d u₀ + k - N).toNat), ?_⟩
    change E u₀ + (N + ((d u₀ + k - N).toNat : ℤ)) • b = g
    have hindex : N + ((d u₀ + k - N).toNat : ℤ) = d u₀ + k := by omega
    rw [hindex]
    exact hgsite.symm

-- the sampled half-strip therefore contains r consecutive original lattice sites on every sufficiently high primitive row.
theorem sampled_half_strip_has_high_consecutive_rows (S : Finset Site) (hS : LatticeConvex S)
    (q₀ a b : Site) (hprimitive : Int.gcd a.1 a.2 = 1) (r t : ℕ)
    (ht : 0 < t) (hdet : 0 < determinant a b)
    (hsub : latticeParallelogram q₀ a b r t ⊆ latticeHull S)
    (μ : Site →+ ℤ) (m : ℤ) (hq₀ : μ q₀ = m) (ha : 0 < μ a) (hb : μ b = 0)
    (E : localParallelogramSites S q₀ a b r t μ m → Site)
    (hcover : ∀ u, ∃ d : ℤ, u.val = E u + d • b) (N : ℤ) :
    ∃ j₀ : ℤ, ∀ j : ℤ, j₀ ≤ j → ∃ F : Site, directionNormal a F = j ∧
      ∀ i : Fin r, F + (i.val : ℤ) • a ∈ sampledHalfStrip E b N := by
  obtain ⟨j₀, hj₀, hhigh⟩ := high_half_open_strip_subset_sampled_half_strip S hS q₀ a b r t ht
    hdet hsub μ m hq₀ ha hb E hcover N
  have hnormal : directionNormal a a = 0 := by simp [directionNormal, determinant, mul_comm]
  refine ⟨j₀, ?_⟩
  intro j hj
  obtain ⟨F, hF, hrun⟩ := half_open_ray_strip_row_run q₀ a b hprimitive hdet r j (hj₀.trans hj)
  refine ⟨F, hF, ?_⟩
  intro i
  apply hhigh _ (hrun i)
  rw [map_add, map_zsmul, hnormal, smul_zero, add_zero, hF]
  exact hj

end KumarNivat
