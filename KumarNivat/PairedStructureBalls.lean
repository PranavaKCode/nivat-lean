module

public import KumarNivat.PairedStructureOrbit
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

namespace KumarNivat

-- squared euclidean distance is an integer, so a first disagreement has an attained minimum.
def latticeEnergy (g : Site) : ℕ := g.1.natAbs ^ 2 + g.2.natAbs ^ 2

-- the exact integer energy has the usual real sum-of-squares value.
theorem latticeEnergy_cast (g : Site) :
    (latticeEnergy g : ℝ) = (g.1 : ℝ) ^ 2 + (g.2 : ℝ) ^ 2 := by
  have hx : (g.1.natAbs : ℤ) ^ 2 = g.1 ^ 2 := by rw [Int.natCast_natAbs, sq_abs]
  have hy : (g.2.natAbs : ℤ) ^ 2 = g.2 ^ 2 := by rw [Int.natCast_natAbs, sq_abs]
  have hi : (latticeEnergy g : ℤ) = g.1 ^ 2 + g.2 ^ 2 := by
    simp only [latticeEnergy, Nat.cast_add, Nat.cast_pow, hx, hy]
  exact_mod_cast hi

-- the square contains every lattice point at squared distance at most its radius squared.
theorem mem_lattice_square_of_energy_le (n : ℕ) (g : Site) (hg : latticeEnergy g ≤ n ^ 2) :
    g ∈ (Finset.Icc (-(n : ℤ)) n).product (Finset.Icc (-(n : ℤ)) n) := by
  have hx : g.1.natAbs ≤ n := by
    have hsq : g.1.natAbs ^ 2 ≤ n ^ 2 := le_trans (Nat.le_add_right _ _) hg
    nlinarith
  have hy : g.2.natAbs ≤ n := by
    have hsq : g.2.natAbs ^ 2 ≤ n ^ 2 := le_trans (Nat.le_add_left _ _) hg
    nlinarith
  apply Finset.mem_product.mpr
  constructor <;> apply Finset.mem_Icc.mpr
  · have he : |g.1| ≤ (n : ℤ) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast hx
    exact abs_le.mp he
  · have he : |g.2| ≤ (n : ℤ) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast hy
    exact abs_le.mp he

-- infinitely many configurations cannot be separated by a single finite window.
theorem infinite_orbitClosure_pairs_agree_window {A : Type*} [TopologicalSpace A]
    [DiscreteTopology A] (c : Site → A) (hc : (Set.range c).Finite)
    (hinfinite : (orbitClosure c).Infinite) (D : Finset Site) :
    ∃ x ∈ orbitClosure c, ∃ y ∈ orbitClosure c, x ≠ y ∧ ∀ g ∈ D, x g = y g := by
  let read : (Site → A) → (D → A) := fun x u => x u.val
  let words : Set (D → A) := {w | ∀ u, w u ∈ Set.range c}
  have hfinite : words.Finite := Set.Finite.pi' (fun _ : D => hc)
  have hmaps : Set.MapsTo read (orbitClosure c) words := by
    intro x hx u
    obtain ⟨t, ht⟩ := languageContained_of_mem_orbitClosure c x hx {0} u.val
    have he := ht 0 (Finset.mem_singleton_self 0)
    simp only [add_zero] at he
    exact ⟨t, he.symm⟩
  obtain ⟨x, hx, y, hy, hne, he⟩ := hinfinite.exists_ne_map_eq_of_mapsTo hmaps hfinite
  exact ⟨x, hx, y, hy, hne, fun g hg => congrFun he ⟨g, hg⟩⟩

-- translating a nearest disagreement to the origin keeps all smaller euclidean balls equal.
theorem infinite_orbitClosure_nearest_disagreement {A : Type*} [TopologicalSpace A]
    [DiscreteTopology A] (c : Site → A) (hc : (Set.range c).Finite)
    (hinfinite : (orbitClosure c).Infinite) (n : ℕ) :
    ∃ x ∈ orbitClosure c, ∃ y ∈ orbitClosure c, ∃ g : Site,
      n ^ 2 < latticeEnergy g ∧ x 0 ≠ y 0 ∧
      ∀ h : Site, latticeEnergy (g + h) < latticeEnergy g → x h = y h := by
  classical
  obtain ⟨x, hx, y, hy, hne, hagree⟩ := infinite_orbitClosure_pairs_agree_window c hc hinfinite
    ((Finset.Icc (-(n : ℤ)) n).product (Finset.Icc (-(n : ℤ)) n))
  have hdiff : ∃ m : ℕ, ∃ g : Site, latticeEnergy g = m ∧ x g ≠ y g := by
    obtain ⟨g, hg⟩ := Function.ne_iff.mp hne
    exact ⟨latticeEnergy g, g, rfl, hg⟩
  obtain ⟨g, henergy, hg⟩ := Nat.find_spec hdiff
  have hlarge : n ^ 2 < latticeEnergy g := by
    by_contra! hsmall
    exact hg (hagree g (mem_lattice_square_of_energy_le n g hsmall))
  refine ⟨shift g x, orbitClosure_shift_mem c x hx g,
    shift g y, orbitClosure_shift_mem c y hy g, g, hlarge, ?_, ?_⟩
  · simpa only [shift, zero_add] using hg
  · intro h hh
    change x (h + g) = y (h + g)
    by_contra hfail
    have hmin := Nat.find_min hdiff (henergy ▸ hh)
    exact hmin ⟨g + h, rfl, by simpa only [add_comm] using hfail⟩

end KumarNivat
