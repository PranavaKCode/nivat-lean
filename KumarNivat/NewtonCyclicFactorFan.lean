import KumarNivat.NewtonCyclicFactorPrimitive
import KumarNivat.NewtonCyclicFactorDouble

namespace KumarNivat

-- the actual distinct factor list constructs its primitive cyclic fan, including antipodal and strict half-turn metadata.
theorem actual_primitive_factor_cyclic_fan (hs : List Site) (hlen : 2 ≤ hs.length)
    (hdirs : ∀ h ∈ hs, h ≠ 0) (hpairs : hs.Pairwise (fun p q => determinant p q ≠ 0)) :
    ∃ q : ℕ, ∃ hq : 2 ≤ q,
      let _ : NeZero q := ⟨by omega⟩
      q = hs.length ∧ ∃ E : ZMod (2 * q) → Site,
        CyclicEdgeOrder E ∧
        (∀ i, E (i + (q : ZMod (2 * q))) = -E i) ∧
        (∀ i (d : ℕ), 0 < d → d < q → 0 < determinant (E i) (E (i + (d : ZMod (2 * q))))) ∧
        (∀ i, Int.gcd (E i).1 (E i).2 = 1) ∧
        (∀ i, ∃ g ∈ hs, determinant (E i) g = 0) ∧
        (∀ g ∈ hs, ∃ i : ZMod (2 * q), determinant (E i) g = 0) ∧
        ∃ f : Fin q → Site, ∃ k : Fin q → ℕ,
          List.ofFn f = upperSortedFactors hs ∧
          (∀ i, 0 < k i ∧ f i = (k i : ℤ) • E (i.val : ZMod (2 * q))) := by
  classical
  obtain ⟨q, hqeq, hq, f, e, k, hlist, hdata, hstrict, hsource⟩ :=
    actual_sorted_primitive_factor_data hs hlen hdirs hpairs
  let _ : NeZero q := ⟨by omega⟩
  let E := doubledFactorDirections q e
  have hfirst (i : Fin q) : E (i.val : ZMod (2 * q)) = e i := by
    have hi : (i.val : ZMod (2 * q)).val = i.val := ZMod.val_natCast_of_lt (by omega)
    simp only [E, doubledFactorDirections, hi, i.isLt, dite_true]
  have hparallel (i : Fin q) : determinant (e i) (f i) = 0 := by
    change directionNormal (e i) (f i) = 0
    rw [(hdata i).2.1, map_zsmul, directionNormal_self, smul_zero]
  have hnegparallel (p g : Site) : determinant (-p) g = -determinant p g := by simp [determinant]; ring
  have hsignsource (i : Fin q) : ∃ g ∈ hs, determinant (e i) g = 0 := by
    obtain ⟨g, hg, hsign⟩ := hsource i
    refine ⟨g, hg, ?_⟩
    have hp := hparallel i
    rcases hsign with he | he
    · rwa [he] at hp
    · change directionNormal (e i) (f i) = 0 at hp
      rw [he, map_neg] at hp
      change determinant (e i) g = 0
      exact neg_eq_zero.mp hp
  have hprimitive (i : ZMod (2 * q)) : Int.gcd (E i).1 (E i).2 = 1 := by
    by_cases hi : i.val < q
    · simpa only [E, doubledFactorDirections, hi, dite_true] using (hdata ⟨i.val, hi⟩).2.2.1
    · let j : Fin q := ⟨i.val - q, by have h := ZMod.val_lt i; omega⟩
      obtain ⟨τ, hτ, _hker⟩ := primitive_direction_coordinate (e j) (hdata j).2.2.1
      have hneg : Int.gcd (-e j).1 (-e j).2 = 1 :=
        primitive_gcd_of_line_coordinate (-e j) (-τ) (by simp [hτ])
      simpa only [E, doubledFactorDirections, hi, dite_false] using hneg
  have hactual (i : ZMod (2 * q)) : ∃ g ∈ hs, determinant (E i) g = 0 := by
    by_cases hi : i.val < q
    · simpa only [E, doubledFactorDirections, hi, dite_true] using hsignsource ⟨i.val, hi⟩
    · let j : Fin q := ⟨i.val - q, by have h := ZMod.val_lt i; omega⟩
      obtain ⟨g, hg, hp⟩ := hsignsource j
      refine ⟨g, hg, ?_⟩
      simp only [E, doubledFactorDirections, hi, dite_false]
      rw [hnegparallel]
      exact neg_eq_zero.mpr hp
  have hcover (g : Site) (hg : g ∈ hs) : ∃ i : ZMod (2 * q), determinant (E i) g = 0 := by
    have hm : upperFactorDirection g ∈ upperSortedFactors hs :=
      (upperSortedFactors_perm hs).mem_iff.mpr (List.mem_map.mpr ⟨g, hg, rfl⟩)
    rw [← hlist] at hm
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hm
    refine ⟨(i.val : ZMod (2 * q)), ?_⟩
    rw [hfirst]
    have hp := hparallel i
    rw [hi] at hp
    rcases upperFactorDirection_choice g with he | he
    · rwa [he] at hp
    · change directionNormal (e i) (upperFactorDirection g) = 0 at hp
      rw [he, map_neg] at hp
      exact neg_eq_zero.mp hp
  refine ⟨q, hq, hqeq, E, doubledFactorDirections_cyclic_order q hq e hstrict,
    doubledFactorDirections_antipodal q e,
    doubledFactorDirections_positive_offset q e hstrict,
    hprimitive, hactual, hcover, f, k, hlist, ?_⟩
  intro i
  rw [hfirst]
  exact ⟨(hdata i).1, (hdata i).2.1⟩

end KumarNivat
