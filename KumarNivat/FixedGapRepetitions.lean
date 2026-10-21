module

public import KumarNivat.FiniteWordDynamics
public import KumarNivat.OrbitLanguage
public import Mathlib.Order.Interval.Finset.Basic

@[expose] public section

namespace KumarNivat

-- a single bounded positive repeat gap occurs at arbitrarily late positions.
theorem fixed_gap_repetitions_unbounded {A : Type*} (s : ℕ → A) (hs : (Set.range s).Finite) :
    ∃ D : ℕ, 0 < D ∧ D ≤ (Set.range s).ncard ∧
      ∀ N : ℕ, ∃ i : ℕ, N ≤ i ∧ s (i + D) = s i := by
  classical
  let M := (Set.range s).ncard
  have hrepeat (b : ℕ) : ∃ D : Fin (M + 1), 0 < D.val ∧
      ∃ i : ℕ, b ≤ i ∧ s (i + D.val) = s i := by
    obtain ⟨i, j, hij, hj, he⟩ := finite_state_short_collision (fun n => s (b + n))
      (Set.range s) hs (fun n => ⟨b + n, rfl⟩)
    refine ⟨⟨j - i, by dsimp [M]; omega⟩, (by change 0 < j - i; omega), b + i, by omega, ?_⟩
    change s (b + i + (j - i)) = s (b + i)
    have hsite : b + i + (j - i) = b + j := by omega
    simpa only [hsite] using he.symm
  let gap : ℕ → Fin (M + 1) := fun b => Classical.choose (hrepeat b)
  have hgap (b : ℕ) : 0 < (gap b).val ∧ ∃ i : ℕ, b ≤ i ∧ s (i + (gap b).val) = s i :=
    Classical.choose_spec (hrepeat b)
  obtain ⟨D, hD⟩ := Finite.exists_infinite_fiber gap
  have hinfinite : (gap ⁻¹' {D}).Infinite := Set.infinite_coe_iff.mp hD
  obtain ⟨b, hb⟩ := hinfinite.nonempty
  have hb' : gap b = D := Set.mem_singleton_iff.mp hb
  have hpositive : 0 < D.val := by simpa only [hb'] using (hgap b).1
  refine ⟨D.val, hpositive, by have hlt := D.isLt; dsimp [M] at hlt; omega, ?_⟩
  intro N
  obtain ⟨b, hb, hNb⟩ := hinfinite.exists_gt N
  have hb' : gap b = D := Set.mem_singleton_iff.mp hb
  obtain ⟨i, hbi, he⟩ := (hgap b).2
  refine ⟨i, by omega, ?_⟩
  simpa only [hb'] using he

-- finite legal patterns provide one displacement that repeats the same finite band arbitrarily far out.
theorem fixed_gap_legal_pattern_repetitions {A : Type*} (c x : Site → A)
    (hc : (Set.range c).Finite) (hlang : LanguageContained x c) (F : Finset Site) (h : Site) :
    ∃ D : ℕ, 0 < D ∧ D ≤ complexity c F ∧
      ∀ N : ℕ, ∃ q : ℕ, N ≤ q ∧ ∀ u ∈ F,
        x ((u + (q : ℤ) • h) + (D : ℤ) • h) = x (u + (q : ℤ) • h) := by
  let s : ℕ → (F → A) := fun q u => x ((q : ℤ) • h + u.val)
  have hsub : Set.range s ⊆ patterns c F := by
    rintro _ ⟨q, rfl⟩
    exact patterns_subset_of_language x c hlang F ⟨(q : ℤ) • h, rfl⟩
  have hfinite := patterns_finite_of_range c hc F
  obtain ⟨D, hD, hbound, hrepeats⟩ := fixed_gap_repetitions_unbounded s (hfinite.subset hsub)
  have hcount : (Set.range s).ncard ≤ complexity c F := Set.ncard_le_ncard hsub hfinite
  refine ⟨D, hD, hbound.trans hcount, ?_⟩
  intro N
  obtain ⟨q, hq, he⟩ := hrepeats N
  refine ⟨q, hq, ?_⟩
  intro u hu
  have he' := congrFun he ⟨u, hu⟩
  simpa only [s, Nat.cast_add, add_smul, add_comm, add_assoc, add_left_comm] using he'

end KumarNivat
