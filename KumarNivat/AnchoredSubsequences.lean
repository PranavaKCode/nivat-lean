module

public import KumarNivat.AnchoredCompactness
public import Mathlib.Order.WellQuasiOrder

@[expose] public section

open Filter Topology

namespace KumarNivat

-- finitely many possible values leave one value on an infinite increasing subsequence.
theorem finite_range_constant_subsequence {A : Type*} (f : ℕ → A)
    (hf : (Set.range f).Finite) :
    ∃ v : A, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, f (φ n) = v := by
  have hfreq : ∃ᶠ n in atTop, ∃ v ∈ Set.range f, f n = v :=
    (Eventually.of_forall (fun n => ⟨f n, ⟨n, rfl⟩, rfl⟩)).frequently
  obtain ⟨v, _hv, hconstant⟩ := hf.frequently_exists.mp hfreq
  obtain ⟨φ, hφ, hφconstant⟩ := extraction_of_frequently_atTop hconstant
  exact ⟨v, φ, hφ, hφconstant⟩

-- a periodic reference has only the integer residue phases along its primitive direction.
theorem shift_multiple_eq_period_phase {A : Type*} (w : Site → A) (a : Site)
    (l : ℕ) (hw : IsPeriod w ((l : ℤ) • a)) (k : ℤ) :
    shift (k • a) w = shift ((k % (l : ℤ)) • a) w := by
  funext g
  change w (g + k • a) = w (g + (k % (l : ℤ)) • a)
  have hvector : k • a = (k % (l : ℤ)) • a +
      (k / (l : ℤ)) • ((l : ℤ) • a) := by
    rw [smul_smul, ← add_zsmul]
    congr 1
    exact (Int.emod_add_ediv_mul k (l : ℤ)).symm
  rw [hvector, ← add_assoc]
  exact hw.zsmul (k / (l : ℤ)) _

-- select one actual phase of the same reference before selecting the configuration limit.
theorem periodic_reference_constant_phase {A : Type*} (w : Site → A) (a : Site)
    (l : ℕ) (hl : 0 < l) (hw : IsPeriod w ((l : ℤ) • a)) (k : ℕ → ℤ) :
    ∃ r : ℤ, 0 ≤ r ∧ r < (l : ℤ) ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ n, shift (k (φ n) • a) w = shift (r • a) w := by
  have hlZ : (0 : ℤ) < l := by exact_mod_cast hl
  have hfinite : (Set.range (fun n => k n % (l : ℤ))).Finite := by
    apply (Set.finite_Icc (0 : ℤ) ((l : ℤ) - 1)).subset
    rintro r ⟨n, rfl⟩
    change 0 ≤ k n % (l : ℤ) ∧ k n % (l : ℤ) ≤ (l : ℤ) - 1
    exact ⟨Int.emod_nonneg _ (ne_of_gt hlZ), by
      have hlt := Int.emod_lt_of_pos (k n) hlZ
      omega⟩
  obtain ⟨r, φ, hφ, hr⟩ := finite_range_constant_subsequence _ hfinite
  have hr₀ : 0 ≤ r := by
    rw [← hr 0]
    exact Int.emod_nonneg _ (ne_of_gt hlZ)
  have hr₁ : r < (l : ℤ) := by
    rw [← hr 0]
    exact Int.emod_lt_of_pos _ hlZ
  refine ⟨r, hr₀, hr₁, φ, hφ, fun n => ?_⟩
  rw [shift_multiple_eq_period_phase w a l hw, hr n]

-- dickson's lemma supplies the nondecreasing primitive edge lengths used after anchoring.
theorem anchored_lengths_monotone_subsequence {ι : Type*} [Finite ι]
    (lengths : ℕ → ι → ℕ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ Monotone (lengths ∘ φ) := by
  obtain ⟨φ, hφ⟩ := wellQuasiOrdered_le.exists_monotone_subseq lengths
  exact ⟨φ, φ.strictMono, hφ⟩

-- taking another increasing subsequence preserves all the retained edge inequalities.
theorem anchored_lengths_monotone_comp {ι : Type*} (lengths : ℕ → ι → ℕ)
    (hmono : Monotone lengths) (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    Monotone (lengths ∘ φ) := hmono.comp hφ.monotone

-- a bounded nondecreasing integer edge length is eventually its largest attained value.
theorem anchored_bounded_length_stabilizes (f : ℕ → ℕ) (hf : Monotone f)
    (M : ℕ) (hM : ∀ n, f n ≤ M) :
    ∃ v : ℕ, ∀ᶠ n in atTop, f n = v := by
  classical
  have hrange : (Set.range f).Finite :=
    (Set.finite_Icc 0 M).subset (by
      rintro v ⟨n, rfl⟩
      exact ⟨Nat.zero_le _, hM n⟩)
  have hnonempty : hrange.toFinset.Nonempty :=
    ⟨f 0, hrange.mem_toFinset.mpr ⟨0, rfl⟩⟩
  obtain ⟨v, hv, hmax⟩ := hrange.toFinset.exists_max_image id hnonempty
  obtain ⟨N, hN⟩ := hrange.mem_toFinset.mp hv
  refine ⟨v, (eventually_ge_atTop N).mono (fun n hn => ?_)⟩
  exact le_antisymm (hmax (f n) (hrange.mem_toFinset.mpr ⟨n, rfl⟩))
    (by simpa only [hN] using hf hn)

-- every selected primitive edge either stabilizes or escapes along its ray.
theorem anchored_monotone_length_dichotomy (f : ℕ → ℕ) (hf : Monotone f) :
    (∃ v : ℕ, ∀ᶠ n in atTop, f n = v) ∨ Tendsto f atTop atTop := by
  by_cases hbounded : ∃ M : ℕ, ∀ n, f n ≤ M
  · obtain ⟨M, hM⟩ := hbounded
    exact Or.inl (anchored_bounded_length_stabilizes f hf M hM)
  · right
    apply hf.tendsto_atTop_atTop
    intro M
    push Not at hbounded
    obtain ⟨n, hn⟩ := hbounded M
    exact ⟨n, le_of_lt hn⟩

end KumarNivat
