module

public import KumarNivat.FailedRayContinuation

@[expose] public section

namespace KumarNivat

open scoped Pointwise

-- a full degree-length zero block propagates forward through every fitting ray recurrence.
theorem zero_tail_of_ray_recurrence_block {K : Type*} [CommRing K] [NoZeroDivisors K]
    (t : ℕ) (α : Fin (t + 1) → K) (a : ℤ → K) (start block : ℤ)
    (hlast : α (Fin.last t) ≠ 0) (hrec : RayRecurrence t α a start) (hblock : start ≤ block)
    (hzero : ∀ i : Fin t, a (block + (i.val : ℤ)) = 0) :
    ∀ n : ℤ, block ≤ n → a n = 0 := by
  intro n hn
  exact zero_of_interval_recurrence_prefix t α a block n hlast
    (fun k hk _hfit => hrec k (hblock.trans hk)) hzero n hn le_rfl

-- absence of an agreement tail forces a disagreement in every late block of the actual degree.
theorem ray_recurrence_no_tail_has_nonzero_blocks {K : Type*} [CommRing K] [NoZeroDivisors K]
    (t : ℕ) (α : Fin (t + 1) → K) (a : ℤ → K) (start : ℤ)
    (hlast : α (Fin.last t) ≠ 0) (hrec : RayRecurrence t α a start)
    (hnotail : ¬ ∃ N : ℤ, ∀ n : ℤ, N ≤ n → a n = 0) :
    ∀ block : ℤ, start ≤ block → ∃ i : Fin t, a (block + (i.val : ℤ)) ≠ 0 := by
  intro block hblock
  by_contra! hzero
  exact hnotail ⟨block, zero_tail_of_ray_recurrence_block t α a start block hlast hrec hblock hzero⟩

-- actual minkowski stencil fits derive the facet recurrence and a persistent finite block directly from failure.
theorem failed_minkowski_boundary_has_finite_disagreement_blocks {K : Type*}
    [CommRing K] [NoZeroDivisors K] (x y : Site → K) (f : Laurent K) (hf : f ≠ 0)
    (hxann : laurentAct f x = 0) (hyann : laurentAct f y = 0)
    (ν : Site →+ ℤ) (hν : ν ≠ 0) (β : ℤ) (b : Site) (hb : ν b = 0)
    (hprimitive : Int.gcd b.1 b.2 = 1) (P C : Set RealPlane)
    (hsum : P = latticeHull f.coeff.support + C)
    (hbound : ∀ z ∈ P, (β : ℝ) ≤ latticeNormal ν z)
    (hforward : ∀ z ∈ P, ∀ s : ℝ, 0 ≤ s → z + s • latticeEmbedding b ∈ P)
    (hagree : ∀ g : Site, latticeEmbedding g ∈ P → β + 1 ≤ ν g → x g = y g)
    (hfail : ∃ g : Site, latticeEmbedding g ∈ P ∧ x g ≠ y g) :
    ∃ A : Site, ∃ t : ℕ, 0 < t ∧ ν A = β ∧ latticeEmbedding A ∈ P ∧
      ∀ n : ℤ, 0 ≤ n → ∃ i : Fin t,
        x (A + (n + (i.val : ℤ)) • b) ≠ y (A + (n + (i.val : ℤ)) • b) := by
  classical
  obtain ⟨A, hA, hneq⟩ := hfail
  have hlevel : ν A = β := by
    have hlow : β ≤ ν A := by
      have h := hbound (latticeEmbedding A) hA
      rw [latticeNormal_embedding] at h
      exact_mod_cast h
    by_contra hn
    exact hneq (hagree A hA (by omega))
  have hbne : b ≠ 0 := by rintro rfl; simp at hprimitive
  have hsupp : f.coeff.support.Nonempty := Finsupp.support_nonempty_iff.mpr
    (fun hz => hf (AddMonoidAlgebra.coeff_injective hz))
  obtain ⟨v, hv, hmin⟩ := f.coeff.support.exists_min_image ν hsupp
  obtain ⟨q₀, t, α, _hfirst, hlast, hq₀, hq₀mem, _hq₁mem, _hexposed, hdecomp, hface⟩ :=
    exists_actual_exposed_geometric_face_data f ν hν (ν v) hmin v b hbne hprimitive hb hv rfl
  let δ := x - y
  have hann : laurentAct f δ = 0 := by rw [laurentAct_config_sub, hxann, hyann, sub_self]
  have hrec : RayRecurrence t α (fun n => δ (A + n • b)) 0 := by
    intro n hn
    apply exposed_line_recurrence_at δ f (f - exposedOperator f ν (ν v)) q₀ b A t α hdecomp hann n
    intro u hu
    have hAn : latticeEmbedding (A + n • b) ∈ P := by
      rw [latticeEmbedding_add, latticeEmbedding_zsmul]
      exact hforward (latticeEmbedding A) hA (n : ℝ) (by exact_mod_cast hn)
    have hAnlevel : ν (A + n • b) = β := by
      rw [map_add, map_zsmul, hb, smul_zero, add_zero, hlevel]
    have hfit := boundary_stencil_fit_of_minkowski_recession f ν (ν v) β hmin q₀ b
      hq₀mem hq₀ t hface P C hsum hbound hforward (A + n • b) hAn hAnlevel
        u (exposed_remainder_support_subset f ν (ν v) hu)
    have hstrict := exposed_remainder_strict_level f ν (ν v) hmin u hu
    have hinput : β + 1 ≤ ν ((A + n • b - q₀) + u) := by
      rw [map_add, map_sub, hAnlevel, hq₀]
      omega
    exact sub_eq_zero.mpr (hagree _ hfit hinput)
  have hnotail : ¬ ∃ N : ℤ, ∀ n : ℤ, N ≤ n → δ (A + n • b) = 0 := by
    rintro ⟨N, htail⟩
    apply no_parallel_agreement_tail_of_failed_minkowski_extension x y f hf hxann hyann
      ν hν β b hb hprimitive P C hsum hbound hforward hagree ⟨A, hA, hneq⟩ A hlevel
    exact ⟨N, fun n hn => sub_eq_zero.mp (htail n hn)⟩
  have hblocks := ray_recurrence_no_tail_has_nonzero_blocks t α (fun n => δ (A + n • b))
    0 hlast hrec hnotail
  obtain ⟨i, _hi⟩ := hblocks 0 le_rfl
  have ht : 0 < t := by have := i.isLt; omega
  refine ⟨A, t, ht, hlevel, hA, ?_⟩
  intro n hn
  obtain ⟨i, hi⟩ := hblocks n hn
  exact ⟨i, fun he => hi (sub_eq_zero.mpr he)⟩

end KumarNivat
