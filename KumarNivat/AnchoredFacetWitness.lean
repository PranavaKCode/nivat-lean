module

public import KumarNivat.GeometricFacetContinuation

@[expose] public section

namespace KumarNivat

open scoped Pointwise

-- successive actual facet recurrences propagate the fixed seed set through a finite expansion.
theorem anchored_finite_relaxations_zero {K : Type*} [CommRing K] [NoZeroDivisors K]
    (δ : Site → K) (f : Laurent K) (ν : Site →+ ℤ) (m β : ℤ)
    (hmin : ∀ u ∈ f.coeff.support, m ≤ ν u)
    (q₀ p : Site) (hpne : p ≠ 0) (hq₀ : ν q₀ = m) (hp : ν p = 0)
    (t : ℕ) (α : Fin (t + 1) → K) (hlast : α (Fin.last t) ≠ 0)
    (hdecomp : f = lineOperator q₀ p t α + (f - exposedOperator f ν m))
    (hann : laurentAct f δ = 0)
    (M : ℕ) (C : ℕ → Set RealPlane) (B : ℕ → RealPlane) (left right : ℕ → ℝ)
    (hC : ∀ j ≤ M, ∀ x ∈ C j, ((β - (j : ℤ) - m : ℤ) : ℝ) ≤ latticeNormal ν x)
    (hSface : normalFace (latticeHull f.coeff.support) (latticeNormal ν) (m : ℝ) =
      lineInterval (latticeEmbedding q₀) (latticeEmbedding p) 0 (t : ℝ))
    (hab : ∀ j ≤ M, left j ≤ right j)
    (hCface : ∀ j ≤ M,
      normalFace (C j) (latticeNormal ν) ((β - (j : ℤ) - m : ℤ) : ℝ) =
        lineInterval (B j) (latticeEmbedding p) (left j) (right j))
    (hprevious : ∀ j < M, ∀ g : Site,
      latticeEmbedding g ∈ latticeHull f.coeff.support + C (j + 1) →
      β - ((j + 1 : ℕ) : ℤ) + 1 ≤ ν g →
      latticeEmbedding g ∈ latticeHull f.coeff.support + C j)
    (E : Finset Site)
    (hseed : ∀ j ≤ M, 0 < j → ∀ g : Site,
      latticeEmbedding g ∈ normalFace (latticeHull f.coeff.support + C j)
        (latticeNormal ν) ((β - (j : ℤ) : ℤ) : ℝ) →
      latticeEmbedding (g - (t : ℤ) • p) ∉
        normalFace (latticeHull f.coeff.support + C j)
          (latticeNormal ν) ((β - (j : ℤ) : ℤ) : ℝ) → g ∈ E)
    (hzero : ∀ g : Site, latticeEmbedding g ∈ latticeHull f.coeff.support + C 0 → δ g = 0)
    (hEzero : ∀ g ∈ E, δ g = 0) :
    ∀ j ≤ M, ∀ g : Site, latticeEmbedding g ∈ latticeHull f.coeff.support + C j → δ g = 0 := by
  intro j
  induction j with
  | zero => exact fun _ => hzero
  | succ j ih =>
    intro hj
    have hj₀ : j ≤ M := by omega
    have hj₁ : j < M := by omega
    have hinterior : ∀ g : Site,
        latticeEmbedding g ∈ latticeHull f.coeff.support + C (j + 1) →
        β - ((j + 1 : ℕ) : ℤ) + 1 ≤ ν g → δ g = 0 :=
      fun g hg hlevel => ih hj₀ g (hprevious j hj₁ g hg hlevel)
    have hboundary := finite_facet_continuation δ f ν m (β - ((j + 1 : ℕ) : ℤ)) hmin
      q₀ p hpne hq₀ hp (C (j + 1)) t α hlast hdecomp hann
      (B (j + 1)) (left (j + 1)) (right (j + 1)) (hab (j + 1) hj)
      (hC (j + 1) hj) hSface (hCface (j + 1) hj) hinterior
      (fun g hg hnot => hEzero g (hseed (j + 1) hj (Nat.succ_pos j) g hg hnot))
    intro g hg
    have hlow : β - ((j + 1 : ℕ) : ℤ) ≤ ν g := by
      obtain ⟨s, hs, v, hv, hsum⟩ := Set.mem_add.mp hg
      have hsbound := lower_face_hull_bound f.coeff.support ν m hmin s hs
      have hvbound := hC (j + 1) hj v hv
      have hnormal : latticeNormal ν (latticeEmbedding g) =
          latticeNormal ν s + latticeNormal ν v := by
        rw [← hsum, map_add]
      have hreal : ((β - ((j + 1 : ℕ) : ℤ) : ℤ) : ℝ) ≤ latticeNormal ν (latticeEmbedding g) := by
        rw [hnormal]
        push_cast at hvbound ⊢
        linarith
      simpa only [latticeNormal_embedding, Int.cast_le] using hreal
    by_cases hin : β - ((j + 1 : ℕ) : ℤ) + 1 ≤ ν g
    · exact hinterior g hg hin
    · apply hboundary g
      refine ⟨hg, ?_⟩
      rw [latticeNormal_embedding]
      have heq : ν g = β - ((j + 1 : ℕ) : ℤ) := by omega
      exact_mod_cast heq

-- maximal agreement at the base forces a failure in the stabilized finite facet seeds.
theorem anchored_finite_seed_failure {K : Type*} [Zero K]
    (δ : Site → K) (E : Finset Site) (R : Set Site)
    (hpropagate : (∀ g ∈ E, δ g = 0) → ∀ g ∈ R, δ g = 0)
    (hfail : ∃ g ∈ R, δ g ≠ 0) : ∃ g ∈ E, δ g ≠ 0 := by
  classical
  by_contra hnot
  have hseeds : ∀ g ∈ E, δ g = 0 := by simpa only [not_exists, not_and, not_not] using hnot
  obtain ⟨g, hg, hne⟩ := hfail
  exact hne (hpropagate hseeds g hg)

end KumarNivat
