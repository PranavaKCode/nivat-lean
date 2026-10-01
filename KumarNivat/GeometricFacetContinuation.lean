import KumarNivat.LineFaceGeometry
import KumarNivat.PairedDirections
import Mathlib.Algebra.Order.Floor.Ring

namespace KumarNivat

open scoped Pointwise

-- an integer tangent step adds its real parameter to the chosen facet coordinate.
theorem facet_embedding_coordinate (E p q₀ : Site) (B : RealPlane) (σ : ℝ)
    (hE : latticeEmbedding E = latticeEmbedding q₀ + B + σ • latticeEmbedding p) (n : ℤ) :
    latticeEmbedding (E + n • p) = latticeEmbedding q₀ + B + (σ + (n : ℝ)) • latticeEmbedding p := by
  rw [latticeEmbedding_add, latticeEmbedding_zsmul, hE, add_smul]
  abel

-- the supporting levels and actual faces determine the finite face of the enlarged region.
theorem minkowski_finite_face (S : Finset Site) (ν : Site →+ ℤ) (m β : ℤ)
    (hmin : ∀ u ∈ S, m ≤ ν u) (C : Set RealPlane)
    (hC : ∀ x ∈ C, ((β - m : ℤ) : ℝ) ≤ latticeNormal ν x)
    (q₀ p : Site) (t : ℕ) (B : RealPlane) (a b : ℝ) (hab : a ≤ b)
    (hSface : normalFace (latticeHull S) (latticeNormal ν) (m : ℝ) =
      lineInterval (latticeEmbedding q₀) (latticeEmbedding p) 0 (t : ℝ))
    (hCface : normalFace C (latticeNormal ν) ((β - m : ℤ) : ℝ) =
      lineInterval B (latticeEmbedding p) a b) :
    normalFace (latticeHull S + C) (latticeNormal ν) (β : ℝ) =
      lineInterval (latticeEmbedding q₀ + B) (latticeEmbedding p) a (b + (t : ℝ)) := by
  have hsum : (β : ℝ) = (m : ℝ) + ((β - m : ℤ) : ℝ) := by push_cast; ring
  rw [hsum, normalFace_add _ _ _ _ _ (lower_face_hull_bound S ν m hmin) hC,
    hSface, hCface, lineInterval_add _ _ _ _ _ _ (Nat.cast_nonneg t) hab]

-- the same face addition identifies a ray by its actual initial endpoint.
theorem minkowski_ray_face (S : Finset Site) (ν : Site →+ ℤ) (m β : ℤ)
    (hmin : ∀ u ∈ S, m ≤ ν u) (C : Set RealPlane)
    (hC : ∀ x ∈ C, ((β - m : ℤ) : ℝ) ≤ latticeNormal ν x)
    (q₀ p : Site) (t : ℕ) (B : RealPlane) (a : ℝ)
    (hSface : normalFace (latticeHull S) (latticeNormal ν) (m : ℝ) =
      lineInterval (latticeEmbedding q₀) (latticeEmbedding p) 0 (t : ℝ))
    (hCface : normalFace C (latticeNormal ν) ((β - m : ℤ) : ℝ) =
      lineRay B (latticeEmbedding p) a) :
    normalFace (latticeHull S + C) (latticeNormal ν) (β : ℝ) =
      lineRay (latticeEmbedding q₀ + B) (latticeEmbedding p) a := by
  have hsum : (β : ℝ) = (m : ℝ) + ((β - m : ℤ) : ℝ) := by push_cast; ring
  rw [hsum, normalFace_add _ _ _ _ _ (lower_face_hull_bound S ν m hmin) hC,
    hSface, hCface, lineInterval_add_ray _ _ _ _ _ (Nat.cast_nonneg t)]

-- real face endpoints supply every fitting base needed for forward finite-facet recurrence.
theorem finite_facet_zero_from_real_endpoints {K : Type*} [CommRing K] [NoZeroDivisors K]
    (δ : Site → K) (f : Laurent K) (ν : Site →+ ℤ) (m β : ℤ)
    (hmin : ∀ u ∈ f.coeff.support, m ≤ ν u) (q₀ p E : Site) (hpne : p ≠ 0)
    (hq₀ : ν q₀ = m) (hp : ν p = 0) (hE : ν E = β) (C : Set RealPlane)
    (t : ℕ) (α : Fin (t + 1) → K) (hlast : α (Fin.last t) ≠ 0)
    (hdecomp : f = lineOperator q₀ p t α + (f - exposedOperator f ν m))
    (hann : laurentAct f δ = 0) (B : RealPlane) (a b σ : ℝ)
    (hemb : latticeEmbedding E = latticeEmbedding q₀ + B + σ • latticeEmbedding p)
    (hσ₀ : a ≤ σ) (hσ₁ : σ < a + 1)
    (hCface : normalFace C (latticeNormal ν) ((β - m : ℤ) : ℝ) =
      lineInterval B (latticeEmbedding p) a b)
    (hface : normalFace (latticeHull f.coeff.support + C) (latticeNormal ν) (β : ℝ) =
      lineInterval (latticeEmbedding q₀ + B) (latticeEmbedding p) a (b + (t : ℝ)))
    (hzero : ∀ g : Site, latticeEmbedding g ∈ latticeHull f.coeff.support + C → β + 1 ≤ ν g → δ g = 0)
    (hseed : ∀ g : Site,
      latticeEmbedding g ∈ normalFace (latticeHull f.coeff.support + C) (latticeNormal ν) (β : ℝ) →
      latticeEmbedding (g - (t : ℤ) • p) ∉ normalFace (latticeHull f.coeff.support + C) (latticeNormal ν) (β : ℝ) →
      δ g = 0) :
    ∀ n : ℤ, 0 ≤ n → σ + (n : ℝ) ≤ b + (t : ℝ) → δ (E + n • p) = 0 := by
  have hv : latticeEmbedding p ≠ 0 := by
    intro he
    exact hpne (latticeEmbedding_injective (by simpa [latticeEmbedding] using he))
  have hinj := smul_left_injective ℝ hv
  let N : ℤ := ⌊b + (t : ℝ) - σ⌋
  have hN : (N : ℝ) ≤ b + (t : ℝ) - σ := Int.floor_le _
  have hrec : IntervalRecurrence t α (fun n => δ (E + n • p)) 0 N := by
    intro n hn hnt
    have hnt' : (n : ℝ) + (t : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnt
    have hbase : latticeEmbedding (E + n • p - q₀) ∈ C := by
      have he : latticeEmbedding (E + n • p - q₀) = B + (σ + (n : ℝ)) • latticeEmbedding p := by
        rw [latticeEmbedding_sub, facet_embedding_coordinate E p q₀ B σ hemb n]
        abel
      rw [he]
      have hf : B + (σ + (n : ℝ)) • latticeEmbedding p ∈
          normalFace C (latticeNormal ν) ((β - m : ℤ) : ℝ) := by
        rw [hCface]
        refine ⟨σ + (n : ℝ), ⟨?_, by linarith⟩, rfl⟩
        have hn' : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        linarith
      exact hf.1
    exact exposed_line_recurrence_at δ f (f - exposedOperator f ν m) q₀ p E t α hdecomp hann n
      (nonface_zero_of_minkowski_base δ f ν m β hmin q₀ p E hq₀ hp hE C hzero n hbase)
  have hprefix : ∀ i : Fin t, (i.val : ℤ) ≤ N → δ (E + (i.val : ℤ) • p) = 0 := by
    intro i hi
    have hi' : (i.val : ℝ) ≤ (N : ℝ) := by exact_mod_cast hi
    have hpoint : latticeEmbedding (E + (i.val : ℤ) • p) ∈
        normalFace (latticeHull f.coeff.support + C) (latticeNormal ν) (β : ℝ) := by
      rw [hface, facet_embedding_coordinate E p q₀ B σ hemb]
      refine ⟨σ + (i.val : ℝ), ⟨?_, by linarith⟩, by norm_cast⟩
      have hi₀ : (0 : ℝ) ≤ (i.val : ℝ) := Nat.cast_nonneg _
      linarith
    apply hseed _ hpoint
    intro hshift
    have hs : E + (i.val : ℤ) • p - (t : ℤ) • p = E + ((i.val : ℤ) - (t : ℤ)) • p := by
      rw [sub_smul]
      abel
    rw [hs, hface, facet_embedding_coordinate E p q₀ B σ hemb] at hshift
    obtain ⟨s, hsa, he⟩ := hshift
    have heq := hinj (add_left_cancel he)
    have hit : (i.val : ℝ) + 1 ≤ (t : ℝ) := by exact_mod_cast Nat.succ_le_of_lt i.isLt
    push_cast at heq
    linarith [hsa.1]
  intro n hn hbound
  have hnN : n ≤ N := Int.le_floor.mpr (by linarith)
  exact zero_of_interval_recurrence_truncated_prefix t α (fun n => δ (E + n • p)) 0 N hlast hrec
    (by simpa only [zero_add] using hprefix) n hn hnN

-- the ray's real endpoint supplies fitting bases at every lattice point and every forward step.
theorem ray_facet_zero_from_real_endpoint {K : Type*} [CommRing K] [NoZeroDivisors K]
    (δ : Site → K) (f : Laurent K) (ν : Site →+ ℤ) (m β : ℤ)
    (hmin : ∀ u ∈ f.coeff.support, m ≤ ν u) (q₀ p E : Site)
    (hq₀ : ν q₀ = m) (hp : ν p = 0) (hE : ν E = β) (C : Set RealPlane)
    (t : ℕ) (α : Fin (t + 1) → K) (hfirst : α 0 ≠ 0)
    (hdecomp : f = lineOperator q₀ p t α + (f - exposedOperator f ν m))
    (hann : laurentAct f δ = 0) (B : RealPlane) (a σ R : ℝ)
    (hemb : latticeEmbedding E = latticeEmbedding q₀ + B + σ • latticeEmbedding p)
    (hσ : a ≤ σ)
    (hCface : normalFace C (latticeNormal ν) ((β - m : ℤ) : ℝ) =
      lineRay B (latticeEmbedding p) a)
    (hzero : ∀ g : Site, latticeEmbedding g ∈ latticeHull f.coeff.support + C → β + 1 ≤ ν g → δ g = 0)
    (htail : ∀ g : Site, ∀ s : ℝ, a ≤ s → R ≤ s →
      latticeEmbedding g = latticeEmbedding q₀ + B + s • latticeEmbedding p → δ g = 0) : δ E = 0 := by
  have hbase : ∀ n : ℤ, 0 ≤ n → latticeEmbedding (E + n • p - q₀) ∈ C := by
    intro n hn
    have he : latticeEmbedding (E + n • p - q₀) = B + (σ + (n : ℝ)) • latticeEmbedding p := by
      rw [latticeEmbedding_sub, facet_embedding_coordinate E p q₀ B σ hemb n]
      abel
    rw [he]
    have hf : B + (σ + (n : ℝ)) • latticeEmbedding p ∈
        normalFace C (latticeNormal ν) ((β - m : ℤ) : ℝ) := by
      rw [hCface]
      refine ⟨σ + (n : ℝ), ?_, rfl⟩
      have hn' : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      change a ≤ σ + (n : ℝ)
      linarith
    exact hf.1
  let N : ℤ := max 0 ⌈R - σ⌉
  have htail' : ∀ n : ℤ, N ≤ n → δ (E + n • p) = 0 := by
    intro n hn
    have hnonneg : 0 ≤ n := le_trans (le_max_left _ _) hn
    have hceil : ⌈R - σ⌉ ≤ n := le_trans (le_max_right _ _) hn
    have hn' : R - σ ≤ (n : ℝ) := Int.ceil_le.mp hceil
    apply htail _ (σ + (n : ℝ))
    · have hn₀ : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnonneg
      linarith
    · linarith
    · exact facet_embedding_coordinate E p q₀ B σ hemb n
  have hz := ray_facet_zero_of_minkowski_fitting_bases δ f ν m β hmin q₀ p E hq₀ hp hE C t α
    hdecomp hann hzero 0 N hfirst hbase htail' 0 le_rfl
  simpa only [zero_smul, add_zero] using hz

-- a finite facet propagates its actual initial lattice seed, including real endpoints and short facets.
theorem finite_facet_continuation {K : Type*} [CommRing K] [NoZeroDivisors K]
    (δ : Site → K) (f : Laurent K) (ν : Site →+ ℤ) (m β : ℤ)
    (hmin : ∀ u ∈ f.coeff.support, m ≤ ν u) (q₀ p : Site) (hpne : p ≠ 0)
    (hq₀ : ν q₀ = m) (hp : ν p = 0) (C : Set RealPlane)
    (t : ℕ) (α : Fin (t + 1) → K) (hlast : α (Fin.last t) ≠ 0)
    (hdecomp : f = lineOperator q₀ p t α + (f - exposedOperator f ν m))
    (hann : laurentAct f δ = 0) (B : RealPlane) (a b : ℝ) (hab : a ≤ b)
    (hC : ∀ x ∈ C, ((β - m : ℤ) : ℝ) ≤ latticeNormal ν x)
    (hSface : normalFace (latticeHull f.coeff.support) (latticeNormal ν) (m : ℝ) =
      lineInterval (latticeEmbedding q₀) (latticeEmbedding p) 0 (t : ℝ))
    (hCface : normalFace C (latticeNormal ν) ((β - m : ℤ) : ℝ) =
      lineInterval B (latticeEmbedding p) a b)
    (hzero : ∀ g : Site, latticeEmbedding g ∈ latticeHull f.coeff.support + C → β + 1 ≤ ν g → δ g = 0)
    (hseed : ∀ g : Site,
      latticeEmbedding g ∈ normalFace (latticeHull f.coeff.support + C) (latticeNormal ν) (β : ℝ) →
      latticeEmbedding (g - (t : ℤ) • p) ∉ normalFace (latticeHull f.coeff.support + C) (latticeNormal ν) (β : ℝ) →
      δ g = 0) :
    ∀ g : Site, latticeEmbedding g ∈
      normalFace (latticeHull f.coeff.support + C) (latticeNormal ν) (β : ℝ) → δ g = 0 := by
  have hface := minkowski_finite_face f.coeff.support ν m β hmin C hC q₀ p t B a b hab hSface hCface
  intro g hg
  have hnormal : ν g = β := Int.cast_injective (by simpa only [latticeNormal_embedding] using hg.2)
  rw [hface] at hg
  obtain ⟨s, ⟨hsa, hsb⟩, he⟩ := hg
  let d : ℤ := ⌊s - a⌋
  let E : Site := g - d • p
  let σ : ℝ := s - (d : ℝ)
  have hd : 0 ≤ d := Int.floor_nonneg.mpr (sub_nonneg.mpr hsa)
  have hd₀ : (d : ℝ) ≤ s - a := Int.floor_le _
  have hd₁ : s - a < (d : ℝ) + 1 := Int.lt_floor_add_one _
  have hE : ν E = β := by
    dsimp [E]
    rw [map_sub, map_zsmul, hp, smul_zero, sub_zero, hnormal]
  have hemb : latticeEmbedding E = latticeEmbedding q₀ + B + σ • latticeEmbedding p := by
    dsimp [E, σ]
    rw [latticeEmbedding_sub, latticeEmbedding_zsmul, ← he, sub_smul]
    simp only [sub_eq_add_neg, add_assoc]
  have hz := finite_facet_zero_from_real_endpoints δ f ν m β hmin q₀ p E hpne hq₀ hp hE C t α hlast
    hdecomp hann B a b σ hemb (by dsimp [σ]; linarith) (by dsimp [σ]; linarith)
    hCface hface hzero hseed d hd (by dsimp [σ]; linarith)
  have hsite : E + d • p = g := by dsimp [E]; abel
  rwa [hsite] at hz

-- an all-zero real-parameter tail extends backwards to every lattice point on the exposed ray.
theorem ray_facet_continuation {K : Type*} [CommRing K] [NoZeroDivisors K]
    (δ : Site → K) (f : Laurent K) (ν : Site →+ ℤ) (m β : ℤ)
    (hmin : ∀ u ∈ f.coeff.support, m ≤ ν u) (q₀ p : Site)
    (hq₀ : ν q₀ = m) (hp : ν p = 0) (C : Set RealPlane)
    (t : ℕ) (α : Fin (t + 1) → K) (hfirst : α 0 ≠ 0)
    (hdecomp : f = lineOperator q₀ p t α + (f - exposedOperator f ν m))
    (hann : laurentAct f δ = 0) (B : RealPlane) (a R : ℝ)
    (hC : ∀ x ∈ C, ((β - m : ℤ) : ℝ) ≤ latticeNormal ν x)
    (hSface : normalFace (latticeHull f.coeff.support) (latticeNormal ν) (m : ℝ) =
      lineInterval (latticeEmbedding q₀) (latticeEmbedding p) 0 (t : ℝ))
    (hCface : normalFace C (latticeNormal ν) ((β - m : ℤ) : ℝ) =
      lineRay B (latticeEmbedding p) a)
    (hzero : ∀ g : Site, latticeEmbedding g ∈ latticeHull f.coeff.support + C → β + 1 ≤ ν g → δ g = 0)
    (htail : ∀ g : Site, ∀ s : ℝ, a ≤ s → R ≤ s →
      latticeEmbedding g = latticeEmbedding q₀ + B + s • latticeEmbedding p → δ g = 0) :
    ∀ g : Site, latticeEmbedding g ∈
      normalFace (latticeHull f.coeff.support + C) (latticeNormal ν) (β : ℝ) → δ g = 0 := by
  have hface := minkowski_ray_face f.coeff.support ν m β hmin C hC q₀ p t B a hSface hCface
  intro g hg
  have hnormal : ν g = β := Int.cast_injective (by simpa only [latticeNormal_embedding] using hg.2)
  rw [hface] at hg
  obtain ⟨s, hsa, he⟩ := hg
  exact ray_facet_zero_from_real_endpoint δ f ν m β hmin q₀ p g hq₀ hp hnormal C t α hfirst
    hdecomp hann B a s R he.symm hsa hCface hzero htail

-- an exposed vertex needs no boundary seed or tail, whatever the residual face's shape.
theorem vertex_facet_continuation {K : Type*} [CommRing K] [NoZeroDivisors K]
    (δ : Site → K) (f : Laurent K) (ν : Site →+ ℤ) (m β : ℤ)
    (hmin : ∀ u ∈ f.coeff.support, m ≤ ν u) (q₀ p : Site)
    (hq₀ : ν q₀ = m) (hp : ν p = 0) (C : Set RealPlane)
    (α : Fin 1 → K) (hfirst : α 0 ≠ 0)
    (hdecomp : f = lineOperator q₀ p 0 α + (f - exposedOperator f ν m))
    (hann : laurentAct f δ = 0)
    (hC : ∀ x ∈ C, ((β - m : ℤ) : ℝ) ≤ latticeNormal ν x)
    (hSface : normalFace (latticeHull f.coeff.support) (latticeNormal ν) (m : ℝ) =
      {latticeEmbedding q₀})
    (hzero : ∀ g : Site, latticeEmbedding g ∈ latticeHull f.coeff.support + C → β + 1 ≤ ν g → δ g = 0) :
    ∀ g : Site, latticeEmbedding g ∈
      normalFace (latticeHull f.coeff.support + C) (latticeNormal ν) (β : ℝ) → δ g = 0 := by
  intro g hg
  have hnormal : ν g = β := Int.cast_injective (by simpa only [latticeNormal_embedding] using hg.2)
  have hsum : (β : ℝ) = (m : ℝ) + ((β - m : ℤ) : ℝ) := by push_cast; ring
  rw [hsum, normalFace_add _ _ _ _ _ (lower_face_hull_bound f.coeff.support ν m hmin) hC,
    hSface] at hg
  obtain ⟨u, hu, v, hv, he⟩ := Set.mem_add.mp hg
  have hu' : u = latticeEmbedding q₀ := Set.mem_singleton_iff.mp hu
  subst u
  have hbase : latticeEmbedding (g + (0 : ℤ) • p - q₀) ∈ C := by
    have hb : latticeEmbedding (g - q₀) = v := by rw [latticeEmbedding_sub, ← he]; abel
    simpa only [zero_smul, add_zero, hb] using hv.1
  have hz := exposed_line_recurrence_at δ f (f - exposedOperator f ν m) q₀ p g 0 α hdecomp hann 0
    (nonface_zero_of_minkowski_base δ f ν m β hmin q₀ p g hq₀ hp hnormal C hzero 0 hbase)
  change (∑ i : Fin 1, α i * δ (g + ((0 : ℤ) + (i.val : ℤ)) • p)) = 0 at hz
  simp only [Fin.sum_univ_one, Fin.val_zero, Nat.cast_zero, zero_add, zero_smul, add_zero] at hz
  exact (mul_eq_zero.mp hz).resolve_left hfirst

end KumarNivat
