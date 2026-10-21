module

public import KumarNivat.MinkowskiStencilFit
public import Mathlib.Analysis.Convex.Combination

@[expose] public section

namespace KumarNivat

open scoped Pointwise

-- the face is the actual slice of a real set by a supporting normal level.
def normalFace (P : Set RealPlane) (ell : RealPlane →ₗ[ℝ] ℝ) (m : ℝ) : Set RealPlane :=
  {x | x ∈ P ∧ ell x = m}

-- both summands must attain their lower normal levels at a point on the sum's face.
theorem normalFace_add (P C : Set RealPlane) (ell : RealPlane →ₗ[ℝ] ℝ) (m γ : ℝ)
    (hP : ∀ x ∈ P, m ≤ ell x) (hC : ∀ x ∈ C, γ ≤ ell x) :
    normalFace (P + C) ell (m + γ) = normalFace P ell m + normalFace C ell γ := by
  ext x
  constructor
  · rintro ⟨hx, hlevel⟩
    obtain ⟨u, hu, v, hv, rfl⟩ := Set.mem_add.mp hx
    rw [map_add] at hlevel
    have hum := hP u hu
    have hvm := hC v hv
    exact Set.mem_add.mpr ⟨u, ⟨hu, by linarith⟩, v, ⟨hv, by linarith⟩, rfl⟩
  · intro hx
    obtain ⟨u, ⟨hu, hum⟩, v, ⟨hv, hvm⟩, rfl⟩ := Set.mem_add.mp hx
    exact ⟨Set.add_mem_add hu hv, by rw [map_add, hum, hvm]⟩

-- an exposed hull face is the hull of precisely the generators on its supporting level.
theorem normalFace_latticeHull (S : Finset Site) (ν : Site →+ ℤ) (m : ℤ)
    (hmin : ∀ u ∈ S, m ≤ ν u) (E : Site) (hE : E ∈ S) (hlevel : ν E = m) :
    normalFace (latticeHull S) (latticeNormal ν) (m : ℝ) =
      latticeHull (S.filter (fun u => ν u = m)) := by
  classical
  let F := S.filter (fun u => ν u = m)
  have hEf : latticeEmbedding E ∈ latticeEmbedding '' (F : Set Site) :=
    ⟨E, Finset.mem_filter.mpr ⟨hE, hlevel⟩, rfl⟩
  ext x
  constructor
  · rintro ⟨hx, hm⟩
    obtain ⟨ι, inst, w, z, hw₀, hw₁, hz, hsum⟩ := mem_convexHull_iff_exists_fintype.mp hx
    let _ := inst
    have hzi (i : ι) : (m : ℝ) ≤ latticeNormal ν (z i) := by
      obtain ⟨u, hu, he⟩ := hz i
      rw [← he, latticeNormal_embedding]
      exact_mod_cast hmin u hu
    have hnorm : ∑ i, w i * latticeNormal ν (z i) = (m : ℝ) := by
      simpa only [map_sum, map_smul, smul_eq_mul, hm] using congrArg (latticeNormal ν) hsum
    have hzero : ∑ i, w i * (latticeNormal ν (z i) - (m : ℝ)) = 0 := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw₁, one_mul, hnorm,
        sub_self]
    have hterm (i : ι) : w i * (latticeNormal ν (z i) - (m : ℝ)) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _hj => mul_nonneg (hw₀ j) (sub_nonneg.mpr (hzi j)))).mp hzero i (Finset.mem_univ i)
    let z' : ι → RealPlane := fun i => if w i = 0 then latticeEmbedding E else z i
    have hz' (i : ι) : z' i ∈ latticeEmbedding '' (F : Set Site) := by
      dsimp [z']
      split_ifs with hwi
      · exact hEf
      · obtain ⟨u, hu, he⟩ := hz i
        have hnormal := sub_eq_zero.mp ((mul_eq_zero.mp (hterm i)).resolve_left hwi)
        rw [← he, latticeNormal_embedding] at hnormal
        exact ⟨u, Finset.mem_filter.mpr ⟨hu, Int.cast_injective hnormal⟩, he⟩
    have hsum' : ∑ i, w i • z' i = x := by
      rw [← hsum]
      apply Finset.sum_congr rfl
      intro i _hi
      by_cases hwi : w i = 0 <;> simp [z', hwi]
    exact mem_convexHull_of_exists_fintype w z' hw₀ hw₁ hz' hsum'
  · intro hx
    have hsub : latticeEmbedding '' (F : Set Site) ⊆
        normalFace (latticeHull S) (latticeNormal ν) (m : ℝ) := by
      rintro _ ⟨u, hu, rfl⟩
      obtain ⟨hum, he⟩ := Finset.mem_filter.mp hu
      exact ⟨subset_convexHull ℝ _ ⟨u, hum, rfl⟩, by rw [latticeNormal_embedding, he]⟩
    have hconv : Convex ℝ (normalFace (latticeHull S) (latticeNormal ν) (m : ℝ)) :=
      (convex_convexHull ℝ _).inter ((convex_singleton (m : ℝ)).linear_preimage (latticeNormal ν))
    exact convexHull_min hsub hconv hx

end KumarNivat
