module

public import KumarNivat.LatticeConvexity

@[expose] public section

namespace KumarNivat

-- a convex set containing two attained levels meets every intermediate normal level.
theorem convex_point_on_intermediate_normal_level (P : Set RealPlane) (hP : Convex ℝ P)
    (ell : RealPlane →ₗ[ℝ] ℝ) (m M : ℝ) (a₀ a₁ : RealPlane)
    (ha₀ : a₀ ∈ P) (ha₁ : a₁ ∈ P) (h₀ : ell a₀ = m) (h₁ : ell a₁ = M)
    (t : ℝ) (ht : m ≤ t ∧ t ≤ M) : ∃ z : RealPlane, z ∈ P ∧ ell z = t := by
  have hlow : m ∈ ell '' P := ⟨a₀, ha₀, h₀⟩
  have hhigh : M ∈ ell '' P := ⟨a₁, ha₁, h₁⟩
  have hlevel : t ∈ segment ℝ m M := by
    rw [segment_eq_Icc (ht.1.trans ht.2)]
    exact ht
  exact (hP.linear_image ell).segment_subset hlow hhigh hlevel

end KumarNivat
