module

public import KumarNivat.AnchoredRegionUnions
public import Mathlib.Analysis.Convex.Combination

@[expose] public section

namespace KumarNivat

open scoped Pointwise

-- convexifying the residual keeps an exact sum when both the resulting region and the newton hull are convex.
theorem convexify_exact_minkowski_residual (R Z C : Set RealPlane)
    (hR : Convex ℝ R) (hZ : Convex ℝ Z) (hsum : R = Z + C) :
    R = Z + convexHull ℝ C := by
  have he : convexHull ℝ R = convexHull ℝ Z + convexHull ℝ C := by
    rw [hsum, convexHull_add]
  simpa only [hR.convexHull_eq, hZ.convexHull_eq] using he

-- the actual convex polygon union therefore retains a convex residual for the same original newton summand.
theorem anchored_union_convex_newton_residual (P : ℕ → Finset Site) (Z : Set RealPlane)
    (hZ : Convex ℝ Z) (hunion : Convex ℝ (⋃ n, latticeHull (P n)))
    (henvelope : ∀ n, ∃ C : Set RealPlane, latticeHull (P n) = Z + C) :
    ∃ C : Set RealPlane, Convex ℝ C ∧ (⋃ n, latticeHull (P n)) = Z + C := by
  choose C hC using henvelope
  let D := ⋃ n, C n
  have hsum : (⋃ n, latticeHull (P n)) = Z + D := minkowski_summand_of_anchored_union P Z C hC
  exact ⟨convexHull ℝ D, convex_convexHull ℝ _, convexify_exact_minkowski_residual _ Z D hunion hZ hsum⟩

end KumarNivat
