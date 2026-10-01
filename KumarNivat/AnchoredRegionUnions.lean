import KumarNivat.AnchoredCompactness
import KumarNivat.LatticeConvexity

open Filter Topology

namespace KumarNivat

open scoped Pointwise

-- lattice convexity identifies the actual lattice sites of the union of polygon hulls.
theorem lattice_points_of_anchored_union (P : ℕ → Finset Site)
    (hP : ∀ n, LatticeConvex (P n)) :
    {g : Site | latticeEmbedding g ∈ ⋃ n, latticeHull (P n)} =
      ⋃ n, (P n : Set Site) := by
  ext g
  constructor
  · intro hg
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hg
    exact Set.mem_iUnion.mpr ⟨n, hP n g hn⟩
  · intro hg
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hg
    apply Set.mem_iUnion.mpr
    refine ⟨n, subset_convexHull ℝ _ ?_⟩
    exact ⟨g, hn, rfl⟩

-- the increasing union retains the same newton summand without changing its actual support.
theorem minkowski_summand_of_anchored_union (P : ℕ → Finset Site)
    (Z : Set RealPlane) (C : ℕ → Set RealPlane)
    (hP : ∀ n, latticeHull (P n) = Z + C n) :
    (⋃ n, latticeHull (P n)) = Z + ⋃ n, C n := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    rw [hP n] at hn
    obtain ⟨z, hz, v, hv, he⟩ := Set.mem_add.mp hn
    exact Set.mem_add.mpr ⟨z, hz, v, Set.mem_iUnion.mpr ⟨n, hv⟩, he⟩
  · intro x hx
    obtain ⟨z, hz, v, hv, he⟩ := Set.mem_add.mp hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hv
    apply Set.mem_iUnion.mpr
    refine ⟨n, ?_⟩
    rw [hP n]
    exact Set.mem_add.mpr ⟨z, hz, v, hn, he⟩

-- convergence gives agreement at every lattice point of the actual real union.
theorem anchored_limit_agrees_on_real_union {A : Type*} [TopologicalSpace A]
    [DiscreteTopology A] (x : ℕ → Site → A) (θ w : Site → A)
    (P : ℕ → Finset Site) (hconvex : ∀ n, LatticeConvex (P n)) (hmono : Monotone P)
    (hlimit : Tendsto x atTop (𝓝 θ))
    (hagree : ∀ n, ∀ g ∈ P n, x n g = w g) :
    ∀ g : Site, latticeEmbedding g ∈ ⋃ n, latticeHull (P n) → θ g = w g := by
  apply configuration_limit_agrees_of_eventually x θ w _ hlimit
  intro g hg
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hg
  have hgn : g ∈ P n := hconvex n g hn
  exact (eventually_ge_atTop n).mono (fun j hnj => hagree j g (hmono hnj hgn))

end KumarNivat
