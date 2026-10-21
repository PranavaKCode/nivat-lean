module

public import KumarNivat.ExposedFaceData
public import KumarNivat.FacetRecurrences

@[expose] public section

namespace KumarNivat

open scoped Pointwise

-- lattice addition agrees with addition in the real polygon coordinates.
theorem latticeEmbedding_add (u v : Site) :
    latticeEmbedding (u + v) = latticeEmbedding u + latticeEmbedding v := by
  ext <;> simp [latticeEmbedding]

-- a base in the residual summand fits every nonface input into the known zero interior.
theorem nonface_zero_of_minkowski_base {K : Type*} [CommRing K]
    (δ : Site → K) (f : Laurent K) (ν : Site →+ ℤ) (m β : ℤ)
    (hmin : ∀ u ∈ f.coeff.support, m ≤ ν u) (q₀ p E : Site)
    (hq₀ : ν q₀ = m) (hp : ν p = 0) (hE : ν E = β) (C : Set RealPlane)
    (hzero : ∀ g : Site, latticeEmbedding g ∈ latticeHull f.coeff.support + C → β + 1 ≤ ν g → δ g = 0)
    (n : ℤ) (hbase : latticeEmbedding (E + n • p - q₀) ∈ C) :
    ∀ u ∈ (f - exposedOperator f ν m).coeff.support, δ ((E + n • p - q₀) + u) = 0 := by
  intro u hu
  have hum := exposed_remainder_support_subset f ν m hu
  have hullmem : latticeEmbedding u ∈ latticeHull f.coeff.support := subset_convexHull ℝ _ ⟨u, hum, rfl⟩
  have hfit : latticeEmbedding ((E + n • p - q₀) + u) ∈ latticeHull f.coeff.support + C := by
    rw [latticeEmbedding_add, add_comm (latticeEmbedding (E + n • p - q₀)) (latticeEmbedding u)]
    exact Set.add_mem_add hullmem hbase
  have hstrict := exposed_remainder_strict_level f ν m hmin u hu
  have hlevel : β + 1 ≤ ν ((E + n • p - q₀) + u) := by
    rw [map_add, map_sub, map_add, map_zsmul, hE, hp, smul_zero, add_zero, hq₀]
    omega
  exact hzero _ hfit hlevel

-- finite-facet propagation follows from fitting bases in the actual minkowski summand.
theorem finite_facet_zero_of_minkowski_fitting_bases {K : Type*} [CommRing K] [NoZeroDivisors K]
    (δ : Site → K) (f : Laurent K) (ν : Site →+ ℤ) (m β : ℤ)
    (hmin : ∀ u ∈ f.coeff.support, m ≤ ν u) (q₀ p E : Site)
    (hq₀ : ν q₀ = m) (hp : ν p = 0) (hE : ν E = β) (C : Set RealPlane)
    (t : ℕ) (α : Fin (t + 1) → K)
    (hdecomp : f = lineOperator q₀ p t α + (f - exposedOperator f ν m))
    (hann : laurentAct f δ = 0)
    (hzero : ∀ g : Site, latticeEmbedding g ∈ latticeHull f.coeff.support + C → β + 1 ≤ ν g → δ g = 0)
    (b N : ℤ) (hlast : α (Fin.last t) ≠ 0)
    (hbase : ∀ n : ℤ, b ≤ n → n + (t : ℤ) ≤ N → latticeEmbedding (E + n • p - q₀) ∈ C)
    (hseed : ∀ i : Fin t, δ (E + (b + (i.val : ℤ)) • p) = 0) :
    ∀ n : ℤ, b ≤ n → n ≤ N → δ (E + n • p) = 0 := by
  apply finite_facet_zero_from_exposed_stencil δ f (f - exposedOperator f ν m) q₀ p E t α
    hdecomp hann b N hlast _ hseed
  intro n hn hN
  exact nonface_zero_of_minkowski_base δ f ν m β hmin q₀ p E hq₀ hp hE C hzero n (hbase n hn hN)

-- backward propagation on a ray needs fitting bases at every point of that ray.
theorem ray_facet_zero_of_minkowski_fitting_bases {K : Type*} [CommRing K] [NoZeroDivisors K]
    (δ : Site → K) (f : Laurent K) (ν : Site →+ ℤ) (m β : ℤ)
    (hmin : ∀ u ∈ f.coeff.support, m ≤ ν u) (q₀ p E : Site)
    (hq₀ : ν q₀ = m) (hp : ν p = 0) (hE : ν E = β) (C : Set RealPlane)
    (t : ℕ) (α : Fin (t + 1) → K)
    (hdecomp : f = lineOperator q₀ p t α + (f - exposedOperator f ν m))
    (hann : laurentAct f δ = 0)
    (hzero : ∀ g : Site, latticeEmbedding g ∈ latticeHull f.coeff.support + C → β + 1 ≤ ν g → δ g = 0)
    (b B : ℤ) (hfirst : α 0 ≠ 0)
    (hbase : ∀ n : ℤ, b ≤ n → latticeEmbedding (E + n • p - q₀) ∈ C)
    (htail : ∀ n : ℤ, B ≤ n → δ (E + n • p) = 0) :
    ∀ n : ℤ, b ≤ n → δ (E + n • p) = 0 := by
  apply ray_facet_zero_from_exposed_stencil δ f (f - exposedOperator f ν m) q₀ p E t α
    hdecomp hann b B hfirst _ htail
  intro n hn
  exact nonface_zero_of_minkowski_base δ f ν m β hmin q₀ p E hq₀ hp hE C hzero n (hbase n hn)

end KumarNivat
