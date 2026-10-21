module

public import KumarNivat.RayBoundaryStencilFit
public import KumarNivat.BoundaryLineRecurrences

@[expose] public section

namespace KumarNivat

open scoped Pointwise

-- actual minkowski geometry fits the exposed recurrence, so a parallel zero tail determines the whole boundary.
theorem zero_on_minkowski_boundary_of_parallel_tail {K : Type*} [CommRing K] [NoZeroDivisors K]
    (δ : Site → K) (f : Laurent K) (hf : f ≠ 0) (hann : laurentAct f δ = 0)
    (ν : Site →+ ℤ) (hν : ν ≠ 0) (β : ℤ) (p : Site) (hp : ν p = 0)
    (hprimitive : Int.gcd p.1 p.2 = 1) (P C : Set RealPlane)
    (hsum : P = latticeHull f.coeff.support + C)
    (hbound : ∀ z ∈ P, (β : ℝ) ≤ latticeNormal ν z)
    (hforward : ∀ z ∈ P, ∀ s : ℝ, 0 ≤ s → z + s • latticeEmbedding p ∈ P)
    (hzero : ∀ g : Site, latticeEmbedding g ∈ P → β + 1 ≤ ν g → δ g = 0)
    (A : Site) (hA : ν A = β) (N : ℤ) (htail : ∀ n : ℤ, N ≤ n → δ (A + n • p) = 0) :
    ∀ g : Site, latticeEmbedding g ∈ P → ν g = β → δ g = 0 := by
  classical
  have hpne : p ≠ 0 := by rintro rfl; simp at hprimitive
  have hsupp : f.coeff.support.Nonempty := Finsupp.support_nonempty_iff.mpr
    (fun hz => hf (AddMonoidAlgebra.coeff_injective hz))
  obtain ⟨v, hv, hmin⟩ := f.coeff.support.exists_min_image ν hsupp
  obtain ⟨q₀, t, α, hfirst, _hlast, hq₀, hq₀mem, _hq₁mem, _hexposed, hdecomp, hface⟩ :=
    exists_actual_exposed_geometric_face_data f ν hν (ν v) hmin v p hpne hprimitive hp hv rfl
  obtain ⟨τ, _hτ, hker⟩ := primitive_direction_coordinate p hprimitive
  intro g hg hlevel
  have hflat : ν (g - A) = 0 := by rw [map_sub, hlevel, hA, sub_self]
  have hparallel := nonzero_normal_kernel_parallel ν hν p (g - A) hp hflat
  have hd := hker (g - A) hparallel
  let k := τ (g - A)
  have hgsite : g = A + k • p := by dsimp [k]; rw [← hd]; abel
  have hinterior (n : ℤ) (hn : 0 ≤ n) (u : Site)
      (hu : u ∈ (f - exposedOperator f ν (ν v)).coeff.support) :
      δ ((g + n • p - q₀) + u) = 0 := by
    have hgn : latticeEmbedding (g + n • p) ∈ P := by
      rw [latticeEmbedding_add, latticeEmbedding_zsmul]
      exact hforward (latticeEmbedding g) hg (n : ℝ) (by exact_mod_cast hn)
    have hgnlevel : ν (g + n • p) = β := by
      rw [map_add, map_zsmul, hp, smul_zero, add_zero, hlevel]
    have hfit := boundary_stencil_fit_of_minkowski_recession f ν (ν v) β hmin q₀ p
      hq₀mem hq₀ t hface P C hsum hbound hforward (g + n • p) hgn hgnlevel
      u (exposed_remainder_support_subset f ν (ν v) hu)
    have hstrict := exposed_remainder_strict_level f ν (ν v) hmin u hu
    have hinputlevel : β + 1 ≤ ν ((g + n • p - q₀) + u) := by
      rw [map_add, map_sub, hgnlevel, hq₀]
      omega
    exact hzero _ hfit hinputlevel
  have htailg (n : ℤ) (hn : N - k ≤ n) : δ (g + n • p) = 0 := by
    have hsite : g + n • p = A + (k + n) • p := by
      rw [hgsite, add_smul]
      abel
    simpa only [hsite] using htail (k + n) (by omega)
  have hz := ray_facet_zero_from_exposed_stencil δ f (f - exposedOperator f ν (ν v)) q₀ p g t α
    hdecomp hann 0 (N - k) hfirst hinterior htailg
  simpa only [zero_smul, add_zero] using hz 0 le_rfl

-- a disagreement in the next layer contradicts any generated agreement tail on its supporting line.
theorem no_parallel_agreement_tail_of_failed_minkowski_extension {K : Type*}
    [CommRing K] [NoZeroDivisors K] (x y : Site → K) (f : Laurent K) (hf : f ≠ 0)
    (hxann : laurentAct f x = 0) (hyann : laurentAct f y = 0)
    (ν : Site →+ ℤ) (hν : ν ≠ 0) (β : ℤ) (p : Site) (hp : ν p = 0)
    (hprimitive : Int.gcd p.1 p.2 = 1) (P C : Set RealPlane)
    (hsum : P = latticeHull f.coeff.support + C)
    (hbound : ∀ z ∈ P, (β : ℝ) ≤ latticeNormal ν z)
    (hforward : ∀ z ∈ P, ∀ s : ℝ, 0 ≤ s → z + s • latticeEmbedding p ∈ P)
    (hagree : ∀ g : Site, latticeEmbedding g ∈ P → β + 1 ≤ ν g → x g = y g)
    (hfail : ∃ g : Site, latticeEmbedding g ∈ P ∧ x g ≠ y g)
    (A : Site) (hA : ν A = β) :
    ¬ ∃ N : ℤ, ∀ n : ℤ, N ≤ n → x (A + n • p) = y (A + n • p) := by
  obtain ⟨g, hg, hneq⟩ := hfail
  have hlow : β ≤ ν g := by
    have hb := hbound (latticeEmbedding g) hg
    rw [latticeNormal_embedding] at hb
    exact_mod_cast hb
  have hlevel : ν g = β := by
    by_contra hne
    exact hneq (hagree g hg (by omega))
  rintro ⟨N, htail⟩
  have hann : laurentAct f (x - y) = 0 := by rw [laurentAct_config_sub, hxann, hyann, sub_self]
  have hz := zero_on_minkowski_boundary_of_parallel_tail (x - y) f hf hann ν hν β p hp hprimitive
    P C hsum hbound hforward (fun z hz hlev => sub_eq_zero.mpr (hagree z hz hlev)) A hA N
      (fun n hn => sub_eq_zero.mpr (htail n hn)) g hg hlevel
  exact hneq (sub_eq_zero.mp hz)

end KumarNivat
