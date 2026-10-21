module

public import KumarNivat.AnchoredFacetWitness
public import KumarNivat.PrimitiveRealLines
public import Mathlib.Algebra.Order.Floor.Ring

@[expose] public section

namespace KumarNivat

open scoped Pointwise

-- rebasing at the left endpoint keeps the same real facet, including rational endpoints.
theorem lineInterval_rebase_left (A v : RealPlane) (left right : ℝ) :
    lineInterval A v left right = lineInterval (A + left • v) v 0 (right - left) := by
  apply Set.Subset.antisymm
  · rintro x ⟨s, hs, he⟩
    refine ⟨s - left, ⟨by linarith [hs.1], by linarith [hs.2]⟩, ?_⟩
    change (A + left • v) + (s - left) • v = x
    change A + s • v = x at he
    calc
      (A + left • v) + (s - left) • v = A + s • v := by rw [sub_smul]; abel
      _ = x := he
  · rintro x ⟨s, hs, he⟩
    refine ⟨s + left, ⟨by linarith [hs.1], by linarith [hs.2]⟩, ?_⟩
    change A + (s + left) • v = x
    change (A + left • v) + s • v = x at he
    rw [add_smul]
    simpa only [add_assoc, add_comm, add_left_comm] using he

-- the first lattice site is the ceiling of the fixed endpoint's primitive tangent coordinate.
noncomputable def facetInitialSeeds (p G : Site) (σ : ℝ) (t : ℕ) : Finset Site :=
  Finset.univ.image (fun i : Fin t => G + (⌈σ⌉ + (i.val : ℤ)) • p)

-- a primitive real line contains lattice sites only at integer primitive tangent parameters.
theorem primitive_real_line_integer_parameter (p : Site)
    (hprimitive : Int.gcd p.1 p.2 = 1) (G g : Site) (s : ℝ)
    (he : latticeEmbedding g = latticeEmbedding G + s • latticeEmbedding p) :
    ∃ n : ℤ, g = G + n • p ∧ s = (n : ℝ) := by
  obtain ⟨τ, _hτ, hker⟩ := primitive_direction_coordinate p hprimitive
  have hnormal : directionNormal p g = directionNormal p G := by
    have hreal : (directionNormal p g : ℝ) = (directionNormal p G : ℝ) := by
      rw [← latticeNormal_embedding, he, map_add, map_smul,
        latticeNormal_embedding, latticeNormal_embedding, directionNormal_self, Int.cast_zero,
        smul_zero, add_zero]
    exact Int.cast_injective hreal
  have hparallel : directionNormal p (g - G) = 0 := by rw [map_sub, hnormal, sub_self]
  let n : ℤ := τ (g - G)
  have hsite : g = G + n • p := by
    have hrep := hker (g - G) hparallel
    dsimp [n]
    rw [← hrep]
    abel
  have hpne : p ≠ 0 := by
    intro hpzero
    rw [hpzero] at hprimitive
    norm_num at hprimitive
  have hv : latticeEmbedding p ≠ 0 := by
    intro hvzero
    apply hpne
    apply latticeEmbedding_injective
    simpa [latticeEmbedding] using hvzero
  refine ⟨n, hsite, ?_⟩
  have hsecond : latticeEmbedding g = latticeEmbedding G + (n : ℝ) • latticeEmbedding p := by
    rw [hsite, latticeEmbedding_add, latticeEmbedding_zsmul]
  exact (smul_left_injective ℝ hv) (add_left_cancel (he.symm.trans hsecond))

-- the first-t condition bounds the parameter independently of the escaping far endpoint.
theorem facet_initial_seed_mem (p : Site) (hprimitive : Int.gcd p.1 p.2 = 1)
    (G g : Site) (σ right : ℝ) (t : ℕ)
    (hg : latticeEmbedding g ∈
      lineInterval (latticeEmbedding G + σ • latticeEmbedding p) (latticeEmbedding p) 0 right)
    (hout : latticeEmbedding (g - (t : ℤ) • p) ∉
      lineInterval (latticeEmbedding G + σ • latticeEmbedding p) (latticeEmbedding p) 0 right) :
    g ∈ facetInitialSeeds p G σ t := by
  classical
  obtain ⟨s, hs, he⟩ := hg
  change (latticeEmbedding G + σ • latticeEmbedding p) + s • latticeEmbedding p =
    latticeEmbedding g at he
  have he' : latticeEmbedding g = latticeEmbedding G + (σ + s) • latticeEmbedding p := by
    rw [add_smul]
    simpa only [add_assoc] using he.symm
  obtain ⟨n, hsite, hparameter⟩ := primitive_real_line_integer_parameter p hprimitive G g (σ + s) he'
  have hst : s < (t : ℝ) := by
    by_contra hnot
    have ht : (t : ℝ) ≤ s := le_of_not_gt hnot
    apply hout
    have htzero : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
    refine ⟨s - (t : ℝ), ⟨by linarith, by linarith [hs.2]⟩, ?_⟩
    change (latticeEmbedding G + σ • latticeEmbedding p) +
      (s - (t : ℝ)) • latticeEmbedding p = latticeEmbedding (g - (t : ℤ) • p)
    rw [latticeEmbedding_sub, latticeEmbedding_zsmul, ← he]
    simp only [Int.cast_natCast]
    rw [sub_smul]
    abel
  have hnlow : ⌈σ⌉ ≤ n := Int.ceil_le.mpr (by linarith [hs.1])
  have hnhigh : n < ⌈σ⌉ + (t : ℤ) := by
    have hceil : σ ≤ (⌈σ⌉ : ℝ) := Int.le_ceil σ
    have hreal : (n : ℝ) < (⌈σ⌉ : ℝ) + (t : ℝ) := by linarith
    exact_mod_cast hreal
  let i : Fin t := ⟨(n - ⌈σ⌉).toNat, by omega⟩
  have hindex : ⌈σ⌉ + (i.val : ℤ) = n := by dsimp [i]; omega
  apply Finset.mem_image.mpr
  exact ⟨i, Finset.mem_univ i, by
    rw [hindex, ← hsite]⟩

-- each canonical seed itself lies on every facet whose primitive length is at least t.
theorem facet_initial_seeds_subset_long_face (p G : Site) (σ right : ℝ) (t : ℕ)
    (hright : (t : ℝ) ≤ right) :
    ∀ g ∈ facetInitialSeeds p G σ t, latticeEmbedding g ∈
      lineInterval (latticeEmbedding G + σ • latticeEmbedding p) (latticeEmbedding p) 0 right := by
  classical
  intro g hg
  obtain ⟨i, _hi, he⟩ := Finset.mem_image.mp hg
  refine ⟨(⌈σ⌉ : ℝ) + (i.val : ℝ) - σ, ⟨?_, ?_⟩, ?_⟩
  · linarith [Int.le_ceil σ, show (0 : ℝ) ≤ (i.val : ℝ) from Nat.cast_nonneg _]
  · have hi : (i.val : ℝ) + 1 ≤ (t : ℝ) := by exact_mod_cast Nat.succ_le_of_lt i.isLt
    linarith [Int.ceil_lt_add_one σ]
  · change (latticeEmbedding G + σ • latticeEmbedding p) +
      ((⌈σ⌉ : ℝ) + (i.val : ℝ) - σ) • latticeEmbedding p = latticeEmbedding g
    rw [← he, latticeEmbedding_add, latticeEmbedding_zsmul]
    push_cast
    rw [sub_smul, add_smul]
    abel

-- all finitely many stabilized layer endpoints have one finite witness set for every far endpoint.
theorem exists_fixed_facet_seed_set {I J : Type*} (p : Site)
    (hprimitive : Int.gcd p.1 p.2 = 1) (layers : Finset J) (level : J → ℤ)
    (V : J → RealPlane)
    (hlevel : ∀ j ∈ layers, latticeNormal (directionNormal p) (V j) = (level j : ℝ))
    (right : I → J → ℝ) (t : ℕ) :
    ∃ E : Finset Site,
      (∀ i : I, ∀ j ∈ layers, ∀ g : Site,
        latticeEmbedding g ∈ lineInterval (V j) (latticeEmbedding p) 0 (right i j) →
        latticeEmbedding (g - (t : ℤ) • p) ∉
          lineInterval (V j) (latticeEmbedding p) 0 (right i j) → g ∈ E) ∧
      (∀ g ∈ E, ∃ j ∈ layers, directionNormal p g = level j) ∧
      ∀ i : I, (∀ j ∈ layers, (t : ℝ) ≤ right i j) →
        ∀ g ∈ E, ∃ j ∈ layers,
          latticeEmbedding g ∈ lineInterval (V j) (latticeEmbedding p) 0 (right i j) := by
  classical
  obtain ⟨τ, hτ, _hker⟩ := primitive_direction_coordinate p hprimitive
  obtain ⟨q, hpq⟩ := primitive_basis_of_line_coordinate p τ hτ
  let G : J → Site := fun j => level j • q
  have hG : ∀ j, directionNormal p (G j) = level j := by
    intro j
    dsimp [G]
    rw [map_zsmul]
    change level j * determinant p q = level j
    rw [hpq, mul_one]
  have hparam : ∀ j ∈ layers, ∃ σ : ℝ,
      V j = latticeEmbedding (G j) + σ • latticeEmbedding p := by
    intro j hj
    apply real_point_on_primitive_lattice_line p hprimitive (G j) (V j)
    rw [hlevel j hj, hG j]
  choose σ hσ using hparam
  let E : Finset Site := layers.attach.biUnion
    (fun j => facetInitialSeeds p (G j.val) (σ j.val j.property) t)
  refine ⟨E, ?_, ?_, ?_⟩
  · intro i j hj g hg hout
    have hmem := facet_initial_seed_mem p hprimitive (G j) g (σ j hj) (right i j) t
      (by rwa [← hσ j hj]) (by rwa [← hσ j hj])
    exact Finset.mem_biUnion.mpr ⟨⟨j, hj⟩, Finset.mem_attach _ _, hmem⟩
  · intro g hg
    obtain ⟨j, _hj, hgseed⟩ := Finset.mem_biUnion.mp hg
    obtain ⟨i, _hi, he⟩ := Finset.mem_image.mp hgseed
    refine ⟨j.val, j.property, ?_⟩
    rw [← he, map_add, hG j.val, map_zsmul, directionNormal_self, smul_zero, add_zero]
  · intro i hright g hg
    obtain ⟨j, _hj, hgseed⟩ := Finset.mem_biUnion.mp hg
    refine ⟨j.val, j.property, ?_⟩
    rw [hσ j.val j.property]
    exact facet_initial_seeds_subset_long_face p (G j.val) (σ j.val j.property)
      (right i j.val) t (hright j.val j.property) g hgseed

-- stabilized left endpoints turn every maximal finite expansion failure into a fixed finite witness.
theorem anchored_relaxation_failures_have_fixed_seeds {K : Type*}
    [CommRing K] [NoZeroDivisors K] (δ : ℕ → Site → K) (f : Laurent K)
    (p : Site) (hprimitive : Int.gcd p.1 p.2 = 1) (m β : ℤ)
    (hmin : ∀ u ∈ f.coeff.support, m ≤ directionNormal p u)
    (q₀ : Site) (hq₀ : directionNormal p q₀ = m)
    (t : ℕ) (α : Fin (t + 1) → K) (hlast : α (Fin.last t) ≠ 0)
    (hdecomp : f = lineOperator q₀ p t α + (f - exposedOperator f (directionNormal p) m))
    (hann : ∀ i, laurentAct f (δ i) = 0)
    (M : ℕ) (C : ℕ → ℕ → Set RealPlane) (B : ℕ → ℕ → RealPlane)
    (left right : ℕ → ℕ → ℝ)
    (hC : ∀ i j, j ≤ M → ∀ x ∈ C i j,
      ((β - (j : ℤ) - m : ℤ) : ℝ) ≤ latticeNormal (directionNormal p) x)
    (hSface : normalFace (latticeHull f.coeff.support) (latticeNormal (directionNormal p)) (m : ℝ) =
      lineInterval (latticeEmbedding q₀) (latticeEmbedding p) 0 (t : ℝ))
    (hab : ∀ i j, j ≤ M → left i j ≤ right i j)
    (hCface : ∀ i j, j ≤ M →
      normalFace (C i j) (latticeNormal (directionNormal p)) ((β - (j : ℤ) - m : ℤ) : ℝ) =
        lineInterval (B i j) (latticeEmbedding p) (left i j) (right i j))
    (hprevious : ∀ i j, j < M → ∀ g : Site,
      latticeEmbedding g ∈ latticeHull f.coeff.support + C i (j + 1) →
      β - ((j + 1 : ℕ) : ℤ) + 1 ≤ directionNormal p g →
      latticeEmbedding g ∈ latticeHull f.coeff.support + C i j)
    (V : ℕ → RealPlane)
    (hstable : ∀ i j, j ≤ M → 0 < j →
      latticeEmbedding q₀ + B i j + left i j • latticeEmbedding p = V j)
    (hzero : ∀ i, ∀ g : Site,
      latticeEmbedding g ∈ latticeHull f.coeff.support + C i 0 → δ i g = 0)
    (hfailure : ∀ i, ∃ g : Site,
      latticeEmbedding g ∈ latticeHull f.coeff.support + C i M ∧ δ i g ≠ 0) :
    ∃ E : Finset Site, (∀ i, ∃ g ∈ E, δ i g ≠ 0) ∧
      (∀ g ∈ E, ∃ j : ℕ, 1 ≤ j ∧ j ≤ M ∧ directionNormal p g = β - (j : ℤ)) ∧
      ∀ i, ∀ g ∈ E, ∃ j : ℕ, 1 ≤ j ∧ j ≤ M ∧ latticeEmbedding g ∈
        normalFace (latticeHull f.coeff.support + C i j) (latticeNormal (directionNormal p))
          ((β - (j : ℤ) : ℤ) : ℝ) := by
  classical
  let layers : Finset ℕ := Finset.Icc 1 M
  have hface (i j : ℕ) (hj : j ≤ M) :
      normalFace (latticeHull f.coeff.support + C i j) (latticeNormal (directionNormal p))
        ((β - (j : ℤ) : ℤ) : ℝ) =
      lineInterval (latticeEmbedding q₀ + B i j) (latticeEmbedding p)
        (left i j) (right i j + (t : ℝ)) :=
    minkowski_finite_face f.coeff.support (directionNormal p) m (β - (j : ℤ))
      hmin (C i j) (hC i j hj) q₀ p t (B i j) (left i j) (right i j)
      (hab i j hj) hSface (hCface i j hj)
  have hlevel : ∀ j ∈ layers,
      latticeNormal (directionNormal p) (V j) = ((β - (j : ℤ) : ℤ) : ℝ) := by
    intro j hj
    obtain ⟨hj₀, hj₁⟩ := Finset.mem_Icc.mp hj
    have hpos : 0 < j := by omega
    have hVmem : V j ∈ normalFace (latticeHull f.coeff.support + C 0 j)
        (latticeNormal (directionNormal p)) ((β - (j : ℤ) : ℤ) : ℝ) := by
      rw [hface 0 j hj₁]
      refine ⟨left 0 j, ⟨le_rfl, ?_⟩, hstable 0 j hj₁ hpos⟩
      linarith [hab 0 j hj₁, show (0 : ℝ) ≤ (t : ℝ) from Nat.cast_nonneg t]
    exact hVmem.2
  obtain ⟨E, hEseed, hElevels, hEplaced⟩ := exists_fixed_facet_seed_set p hprimitive layers
    (fun j => β - (j : ℤ)) V hlevel (fun i j => right i j + (t : ℝ) - left i j) t
  have hrebased (i j : ℕ) (hj : j ≤ M) (hpos : 0 < j) :
      normalFace (latticeHull f.coeff.support + C i j) (latticeNormal (directionNormal p))
        ((β - (j : ℤ) : ℤ) : ℝ) =
      lineInterval (V j) (latticeEmbedding p) 0 (right i j + (t : ℝ) - left i j) := by
    rw [hface i j hj, lineInterval_rebase_left, hstable i j hj hpos]
  have hpne : p ≠ 0 := by
    intro hz
    rw [hz] at hprimitive
    norm_num at hprimitive
  refine ⟨E, ?_, ?_, ?_⟩
  · intro i
    apply anchored_finite_seed_failure (δ i) E
      {g | latticeEmbedding g ∈ latticeHull f.coeff.support + C i M}
    · intro hEzero g hg
      apply anchored_finite_relaxations_zero (δ i) f (directionNormal p) m β hmin
        q₀ p hpne hq₀ (directionNormal_self p) t α hlast hdecomp (hann i)
        M (C i) (B i) (left i) (right i) (hC i) hSface (hab i) (hCface i)
        (hprevious i) E _ (hzero i) hEzero M le_rfl g hg
      intro j hj hpos u hu hout
      have hjlayer : j ∈ layers := Finset.mem_Icc.mpr ⟨by omega, hj⟩
      apply hEseed i j hjlayer u
      · rwa [← hrebased i j hj hpos]
      · rwa [← hrebased i j hj hpos]
    · obtain ⟨g, hg, hne⟩ := hfailure i
      exact ⟨g, hg, hne⟩
  · intro g hg
    obtain ⟨j, hj, hlevelj⟩ := hElevels g hg
    obtain ⟨hjl, hjr⟩ := Finset.mem_Icc.mp hj
    exact ⟨j, hjl, hjr, hlevelj⟩
  · intro i g hg
    have hlength : ∀ j ∈ layers, (t : ℝ) ≤ right i j + (t : ℝ) - left i j := by
      intro j hj
      have hjr := (Finset.mem_Icc.mp hj).2
      linarith [hab i j hjr]
    obtain ⟨j, hj, hplacement⟩ := hEplaced i hlength g hg
    obtain ⟨hjl, hjr⟩ := Finset.mem_Icc.mp hj
    refine ⟨j, hjl, hjr, ?_⟩
    rwa [hrebased i j hjr (by omega)]

end KumarNivat
