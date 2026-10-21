module

public import KumarNivat.PairedStructureRayChainNormals
public import KumarNivat.AdjoinedFacetRegions

@[expose] public section

namespace KumarNivat

-- the actual successor ray decreases only the moving facet among the surviving chain normals.
theorem forward_factor_successor_relaxation_signs {q : ℕ} [NeZero (2 * q)]
    (e : ZMod (2 * q) → Site) (hfan : AnchoredChainFanOrder e)
    (k : ℕ) (hk₀ : 0 < k) (hkq : k < q) :
    (-directionNormal (e (k : ZMod (2 * q)))) (e ((k + 1 : ℕ) : ZMod (2 * q))) < 0 ∧
      0 ≤ directionNormal (e 0) (e ((k + 1 : ℕ) : ZMod (2 * q))) ∧
      ∀ i ∈ Finset.Icc (k + 1) (q - 1),
        0 ≤ (-directionNormal (e (i : ZMod (2 * q)))) (e ((k + 1 : ℕ) : ZMod (2 * q))) := by
  have hcross (a b : Site) : (-directionNormal b) a = determinant a b := by simp [directionNormal, determinant]; ring
  by_cases hnext : k + 1 < q
  · have hturn := anchored_chain_first_half_pair_positive e hfan k (k + 1) (by omega) hnext
    have hη : (-directionNormal (e (k : ZMod (2 * q)))) (e ((k + 1 : ℕ) : ZMod (2 * q))) < 0 := by
      change -determinant (e (k : ZMod (2 * q))) (e ((k + 1 : ℕ) : ZMod (2 * q))) < 0
      omega
    have hν : 0 < directionNormal (e 0) (e ((k + 1 : ℕ) : ZMod (2 * q))) := by
      change 0 < determinant (e 0) (e ((k + 1 : ℕ) : ZMod (2 * q)))
      simpa only [Nat.cast_zero] using anchored_chain_first_half_pair_positive e hfan 0 (k + 1) (by omega) hnext
    refine ⟨hη, hν.le, ?_⟩
    intro i hi
    obtain ⟨hki, hiq⟩ := Finset.mem_Icc.mp hi
    by_cases he : i = k + 1
    · subst i
      simp [directionNormal_self]
    · rw [hcross]
      exact (anchored_chain_first_half_pair_positive e hfan (k + 1) i (by omega) (by omega)).le
  · have he : k + 1 = q := by omega
    have hanti : e (q : ZMod (2 * q)) = -e 0 := by simpa only [zero_add] using hfan.opposite 0
    have hη := (forward_factor_ray_chain_slopes e hfan k hk₀ hkq).2.1
    rw [he, hanti]
    refine ⟨?_, by simp [directionNormal_self], ?_⟩
    · rw [map_neg]
      omega
    · intro i hi
      obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hi
      omega

-- real levels reindex by the same actual surviving fan, without assuming any integer residual vertices.
theorem real_forward_surviving_facets_reindex {q : ℕ} [NeZero (2 * q)]
    (e : ZMod (2 * q) → Site) (hfan : AnchoredChainFanOrder e)
    (k : ℕ) (hk₀ : 0 < k) (hkq : k < q) (z : ℕ → ℝ) :
    {x : RealPlane | ∀ i : ℕ, i < 2 * q →
      0 ≤ directionNormal (e (i : ZMod (2 * q))) (e 0) →
        0 ≤ directionNormal (e (i : ZMod (2 * q))) (e (k : ZMod (2 * q))) →
          z i ≤ latticeNormal (directionNormal (e (i : ZMod (2 * q)))) x} =
      {x : RealPlane | z 0 ≤ latticeNormal (directionNormal (e 0)) x ∧
        ∀ i ∈ Finset.Icc k (q - 1), z (q + i) ≤ latticeNormal (-directionNormal (e (i : ZMod (2 * q)))) x} := by
  classical
  have hnormal (a : Site) : directionNormal (-a) = -directionNormal a := by
    ext g
    simp [directionNormal, determinant]
    ring
  have hindex (i : ℕ) : e ((q + i : ℕ) : ZMod (2 * q)) = -e (i : ZMod (2 * q)) := by
    rw [Nat.cast_add, add_comm, hfan.opposite]
  ext x
  constructor
  · intro hx
    have hzero := (forward_factor_normal_survives_iff e hfan k hk₀ hkq 0 (by omega)).mpr (Or.inl rfl)
    refine ⟨by simpa only [Nat.cast_zero] using hx 0 (by omega) hzero.1 hzero.2, ?_⟩
    intro i hi
    obtain ⟨hki, hiq⟩ := Finset.mem_Icc.mp hi
    have hsign := (forward_factor_normal_survives_iff e hfan k hk₀ hkq (q + i) (by omega)).mpr (Or.inr (by omega))
    simpa only [hindex, hnormal] using hx (q + i) (by omega) hsign.1 hsign.2
  · intro hx i hiq ha hb
    rcases (forward_factor_normal_survives_iff e hfan k hk₀ hkq i hiq).mp ⟨ha, hb⟩ with hi₀ | hki
    · subst i
      simpa only [Nat.cast_zero] using hx.1
    · have hj : i - q ∈ Finset.Icc k (q - 1) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      have he : q + (i - q) = i := by omega
      change z i ≤ latticeNormal (directionNormal (e (i : ZMod (2 * q)))) x
      rw [← he, hindex, hnormal]
      exact hx.2 (i - q) hj

-- separating the first actual facet from the later chain is an exact region identity.
theorem inward_chain_eq_adjoined_first_facet (ν : Site →+ ℤ) (cut : ℤ)
    (q k : ℕ) (hkq : k < q) (μ : ℕ → Site →+ ℤ) (z : ℕ → ℤ) :
    inwardLayerRegion ν cut (Finset.Icc k (q - 1)) μ z =
      inwardLayerRegion ν cut (facetIndexSet (Finset.Icc (k + 1) (q - 1)))
        (facetNormals (μ k) μ) (facetLevels (z k) z) := by
  ext x
  rw [mem_inward_region_adjoined_facet]
  constructor
  · intro hx
    refine ⟨hx.1, hx.2 k (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩), ?_⟩
    intro i hi
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hi
    exact hx.2 i (Finset.mem_Icc.mpr ⟨by omega, hhi⟩)
  · rintro ⟨hν, hfirst, hrest⟩
    refine ⟨hν, ?_⟩
    intro i hi
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hi
    by_cases he : i = k
    · simpa only [he] using hfirst
    · exact hrest i (Finset.mem_Icc.mpr ⟨by omega, hhi⟩)

end KumarNivat
