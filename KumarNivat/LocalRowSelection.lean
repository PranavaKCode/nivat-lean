module

public import KumarNivat.LocalParallelograms

@[expose] public section

namespace KumarNivat

open scoped Pointwise

-- these are exactly the lattice sites of the local parallelogram away from its supporting edge.
noncomputable def localParallelogramSites (S : Finset Site) (q₀ a b : Site) (r t : ℕ)
    (μ : Site →+ ℤ) (m : ℤ) : Finset Site := by
  classical
  exact S.filter (fun g => latticeEmbedding g ∈ latticeParallelogram q₀ a b r t ∧ μ g ≠ m)

-- one row representative and consecutive block is chosen for each actual local lattice site.
theorem exists_local_parallelogram_row_selector (S : Finset Site) (hS : LatticeConvex S)
    (q₀ a b : Site) (r t : ℕ) (ht : 0 < t)
    (hsub : latticeParallelogram q₀ a b r t ⊆ latticeHull S)
    (μ : Site →+ ℤ) (m : ℤ) (hb : μ b = 0) :
    ∃ E : localParallelogramSites S q₀ a b r t μ m → Site,
      (∀ u, E u ∈ S \ lowerLatticeFace S μ m) ∧
      (∀ u, ∃ d : ℤ, u.val = E u + d • b) ∧
      ∀ u, ∀ i : Fin t, E u + (i.val : ℤ) • b ∈ S \ lowerLatticeFace S μ m := by
  classical
  have hdata (u : localParallelogramSites S q₀ a b r t μ m) :=
    off_face_row_run_of_contained_parallelogram S hS q₀ a b r t ht hsub μ m hb u.val
      (Finset.mem_filter.mp u.property).2.1 (Finset.mem_filter.mp u.property).2.2
  choose E d he hmem hrun using hdata
  exact ⟨E, hmem, fun u => ⟨d u, he u⟩, hrun⟩

-- actual opposite faces and the generated transverse edge supply a nonempty local parallelogram and all its row runs.
theorem exists_generating_local_parallelogram_data {A : Type*} (c : Site → A)
    (R S : Finset Site) (hgen : GeneratingPolygon c R S)
    (a : Site) (hprimitiveA : Int.gcd a.1 a.2 = 1) (mA MA : ℤ)
    (hbounds : ∀ u ∈ S, mA ≤ directionNormal a u ∧ directionNormal a u ≤ MA)
    (r : ℕ) (hr : 0 < r)
    (hlower : r + 1 ≤ (lowerLatticeFace S (directionNormal a) mA).card)
    (hupper : r + 1 ≤ (lowerLatticeFace S (-directionNormal a) (-MA)).card)
    (b : Site) (hprimitiveB : Int.gcd b.1 b.2 = 1) (μ : Site →+ ℤ) (hμ : μ ≠ 0)
    (mB : ℤ) (hminB : ∀ u ∈ S, mB ≤ μ u) (hb : μ b = 0) (ha : 0 < μ a)
    (hfaceB : 2 ≤ (lowerLatticeFace S μ mB).card) :
    ∃ q₀ : Site, ∃ t : ℕ, μ q₀ = mB ∧ q₀ ∈ S ∧ q₀ + (t : ℤ) • b ∈ S ∧ 0 < t ∧
      (lowerLatticeFace S μ mB).card = t + 1 ∧
      latticeParallelogram q₀ a b r t ⊆ latticeHull S ∧
      (localParallelogramSites S q₀ a b r t μ mB).Nonempty ∧
      ∃ E : localParallelogramSites S q₀ a b r t μ mB → Site,
        (∀ u, E u ∈ S \ lowerLatticeFace S μ mB) ∧
        (∀ u, ∃ d : ℤ, u.val = E u + d • b) ∧
        ∀ u, ∀ i : Fin t, E u + (i.val : ℤ) • b ∈ S \ lowerLatticeFace S μ mB := by
  classical
  obtain ⟨C, _hC, hsum⟩ := segment_summand_of_opposite_face_cardinalities S hgen.2.1 a hprimitiveA
    mA MA hbounds r hlower hupper
  obtain ⟨q₀, t, hq₀, hfirst, hlast, _hblock, _hpoints, hcard, _hgenfirst, _hgenlast⟩ :=
    exists_generating_polygon_face_block c R S hgen μ hμ mB hminB
      (Finset.card_pos.mp (by omega)) b hb hprimitiveB
  have ht : 0 < t := by omega
  have hsub := supporting_edge_parallelogram_subset_hull S a b q₀ r t C hsum μ mB ha hb
    hminB hfirst hlast hq₀
  have hstart : latticeEmbedding q₀ ∈ lineInterval (latticeEmbedding q₀) (latticeEmbedding b) 0 (t : ℝ) :=
    ⟨0, ⟨le_rfl, Nat.cast_nonneg t⟩, by simp only [zero_smul, add_zero]⟩
  have hunit : latticeEmbedding a ∈ lineInterval 0 (latticeEmbedding a) 0 (r : ℝ) :=
    ⟨1, ⟨by norm_num, by exact_mod_cast hr⟩, by simp only [one_smul, zero_add]⟩
  have hpoint : latticeEmbedding (q₀ + a) ∈ latticeParallelogram q₀ a b r t := by
    rw [latticeEmbedding_add]
    exact Set.add_mem_add hstart hunit
  have hsites : (localParallelogramSites S q₀ a b r t μ mB).Nonempty := by
    refine ⟨q₀ + a, Finset.mem_filter.mpr ⟨hgen.2.1 _ (hsub hpoint), hpoint, ?_⟩⟩
    rw [map_add, hq₀]
    omega
  obtain ⟨E, hmem, hcover, hfit⟩ := exists_local_parallelogram_row_selector S hgen.2.1 q₀ a b r t ht hsub μ mB hb
  exact ⟨q₀, t, hq₀, hfirst, hlast, ht, hcard, hsub, hsites, E, hmem, hcover, hfit⟩

end KumarNivat
