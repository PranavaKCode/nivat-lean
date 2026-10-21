module

public import KumarNivat.SupportingFaceVertices
public import KumarNivat.ExposedFaceData
public import KumarNivat.ThinRectangles

@[expose] public section

namespace KumarNivat

-- the existing finite-window stencil represents the polygon with one coefficient per actual site.
noncomputable def polygonIndicator (S : Finset Site) : Laurent ℤ :=
  AddMonoidAlgebra.ofCoeff (localStencil S (fun _u => (1 : ℤ)))

-- the indicator's actual support is exactly the original polygon's lattice set.
theorem polygonIndicator_support (S : Finset Site) : (polygonIndicator S).coeff.support = S := by
  classical
  change (localStencil S (fun _u => (1 : ℤ))).support = S
  apply Finset.Subset.antisymm (localStencil_support_subset S _)
  intro u hu
  apply Finsupp.mem_support_iff.mpr
  have he := localStencil_coeff S (fun _u => (1 : ℤ)) ⟨u, hu⟩
  rw [he]
  decide

-- lattice convexity fills every consecutive site between two integer line endpoints.
theorem lattice_line_block_mem (S : Finset Site) (hS : LatticeConvex S) (q₀ p : Site) (t : ℕ)
    (hq₀ : q₀ ∈ S) (hq₁ : q₀ + (t : ℤ) • p ∈ S) :
    ∀ i : Fin (t + 1), q₀ + (i.val : ℤ) • p ∈ S := by
  have hsegment : lineInterval (latticeEmbedding q₀) (latticeEmbedding p) 0 (t : ℝ) ⊆ latticeHull S := by
    rw [lineInterval_eq_segment _ _ _ _ (Nat.cast_nonneg t)]
    simp only [zero_smul, add_zero]
    apply (convex_convexHull ℝ _).segment_subset
    · exact subset_convexHull ℝ _ ⟨q₀, hq₀, rfl⟩
    · have he := subset_convexHull ℝ (latticeEmbedding '' (S : Set Site)) ⟨q₀ + (t : ℤ) • p, hq₁, rfl⟩
      simpa only [latticeEmbedding_add, latticeEmbedding_zsmul, Int.cast_natCast] using he
  intro i
  apply hS
  apply hsegment
  refine ⟨(i.val : ℝ), ⟨Nat.cast_nonneg _, by exact_mod_cast Nat.le_of_lt_succ i.isLt⟩, ?_⟩
  simp only [latticeEmbedding_add, latticeEmbedding_zsmul, Int.cast_natCast]

-- an actual supporting face is a full consecutive lattice block with its true cardinality and vertices.
theorem exists_actual_polygon_face_block (S : Finset Site) (hS : LatticeConvex S)
    (ν : Site →+ ℤ) (hν : ν ≠ 0) (m : ℤ) (hmin : ∀ u ∈ S, m ≤ ν u)
    (hface : (lowerLatticeFace S ν m).Nonempty) (p : Site) (hp : ν p = 0)
    (hprimitive : Int.gcd p.1 p.2 = 1) :
    ∃ q₀ : Site, ∃ t : ℕ, ν q₀ = m ∧ q₀ ∈ S ∧ q₀ + (t : ℤ) • p ∈ S ∧
      (∀ i : Fin (t + 1), q₀ + (i.val : ℤ) • p ∈ S) ∧
      (∀ u ∈ lowerLatticeFace S ν m, ∃ i : Fin (t + 1), u = q₀ + (i.val : ℤ) • p) ∧
      (lowerLatticeFace S ν m).card = t + 1 ∧
      IsLatticeVertex S q₀ ∧ IsLatticeVertex S (q₀ + (t : ℤ) • p) := by
  classical
  have hpne : p ≠ 0 := by rintro rfl; simp at hprimitive
  obtain ⟨v, hv⟩ := hface
  have hvm := (Finset.mem_filter.mp hv).1
  have hvlevel := (Finset.mem_filter.mp hv).2
  let f := polygonIndicator S
  have hfs : f.coeff.support = S := polygonIndicator_support S
  obtain ⟨q₀, t, α, _hfirst, _hlast, hq₀, hq₀mem, hq₁mem, _hfaceeq, hpoints, _hdecomp, _hstrict⟩ :=
    exists_actual_exposed_face_data f ν hν m (by simpa only [hfs] using hmin) v p hpne hprimitive hp
      (by rw [hfs]; exact hvm) hvlevel
  rw [hfs] at hq₀mem hq₁mem hpoints
  have hblock := lattice_line_block_mem S hS q₀ p t hq₀mem hq₁mem
  have hnormalFace := normalFace_latticeHull_eq_lineInterval S ν m hmin q₀ p t hq₀mem hq₁mem hq₀ hp hpoints
  have hvertices := supporting_line_face_endpoints_lattice_vertices S ν m hmin q₀ p hprimitive t hnormalFace
  have hF : lowerLatticeFace S ν m = Finset.univ.image (fun i : Fin (t + 1) => q₀ + (i.val : ℤ) • p) := by
    ext u
    constructor
    · intro hu
      obtain ⟨hum, hun⟩ := Finset.mem_filter.mp hu
      obtain ⟨i, he⟩ := hpoints u hum hun
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, he.symm⟩
    · intro hu
      obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hu
      exact Finset.mem_filter.mpr ⟨hblock i, by rw [map_add, map_zsmul, hp, smul_zero, add_zero, hq₀]⟩
  have hinj : Function.Injective (fun i : Fin (t + 1) => q₀ + (i.val : ℤ) • p) := by
    intro i j he
    have hcast := integer_direction_multiple_injective p hpne (add_left_cancel he)
    exact Fin.ext (Int.ofNat_inj.mp hcast)
  have hcard : (lowerLatticeFace S ν m).card = t + 1 := by
    rw [hF, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  refine ⟨q₀, t, hq₀, hq₀mem, hq₁mem, hblock, ?_, hcard, hvertices.1, hvertices.2⟩
  intro u hu
  obtain ⟨hum, hun⟩ := Finset.mem_filter.mp hu
  exact hpoints u hum hun

-- the generating polygon now supplies both endpoint rules without an additional generation premise.
theorem exists_generating_polygon_face_block {A : Type*} (c : Site → A) (R S : Finset Site)
    (hgen : GeneratingPolygon c R S) (ν : Site →+ ℤ) (hν : ν ≠ 0) (m : ℤ)
    (hmin : ∀ u ∈ S, m ≤ ν u) (hface : (lowerLatticeFace S ν m).Nonempty)
    (p : Site) (hp : ν p = 0) (hprimitive : Int.gcd p.1 p.2 = 1) :
    ∃ q₀ : Site, ∃ t : ℕ, ν q₀ = m ∧ q₀ ∈ S ∧ q₀ + (t : ℤ) • p ∈ S ∧
      (∀ i : Fin (t + 1), q₀ + (i.val : ℤ) • p ∈ S) ∧
      (∀ u ∈ lowerLatticeFace S ν m, ∃ i : Fin (t + 1), u = q₀ + (i.val : ℤ) • p) ∧
      (lowerLatticeFace S ν m).card = t + 1 ∧ GeneratedSite c S q₀ ∧
      GeneratedSite c S (q₀ + (t : ℤ) • p) := by
  obtain ⟨q₀, t, hq₀, hq₀mem, hq₁mem, hblock, hpoints, hcard, hv₀, hv₁⟩ :=
    exists_actual_polygon_face_block S hgen.2.1 ν hν m hmin hface p hp hprimitive
  exact ⟨q₀, t, hq₀, hq₀mem, hq₁mem, hblock, hpoints, hcard,
    hgen.2.2.2.1 q₀ hv₀, hgen.2.2.2.1 _ hv₁⟩

end KumarNivat
