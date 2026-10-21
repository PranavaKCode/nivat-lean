module

public import KumarNivat.GeneratingSets
public import KumarNivat.GeneratedHalfplanes

@[expose] public section

namespace KumarNivat

noncomputable section

-- a real lattice normal extends along the two coordinate basis vectors.
def realLatticeNormal (ell : Site →+ ℝ) : RealPlane →ₗ[ℝ] ℝ where
  toFun x := ell (1, 0) * x.1 + ell (0, 1) * x.2
  map_add' x y := by simp; ring
  map_smul' a x := by simp; ring

-- the extension recovers the original normal on every integer lattice point.
theorem realLatticeNormal_embedding (ell : Site →+ ℝ) (u : Site) :
    realLatticeNormal ell (latticeEmbedding u) = ell u := by
  have hsite : u.1 • (1, 0) + u.2 • (0, 1) = u := by ext <;> simp
  have he := congrArg ell hsite
  rw [map_add, map_zsmul, map_zsmul] at he
  simp only [zsmul_eq_mul] at he
  change ell (1, 0) * (u.1 : ℝ) + ell (0, 1) * (u.2 : ℝ) = ell u
  nlinarith [he]

-- a point together with the open half-space strictly above its level forms a convex set.
theorem convex_apex_strict_halfspace (L : RealPlane →ₗ[ℝ] ℝ) (v : RealPlane) :
    Convex ℝ {x : RealPlane | x = v ∨ L v < L x} := by
  intro x hx y hy a b ha hb hab
  by_cases haz : a = 0
  · have hb₁ : b = 1 := by linarith
    simpa only [haz, hb₁, zero_smul, one_smul, zero_add] using hy
  by_cases hbz : b = 0
  · have ha₁ : a = 1 := by linarith
    simpa only [hbz, ha₁, zero_smul, one_smul, add_zero] using hx
  have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm haz)
  have hbp : 0 < b := lt_of_le_of_ne hb (Ne.symm hbz)
  have hbase : a * L v + b * L v = L v := by rw [← add_mul, hab, one_mul]
  rcases hx with hxv | hx
  · rcases hy with hyv | hy
    · left
      rw [hxv, hyv, ← add_smul, hab, one_smul]
    · right
      rw [hxv, map_add, map_smul, map_smul]
      change L v < a * L v + b * L y
      have hlt := mul_lt_mul_of_pos_left hy hbp
      linarith
  · rcases hy with hyv | hy
    · right
      rw [hyv, map_add, map_smul, map_smul]
      change L v < a * L x + b * L v
      have hlt := mul_lt_mul_of_pos_left hx hap
      linarith
    · right
      rw [map_add, map_smul, map_smul]
      change L v < a * L x + b * L y
      have hlt₁ := mul_lt_mul_of_pos_left hx hap
      have hlt₂ := mul_lt_mul_of_pos_left hy hbp
      linarith

-- a uniquely minimizing site is an actual extreme point of the real convex hull.
theorem latticeVertex_of_unique_real_minimum (S : Finset Site) (v : Site) (hv : v ∈ S)
    (ell : Site →+ ℝ) (hstrict : ∀ u ∈ S, u ≠ v → ell v < ell u) : IsLatticeVertex S v := by
  let L := realLatticeNormal ell
  let V := latticeEmbedding v
  have hsub : latticeEmbedding '' (S : Set Site) ⊆ {x : RealPlane | x = V ∨ L V < L x} := by
    rintro _ ⟨u, hu, rfl⟩
    by_cases he : u = v
    · left
      rw [he]
    · right
      exact (realLatticeNormal_embedding ell v).trans_lt
        ((hstrict u hu he).trans_eq (realLatticeNormal_embedding ell u).symm)
  have hHull := convexHull_min hsub (convex_apex_strict_halfspace L V)
  have hdiff : latticeHull S \ {V} = latticeHull S ∩ {x : RealPlane | L V < L x} := by
    ext x
    constructor
    · rintro ⟨hx, hne⟩
      refine ⟨hx, ?_⟩
      rcases hHull hx with he | hl
      · exact (hne (Set.mem_singleton_iff.mpr he)).elim
      · exact hl
    · rintro ⟨hx, hl⟩
      change L V < L x at hl
      refine ⟨hx, ?_⟩
      intro he
      rw [Set.mem_singleton_iff.mp he] at hl
      exact lt_irrefl _ hl
  apply (Convex.mem_extremePoints_iff_convex_sdiff
    (convex_convexHull ℝ (latticeEmbedding '' (S : Set Site)))).mpr
  refine ⟨subset_convexHull ℝ _ ⟨v, hv, rfl⟩, ?_⟩
  change Convex ℝ (latticeHull S \ {V})
  rw [hdiff]
  exact (convex_convexHull ℝ _).inter ((convex_Ioi (L V)).linear_preimage L)

-- nonexpansiveness forces a non-singleton supporting face of the actual generating polygon.
theorem oneSidedNonexpansive_supporting_pair {A : Type*} [TopologicalSpace A] [DiscreteTopology A]
    (c : Site → A) (R S : Finset Site) (hgen : GeneratingPolygon c R S)
    (ell : Site →+ ℝ) (hNE : OneSidedNonexpansive c ell) :
    ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ ell u = ell v ∧ ∀ w ∈ S, ell u ≤ ell w := by
  classical
  have hSne : S.Nonempty := by
    obtain ⟨u, hu, _v, _hv, _w, _hw, _hdet⟩ := hgen.2.2.1
    exact ⟨u, hu⟩
  obtain ⟨u, hu, hmin⟩ := S.exists_min_image ell hSne
  have hex : ∃ v ∈ S, v ≠ u ∧ ell v = ell u := by
    by_contra hn
    have hstrict : ∀ v ∈ S, v ≠ u → ell u < ell v := by
      intro v hv hvu
      apply lt_of_le_of_ne (hmin v hv)
      intro he
      exact hn ⟨v, hv, hvu, he.symm⟩
    have hvertex := latticeVertex_of_unique_real_minimum S u hu ell hstrict
    exact not_oneSidedNonexpansive_of_generated_unique_minimum c S u hu
      (hgen.2.2.2.1 u hvertex) ell hstrict hNE
  obtain ⟨v, hv, hvu, he⟩ := hex
  exact ⟨u, hu, v, hv, Ne.symm hvu, he.symm, hmin⟩

-- two minimizing lattice sites supply a primitive tangent and its exact integer line coordinate.
theorem oneSidedNonexpansive_primitive_direction {A : Type*} [TopologicalSpace A] [DiscreteTopology A]
    (c : Site → A) (R S : Finset Site) (hgen : GeneratingPolygon c R S)
    (ell : Site →+ ℝ) (hNE : OneSidedNonexpansive c ell) :
    ∃ p : Site, p ≠ 0 ∧ ∃ τ : Site →+ ℤ, τ p = 1 ∧
      ∀ g : Site, ell g = 0 ↔ g = τ g • p := by
  obtain ⟨u, hu, v, hv, huv, huvell, _hmin⟩ := oneSidedNonexpansive_supporting_pair c R S hgen ell hNE
  have hd : v - u ≠ 0 := sub_ne_zero.mpr (Ne.symm huv)
  obtain ⟨p, a, ha, he, hp, τ, hτ, hker⟩ := exists_primitive_direction_coordinate (v - u) hd
  have hz : ell (v - u) = 0 := by rw [map_sub, huvell, sub_self]
  rw [he, map_zsmul] at hz
  simp only [zsmul_eq_mul] at hz
  have haR : (a : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt ha
  have hpell : ell p = 0 := (mul_eq_zero.mp hz).resolve_left haR
  have hex : ∃ q : Site, ell q ≠ 0 := by
    by_contra hn
    apply hNE.1
    ext q
    by_contra hq
    exact hn ⟨q, hq⟩
  obtain ⟨q, hq⟩ := hex
  refine ⟨p, hp, τ, hτ, ?_⟩
  intro g
  constructor
  · intro hg
    have hid := congrArg ell (determinant_smul_identity p q g)
    rw [map_add, map_zsmul, map_zsmul, map_zsmul] at hid
    simp only [zsmul_eq_mul] at hid
    rw [hg, hpell, mul_zero, mul_zero, zero_add] at hid
    have hdetR : (determinant p g : ℝ) = 0 := (mul_eq_zero.mp hid.symm).resolve_right hq
    exact hker g (Int.cast_eq_zero.mp hdetR)
  · intro hg
    rw [hg, map_zsmul, hpell, smul_zero]

end

end KumarNivat
