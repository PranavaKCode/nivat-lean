import KumarNivat.ReflectionPatterns
import KumarNivat.PolyhedralRays

namespace KumarNivat

-- reflection preserves window inclusion and the exact set difference used for each observed base.
theorem reflectedWindow_subset {S T : Finset Site} (h : T ⊆ S) : reflectedWindow T ⊆ reflectedWindow S := by
  intro g hg
  exact (mem_reflectedWindow S g).mpr (h ((mem_reflectedWindow T g).mp hg))

theorem reflectedWindow_sdiff (S T : Finset Site) :
    reflectedWindow (S \ T) = reflectedWindow S \ reflectedWindow T :=
  Finset.image_sdiff S T siteReflection.injective

theorem reflectedWindow_erase (S : Finset Site) (v : Site) :
    reflectedWindow (S.erase v) = (reflectedWindow S).erase (siteReflection v) :=
  Finset.image_erase siteReflection.injective S v

-- no normal is lost when its coordinates are reflected.
theorem reflectedNormal_ne_zero (ν : Site →+ ℤ) (hν : ν ≠ 0) : reflectedNormal ν ≠ 0 := by
  intro hz
  apply hν
  ext g
  have he := congrArg (fun μ : Site →+ ℤ => μ (siteReflection g)) hz
  simpa only [reflectedNormal_reflected_site, AddMonoidHom.zero_apply] using he

-- negating an inward normal commutes with the coordinate change.
@[simp] theorem reflectedNormal_neg (ν : Site →+ ℤ) : reflectedNormal (-ν) = -reflectedNormal ν := by
  ext g
  rfl

-- the tangent normal changes sign exactly as the determinant does.
theorem directionNormal_siteReflection (a : Site) :
    directionNormal (siteReflection a) = reflectedNormal (-directionNormal a) := by
  ext g
  change determinant (siteReflection a) g = -determinant a (siteReflection g)
  conv_lhs => rw [← siteReflection_twice g]
  exact determinant_siteReflection a (siteReflection g)

-- primitivity is unchanged by reversing one integer coordinate.
theorem primitive_siteReflection (a : Site) (ha : Int.gcd a.1 a.2 = 1) :
    Int.gcd (siteReflection a).1 (siteReflection a).2 = 1 := by
  obtain ⟨τ, hτ, _hker⟩ := primitive_direction_coordinate a ha
  apply primitive_gcd_of_line_coordinate (siteReflection a) (reflectedNormal τ)
  rwa [reflectedNormal_reflected_site]

-- the real normal evaluation is invariant when both normal and point are reflected.
theorem latticeNormal_reflection (ν : Site →+ ℤ) (z : RealPlane) :
    latticeNormal (reflectedNormal ν) (planeReflection z) = latticeNormal ν z := by
  have he : ν (0, -1) = -ν (0, 1) := by
    simpa only [Prod.neg_mk, neg_zero] using map_neg ν (0, 1)
  change (ν (1, 0) : ℝ) * z.1 + (ν (0, -1) : ℝ) * (-z.2) =
    (ν (1, 0) : ℝ) * z.1 + (ν (0, 1) : ℝ) * z.2
  rw [he, Int.cast_neg]
  ring

-- actual integer supporting faces transform together with their normals.
theorem lowerLatticeFace_reflection (S : Finset Site) (ν : Site →+ ℤ) (m : ℤ) :
    lowerLatticeFace (reflectedWindow S) (reflectedNormal ν) m = reflectedWindow (lowerLatticeFace S ν m) := by
  ext g
  simp only [lowerLatticeFace, Finset.mem_filter, mem_reflectedWindow]
  rfl

-- reflection preserves all lattice sites of the real hull.
theorem LatticeConvex.reflection {S : Finset Site} (hS : LatticeConvex S) : LatticeConvex (reflectedWindow S) := by
  intro g hg
  rw [latticeHull_reflectedWindow] at hg
  obtain ⟨z, hz, he⟩ := hg
  have he' := congrArg planeReflection he
  rw [planeReflection_twice, planeReflection_embedding] at he'
  apply (mem_reflectedWindow S g).mpr
  apply hS
  rwa [← he']

-- extreme points of the real hull are preserved by the invertible linear reflection.
theorem isLatticeVertex_reflection (S : Finset Site) (v : Site) :
    IsLatticeVertex (reflectedWindow S) (siteReflection v) ↔ IsLatticeVertex S v := by
  unfold IsLatticeVertex
  rw [latticeHull_reflectedWindow, ← image_extremePoints planeReflection]
  constructor
  · rintro ⟨z, hz, he⟩
    rw [← planeReflection_embedding] at he
    exact planeReflection.injective he ▸ hz
  · intro hv
    exact ⟨latticeEmbedding v, hv, planeReflection_embedding v⟩

-- signed areas reverse but a genuine two-dimensional generating polygon stays two-dimensional.
theorem NoncollinearSites.reflection {S : Finset Site} (hS : NoncollinearSites S) :
    NoncollinearSites (reflectedWindow S) := by
  obtain ⟨u, hu, v, hv, w, hw, hdet⟩ := hS
  refine ⟨siteReflection u, (mem_reflectedWindow S _).mpr (by rwa [siteReflection_twice]),
    siteReflection v, (mem_reflectedWindow S _).mpr (by rwa [siteReflection_twice]),
    siteReflection w, (mem_reflectedWindow S _).mpr (by rwa [siteReflection_twice]), ?_⟩
  rw [← map_sub, ← map_sub, determinant_siteReflection]
  exact neg_ne_zero.mpr hdet

-- unique legal extensions are unchanged by the bijective window coordinates.
theorem extensionUnique_reflection {A : Type*} (c : Site → A) (S T : Finset Site)
    (hunique : ExtensionUnique c T S) :
    ExtensionUnique (reflectedConfig c) (reflectedWindow T) (reflectedWindow S) := by
  intro g h hagree u hu
  change c (siteReflection (g + u)) = c (siteReflection (h + u))
  rw [map_add, map_add]
  apply hunique (siteReflection g) (siteReflection h)
  · intro v hv
    have he := hagree (siteReflection v) ((mem_reflectedWindow T _).mpr (by rwa [siteReflection_twice]))
    simpa only [reflectedConfig, map_add, siteReflection_twice] using he
  · exact (mem_reflectedWindow S u).mp hu

-- the generating property and every exact edge budget survive reflection.
theorem GeneratingPolygon.reflection {A : Type*} {c : Site → A} {R S : Finset Site}
    (hgen : GeneratingPolygon c R S) :
    GeneratingPolygon (reflectedConfig c) (reflectedWindow R) (reflectedWindow S) := by
  refine ⟨reflectedWindow_subset hgen.1, hgen.2.1.reflection, hgen.2.2.1.reflection, ?_, ?_⟩
  · intro v hv
    have hvertex : IsLatticeVertex S (siteReflection v) :=
      (isLatticeVertex_reflection S (siteReflection v)).mp (by simpa only [siteReflection_twice] using hv)
    have hsite := extensionUnique_reflection c S (S.erase (siteReflection v)) (hgen.2.2.2.1 _ hvertex)
    simpa only [GeneratedSite, reflectedWindow_erase, siteReflection_twice] using hsite
  · intro ν hν m hmin hface
    let η := reflectedNormal ν
    have hη : η ≠ 0 := reflectedNormal_ne_zero ν hν
    have hmin' : ∀ u ∈ S, m ≤ η u := by
      intro u hu
      exact hmin (siteReflection u) ((mem_reflectedWindow S _).mpr (by rwa [siteReflection_twice]))
    have hνback : reflectedNormal η = ν := by ext g; exact congrArg ν (siteReflection_twice g)
    have hfaceEq : lowerLatticeFace (reflectedWindow S) ν m = reflectedWindow (lowerLatticeFace S η m) := by
      rw [← hνback]
      exact lowerLatticeFace_reflection S η m
    have hface' : (lowerLatticeFace S η m).Nonempty := by
      rw [hfaceEq] at hface
      obtain ⟨v, hv⟩ := hface
      exact ⟨siteReflection v, (mem_reflectedWindow _ v).mp hv⟩
    have hbudget := hgen.2.2.2.2 η hη m hmin' hface'
    rw [hfaceEq, ← reflectedWindow_sdiff, complexity_reflection, complexity_reflection, reflectedWindow_card]
    exact hbudget

-- inward inequality regions describe the same points after reflection.
theorem mem_inwardLayerRegion_reflection {I : Type*} (ν : Site →+ ℤ) (cut : ℤ)
    (J : Finset I) (μ : I → Site →+ ℤ) (z : I → ℤ) (w : RealPlane) :
    planeReflection w ∈ inwardLayerRegion (reflectedNormal ν) cut J
      (fun i => reflectedNormal (μ i)) z ↔ w ∈ inwardLayerRegion ν cut J μ z := by
  simp only [inwardLayerRegion, Set.mem_ofPred_eq, latticeNormal_reflection]

-- lattice membership uses the same original integer inequalities under the reflected site.
theorem mem_inwardLayerRegion_reflected_site {I : Type*} (ν : Site →+ ℤ) (cut : ℤ)
    (J : Finset I) (μ : I → Site →+ ℤ) (z : I → ℤ) (g : Site) :
    latticeEmbedding (siteReflection g) ∈ inwardLayerRegion (reflectedNormal ν) cut J
      (fun i => reflectedNormal (μ i)) z ↔ latticeEmbedding g ∈ inwardLayerRegion ν cut J μ z := by
  rw [← planeReflection_embedding]
  exact mem_inwardLayerRegion_reflection ν cut J μ z (latticeEmbedding g)

end KumarNivat
