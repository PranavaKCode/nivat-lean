import KumarNivat.MinkowskiStencilFit
import KumarNivat.GeneratingSets

namespace KumarNivat

-- reflect one lattice axis to reverse orientation without changing any site arithmetic.
def siteReflection : Site ≃+ Site where
  toFun g := (g.1, -g.2)
  invFun g := (g.1, -g.2)
  left_inv g := by ext <;> simp
  right_inv g := by ext <;> simp
  map_add' g h := by
    ext
    · rfl
    · change -(g.2 + h.2) = -g.2 + -h.2
      abel

-- the same reflection acts linearly on the real polygon coordinates.
def planeReflection : RealPlane ≃ₗ[ℝ] RealPlane where
  toFun g := (g.1, -g.2)
  invFun g := (g.1, -g.2)
  left_inv g := by ext <;> simp
  right_inv g := by ext <;> simp
  map_add' g h := by
    ext
    · rfl
    · change -(g.2 + h.2) = -g.2 + -h.2
      abel
  map_smul' r g := by ext <;> simp

@[simp] theorem siteReflection_twice (g : Site) : siteReflection (siteReflection g) = g := by
  ext <;> simp [siteReflection]

@[simp] theorem planeReflection_twice (g : RealPlane) : planeReflection (planeReflection g) = g := by
  ext <;> simp [planeReflection]

-- the integer and real actions commute with the actual lattice embedding.
@[simp] theorem planeReflection_embedding (g : Site) :
    planeReflection (latticeEmbedding g) = latticeEmbedding (siteReflection g) := by
  ext <;> simp [planeReflection, latticeEmbedding, siteReflection]

-- exactly one axis reversal changes the signed determinant's sign.
theorem determinant_siteReflection (a b : Site) :
    determinant (siteReflection a) (siteReflection b) = -determinant a b := by
  simp only [siteReflection, AddEquiv.coe_mk, Equiv.coe_fn_mk, determinant]
  ring

-- reflected windows contain precisely the reflected original sites.
def reflectedWindow (S : Finset Site) : Finset Site := S.image siteReflection

@[simp] theorem mem_reflectedWindow (S : Finset Site) (g : Site) :
    g ∈ reflectedWindow S ↔ siteReflection g ∈ S := by
  classical
  constructor
  · rintro hg
    obtain ⟨u, hu, he⟩ := Finset.mem_image.mp hg
    rw [← he, siteReflection_twice]
    exact hu
  · intro hg
    exact Finset.mem_image.mpr ⟨siteReflection g, hg, siteReflection_twice g⟩

@[simp] theorem reflectedWindow_twice (S : Finset Site) : reflectedWindow (reflectedWindow S) = S := by
  ext g
  simp only [mem_reflectedWindow, siteReflection_twice]

theorem reflectedWindow_card (S : Finset Site) : (reflectedWindow S).card = S.card :=
  Finset.card_image_of_injective _ siteReflection.injective

-- reflection identifies the real hull of the transformed window exactly.
theorem latticeHull_reflectedWindow (S : Finset Site) :
    latticeHull (reflectedWindow S) = planeReflection '' latticeHull S := by
  have hgen : latticeEmbedding '' (reflectedWindow S : Set Site) =
      planeReflection '' (latticeEmbedding '' (S : Set Site)) := by
    ext z
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨latticeEmbedding (siteReflection g), ⟨siteReflection g,
        (mem_reflectedWindow S g).mp hg, rfl⟩, by rw [planeReflection_embedding, siteReflection_twice]⟩
    · rintro ⟨_z, ⟨g, hg, rfl⟩, rfl⟩
      exact ⟨siteReflection g, (mem_reflectedWindow S _).mpr (by rwa [siteReflection_twice]),
        (planeReflection_embedding g).symm⟩
  unfold latticeHull
  rw [hgen]
  exact (planeReflection.toLinearMap.toAffineMap.image_convexHull
    (latticeEmbedding '' (S : Set Site))).symm

-- pull the same array back through the orientation change.
def reflectedConfig {A : Type*} (c : Site → A) : Site → A := fun g => c (siteReflection g)

-- a normal is pulled back by the same involution as the array.
def reflectedNormal (ν : Site →+ ℤ) : Site →+ ℤ := ν.comp siteReflection.toAddMonoidHom

@[simp] theorem reflectedNormal_reflected_site (ν : Site →+ ℤ) (g : Site) :
    reflectedNormal ν (siteReflection g) = ν g := by
  change ν (siteReflection (siteReflection g)) = ν g
  rw [siteReflection_twice]

-- each original site and reflected site describe the same finite pattern coordinate.
def reflectionWindowEquiv (S : Finset Site) : S ≃ reflectedWindow S where
  toFun u := ⟨siteReflection u.val, (mem_reflectedWindow S _).mpr (by rw [siteReflection_twice]; exact u.property)⟩
  invFun u := ⟨siteReflection u.val, (mem_reflectedWindow S _).mp u.property⟩
  left_inv u := Subtype.ext (siteReflection_twice u.val)
  right_inv u := Subtype.ext (siteReflection_twice u.val)

end KumarNivat
