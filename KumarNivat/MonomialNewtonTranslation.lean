module

public import KumarNivat.OrientedProductUnits
public import KumarNivat.MinkowskiStencilFit

@[expose] public section

namespace KumarNivat

open scoped Pointwise

-- the exact support translation gives the same translation of the real newton hull.
theorem latticeHull_nonzero_monomial_translate {K : Type*} [CommRing K] [NoZeroDivisors K]
    (v : Site) (ε : K) (hε : ε ≠ 0) (f : Laurent K) :
    latticeHull (AddMonoidAlgebra.single v ε * f).coeff.support =
      (fun z : RealPlane => latticeEmbedding v + z) '' latticeHull f.coeff.support := by
  have hgen : latticeEmbedding '' ((AddMonoidAlgebra.single v ε * f).coeff.support : Set Site) =
      latticeEmbedding v +ᵥ (latticeEmbedding '' (f.coeff.support : Set Site)) := by
    change latticeEmbedding '' ((AddMonoidAlgebra.single v ε * f).coeff.support : Set Site) =
      (fun z : RealPlane => latticeEmbedding v + z) '' (latticeEmbedding '' (f.coeff.support : Set Site))
    ext z
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨latticeEmbedding (u - v), ⟨u - v,
        (nonzero_monomial_translate_mem_support v ε hε f u).mp hu, rfl⟩, ?_⟩
      change latticeEmbedding v + latticeEmbedding (u - v) = latticeEmbedding u
      rw [← latticeEmbedding_add]
      congr 1
      abel
    · rintro ⟨_z, ⟨u, hu, rfl⟩, rfl⟩
      change u ∈ f.coeff.support at hu
      refine ⟨v + u, ?_, latticeEmbedding_add v u⟩
      apply (nonzero_monomial_translate_mem_support v ε hε f (v + u)).mpr
      simpa only [add_sub_cancel_left] using hu
  unfold latticeHull
  rw [hgen, convexHull_vadd]
  rfl

-- undoing a translation preserves a real minkowski summand exactly.
theorem undo_translated_minkowski_summand (P S C : Set RealPlane) (v : RealPlane)
    (h : (fun z : RealPlane => v + z) '' P = S + C) :
    P = S + (fun z : RealPlane => z - v) '' C := by
  ext z
  constructor
  · intro hz
    have hm : v + z ∈ S + C := by rw [← h]; exact ⟨z, hz, rfl⟩
    obtain ⟨s, hs, c, hc, he⟩ := Set.mem_add.mp hm
    refine Set.mem_add.mpr ⟨s, hs, c - v, ⟨c, hc, rfl⟩, ?_⟩
    calc
      s + (c - v) = (s + c) - v := (add_sub_assoc s c v).symm
      _ = (v + z) - v := congrArg (fun x : RealPlane => x - v) he
      _ = z := add_sub_cancel_left v z
  · intro hz
    obtain ⟨s, hs, _c, ⟨c, hc, rfl⟩, rfl⟩ := Set.mem_add.mp hz
    have hm : v + (s + (c - v)) ∈ S + C := by
      have he : v + (s + (c - v)) = s + c := by abel
      rw [he]
      exact Set.add_mem_add hs hc
    rw [← h] at hm
    obtain ⟨z, hz, he⟩ := hm
    exact add_left_cancel he ▸ hz

end KumarNivat
