import KumarNivat.AnchoredPolygonTransport

namespace KumarNivat

open scoped Pointwise

-- translating a sum moves the residual and keeps the original newton summand.
theorem translated_minkowski_residual (Z C : Set RealPlane) (U : RealPlane) :
    (fun z => U + z) '' (Z + C) = Z + (fun z => U + z) '' C := by
  ext x
  constructor
  · rintro ⟨_y, ⟨z, hz, c, hc, rfl⟩, rfl⟩
    exact Set.mem_add.mpr ⟨z, hz, U + c, ⟨c, hc, rfl⟩,
      add_left_comm z U c⟩
  · rintro ⟨z, hz, _y, ⟨c, hc, rfl⟩, rfl⟩
    exact ⟨z + c, Set.add_mem_add hz hc,
      add_left_comm U z c⟩

-- the actual cyclic envelope survives the same integer translation as its polygon.
theorem AnchoredCyclicEnvelope.translation {n : ℕ} [NeZero n]
    {e : ZMod n → Site} {Z : Set RealPlane} {M : Finset Site}
    (hEnvelope : AnchoredCyclicEnvelope e Z M) (hM : LatticeConvex M) (U : Site) :
    AnchoredCyclicEnvelope e Z (M.image (fun g => U + g)) := by
  obtain ⟨⟨P⟩, C, hconvex, hcompact, hnonempty, hsum⟩ := hEnvelope
  refine ⟨⟨orderedCyclicPolygonTranslation e M P hM U⟩,
    (fun z : RealPlane => latticeEmbedding U + z) '' C, ?_, ?_, ?_, ?_⟩
  · simpa only [one_smul] using hconvex.affinity (latticeEmbedding U) (1 : ℝ)
  · exact hcompact.image (by fun_prop)
  · obtain ⟨c, hc⟩ := hnonempty
    exact ⟨latticeEmbedding U + c, c, hc, rfl⟩
  · have hHull : latticeHull (M.image (fun g => U + g)) =
        (fun z : RealPlane => latticeEmbedding U + z) '' latticeHull M := by
      simpa only [one_smul, Int.cast_one] using latticeHull_integer_affinity M 1 U
    rw [hHull, hsum, translated_minkowski_residual]

-- the finite-window translation carries every forward lattice row to its actual translated base.
theorem polygon_half_strip_add_translation (F : Finset Site) (a U g : Site)
    (hg : g ∈ polygonHalfStrip F a) :
    U + g ∈ polygonHalfStrip (F.image (fun h => U + h)) a := by
  classical
  obtain ⟨⟨u, n⟩, he⟩ := hg
  refine ⟨(⟨U + u.val, Finset.mem_image.mpr ⟨u.val, u.property, rfl⟩⟩, n), ?_⟩
  change (U + u.val) + (0 + (n : ℤ)) • a = U + g
  change u.val + (0 + (n : ℤ)) • a = g at he
  rw [← he]
  abel

-- opposite translations recover the same finite observation set exactly.
theorem lattice_window_opposite_translation (F : Finset Site) (U : Site) :
    (F.image (fun g => U + g)).image (fun g => -U + g) = F := by
  classical
  rw [Finset.image_image]
  change F.image (fun g => -U + (U + g)) = F
  have he : (fun g : Site => -U + (U + g)) = id := by funext g; simp
  rw [he, Finset.image_id]

-- the reference and source shifts undo the same change of lattice origin.
theorem shift_opposite_translation {A : Type*} (x : Site → A) (U : Site) :
    shift U (shift (-U) x) = x := by
  funext g
  simp only [shift, add_assoc, add_neg_cancel, add_zero]

-- agreement, the actual half-strip, and the compact convex residual all translate together.
theorem AnchoredCyclicAgreement.translation {A : Type*} {n : ℕ} [NeZero n]
    {z w : Site → A} {F M : Finset Site} {a : Site} {e : ZMod n → Site} {Z : Set RealPlane}
    (hM : AnchoredCyclicAgreement z w F a e Z M) (U : Site) :
    AnchoredCyclicAgreement (shift (-U) z) (shift (-U) w)
      (F.image (fun g => U + g)) a e Z (M.image (fun g => U + g)) := by
  classical
  obtain ⟨hEnvelope, hconvex, hFM, hstrip, hagree⟩ := hM
  refine ⟨hEnvelope.translation hconvex U, latticeConvex_integer_translation M hconvex U,
    Finset.image_subset_image hFM, ?_, ?_⟩
  · intro g hg
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hg
    exact polygon_half_strip_add_translation F a U h (hstrip h hh)
  · intro g hg
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hg
    change z (U + h + -U) = w (U + h + -U)
    have he : U + h + -U = h := by abel
    rw [he]
    exact hagree h hh

-- inverse translation makes anchored maximality the original actual maximality theorem.
theorem anchored_cyclic_maximality_translation {A : Type*} {n : ℕ} [NeZero n]
    (z w : Site → A) (F M : Finset Site) (a : Site) (e : ZMod n → Site) (Z : Set RealPlane)
    (hmax : ∀ Q : Finset Site, AnchoredCyclicAgreement z w F a e Z Q → M ⊆ Q → Q = M)
    (U : Site) :
    ∀ Q : Finset Site, AnchoredCyclicAgreement (shift (-U) z) (shift (-U) w)
      (F.image (fun g => U + g)) a e Z Q → M.image (fun g => U + g) ⊆ Q →
        Q = M.image (fun g => U + g) := by
  classical
  intro Q hQ hMQ
  have hback : AnchoredCyclicAgreement z w F a e Z (Q.image (fun g => -U + g)) := by
    simpa only [neg_neg, shift_opposite_translation, lattice_window_opposite_translation] using hQ.translation (-U)
  have hsub : M ⊆ Q.image (fun g => -U + g) := by
    intro g hg
    have hmem : U + g ∈ Q := hMQ (Finset.mem_image.mpr ⟨g, hg, rfl⟩)
    exact Finset.mem_image.mpr ⟨U + g, hmem, by simp⟩
  have he := congrArg (fun S : Finset Site => S.image (fun g => U + g))
    (hmax _ hback hsub)
  have hcancel : (Q.image (fun g => -U + g)).image (fun g => U + g) = Q := by
    simpa only [neg_neg] using lattice_window_opposite_translation Q (-U)
  rwa [hcancel] at he

end KumarNivat
