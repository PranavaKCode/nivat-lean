module

public import KumarNivat.AnchoredEnvelopeLengths
public import KumarNivat.ExposedFacetGeometry

@[expose] public section

namespace KumarNivat

-- the same nonzero oriented interval has one initial endpoint and one length.
theorem oriented_line_interval_endpoints_unique (A B v : RealPlane) (hv : v ≠ 0)
    (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (heq : lineInterval A v 0 r = lineInterval B v 0 s) : A = B ∧ r = s := by
  have hA : A ∈ lineInterval A v 0 r := ⟨0, ⟨le_rfl, hr⟩, by simp⟩
  have hB : B ∈ lineInterval B v 0 s := ⟨0, ⟨le_rfl, hs⟩, by simp⟩
  have hAr : A + r • v ∈ lineInterval A v 0 r := ⟨r, ⟨hr, le_rfl⟩, rfl⟩
  have hBs : B + s • v ∈ lineInterval B v 0 s := ⟨s, ⟨hs, le_rfl⟩, rfl⟩
  have hA' : A ∈ lineInterval B v 0 s := heq ▸ hA
  have hB' : B ∈ lineInterval A v 0 r := heq.symm ▸ hB
  have hrs : r ≤ s := translated_segment_length_le_interval B A v hv r s hA' (heq ▸ hAr)
  have hsr : s ≤ r := translated_segment_length_le_interval A B v hv s r hB' (heq.symm ▸ hBs)
  obtain ⟨u, hu, hAu⟩ := hA'
  obtain ⟨t, ht, hBt⟩ := hB'
  change B + u • v = A at hAu
  change A + t • v = B at hBt
  have hzero : (u + t) • v = (0 : ℝ) • v := by
    rw [← hAu] at hBt
    have hsum : B + (u • v + t • v) = B := by simpa only [add_assoc] using hBt
    exact add_left_cancel (show B + (u + t) • v = B + (0 : ℝ) • v by
      rw [add_smul, hsum, zero_smul, add_zero])
  have hparameters : u + t = 0 := (smul_left_injective ℝ hv) hzero
  have hu0 : u = 0 := by linarith [hu.1, ht.1]
  exact ⟨by simpa only [hu0, zero_smul, add_zero] using hAu.symm, le_antisymm hrs hsr⟩

-- the actual cyclic newton vertex is also the first nonzero coefficient of its exposed primitive line block.
theorem actual_cyclic_exposed_operator_data {K : Type*} [CommRing K] {n : ℕ} [NeZero n]
    (f : Laurent K) (e : ZMod n → Site) (horder : CyclicEdgeOrder e)
    (P : OrderedCyclicLatticePolygon e f.coeff.support) (i : ZMod n)
    (hprimitive : Int.gcd (e i).1 (e i).2 = 1) :
    ∃ t : ℕ, ∃ α : Fin (t + 1) → K,
      (t : ℤ) = P.edgeLength i ∧ 0 < t ∧ α 0 ≠ 0 ∧ α (Fin.last t) ≠ 0 ∧
      exposedOperator f (directionNormal (e i)) (directionNormal (e i) (P.vertex i)) =
        lineOperator (P.vertex i) (e i) t α ∧
      f = lineOperator (P.vertex i) (e i) t α +
        (f - exposedOperator f (directionNormal (e i)) (directionNormal (e i) (P.vertex i))) ∧
      normalFace (latticeHull f.coeff.support) (latticeNormal (directionNormal (e i)))
        (directionNormal (e i) (P.vertex i) : ℝ) =
          lineInterval (latticeEmbedding (P.vertex i)) (latticeEmbedding (e i)) 0 (t : ℝ) := by
  have hp : e i ≠ 0 := by
    intro he
    have hpos := horder.adjacent_pos i
    rw [he] at hpos
    simp [determinant] at hpos
  have hν : directionNormal (e i) ≠ 0 := directionNormal_ne_zero _ hp
  have hmin : ∀ u ∈ f.coeff.support,
      directionNormal (e i) (P.vertex i) ≤ directionNormal (e i) u := by
    intro u hu
    have h := ordered_cyclic_real_point_normal_minimum e horder f.coeff.support P
      (latticeEmbedding u) (subset_convexHull ℝ _ ⟨u, hu, rfl⟩) i
    rw [latticeNormal_embedding] at h
    exact_mod_cast h
  obtain ⟨q₀, t, α, hfirst, hlast, _hqlevel, _hqmem, _hendmem, hcoeff, hdecomp, hface⟩ :=
    exists_actual_exposed_geometric_face_data f (directionNormal (e i)) hν
      (directionNormal (e i) (P.vertex i)) hmin (P.vertex i) (e i) hp hprimitive
        (directionNormal_self _) (P.vertex_mem i) rfl
  have hv : latticeEmbedding (e i) ≠ 0 := by
    intro he
    exact hp (latticeEmbedding_injective (by simpa [latticeEmbedding] using he))
  obtain ⟨hstart, hlength⟩ := oriented_line_interval_endpoints_unique
    (latticeEmbedding q₀) (latticeEmbedding (P.vertex i)) (latticeEmbedding (e i)) hv
    (t : ℝ) (P.edgeLength i : ℝ) (Nat.cast_nonneg _) (by exact_mod_cast (P.length_pos i).le)
    (hface.symm.trans (ordered_cyclic_facet_is_actual_edge e horder f.coeff.support P i))
  have hq : q₀ = P.vertex i := latticeEmbedding_injective hstart
  have ht : (t : ℤ) = P.edgeLength i := by exact_mod_cast hlength
  have htpos : 0 < t := by have hpos := P.length_pos i; omega
  rw [hq] at hcoeff hdecomp hface
  exact ⟨t, α, ht, htpos, hfirst, hlast, hcoeff, hdecomp, hface⟩

end KumarNivat
