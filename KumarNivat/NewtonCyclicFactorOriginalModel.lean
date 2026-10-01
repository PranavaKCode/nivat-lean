import KumarNivat.NewtonCyclicFactorOriginalSigning
import KumarNivat.NewtonCyclicFactorFan
import KumarNivat.NewtonCyclicFactorHull
import KumarNivat.NewtonCyclicFactorCorners

namespace KumarNivat

-- each antipodal edge retains its original positive primitive integer length.
def cyclicFactorPrimitiveLengths (q : ℕ) [NeZero q] (k : Fin q → ℕ) : ZMod (2 * q) → ℤ :=
  fun i => if hi : i.val < q then (k ⟨i.val, hi⟩ : ℤ)
    else (k ⟨i.val - q, by have hv := ZMod.val_lt i; omega⟩ : ℤ)

-- both halves use the same actual positive gcd length.
theorem cyclicFactorPrimitiveLengths_pos (q : ℕ) [NeZero q] (k : Fin q → ℕ)
    (hk : ∀ i, 0 < k i) : ∀ i, 0 < cyclicFactorPrimitiveLengths q k i := by
  intro i
  unfold cyclicFactorPrimitiveLengths
  split_ifs with hi <;> exact_mod_cast hk _

-- the signed actual factors coincide with those primitive edges and their actual lengths.
theorem doubled_factor_primitive_edge_eq (q : ℕ) [NeZero q]
    (f : Fin q → Site) (E : ZMod (2 * q) → Site) (k : Fin q → ℕ)
    (hanti : ∀ i, E (i + (q : ZMod (2 * q))) = -E i)
    (hfactor : ∀ j, f j = (k j : ℤ) • E (j.val : ZMod (2 * q))) :
    ∀ i, doubledFactorDirections q f i = cyclicFactorPrimitiveLengths q k i • E i := by
  intro i
  by_cases hi : i.val < q
  · let j : Fin q := ⟨i.val, hi⟩
    have he := hfactor j
    have hcast : (j.val : ZMod (2 * q)) = i := ZMod.natCast_zmod_val i
    rw [hcast] at he
    simpa only [doubledFactorDirections, cyclicFactorPrimitiveLengths, hi, dite_true] using he
  · let j : Fin q := ⟨i.val - q, by have hv := ZMod.val_lt i; omega⟩
    have hshift : (j.val : ZMod (2 * q)) + (q : ZMod (2 * q)) = i := by
      rw [← Nat.cast_add]
      have he : j.val + q = i.val := by dsimp [j]; omega
      rw [he, ZMod.natCast_zmod_val]
    simp only [doubledFactorDirections, cyclicFactorPrimitiveLengths, hi, dite_false]
    rw [hfactor j, ← smul_neg, ← hanti (j.val : ZMod (2 * q)), hshift]

-- undoing the actual integer signing translation preserves the exact vertex hull.
theorem original_hull_of_translated_vertex_hull {I : Type*} (T : Finset Site)
    (v : I → Site) (s : Site)
    (htranslate : (fun z : RealPlane => latticeEmbedding s + z) '' latticeHull T =
      convexHull ℝ (Set.range (fun i => latticeEmbedding (v i)))) :
    latticeHull T = convexHull ℝ (Set.range (fun i => latticeEmbedding (v i - s))) := by
  have hgen : Set.range (fun i => latticeEmbedding (v i - s)) =
      (fun z : RealPlane => -latticeEmbedding s + z) '' Set.range (fun i => latticeEmbedding (v i)) := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      refine ⟨latticeEmbedding (v i), ⟨i, rfl⟩, ?_⟩
      change -latticeEmbedding s + latticeEmbedding (v i) = latticeEmbedding (v i - s)
      rw [latticeEmbedding_sub]
      abel
    · rintro ⟨_w, ⟨i, rfl⟩, rfl⟩
      refine ⟨i, ?_⟩
      change latticeEmbedding (v i - s) = -latticeEmbedding s + latticeEmbedding (v i)
      rw [latticeEmbedding_sub]
      abel
  have hinverse : convexHull ℝ (Set.range (fun i => latticeEmbedding (v i - s))) =
      (fun z : RealPlane => -latticeEmbedding s + z) ''
        convexHull ℝ (Set.range (fun i => latticeEmbedding (v i))) := by
    rw [hgen]
    exact convexHull_vadd (-latticeEmbedding s) _
  rw [← htranslate, Set.image_image] at hinverse
  have hcancel : (fun z : RealPlane => -latticeEmbedding s + (latticeEmbedding s + z)) = id := by
    funext z
    dsimp
    abel
  rw [hcancel, Set.image_id] at hinverse
  exact hinverse.symm

-- the original product's actual support now supplies its complete primitive cyclic polygon model.
theorem actual_original_difference_product_cyclic_model {K : Type*} [CommRing K] [Nontrivial K] [NoZeroDivisors K]
    (hs : List Site) (hlen : 2 ≤ hs.length) (hdirs : ∀ h ∈ hs, h ≠ 0)
    (hpairs : hs.Pairwise (fun p q => determinant p q ≠ 0)) :
    ∃ q : ℕ, ∃ hq : 2 ≤ q,
      let _ : NeZero q := ⟨by omega⟩
      q = hs.length ∧ ∃ E : ZMod (2 * q) → Site,
        CyclicEdgeOrder E ∧
        (∀ i, E (i + (q : ZMod (2 * q))) = -E i) ∧
        (∀ i (d : ℕ), 0 < d → d < q → 0 < determinant (E i) (E (i + (d : ZMod (2 * q))))) ∧
        (∀ i, Int.gcd (E i).1 (E i).2 = 1) ∧
        (∀ i, ∃ g ∈ hs, determinant (E i) g = 0) ∧
        (∀ g ∈ hs, ∃ i : ZMod (2 * q), determinant (E i) g = 0) ∧
        Nonempty (OrderedCyclicLatticePolygon E (differenceProduct (K := K) hs).coeff.support) := by
  classical
  obtain ⟨q, hq, hfan⟩ := actual_primitive_factor_cyclic_fan hs hlen hdirs hpairs
  let _ : NeZero q := ⟨by omega⟩
  obtain ⟨hqeq, E, horder, hanti, hstrict, hprimitive, hsource, hcover, f, k, hlist, hfactor⟩ := hfan
  have hk : ∀ j, 0 < k j := fun j => (hfactor j).1
  let r := cyclicFactorPrimitiveLengths q k
  let v := doubledFactorVertices q f
  have hr : ∀ i, 0 < r i := cyclicFactorPrimitiveLengths_pos q k hk
  have hedge : ∀ i, v (i + 1) = v i + r i • E i := by
    intro i
    change doubledFactorVertices q f (i + 1) = doubledFactorVertices q f i +
      cyclicFactorPrimitiveLengths q k i • E i
    rw [doubledFactorVertices_next,
      doubled_factor_primitive_edge_eq q f E k hanti (fun j => (hfactor j).2)]
  obtain ⟨_hperm, _hlen, hupper, hsort, _hprovenance⟩ := upperSortedFactors_actual_data hs hdirs hpairs
  have hfstrict : ∀ i j : Fin q, i < j → 0 < determinant (f i) (f j) := by
    have hp : (List.ofFn f).Pairwise (fun p q => 0 < determinant p q) := by rw [hlist]; exact hsort
    exact fun i j hij => List.pairwise_ofFn.mp hp hij
  have hnonzero : ∀ g ∈ upperSortedFactors hs, g ≠ 0 := by
    intro g hg he
    have hu := hupper g hg
    simp [he, InUpperFactorHalf] at hu
  have hsorted : latticeHull (differenceProduct (K := K) (upperSortedFactors hs)).coeff.support =
      convexHull ℝ (Set.range (fun i => latticeEmbedding (v i))) := by
    rw [latticeHull_differenceProduct_eq_zonotope (upperSortedFactors hs) hnonzero, ← hlist]
    exact (ordered_factor_prefix_hull_eq_zonotope q hq f hfstrict).symm
  obtain ⟨s, ε, hε, hsigning⟩ := upper_sorted_difference_product_monomial (K := K) hs hdirs
  let T := (differenceProduct (K := K) hs).coeff.support
  have htranslate : (fun z : RealPlane => latticeEmbedding s + z) '' latticeHull T =
      convexHull ℝ (Set.range (fun i => latticeEmbedding (v i))) := by
    change (fun z : RealPlane => latticeEmbedding s + z) ''
      latticeHull (differenceProduct (K := K) hs).coeff.support = _
    rw [← latticeHull_nonzero_monomial_translate s ε hε (differenceProduct (K := K) hs), ← hsigning]
    exact hsorted
  let w := fun i => v i - s
  have hwhull : latticeHull T = convexHull ℝ (Set.range (fun i => latticeEmbedding (w i))) :=
    original_hull_of_translated_vertex_hull T v s htranslate
  have hwedge : ∀ i, w (i + 1) = w i + r i • E i := by
    intro i
    dsimp [w]
    rw [hedge]
    abel
  let P : OrderedCyclicLatticePolygon E T :=
    { vertex := w
      edgeLength := r
      length_pos := hr
      edge_eq := hwedge
      vertex_mem := ordered_cyclic_walk_vertex_mem_actual_support E horder w r hr hwedge T hwhull
      hull_eq := hwhull }
  exact ⟨q, hq, hqeq, E, horder, hanti, hstrict, hprimitive, hsource, hcover, ⟨P⟩⟩

end KumarNivat
