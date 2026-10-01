import KumarNivat.NewtonCyclicFactorOriginalModel
import KumarNivat.PairedStructureRayChainFan

namespace KumarNivat

-- the original newton model rotates to the prescribed actual primitive tangent, without an external polygon model.
theorem actual_original_cyclic_model_with_prescribed_factor {K : Type*}
    [CommRing K] [Nontrivial K] [NoZeroDivisors K]
    (hs : List Site) (hlen : 2 ≤ hs.length) (hdirs : ∀ h ∈ hs, h ≠ 0)
    (hpairs : hs.Pairwise (fun p q => determinant p q ≠ 0))
    (a : Site) (ha : Int.gcd a.1 a.2 = 1) (p : Site) (hp : p ∈ hs)
    (hparallel : determinant a p = 0) :
    ∃ q : ℕ, ∃ hq : 2 ≤ q,
      let _ : NeZero q := ⟨by omega⟩
      q = hs.length ∧ ∃ e : ZMod (2 * q) → Site,
        e 0 = a ∧ AnchoredChainFanOrder e ∧
        (∀ i, Int.gcd (e i).1 (e i).2 = 1) ∧
        (∀ i, ∃ g ∈ hs, determinant (e i) g = 0) ∧
        (∀ g ∈ hs, ∃ i, determinant (e i) g = 0) ∧
        Nonempty (OrderedCyclicLatticePolygon e (differenceProduct (K := K) hs).coeff.support) := by
  classical
  obtain ⟨q, hq, hmodel⟩ := actual_original_difference_product_cyclic_model (K := K) hs hlen hdirs hpairs
  let _ : NeZero q := ⟨by omega⟩
  obtain ⟨hqeq, E, horder, hanti, hpositive, hprimitive, hsource, hcover, ⟨P⟩⟩ := hmodel
  have hfan : AnchoredChainFanOrder E :=
    ⟨horder, hanti, fun i d hd₀ hdq => ne_of_gt (hpositive i d hd₀ hdq)⟩
  obtain ⟨j, hj⟩ := primitive_factor_occurs_in_fan hs E hanti hprimitive hcover
    a ha p hp (hdirs p hp) hparallel
  let e := fun i => E (i + j)
  have hfirst : e 0 = a := by simpa only [e, zero_add] using hj
  have hprimitive' : ∀ i, Int.gcd (e i).1 (e i).2 = 1 := fun i => hprimitive (i + j)
  have hsource' : ∀ i, ∃ g ∈ hs, determinant (e i) g = 0 := fun i => hsource (i + j)
  have hcover' : ∀ g ∈ hs, ∃ i, determinant (e i) g = 0 := by
    intro g hg
    obtain ⟨i, hi⟩ := hcover g hg
    refine ⟨i - j, ?_⟩
    simpa only [e, sub_add_cancel] using hi
  exact ⟨q, hq, hqeq, e, hfirst, hfan.rotation j, hprimitive', hsource', hcover', ⟨P.rotation j⟩⟩

end KumarNivat
