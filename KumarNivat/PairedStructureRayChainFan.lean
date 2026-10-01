import KumarNivat.NewtonCyclicFactorFan
import KumarNivat.AnchoredCyclicRotation
import KumarNivat.PrimitiveDirections

namespace KumarNivat

-- primitive parallel lattice directions differ only by their orientation.
theorem primitive_parallel_eq_or_neg (a b : Site)
    (ha : Int.gcd a.1 a.2 = 1) (hb : Int.gcd b.1 b.2 = 1)
    (hparallel : determinant a b = 0) : b = a ∨ b = -a := by
  obtain ⟨τ, hτ, hline⟩ := primitive_direction_coordinate a ha
  obtain ⟨σ, hσ, _hlineb⟩ := primitive_direction_coordinate b hb
  have hbline := hline b hparallel
  have hunit : τ b * σ a = 1 := by
    have h := congrArg σ hbline
    rw [hσ, map_zsmul, smul_eq_mul] at h
    exact h.symm
  rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hunit with h | h
  · left
    simpa only [h.1, one_smul] using hbline
  · right
    simpa only [h.1, neg_one_smul] using hbline

-- actual factor provenance selects the prescribed primitive orientation in the doubled fan.
theorem primitive_factor_occurs_in_fan {q : ℕ} [NeZero (2 * q)]
    (hs : List Site) (e : ZMod (2 * q) → Site)
    (hopposite : ∀ i, e (i + (q : ZMod (2 * q))) = -e i)
    (hprimitive : ∀ i, Int.gcd (e i).1 (e i).2 = 1)
    (hcover : ∀ g ∈ hs, ∃ i, determinant (e i) g = 0)
    (a : Site) (ha : Int.gcd a.1 a.2 = 1)
    (p : Site) (hp : p ∈ hs) (hpne : p ≠ 0) (hparallel : determinant a p = 0) :
    ∃ i, e i = a := by
  obtain ⟨τ, _hτ, hline⟩ := primitive_direction_coordinate a ha
  have hpline := hline p hparallel
  have hm : τ p ≠ 0 := by
    intro hm
    exact hpne (by rw [hpline, hm, zero_smul])
  obtain ⟨i, hi⟩ := hcover p hp
  have hia : determinant (e i) a = 0 := by
    change directionNormal (e i) p = 0 at hi
    rw [hpline, map_zsmul, smul_eq_mul] at hi
    exact (mul_eq_zero.mp hi).resolve_left hm
  rcases primitive_parallel_eq_or_neg a (e i) ha (hprimitive i)
    (by simp only [determinant] at hia ⊢; nlinarith) with he | he
  · exact ⟨i, he⟩
  · refine ⟨i + (q : ZMod (2 * q)), ?_⟩
    rw [hopposite, he, neg_neg]

-- a positive turn from the prescribed first ray lies strictly inside the actual first half of the fan.
theorem positive_factor_fan_index {q : ℕ} [NeZero (2 * q)]
    (e : ZMod (2 * q) → Site) (hfan : AnchoredChainFanOrder e)
    (i : ZMod (2 * q)) (hpos : 0 < determinant (e 0) (e i)) :
    0 < i.val ∧ i.val < q := by
  have hi := ZMod.val_lt i
  have he : e i = e ((i.val : ℕ) : ZMod (2 * q)) := by rw [ZMod.natCast_zmod_val]
  have h₀ : i.val ≠ 0 := by
    intro hz
    rw [he, hz, Nat.cast_zero] at hpos
    simp [determinant, mul_comm] at hpos
  by_contra hnot
  have hiq : q ≤ i.val := by omega
  have hindex : (i.val : ZMod (2 * q)) =
      ((i.val - q : ℕ) : ZMod (2 * q)) + (q : ZMod (2 * q)) := by
    rw [← Nat.cast_add, Nat.sub_add_cancel hiq]
  rw [he, hindex, hfan.opposite] at hpos
  by_cases hiqeq : i.val = q
  · rw [hiqeq, Nat.sub_self, Nat.cast_zero] at hpos
    simp [determinant, mul_comm] at hpos
  · have hturn := anchored_chain_half_turn_positive e hfan 0 (i.val - q) (by omega) (by omega)
    simp only [zero_add] at hturn
    have hneg : determinant (e 0) (-e ((i.val - q : ℕ) : ZMod (2 * q))) =
        -determinant (e 0) (e ((i.val - q : ℕ) : ZMod (2 * q))) := by simp [determinant]; ring
    rw [hneg] at hpos
    omega

-- sorting the original factors and rotating at the actual initial ray constructs the complete finite forward fan.
theorem actual_forward_factor_fan (hs : List Site) (hlen : 2 ≤ hs.length)
    (hdirs : ∀ p ∈ hs, p ≠ 0) (hpairs : hs.Pairwise (fun p q => determinant p q ≠ 0))
    (a b : Site) (ha : Int.gcd a.1 a.2 = 1) (hb : Int.gcd b.1 b.2 = 1)
    (hdet : 0 < determinant a b)
    (pa pb : Site) (hpa : pa ∈ hs) (hpb : pb ∈ hs)
    (haparallel : determinant a pa = 0) (hbparallel : determinant b pb = 0) :
    ∃ q : ℕ, ∃ hq : 2 ≤ q,
      let _ : NeZero q := ⟨by omega⟩
      q = hs.length ∧ ∃ e : ZMod (2 * q) → Site, ∃ j : ℕ,
        AnchoredChainFanOrder e ∧ e 0 = a ∧ 0 < j ∧ j < q ∧ e (j : ZMod (2 * q)) = b ∧
        (∀ i, Int.gcd (e i).1 (e i).2 = 1) ∧
        (∀ i, ∃ g ∈ hs, determinant (e i) g = 0) ∧
        (∀ g ∈ hs, ∃ i, determinant (e i) g = 0) := by
  classical
  obtain ⟨q, hq, hqeq, E, horder, hopposite, hpositive, hprimitive, hsource, hcover,
    _f, _k, _hlist, _hlengths⟩ := actual_primitive_factor_cyclic_fan hs hlen hdirs hpairs
  let _ : NeZero q := ⟨by omega⟩
  obtain ⟨i, hi⟩ := primitive_factor_occurs_in_fan hs E hopposite hprimitive hcover
    a ha pa hpa (hdirs pa hpa) haparallel
  let e : ZMod (2 * q) → Site := fun t => E (t + i)
  have hfanE : AnchoredChainFanOrder E :=
    ⟨horder, hopposite, fun t d hd₀ hdq => ne_of_gt (hpositive t d hd₀ hdq)⟩
  have hfan : AnchoredChainFanOrder e := hfanE.rotation i
  have he₀ : e 0 = a := by simpa only [e, zero_add] using hi
  have hprimitive' : ∀ t, Int.gcd (e t).1 (e t).2 = 1 := fun t => hprimitive (t + i)
  have hsource' : ∀ t, ∃ g ∈ hs, determinant (e t) g = 0 := fun t => hsource (t + i)
  have hcover' : ∀ g ∈ hs, ∃ t, determinant (e t) g = 0 := by
    intro g hg
    obtain ⟨t, ht⟩ := hcover g hg
    refine ⟨t - i, ?_⟩
    simpa only [e, sub_add_cancel] using ht
  obtain ⟨t, ht⟩ := primitive_factor_occurs_in_fan hs e hfan.opposite hprimitive' hcover'
    b hb pb hpb (hdirs pb hpb) hbparallel
  have hj := positive_factor_fan_index e hfan t (by rwa [he₀, ht])
  refine ⟨q, hq, hqeq, e, t.val, hfan, he₀, hj.1, hj.2, ?_, hprimitive', hsource', hcover'⟩
  simpa only [ZMod.natCast_zmod_val] using ht

end KumarNivat
