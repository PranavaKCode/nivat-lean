module

public import KumarNivat.PairedStructureLocality
public import KumarNivat.PairedStructureRows
public import KumarNivat.RowFrames

@[expose] public section

namespace KumarNivat

-- equal binomial outputs make the difference of the two arrays periodic along that factor.
theorem periodic_difference_of_equal_binomial_output {K : Type*} [CommRing K]
    (x y : Site → K) (p : Site) (he : difference p x = difference p y) :
    IsPeriod (x - y) p := by
  intro g
  have h := congrFun he g
  change x (g + p) - x g = y (g + p) - y g at h
  exact sub_eq_sub_iff_sub_eq_sub.mp h

-- translation commutes with the same binomial output on every fiber member.
theorem difference_shift_configuration {K : Type*} [CommRing K]
    (x : Site → K) (p h : Site) : difference p (shift h x) = shift h (difference p x) := by
  rw [← laurentAct_binomial, laurentAct_shift, laurentAct_binomial]

-- one complete period on each row determines an entire finite-width band of a periodic difference.
theorem full_band_agreement_of_equal_binomial_output {K : Type*} [CommRing K]
    (x y : Site → K) (a v : Site) (hav : determinant a v = 1)
    (L : ℕ) (hL : 0 < L) (d : ℕ)
    (he : difference ((L : ℤ) • a) x = difference ((L : ℤ) • a) y)
    (hframe : ∀ u ∈ rowFrame 0 a v L d, x u = y u) :
    ∀ g : Site, 0 ≤ directionNormal a g → directionNormal a g ≤ (d : ℤ) → x g = y g := by
  have hp := periodic_difference_of_equal_binomial_output x y ((L : ℤ) • a) he
  intro g hg₀ hgd
  let m : ℤ := determinant g v
  let n : ℤ := directionNormal a g
  have hrep : g = m • a + n • v := by
    change g = determinant g v • a + determinant a g • v
    simpa only [hav, one_smul] using determinant_smul_identity a v g
  have hn₀ : 0 ≤ n := hg₀
  have hnd : n ≤ (d : ℤ) := hgd
  let j : Fin (d + 1) := ⟨n.toNat, by omega⟩
  have hj : (j.val : ℤ) = n := by dsimp [j]; omega
  let i := periodicRowIndex L hL m
  have hvalue := periodic_row_value (x - y) a v L hL hp m n
  have hsite : n • v + (i.val : ℤ) • a = 0 + (i.val : ℤ) • a + (j.val : ℤ) • v := by
    rw [hj, zero_add]
    abel
  have hz : periodicRowWord (x - y) a v L n i = 0 := by
    change x (n • v + (i.val : ℤ) • a) - y (n • v + (i.val : ℤ) • a) = 0
    rw [hsite]
    exact sub_eq_zero.mpr (hframe _ (rowFrame_mem 0 a v L d i j))
  apply sub_eq_zero.mp
  change (x - y) g = 0
  rw [hrep, hvalue]
  exact hz

-- one finite patch determines the opposite half-plane inside every common binomial fiber.
theorem exists_binomial_fiber_halfplane_patch {K : Type*} [CommRing K]
    [TopologicalSpace K] [DiscreteTopology K] (c : Site → K) (hc : (Set.range c).Finite)
    (a v : Site) (hav : determinant a v = 1) (L : ℕ) (hL : 0 < L)
    (hnoNE : ¬ OneSidedNonexpansive c (integerNormalAsReal (directionNormal a))) :
    ∃ d : ℕ, ∀ x ∈ orbitClosure c, ∀ y ∈ orbitClosure c,
      difference ((L : ℤ) • a) x = difference ((L : ℤ) • a) y →
      (∀ u ∈ rowFrame 0 a v L d, x u = y u) →
      ∀ g : Site, directionNormal a g ≤ (d : ℤ) → x g = y g := by
  classical
  let ν := directionNormal a
  have hell : integerNormalAsReal ν ≠ 0 := by
    intro hz
    have he := congrArg (fun ell : Site →+ ℝ => ell v) hz
    change (determinant a v : ℝ) = 0 at he
    rw [hav] at he
    norm_num at he
  obtain ⟨D, hD, hlocal⟩ := finite_halfplane_determines_site_of_not_nonexpansive
    c hc (integerNormalAsReal ν) hell hnoNE (-v)
  let d : ℕ := ∑ u ∈ D, (ν u).natAbs
  have hlow (u : Site) (hu : u ∈ D) : 0 ≤ ν u := by
    have h := hD u hu
    change (0 : ℝ) ≤ (ν u : ℝ) at h
    exact_mod_cast h
  have hupp (u : Site) (hu : u ∈ D) : ν u ≤ (d : ℤ) := by
    apply (le_abs_self (ν u)).trans
    rw [← Int.natCast_natAbs]
    exact_mod_cast (Finset.single_le_sum (fun q _ => Nat.zero_le (ν q).natAbs) hu)
  refine ⟨d, ?_⟩
  intro x hx y hy houtput hframe
  have hseed := full_band_agreement_of_equal_binomial_output x y a v hav L hL d houtput hframe
  have hband (n : ℕ) : ∀ g : Site, -(n : ℤ) ≤ ν g → ν g ≤ (d : ℤ) → x g = y g := by
    induction n with
    | zero => simpa only [Nat.cast_zero, neg_zero] using hseed
    | succ n ih =>
      intro g hg hgd
      by_cases hinside : -(n : ℤ) ≤ ν g
      · exact ih g hinside hgd
      · have he := hlocal (shift (g + v) x) (orbitClosure_shift_mem c x hx (g + v))
          (shift (g + v) y) (orbitClosure_shift_mem c y hy (g + v)) (by
            intro u hu
            change x (u + (g + v)) = y (u + (g + v))
            apply ih
            · have hn : ν (u + (g + v)) = ν u + ν g + 1 := by
                rw [map_add, map_add]
                change ν u + (ν g + determinant a v) = ν u + ν g + 1
                rw [hav]
                ring
              rw [hn]
              have hl := hlow u hu
              omega
            · have hn : ν (u + (g + v)) = ν u + ν g + 1 := by
                rw [map_add, map_add]
                change ν u + (ν g + determinant a v) = ν u + ν g + 1
                rw [hav]
                ring
              rw [hn]
              have hu' := hupp u hu
              omega)
        have hsite : -v + (g + v) = g := by abel
        simpa only [shift, hsite] using he
  intro g hg
  exact hband (-ν g).toNat g (by omega) hg

end KumarNivat
