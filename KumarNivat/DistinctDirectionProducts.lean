module

public import KumarNivat.ParallelDifferences
public import Mathlib.Data.List.Pairwise

@[expose] public section

namespace KumarNivat

-- use one shared operator for a finite list of directional differences.
noncomputable def differenceProduct {K : Type*} [CommRing K] (hs : List Site) : Laurent K :=
  (hs.map (fun h => binomial h)).prod

-- the empty list is the identity operator.
@[simp] theorem differenceProduct_nil {K : Type*} [CommRing K] :
    differenceProduct (K := K) [] = 1 := rfl

-- adjoining a direction multiplies its difference binomial into the operator.
@[simp] theorem differenceProduct_cons {K : Type*} [CommRing K] (p : Site) (hs : List Site) :
    differenceProduct (K := K) (p :: hs) = binomial p * differenceProduct hs := rfl

-- list concatenation corresponds to multiplication of the two product operators.
theorem differenceProduct_append {K : Type*} [CommRing K] (xs ys : List Site) :
    differenceProduct (K := K) (xs ++ ys) = differenceProduct xs * differenceProduct ys := by
  simp [differenceProduct, List.prod_append]

-- a zero directional difference is equivalent to a genuine global period.
theorem binomial_annihilates_iff_period {K : Type*} [CommRing K] (c : Site → K) (v : Site) :
    laurentAct (binomial v) c = 0 ↔ IsPeriod c v := by
  rw [laurentAct_binomial]
  constructor
  · intro he g
    exact sub_eq_zero.mp (congrFun he g)
  · intro hp
    funext g
    exact sub_eq_zero.mpr (hp g)

-- merging parallel factors preserves annihilation and leaves one factor per lattice direction.
theorem normalize_difference_directions {K : Type*} [Field K] [CharZero K]
    (hs : List Site) (hdirs : ∀ h ∈ hs, h ≠ 0) (c : Site → K)
    (hc : (Set.range c).Finite) (hann : laurentAct (differenceProduct hs) c = 0) :
    ∃ ts : List Site, ts.Pairwise (fun p q => determinant p q ≠ 0) ∧
      (∀ h ∈ ts, h ≠ 0) ∧ laurentAct (differenceProduct ts) c = 0 := by
  classical
  induction hs generalizing c with
  | nil => exact ⟨[], by simp, by simp, hann⟩
  | cons p xs ih =>
    have hp : p ≠ 0 := hdirs p List.mem_cons_self
    let d := difference p c
    have hd : (Set.range d).Finite := finite_range_difference c hc p
    have hdann : laurentAct (differenceProduct xs) d = 0 := by
      dsimp only [d]
      rw [← laurentAct_binomial, ← laurentAct_mul, mul_comm]
      exact hann
    obtain ⟨ts, hpairs, hnonzero, htsann⟩ := ih
      (fun h hh => hdirs h (List.mem_cons_of_mem p hh)) d hd hdann
    have hprod : laurentAct (binomial p * differenceProduct ts) c = 0 := by
      rw [mul_comm, laurentAct_mul, laurentAct_binomial]
      exact htsann
    by_cases hall : ∀ q ∈ ts, determinant p q ≠ 0
    · refine ⟨p :: ts, List.pairwise_cons.mpr ⟨hall, hpairs⟩, ?_, hprod⟩
      intro h hh
      rcases List.mem_cons.mp hh with rfl | hh
      · exact hp
      · exact hnonzero h hh
    · obtain ⟨q, hqmem, hparallel⟩ : ∃ q ∈ ts, determinant p q = 0 := by
        simpa only [not_forall, not_imp, Classical.not_not, exists_prop] using hall
      have hq : q ≠ 0 := hnonzero q hqmem
      obtain ⟨as, bs, hsplit⟩ := List.mem_iff_append.mp hqmem
      let rest := as ++ bs
      let R : Laurent K := differenceProduct rest
      have hsplitprod : differenceProduct (K := K) ts = binomial q * R := by
        rw [hsplit, differenceProduct_append, differenceProduct_cons]
        dsimp [R, rest]
        rw [differenceProduct_append]
        ring
      have hpairann : laurentAct (binomial p * binomial q) (laurentAct R c) = 0 := by
        rw [← laurentAct_mul]
        rw [hsplitprod] at hprod
        simpa only [mul_assoc] using hprod
      have hRfinite : (Set.range (laurentAct R c)).Finite := finite_range_act c hc R.coeff
      obtain ⟨h, b, hb, hrep, hne, hperiod⟩ := collapse_parallel_differences
        (laurentAct R c) hRfinite p q hp hq hparallel hpairann
      have hpairparts := List.pairwise_append.mp (hsplit ▸ hpairs)
      have hqparts := List.pairwise_cons.mp hpairparts.2.1
      have hpairsrest : rest.Pairwise (fun p q => determinant p q ≠ 0) := by
        apply List.pairwise_append.mpr
        refine ⟨hpairparts.1, hqparts.2, ?_⟩
        intro x hx y hy
        exact hpairparts.2.2 x hx y (List.mem_cons_of_mem q hy)
      have hqind (x : Site) (hx : x ∈ rest) : determinant q x ≠ 0 := by
        rcases List.mem_append.mp hx with hx | hx
        · have he := hpairparts.2.2 x hx q List.mem_cons_self
          have hswap : determinant q x = -determinant x q := by simp [determinant]; ring
          rw [hswap]
          exact neg_ne_zero.mpr he
        · exact hqparts.1 x hx
      have hind (x : Site) (hx : x ∈ rest) : determinant h x ≠ 0 := by
        rw [hrep]
        have he := determinant_zsmul q x b 1
        simp only [one_smul, mul_one] at he
        rw [he]
        exact mul_ne_zero hb (hqind x hx)
      refine ⟨h :: rest, List.pairwise_cons.mpr ⟨hind, hpairsrest⟩, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hne
        · apply hnonzero x
          rw [hsplit]
          rcases List.mem_append.mp hx with hx | hx
          · exact List.mem_append_left _ hx
          · exact List.mem_append_right _ (List.mem_cons_of_mem q hx)
      · rw [differenceProduct_cons, laurentAct_mul]
        exact (binomial_annihilates_iff_period (laurentAct R c) h).mpr hperiod

end KumarNivat
