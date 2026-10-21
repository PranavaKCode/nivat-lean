module

public import KumarNivat.DilationInterpolation
public import KumarNivat.IntegerAnnihilator

@[expose] public section

namespace KumarNivat

-- translating a selected nonzero coefficient to zero makes interpolation applicable.
theorem exists_integer_difference_product (c : Site → ℤ) (hc : (Set.range c).Finite)
    (f : Laurent ℤ) (hf : f ≠ 0) (hann : laurentAct f c = 0) :
    ∃ hs : List Site, (∀ h ∈ hs, h ≠ 0) ∧
      laurentAct ((hs.map (fun h => (binomial h : Laurent ℤ))).prod) c = 0 := by
  classical
  have hsupport : f.coeff.support.Nonempty := Finsupp.support_nonempty_iff.mpr
    (fun hz => hf (AddMonoidAlgebra.coeff_injective hz))
  obtain ⟨u, hu⟩ := hsupport
  let F := AddMonoidAlgebra.single (-u) (1 : ℤ) * f
  have hcenter : F.coeff 0 ≠ 0 := by
    simpa [F, AddMonoidAlgebra.coeff_single_mul_apply] using Finsupp.mem_support_iff.mp hu
  have hF : laurentAct F c = 0 := by
    rw [laurentAct_mul, hann, laurentAct_config_zero]
  obtain ⟨r, hr, hprod⟩ := centered_integer_product_annihilator F c hcenter hc hF
  let hs := F.coeff.support.erase 0 |>.toList.map (fun v => r • v)
  refine ⟨hs, ?_, ?_⟩
  · intro v hv
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
    have hwne : w ≠ 0 := (Finset.mem_erase.mp (Finset.mem_toList.mp hw)).1
    exact smul_ne_zero (Nat.ne_of_gt hr) hwne
  · simpa only [hs, List.map_map, Finset.prod_map_toList, Function.comp_apply] using hprod

-- for a nonzero array the difference product cannot be empty.
theorem exists_nonempty_integer_difference_product (c : Site → ℤ)
    (hc : (Set.range c).Finite) (hcne : c ≠ 0)
    (f : Laurent ℤ) (hf : f ≠ 0) (hann : laurentAct f c = 0) :
    ∃ hs : List Site, hs ≠ [] ∧ (∀ h ∈ hs, h ≠ 0) ∧
      laurentAct ((hs.map (fun h => (binomial h : Laurent ℤ))).prod) c = 0 := by
  obtain ⟨hs, hdirs, hprod⟩ := exists_integer_difference_product c hc f hf hann
  refine ⟨hs, ?_, hdirs, hprod⟩
  intro hnil
  rw [hnil, List.map_nil, List.prod_nil, laurentAct_one] at hprod
  exact hcne hprod

-- coefficient casting preserves the actual product operator and its annihilation identity.
theorem map_integer_difference_product {K : Type*} [CommRing K] (hs : List Site) :
    AddMonoidAlgebra.mapRingHom Site (Int.castRingHom K)
      ((hs.map (fun h => (binomial h : Laurent ℤ))).prod) =
        (hs.map (fun h => (binomial h : Laurent K))).prod := by
  rw [map_list_prod, List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro h hh
  simp [binomial]

-- coefficient casting preserves the actual product operator and its annihilation identity.
theorem cast_integer_difference_product {K : Type*} [CommRing K]
    (c : Site → ℤ) (hs : List Site)
    (hann : laurentAct ((hs.map (fun h => (binomial h : Laurent ℤ))).prod) c = 0) :
    laurentAct ((hs.map (fun h => (binomial h : Laurent K))).prod)
      (fun g => (c g : K)) = 0 := by
  let cast : ℤ →+* K := Int.castRingHom K
  have he := laurentAct_mapRing cast ((hs.map (fun h => (binomial h : Laurent ℤ))).prod) c
  rw [hann] at he
  rw [map_integer_difference_product] at he
  exact he.trans (by funext g; exact map_zero cast)

-- an injective characteristic-zero cast also reflects the integer annihilation identity.
theorem integer_difference_product_of_cast_zero {K : Type*} [CommRing K] [CharZero K]
    (c : Site → ℤ) (hs : List Site)
    (hann : laurentAct ((hs.map (fun h => (binomial h : Laurent K))).prod)
      (fun g => (c g : K)) = 0) :
    laurentAct ((hs.map (fun h => (binomial h : Laurent ℤ))).prod) c = 0 := by
  have he := laurentAct_mapRing (Int.castRingHom K)
    ((hs.map (fun h => (binomial h : Laurent ℤ))).prod) c
  rw [map_integer_difference_product] at he
  change laurentAct ((hs.map (fun h => (binomial h : Laurent K))).prod)
    (fun g => (c g : K)) = fun g =>
      ((laurentAct ((hs.map (fun h => (binomial h : Laurent ℤ))).prod) c g : ℤ) : K) at he
  rw [hann] at he
  funext g
  exact Int.cast_eq_zero.mp (congrFun he g).symm

-- the initial low-complexity annihilator now supplies a genuine nonempty product of differences.
theorem low_complexity_integer_difference_product (c : Site → ℤ)
    (hc : (Set.range c).Finite) (hcne : c ≠ 0) (D : Finset Site)
    (hlow : complexity c D ≤ D.card) :
    ∃ hs : List Site, hs ≠ [] ∧ (∀ h ∈ hs, h ≠ 0) ∧
      laurentAct ((hs.map (fun h => (binomial h : Laurent ℤ))).prod) c = 0 := by
  obtain ⟨F, hF, hann⟩ := exists_integer_annihilator c hc D hlow
  apply exists_nonempty_integer_difference_product c hc hcne (AddMonoidAlgebra.ofCoeff F)
  · intro hz
    exact hF (congrArg AddMonoidAlgebra.coeff hz)
  · exact funext hann

end KumarNivat
