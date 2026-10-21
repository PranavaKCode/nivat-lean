module

public import KumarNivat.LaurentMaps

@[expose] public section

namespace KumarNivat

-- natural dilation preserves lattice addition and leaves coefficients alone.
def scaleLattice (n : ℕ) : Site →+ Site where
  toFun u := n • u
  map_zero' := nsmul_zero n
  map_add' u v := nsmul_add u v n

-- the exponent dilation extends to a laurent ring homomorphism.
noncomputable def dilate {K : Type*} [CommRing K] (n : ℕ) : Laurent K →+* Laurent K :=
  AddMonoidAlgebra.mapDomainRingHom K (scaleLattice n)

-- one exponent is sent to its dilated lattice site.
@[simp] theorem dilate_single {K : Type*} [CommRing K] (n : ℕ) (u : Site) (a : K) :
    dilate n (AddMonoidAlgebra.single u a) = AddMonoidAlgebra.single (n • u) a := by
  simp [dilate, scaleLattice]

-- exponent dilation by one fixes every operator.
@[simp] theorem dilate_one {K : Type*} [CommRing K] (f : Laurent K) : dilate 1 f = f := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f h hf hh => simp only [map_add, hf, hh]
  | single u a => simp

-- composing exponent dilations multiplies their positive parameters.
theorem dilate_comp {K : Type*} [CommRing K] (m n : ℕ) (f : Laurent K) :
    dilate m (dilate n f) = dilate (m * n) f := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f h hf hh => simp only [map_add, hf, hh]
  | single u a => simp only [dilate_single, smul_smul]

-- reducing coefficients and dilating exponents are independent operations.
theorem dilate_mapRing {K L : Type*} [CommRing K] [CommRing L]
    (ρ : K →+* L) (n : ℕ) (f : Laurent K) :
    dilate n (AddMonoidAlgebra.mapRingHom Site ρ f) =
      AddMonoidAlgebra.mapRingHom Site ρ (dilate n f) := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f h hf hh => simp only [map_add, hf, hh]
  | single u a => simp

-- all dilated outputs use the same finite set of coefficient-weighted value tuples.
theorem finite_range_dilated_outputs {K : Type*} [CommRing K]
    (f : Laurent K) (c : Site → K) (hc : (Set.range c).Finite) :
    (Set.range (fun z : ℕ × Site => laurentAct (dilate z.1 f) c z.2)).Finite := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f h hf hh =>
    apply ((hf.prod hh).image (fun v : K × K => v.1 + v.2)).subset
    rintro y ⟨z, rfl⟩
    refine ⟨(laurentAct (dilate z.1 f) c z.2, laurentAct (dilate z.1 h) c z.2),
      ⟨⟨z, rfl⟩, ⟨z, rfl⟩⟩, ?_⟩
    simp only [map_add, laurentAct_add, Pi.add_apply]
  | single u a =>
    apply (hc.image (fun x : K => a * x)).subset
    rintro y ⟨z, rfl⟩
    refine ⟨c (z.2 + z.1 • u), ⟨_, rfl⟩, ?_⟩
    simp only [dilate_single, laurentAct_single]

-- finite integer outputs have one absolute-value bound across every dilation and site.
theorem exists_dilated_output_bound (f : Laurent ℤ) (c : Site → ℤ)
    (hc : (Set.range c).Finite) :
    ∃ B : ℕ, ∀ n : ℕ, ∀ g : Site, (laurentAct (dilate n f) c g).natAbs ≤ B := by
  classical
  let S := (finite_range_dilated_outputs f c hc).toFinset
  refine ⟨S.sup Int.natAbs, ?_⟩
  intro n g
  apply Finset.le_sup (f := Int.natAbs)
  exact (finite_range_dilated_outputs f c hc).mem_toFinset.mpr ⟨(n, g), rfl⟩

end KumarNivat
