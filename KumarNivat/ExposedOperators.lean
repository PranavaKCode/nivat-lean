module

public import KumarNivat.AffineLineOperators
public import KumarNivat.HalfplaneRecurrence

@[expose] public section

namespace KumarNivat

-- retain exactly the coefficients on one exposed integer normal level.
noncomputable def exposedOperator {K : Type*} [CommRing K]
    (f : Laurent K) (ν : Site →+ ℤ) (m : ℤ) : Laurent K :=
  AddMonoidAlgebra.ofCoeff (f.coeff.filter (fun u => ν u = m))

-- filtering preserves the original coefficient at that level and removes every other one.
@[simp] theorem exposedOperator_coeff {K : Type*} [CommRing K]
    (f : Laurent K) (ν : Site →+ ℤ) (m : ℤ) (u : Site) :
    (exposedOperator f ν m).coeff u = if ν u = m then f.coeff u else 0 := by
  rfl

-- the exposed support is the actual filtered support, including possible zero interior coefficients.
theorem exposedOperator_support {K : Type*} [CommRing K]
    (f : Laurent K) (ν : Site →+ ℤ) (m : ℤ) :
    (exposedOperator f ν m).coeff.support = f.coeff.support.filter (fun u => ν u = m) := by
  classical
  simp only [exposedOperator, AddMonoidAlgebra.coeff_ofCoeff, Finsupp.support_filter]

-- an attained supporting level contains a nonzero coefficient of the exposed operator.
theorem exposedOperator_ne_zero_of_support {K : Type*} [CommRing K]
    (f : Laurent K) (ν : Site →+ ℤ) (m : ℤ) (E : Site)
    (hE : E ∈ f.coeff.support) (hlevel : ν E = m) : exposedOperator f ν m ≠ 0 := by
  intro hz
  have he := congrArg (fun q : Laurent K => q.coeff E) hz
  simp only [exposedOperator_coeff, hlevel, ite_true, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at he
  exact Finsupp.mem_support_iff.mp hE he

-- deleting the face cannot introduce a coefficient outside the original stencil.
theorem exposed_remainder_support_subset {K : Type*} [CommRing K]
    (f : Laurent K) (ν : Site →+ ℤ) (m : ℤ) :
    (f - exposedOperator f ν m).coeff.support ⊆ f.coeff.support := by
  classical
  intro u hu
  by_contra hn
  have hf : f.coeff u = 0 := Finsupp.notMem_support_iff.mp hn
  have hz : (f - exposedOperator f ν m).coeff u = 0 := by
    simp only [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, exposedOperator_coeff, hf]
    split <;> simp
  exact Finsupp.mem_support_iff.mp hu hz

-- each nonface input lies at least one integer level strictly inward of the exposed face.
theorem exposed_remainder_strict_level {K : Type*} [CommRing K]
    (f : Laurent K) (ν : Site →+ ℤ) (m : ℤ)
    (hmin : ∀ u ∈ f.coeff.support, m ≤ ν u) :
    ∀ u ∈ (f - exposedOperator f ν m).coeff.support, m + 1 ≤ ν u := by
  intro u hu
  have hbound := hmin u (exposed_remainder_support_subset f ν m hu)
  have hne : ν u ≠ m := by
    intro he
    have hz : (f - exposedOperator f ν m).coeff u = 0 := by
      simp only [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, exposedOperator_coeff,
        he, ite_true, sub_self]
    exact Finsupp.mem_support_iff.mp hu hz
  omega

-- an actual supporting face supplies its primitive line block and the strictly inward remainder.
theorem exposed_line_decomposition_of_supporting_level {K : Type*} [CommRing K]
    (f : Laurent K) (ν : Site →+ ℤ) (hν : ν ≠ 0) (m : ℤ)
    (hmin : ∀ u ∈ f.coeff.support, m ≤ ν u) (E p : Site) (hp : p ≠ 0)
    (hprimitive : Int.gcd p.1 p.2 = 1) (htangent : ν p = 0)
    (hE : E ∈ f.coeff.support) (hlevel : ν E = m) :
    ∃ q₀ : Site, ∃ t : ℕ, ∃ α : Fin (t + 1) → K,
      α 0 ≠ 0 ∧ α (Fin.last t) ≠ 0 ∧ ν q₀ = m ∧
        f = lineOperator q₀ p t α + (f - exposedOperator f ν m) ∧
        ∀ u ∈ (f - exposedOperator f ν m).coeff.support, m + 1 ≤ ν u := by
  classical
  obtain ⟨τ, _hτ, hker⟩ := primitive_direction_coordinate p hprimitive
  have hface := exposedOperator_ne_zero_of_support f ν m E hE hlevel
  have hline : ((exposedOperator f ν m).coeff.support : Set Site) ⊆
      Set.range (fun n : ℤ => E + n • p) := by
    intro u hu
    rw [exposedOperator_support] at hu
    have huf := Finset.mem_filter.mp hu
    have hflat : ν (u - E) = 0 := by rw [map_sub, huf.2, hlevel, sub_self]
    have hdet := nonzero_normal_kernel_parallel ν hν p (u - E) htangent hflat
    have he := hker (u - E) hdet
    refine ⟨τ (u - E), ?_⟩
    simpa only [add_sub_cancel] using congrArg (fun v => E + v) he.symm
  obtain ⟨j, t, α, hfirst, hlast, hblock⟩ := exists_affine_support_line_block
    (exposedOperator f ν m) hface E p hp hline
  have hq₀ : ν (E + j • p) = m := by
    rw [map_add, map_zsmul, htangent, smul_zero, add_zero, hlevel]
  refine ⟨E + j • p, t, α, hfirst, hlast, hq₀, ?_, exposed_remainder_strict_level f ν m hmin⟩
  rw [← hblock]
  abel

end KumarNivat
