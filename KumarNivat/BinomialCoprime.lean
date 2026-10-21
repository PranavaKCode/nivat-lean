module

public import KumarNivat.SupportExtrema
public import KumarNivat.TangentNormals
public import KumarNivat.EulerOperators

@[expose] public section

namespace KumarNivat

-- the determinant with a fixed direction is its integer tangent normal.
def directionNormal (p : Site) : Site →+ ℤ where
  toFun g := determinant p g
  map_zero' := by simp [determinant]
  map_add' g h := by simp [determinant]; ring

-- a direction lies on the kernel line of its own normal.
@[simp] theorem directionNormal_self (p : Site) : directionNormal p p = 0 := by
  simp [directionNormal, determinant]
  ring

-- a nonzero direction gives a nonzero normal.
theorem directionNormal_ne_zero (p : Site) (hp : p ≠ 0) : directionNormal p ≠ 0 := by
  intro hz
  have hx := congrArg (fun ν : Site →+ ℤ => ν (0, 1)) hz
  have hy := congrArg (fun ν : Site →+ ℤ => ν (1, 0)) hz
  have hp₁ : p.1 = 0 := by simpa [directionNormal, determinant] using hx
  have hp₂ : p.2 = 0 := by simpa [directionNormal, determinant] using hy
  exact hp (Prod.ext hp₁ hp₂)

-- a tangent normal vanishes on every exponent of its direction's difference binomial.
theorem binomial_support_normal_zero {K : Type*} [CommRing K]
    (p : Site) (ν : Site →+ ℤ) (hp : ν p = 0) :
    ∀ u ∈ (binomial p : Laurent K).coeff.support, ν u = 0 := by
  classical
  intro u hu
  by_cases hup : u = p
  · rw [hup]
    exact hp
  · by_cases hu₀ : u = 0
    · rw [hu₀, map_zero]
    · have hval := Finsupp.mem_support_iff.mp hu
      have hzero : (binomial p : Laurent K).coeff u = 0 := by
        simp [binomial, AddMonoidAlgebra.one_def, Ne.symm hup, Ne.symm hu₀]
      exact (hval hzero).elim

-- zero width of a product in one normal forces a factor's support onto one affine line.
theorem factor_support_normal_fiber {K : Type*} [Field K]
    (f g : Laurent K) (hf : f ≠ 0) (hg : g ≠ 0)
    (ν μ : Site →+ ℤ) (hinj : Function.Injective (ν.prod μ))
    (hflat : ∀ u ∈ (f * g).coeff.support, ν u = 0) :
    ∃ β : ℤ, ∀ u ∈ f.coeff.support, ν u = β := by
  have hgS : g.coeff.support.Nonempty := Finsupp.support_nonempty_iff.mpr
    (fun hz => hg (AddMonoidAlgebra.coeff_injective hz))
  obtain ⟨v, hv⟩ := hgS
  have hupper := coordinate_sum_bound f g hf hg (ν.prod μ) hinj 0
    (fun u hu => le_of_eq (hflat u hu))
  let negF := (AddEquiv.neg Site).toAddMonoidHom.comp (ν.prod μ)
  have hneg : Function.Injective negF := (AddEquiv.neg Site).injective.comp hinj
  have hlower := coordinate_sum_bound f g hf hg negF hneg 0 (by
    intro u hu
    change -ν u ≤ 0
    rw [hflat u hu]
    rfl)
  refine ⟨-ν v, ?_⟩
  intro u hu
  have h₁ := hupper u hu v hv
  have h₂ := hlower u hu v hv
  change ν (u + v) ≤ 0 at h₁
  change -ν (u + v) ≤ 0 at h₂
  rw [map_add] at h₁ h₂
  omega

-- independent difference directions have no common nonunit laurent divisor.
theorem independent_binomials_isRelPrime {K : Type*} [Field K]
    (p q : Site) (hdet : determinant p q ≠ 0) :
    IsRelPrime (binomial p : Laurent K) (binomial q) := by
  have hp : p ≠ 0 := by intro hz; apply hdet; simp [hz, determinant]
  have hq : q ≠ 0 := by intro hz; apply hdet; simp [hz, determinant]
  let ν := directionNormal p
  let μ := directionNormal q
  have hinj : Function.Injective (ν.prod μ) := independent_tangent_normals ν μ p q
    (directionNormal_ne_zero p hp) (directionNormal_ne_zero q hq) hdet
    (directionNormal_self p) (directionNormal_self q)
  have hinj' : Function.Injective (μ.prod ν) := by
    intro x y he
    apply hinj
    exact Prod.ext (congrArg Prod.snd he) (congrArg Prod.fst he)
  intro d hdp hdq
  obtain ⟨f, hf⟩ := hdp
  obtain ⟨g, hg⟩ := hdq
  have hdf : d * f ≠ 0 := by rw [← hf]; exact binomial_ne_zero p hp
  have hdg : d * g ≠ 0 := by rw [← hg]; exact binomial_ne_zero q hq
  have hd : d ≠ 0 := left_ne_zero_of_mul hdf
  obtain ⟨a, ha⟩ := factor_support_normal_fiber d f hd (right_ne_zero_of_mul hdf) ν μ hinj (by
    rw [← hf]
    exact binomial_support_normal_zero p ν (directionNormal_self p))
  obtain ⟨b, hb⟩ := factor_support_normal_fiber d g hd (right_ne_zero_of_mul hdg) μ ν hinj' (by
    rw [← hg]
    exact binomial_support_normal_zero q μ (directionNormal_self q))
  have hdS : d.coeff.support.Nonempty := Finsupp.support_nonempty_iff.mpr
    (fun hz => hd (AddMonoidAlgebra.coeff_injective hz))
  obtain ⟨u, hu⟩ := hdS
  have hsingleton : d.coeff.support ⊆ {u} := by
    intro v hv
    apply Finset.mem_singleton.mpr
    apply hinj
    exact Prod.ext ((ha v hv).trans (ha u hu).symm) ((hb v hv).trans (hb u hu).symm)
  have hsingle : d = AddMonoidAlgebra.single u (d.coeff u) := by
    apply AddMonoidAlgebra.coeff_injective
    exact Finsupp.eq_single_iff.mpr ⟨hsingleton, rfl⟩
  rw [hsingle]
  exact single_isUnit u (d.coeff u) (Finsupp.mem_support_iff.mp hu)

-- one nonzero coordinate supplies a normal value for the squarefree derivative argument.
theorem binomial_squarefree {K : Type*} [Field K] [CharZero K]
    (p : Site) (hp : p ≠ 0) : Squarefree (binomial p : Laurent K) := by
  by_cases hp₁ : p.1 = 0
  · have hp₂ : p.2 ≠ 0 := by intro hz; exact hp (Prod.ext hp₁ hz)
    exact binomial_squarefree_of_normal (AddMonoidHom.snd ℤ ℤ) p hp₂
  · exact binomial_squarefree_of_normal (AddMonoidHom.fst ℤ ℤ) p hp₁

end KumarNivat
