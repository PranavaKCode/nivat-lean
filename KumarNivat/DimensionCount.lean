import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Lean.Elab.Tactic.Omega

namespace KumarNivat

-- section 4 combines affine rank-nullity with observable independence modulo affine functions.
theorem dimension_count {K P I J M : Type*} [Field K]
    [Fintype P] [Fintype I] [Fintype J] [AddCommGroup M] [Module K M]
    (F : (I → K) →ₗ[K] (P → K)) (H : (J → K) →ₗ[K] (P → K))
    (Q : (P → K) →ₗ[K] M) (hkill : Q.comp F = 0)
    (hobs : Function.Injective (Q.comp H))
    (hrelations : Module.finrank K (LinearMap.ker F) ≤ Fintype.card J) :
    Fintype.card I ≤ Fintype.card P := by
  classical
  have hQr (x : LinearMap.range F) : Q (x : P → K) = 0 := by
    obtain ⟨v, hv⟩ := x.property
    rw [← hv]
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using
      LinearMap.congr_fun hkill v
  let L : (LinearMap.range F × (J → K)) →ₗ[K] (P → K) :=
    (LinearMap.range F).subtype.comp (LinearMap.fst K (LinearMap.range F) (J → K)) +
      H.comp (LinearMap.snd K (LinearMap.range F) (J → K))
  have hL : Function.Injective L := by
    intro x y hxy
    have he : Q (H x.2) = Q (H y.2) := by
      have hq := congrArg Q hxy
      simpa only [L, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.fst_apply,
        LinearMap.snd_apply, Submodule.subtype_apply, map_add, hQr, zero_add] using hq
    have hsecond : x.2 = y.2 := hobs he
    apply Prod.ext _ hsecond
    apply Subtype.ext
    have hfirst : (x.1 : P → K) + H x.2 = (y.1 : P → K) + H y.2 := hxy
    rw [hsecond] at hfirst
    exact add_right_cancel hfirst
  have hdim := LinearMap.finrank_le_finrank_of_injective hL
  have hrank := F.finrank_range_add_finrank_ker
  have hdim' : Module.finrank K (LinearMap.range F) + Fintype.card J ≤ Fintype.card P := by
    simpa [Module.finrank_prod] using hdim
  have hrank' : Module.finrank K (LinearMap.range F) + Module.finrank K (LinearMap.ker F) =
      Fintype.card I := by simpa using hrank
  omega

end KumarNivat
