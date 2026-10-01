import KumarNivat.PeriodLattice

namespace KumarNivat

-- a nonzero normal tangent to one basis direction cannot vanish on the other.
theorem tangent_normal_transverse_ne_zero (ν : Site →+ ℤ) (v w : Site)
    (hν : ν ≠ 0) (hdet : determinant v w ≠ 0) (hv : ν v = 0) : ν w ≠ 0 := by
  intro hw
  apply hν
  ext h
  have he := normal_cramer_identity ν v w h
  rw [hv, hw, mul_zero, mul_zero, add_zero] at he
  exact (mul_eq_zero.mp he).resolve_left hdet

-- the two tangent half-plane normals define independent integer coordinates.
theorem independent_tangent_normals (ν₁ ν₂ : Site →+ ℤ) (v w : Site)
    (hν₁ : ν₁ ≠ 0) (hν₂ : ν₂ ≠ 0) (hdet : determinant v w ≠ 0)
    (hv : ν₁ v = 0) (hw : ν₂ w = 0) : Function.Injective (ν₁.prod ν₂) := by
  have hν₁w := tangent_normal_transverse_ne_zero ν₁ v w hν₁ hdet hv
  have hν₂v : ν₂ v ≠ 0 := by
    have hrev : determinant w v ≠ 0 := by
      have he : determinant w v = -determinant v w := by simp [determinant]; ring
      rw [he]
      exact neg_ne_zero.mpr hdet
    exact tangent_normal_transverse_ne_zero ν₂ w v hν₂ hrev hw
  intro x y he
  have he₁ : ν₁ x = ν₁ y := congrArg Prod.fst he
  have he₂ : ν₂ x = ν₂ y := congrArg Prod.snd he
  have hd₁ : ν₁ (x - y) = 0 := by rw [map_sub, he₁, sub_self]
  have hd₂ : ν₂ (x - y) = 0 := by rw [map_sub, he₂, sub_self]
  have h₁ := normal_cramer_identity ν₁ v w (x - y)
  have h₂ := normal_cramer_identity ν₂ v w (x - y)
  rw [hd₁, hv, mul_zero, mul_zero, zero_add] at h₁
  rw [hd₂, hw, mul_zero, mul_zero, add_zero] at h₂
  have hdet₁ : determinant v (x - y) = 0 :=
    (mul_eq_zero.mp h₁.symm).resolve_right hν₁w
  have hdet₂ : determinant (x - y) w = 0 :=
    (mul_eq_zero.mp h₂.symm).resolve_right hν₂v
  have hid := determinant_smul_identity v w (x - y)
  rw [hdet₁, hdet₂, zero_smul, zero_smul, zero_add] at hid
  have hx : x.1 - y.1 = 0 := by
    have heq := congrArg Prod.fst hid
    change determinant v w * (x.1 - y.1) = 0 at heq
    exact (mul_eq_zero.mp heq).resolve_left hdet
  have hy : x.2 - y.2 = 0 := by
    have heq := congrArg Prod.snd hid
    change determinant v w * (x.2 - y.2) = 0 at heq
    exact (mul_eq_zero.mp heq).resolve_left hdet
  exact Prod.ext (sub_eq_zero.mp hx) (sub_eq_zero.mp hy)

-- changing both normal orientations preserves injectivity for the support cone.
theorem independent_negative_normals (ν₁ ν₂ : Site →+ ℤ)
    (hinj : Function.Injective (ν₁.prod ν₂)) :
    Function.Injective ((-ν₁).prod (-ν₂)) := by
  intro x y he
  apply hinj
  apply Prod.ext
  · have hx := congrArg Prod.fst he
    exact neg_injective hx
  · have hy := congrArg Prod.snd he
    exact neg_injective hy

end KumarNivat
