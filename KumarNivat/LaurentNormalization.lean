import KumarNivat.DirectionalLineFactors

namespace KumarNivat

-- a monomial translation shifts support exactly, with no coefficient cancellation.
theorem monomial_translate_mem_support {K : Type*} [CommRing K]
    (v : Site) (f : Laurent K) (u : Site) :
    u ∈ (AddMonoidAlgebra.single v (1 : K) * f).coeff.support ↔
      u - v ∈ f.coeff.support := by
  classical
  simp only [Finsupp.mem_support_iff, AddMonoidAlgebra.coeff_single_mul_apply, one_mul]
  simp only [sub_eq_add_neg, add_comm]

-- the attained coordinate minima give a normalized support rectangle for any nonzero filter.
theorem exists_normalized_laurent_box {K : Type*} [Field K]
    (f : Laurent K) (hf : f ≠ 0) :
    ∃ v : Site, ∃ r s : ℕ,
      BoxExtrema (AddMonoidAlgebra.single v (1 : K) * f) r s ∧
        (AddMonoidAlgebra.single v (1 : K) * f).coeff.support ⊆ rectangle (r + 1) (s + 1) := by
  classical
  have hsupport : f.coeff.support.Nonempty := Finsupp.support_nonempty_iff.mpr
    (fun hz => hf (AddMonoidAlgebra.coeff_injective hz))
  obtain ⟨xl, hxl, hxlo⟩ := f.coeff.support.exists_min_image Prod.fst hsupport
  obtain ⟨xu, hxu, hxhi⟩ := f.coeff.support.exists_max_image Prod.fst hsupport
  obtain ⟨yl, hyl, hylo⟩ := f.coeff.support.exists_min_image Prod.snd hsupport
  obtain ⟨yu, hyu, hyhi⟩ := f.coeff.support.exists_max_image Prod.snd hsupport
  let v : Site := (-xl.1, -yl.2)
  let r := (xu.1 - xl.1).toNat
  let s := (yu.2 - yl.2).toNat
  have hr : (r : ℤ) = xu.1 - xl.1 := by
    have hb := hxlo xu hxu
    dsimp [r]
    omega
  have hs : (s : ℤ) = yu.2 - yl.2 := by
    have hb := hylo yu hyu
    dsimp [s]
    omega
  have hshift (z : Site) (hz : z ∈ f.coeff.support) :
      z + v ∈ (AddMonoidAlgebra.single v (1 : K) * f).coeff.support := by
    rw [monomial_translate_mem_support, add_sub_cancel_right]
    exact hz
  refine ⟨v, r, s, ?_, ?_⟩
  · refine ⟨⟨xl + v, hshift xl hxl, ?_⟩, ⟨xu + v, hshift xu hxu, ?_⟩,
      ⟨yl + v, hshift yl hyl, ?_⟩, ⟨yu + v, hshift yu hyu, ?_⟩⟩
    · simp [v]
    · simp only [Prod.fst_add, v, hr]
      omega
    · simp [v]
    · simp only [Prod.snd_add, v, hs]
      omega
  · intro u hu
    have hu' := (monomial_translate_mem_support v f u).mp hu
    have hx₁ := hxlo (u - v) hu'
    have hx₂ := hxhi (u - v) hu'
    have hy₁ := hylo (u - v) hu'
    have hy₂ := hyhi (u - v) hu'
    simp only [Prod.fst_sub, Prod.snd_sub, v] at hx₁ hx₂ hy₁ hy₂
    apply (mem_rectangle_iff u (r + 1) (s + 1)).mpr
    push_cast
    omega

-- normalize a proper line factor while preserving its primitive direction and nonzero endpoints.
theorem exists_normalized_proper_line_factor {K : Type*} [Field K]
    (h : Site) (hh : h ≠ 0) (ψ : Laurent K) (hdiv : ψ ∣ binomial h)
    (hproper : ¬ IsUnit ψ) :
    ∃ p : Site, ∃ a : ℕ, 0 < a ∧ h = (a : ℤ) • p ∧ p ≠ 0 ∧
      ∃ v E : Site, ∃ t r s : ℕ, 0 < t ∧ ∃ α : Fin (t + 1) → K,
        α 0 ≠ 0 ∧ α (Fin.last t) ≠ 0 ∧
          lineOperator E p t α = AddMonoidAlgebra.single v (1 : K) * ψ ∧
          BoxExtrema (lineOperator E p t α) r s ∧
          E ∈ rectangle (r + 1) (s + 1) ∧
          E + (t : ℤ) • p ∈ rectangle (r + 1) (s + 1) := by
  obtain ⟨p, a, ha, he, hp, E, t, ht, α, hfirst, hlast, hψ⟩ :=
    exists_proper_binomial_divisor_line_block h hh ψ hdiv hproper
  have hψnz : ψ ≠ 0 := by
    obtain ⟨f, hf⟩ := hdiv
    exact left_ne_zero_of_mul (show ψ * f ≠ 0 by rw [← hf]; exact binomial_ne_zero h hh)
  obtain ⟨v, r, s, hext, hbox⟩ := exists_normalized_laurent_box ψ hψnz
  have hnorm : lineOperator (v + E) p t α = AddMonoidAlgebra.single v (1 : K) * ψ := by
    rw [hψ, single_mul_lineOperator]
  rw [← hnorm] at hext hbox
  have hend := lineOperator_endpoints_mem (v + E) p hp t α hfirst hlast
  exact ⟨p, a, ha, he, hp, v, v + E, t, r, s, ht, α, hfirst, hlast,
    hnorm, hext, hbox hend.1, hbox hend.2⟩

end KumarNivat
