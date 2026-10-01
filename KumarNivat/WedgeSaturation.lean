import KumarNivat.DefectHalfplanes
import KumarNivat.PeriodLattice
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.FieldSimp

namespace KumarNivat

-- integer normals describe the lattice points of a rational wedge.
def AgreesOnWedge {A : Type*} (ell μ : Site →+ ℤ) (a b : ℤ) (x B : Site → A) : Prop :=
  ∀ g, a ≤ ell g → b ≤ μ g → x g = B g

-- every additive lattice normal is determined by its two integer basis values.
theorem integer_normal_apply (ν : Site →+ ℤ) (g : Site) :
    ν g = g.1 * ν (1, 0) + g.2 * ν (0, 1) := by
  have he : g = g.1 • ((1, 0) : Site) + g.2 • ((0, 1) : Site) := by
    ext <;> simp
  calc
    ν g = ν (g.1 • ((1, 0) : Site) + g.2 • ((0, 1) : Site)) := congrArg ν he
    _ = g.1 * ν (1, 0) + g.2 * ν (0, 1) := by
      rw [map_add, map_zsmul, map_zsmul]
      simp

-- a single integer normal always has a nonzero tangent lattice vector.
theorem exists_nonzero_normal_kernel (ν : Site →+ ℤ) :
    ∃ h : Site, h ≠ 0 ∧ ν h = 0 := by
  by_cases hz : ν (1, 0) = 0 ∧ ν (0, 1) = 0
  · exact ⟨(1, 0), by decide, hz.1⟩
  · let h : Site := (ν (0, 1), -ν (1, 0))
    refine ⟨h, ?_, ?_⟩
    · intro hh
      have hy : ν (0, 1) = 0 := congrArg Prod.fst hh
      have hx : -ν (1, 0) = 0 := congrArg Prod.snd hh
      exact hz ⟨neg_eq_zero.mp hx, hy⟩
    · rw [integer_normal_apply]
      change ν (0, 1) * ν (1, 0) + -ν (1, 0) * ν (0, 1) = 0
      ring

-- independent wedge normals are both nonzero as additive maps.
theorem independent_normals_nonzero (ell μ : Site →+ ℤ)
    (hinj : Function.Injective (ell.prod μ)) : ell ≠ 0 ∧ μ ≠ 0 := by
  constructor
  · intro hz
    obtain ⟨h, hne, hμ⟩ := exists_nonzero_normal_kernel μ
    apply hne
    apply hinj
    change (ell h, μ h) = (ell 0, μ 0)
    simp [hz, hμ]
  · intro hz
    obtain ⟨h, hne, hEll⟩ := exists_nonzero_normal_kernel ell
    apply hne
    apply hinj
    change (ell h, μ h) = (ell 0, μ 0)
    simp [hz, hEll]

-- agreement can be transported back along any common period multiple.
theorem agreement_of_period_translate {A : Type*} (x B : Site → A) (v g : Site) (t : ℤ)
    (hx : IsPeriod x v) (hB : IsPeriod B v)
    (hagree : x (g + t • v) = B (g + t • v)) : x g = B g := by
  calc
    x g = x (g + t • v) := (hx.zsmul t g).symm
    _ = B (g + t • v) := hagree
    _ = B g := hB.zsmul t g

-- two positive normal increments let a common period reach the wedge from every site.
theorem wedge_agreement_global_of_positive {A : Type*} (x B : Site → A)
    (ell μ : Site →+ ℤ) (a b : ℤ) (v : Site)
    (hx : IsPeriod x v) (hB : IsPeriod B v) (hwedge : AgreesOnWedge ell μ a b x B)
    (hEll : 0 < ell v) (hμ : 0 < μ v) : x = B := by
  funext g
  let t : ℤ := max 0 (max (a - ell g) (b - μ g))
  have ht : 0 ≤ t := by dsimp [t]; omega
  have hta : a - ell g ≤ t := by dsimp [t]; omega
  have htb : b - μ g ≤ t := by dsimp [t]; omega
  have hmulell : t ≤ t * ell v := by
    have he := mul_le_mul_of_nonneg_left (show 1 ≤ ell v by omega) ht
    simpa using he
  have hmulμ : t ≤ t * μ v := by
    have he := mul_le_mul_of_nonneg_left (show 1 ≤ μ v by omega) ht
    simpa using he
  have hfirst : a ≤ ell (g + t • v) := by
    simp only [map_add, map_zsmul, smul_eq_mul]
    omega
  have hsecond : b ≤ μ (g + t • v) := by
    simp only [map_add, map_zsmul, smul_eq_mul]
    omega
  exact agreement_of_period_translate x B v g t hx hB (hwedge _ hfirst hsecond)

-- a flat first normal leaves exactly its own half-plane constraint.
theorem wedge_agreement_flat_positive {A : Type*} (x B : Site → A)
    (ell μ : Site →+ ℤ) (a b : ℤ) (v : Site)
    (hx : IsPeriod x v) (hB : IsPeriod B v) (hwedge : AgreesOnWedge ell μ a b x B)
    (hEll : ell v = 0) (hμ : 0 < μ v) : AgreesAbove ell a x B := by
  intro g hg
  let t : ℤ := max 0 (b - μ g)
  have ht : 0 ≤ t := by dsimp [t]; omega
  have htb : b - μ g ≤ t := by dsimp [t]; omega
  have hmul : t ≤ t * μ v := by
    have he := mul_le_mul_of_nonneg_left (show 1 ≤ μ v by omega) ht
    simpa using he
  have hfirst : a ≤ ell (g + t • v) := by
    simpa only [map_add, map_zsmul, hEll, smul_zero, add_zero] using hg
  have hsecond : b ≤ μ (g + t • v) := by
    simp only [map_add, map_zsmul, smul_eq_mul]
    omega
  exact agreement_of_period_translate x B v g t hx hB (hwedge _ hfirst hsecond)

-- reversing a common period handles the negative nonflat increment as well.
theorem wedge_agreement_flat {A : Type*} (x B : Site → A)
    (ell μ : Site →+ ℤ) (a b : ℤ) (v : Site)
    (hx : IsPeriod x v) (hB : IsPeriod B v) (hwedge : AgreesOnWedge ell μ a b x B)
    (hEll : ell v = 0) (hμ : μ v ≠ 0) : AgreesAbove ell a x B := by
  by_cases hp : 0 < μ v
  · exact wedge_agreement_flat_positive x B ell μ a b v hx hB hwedge hEll hp
  · exact wedge_agreement_flat_positive x B ell μ a b (-v) hx.neg hB.neg hwedge
      (by simp only [map_neg, hEll, neg_zero]) (by rw [map_neg]; omega)

-- a unit-length rational interval always contains an integer, regardless of period primitivity.
theorem exists_integer_in_unit_interval (lo hi : ℚ) (hgap : lo + 1 ≤ hi) :
    ∃ t : ℤ, lo ≤ (t : ℚ) ∧ (t : ℚ) ≤ hi := by
  exact ⟨⌈lo⌉, Int.le_ceil lo, (Int.ceil_lt_add_one lo).le.trans hgap⟩

-- this positive combination is tangent to the common period in the opposing-sign case.
def weightedNormal (ell μ : Site →+ ℤ) (b a : ℤ) : Site →+ ℤ where
  toFun g := b * ell g + a * μ g
  map_zero' := by simp
  map_add' g h := by simp [mul_add]; ring

-- the weighted normal cannot vanish when the wedge's two normals are independent.
theorem weightedNormal_nonzero (ell μ : Site →+ ℤ)
    (hinj : Function.Injective (ell.prod μ)) (b a : ℤ) (ha : a ≠ 0) :
    weightedNormal ell μ b a ≠ 0 := by
  intro hz
  obtain ⟨h, hne, hEll⟩ := exists_nonzero_normal_kernel ell
  have he := congrArg (fun ν : Site →+ ℤ => ν h) hz
  change b * ell h + a * μ h = 0 at he
  rw [hEll, mul_zero, zero_add] at he
  have hμ : μ h = 0 := (mul_eq_zero.mp he).resolve_left ha
  apply hne
  apply hinj
  change (ell h, μ h) = (ell 0, μ 0)
  simp [hEll, hμ]

-- the manuscript's inset guarantees an integer translate satisfying both wedge inequalities.
theorem wedge_agreement_opposing {A : Type*} (x B : Site → A)
    (ell μ : Site →+ ℤ) (a₀ b₀ : ℤ) (v : Site)
    (hx : IsPeriod x v) (hB : IsPeriod B v) (hwedge : AgreesOnWedge ell μ a₀ b₀ x B)
    (hEll : 0 < ell v) (hμ : μ v < 0) :
    AgreesAbove (weightedNormal ell μ (-μ v) (ell v))
      ((-μ v) * a₀ + ell v * b₀ + ell v * (-μ v)) x B := by
  intro g hg
  let a : ℤ := ell v
  let b : ℤ := -μ v
  have ha : 0 < a := hEll
  have hb : 0 < b := by dsimp [b]; omega
  have haQ : (0 : ℚ) < a := by exact_mod_cast ha
  have hbQ : (0 : ℚ) < b := by exact_mod_cast hb
  let lo : ℚ := ((a₀ - ell g : ℤ) : ℚ) / (a : ℚ)
  let hi : ℚ := ((μ g - b₀ : ℤ) : ℚ) / (b : ℚ)
  have hgapInt : b * (a₀ - ell g + a) ≤ a * (μ g - b₀) := by
    change b * a₀ + a * b₀ + a * b ≤ b * ell g + a * μ g at hg
    nlinarith
  have hlo : lo + 1 = ((a₀ - ell g + a : ℤ) : ℚ) / (a : ℚ) := by
    dsimp [lo]
    push_cast
    field_simp [haQ.ne']
  have hgap : lo + 1 ≤ hi := by
    rw [hlo]
    apply (div_le_div_iff₀ haQ hbQ).mpr
    have he : (b : ℚ) * ((a₀ - ell g + a : ℤ) : ℚ) ≤
        (a : ℚ) * ((μ g - b₀ : ℤ) : ℚ) := by exact_mod_cast hgapInt
    simpa only [mul_comm] using he
  obtain ⟨t, htlo, hthi⟩ := exists_integer_in_unit_interval lo hi hgap
  have hlowQ : ((a₀ - ell g : ℤ) : ℚ) ≤ (t : ℚ) * (a : ℚ) :=
    (div_le_iff₀ haQ).mp htlo
  have hhighQ : (t : ℚ) * (b : ℚ) ≤ ((μ g - b₀ : ℤ) : ℚ) :=
    (le_div_iff₀ hbQ).mp hthi
  have hlow : a₀ - ell g ≤ t * a := by exact_mod_cast hlowQ
  have hhigh : t * b ≤ μ g - b₀ := by exact_mod_cast hhighQ
  have hfirst : a₀ ≤ ell (g + t • v) := by
    simp only [map_add, map_zsmul, smul_eq_mul]
    change a₀ ≤ ell g + t * a
    omega
  have hsecond : b₀ ≤ μ (g + t • v) := by
    simp only [map_add, map_zsmul, smul_eq_mul]
    have he : μ v = -b := by dsimp [b]; omega
    rw [he, mul_neg]
    omega
  exact agreement_of_period_translate x B v g t hx hB (hwedge _ hfirst hsecond)

-- the three sign cases give either global agreement or an inset tangent half-plane.
theorem common_period_wedge_saturation_nonnegative {A : Type*} (x B : Site → A)
    (ell μ : Site →+ ℤ) (a b : ℤ) (v : Site) (hv : v ≠ 0)
    (hinj : Function.Injective (ell.prod μ))
    (hx : IsPeriod x v) (hB : IsPeriod B v) (hwedge : AgreesOnWedge ell μ a b x B)
    (hEll : 0 ≤ ell v) :
    x = B ∨ ∃ ν : Site →+ ℤ, ν ≠ 0 ∧ ν v = 0 ∧ ∃ β : ℤ, AgreesAbove ν β x B := by
  have hnormals := independent_normals_nonzero ell μ hinj
  by_cases hflat : ell v = 0
  · right
    have hμ : μ v ≠ 0 := by
      intro hz
      apply hv
      apply hinj
      change (ell v, μ v) = (ell 0, μ 0)
      simp [hflat, hz]
    exact ⟨ell, hnormals.1, hflat, a, wedge_agreement_flat x B ell μ a b v hx hB hwedge hflat hμ⟩
  · have hpos : 0 < ell v := by omega
    by_cases hμneg : μ v < 0
    · right
      refine ⟨weightedNormal ell μ (-μ v) (ell v),
        weightedNormal_nonzero ell μ hinj (-μ v) (ell v) hpos.ne', ?_,
        (-μ v) * a + ell v * b + ell v * (-μ v),
        wedge_agreement_opposing x B ell μ a b v hx hB hwedge hpos hμneg⟩
      change (-μ v) * ell v + ell v * μ v = 0
      ring
    · by_cases hμflat : μ v = 0
      · right
        refine ⟨μ, hnormals.2, hμflat, b, ?_⟩
        have hwedge' : AgreesOnWedge μ ell b a x B := fun g h₁ h₂ => hwedge g h₂ h₁
        exact wedge_agreement_flat x B μ ell b a v hx hB hwedge' hμflat hpos.ne'
      · left
        exact wedge_agreement_global_of_positive x B ell μ a b v hx hB hwedge hpos (by omega)

-- lemma 2.4's geometric conclusion excludes the global case using non-full-periodicity.
theorem exists_halfplane_agreement_of_common_period {A : Type*} (x B : Site → A)
    (ell μ : Site →+ ℤ) (a b : ℤ) (v : Site) (hv : v ≠ 0)
    (hinj : Function.Injective (ell.prod μ))
    (hx : IsPeriod x v) (hB : IsPeriod B v) (hwedge : AgreesOnWedge ell μ a b x B)
    (hnot : ¬ FullyPeriodic x) (hfull : FullyPeriodic B) :
    ∃ ν : Site →+ ℤ, ν ≠ 0 ∧ ν v = 0 ∧ ∃ β : ℤ, AgreesAbove ν β x B := by
  by_cases hEll : 0 ≤ ell v
  · rcases common_period_wedge_saturation_nonnegative x B ell μ a b v hv hinj hx hB hwedge hEll
      with heq | hplane
    · exact (hnot (heq.symm ▸ hfull)).elim
    · exact hplane
  · have hv' : -v ≠ 0 := by intro hz; exact hv (neg_eq_zero.mp hz)
    rcases common_period_wedge_saturation_nonnegative x B ell μ a b (-v) hv' hinj hx.neg hB.neg
      hwedge (by rw [map_neg]; omega) with heq | hplane
    · exact (hnot (heq.symm ▸ hfull)).elim
    · obtain ⟨ν, hν, hνv, β, hagree⟩ := hplane
      exact ⟨ν, hν, by simpa only [map_neg, neg_eq_zero] using hνv, β, hagree⟩

end KumarNivat
