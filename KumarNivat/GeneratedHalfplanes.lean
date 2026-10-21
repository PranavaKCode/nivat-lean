module

public import KumarNivat.PatternRestriction
public import KumarNivat.OrbitLanguage
public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section

namespace KumarNivat

-- generation applies to every legal local pattern in the actual orbit language.
theorem generatedSite_inherited {A : Type*} (c x y : Site → A)
    (S : Finset Site) (v : Site) (hv : v ∈ S) (hgen : GeneratedSite c S v)
    (hx : LanguageContained x c) (hy : LanguageContained y c) (g : Site)
    (hagree : ∀ u ∈ S.erase v, x (g + u) = y (g + u)) : x (g + v) = y (g + v) := by
  obtain ⟨tx, htx⟩ := hx S g
  obtain ⟨ty, hty⟩ := hy S g
  have he := hgen tx ty (by
    intro u hu
    have hum := Finset.mem_of_mem_erase hu
    exact (htx u hum).symm.trans ((hagree u hu).trans (hty u hum))) v hv
  exact (htx v hv).trans (he.trans (hty v hv).symm)

-- a uniform normal gap determines one more slab from agreement on its inward side.
theorem generated_halfplane_agreement_step {A : Type*} (c x y : Site → A)
    (S : Finset Site) (v : Site) (hv : v ∈ S) (hgen : GeneratedSite c S v)
    (hx : LanguageContained x c) (hy : LanguageContained y c)
    (ell : Site →+ ℝ) (δ b : ℝ) (hgap : ∀ u ∈ S.erase v, δ ≤ ell (u - v))
    (hagree : ∀ g : Site, b ≤ ell g → x g = y g) :
    ∀ g : Site, b - δ ≤ ell g → x g = y g := by
  intro g hg
  have he := generatedSite_inherited c x y S v hv hgen hx hy (g - v) (by
    intro u hu
    apply hagree
    have hnormal : ell (g - v + u) = ell g + ell (u - v) := by
      simp only [map_add, map_sub]
      ring
    rw [hnormal]
    have huδ := hgap u hu
    linarith)
  simpa only [sub_add_cancel] using he

-- a finite unique minimizing face gives a positive slab thickness, even for irrational normals.
theorem exists_positive_normal_gap (S : Finset Site) (v : Site) (ell : Site →+ ℝ)
    (hstrict : ∀ u ∈ S, u ≠ v → ell v < ell u) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ u ∈ S.erase v, δ ≤ ell (u - v) := by
  classical
  by_cases hne : (S.erase v).Nonempty
  · obtain ⟨u, hu, hmin⟩ := (S.erase v).exists_min_image (fun z => ell (z - v)) hne
    have hum := Finset.mem_erase.mp hu
    refine ⟨ell (u - v), ?_, hmin⟩
    rw [map_sub]
    exact sub_pos.mpr (hstrict u hum.2 hum.1)
  · exact ⟨1, zero_lt_one, fun u hu => (hne ⟨u, hu⟩).elim⟩

-- repeated slab propagation makes a singleton generated supporting face expansive.
theorem generated_unique_minimum_forces_global_agreement {A : Type*} (c x y : Site → A)
    (S : Finset Site) (v : Site) (hv : v ∈ S) (hgen : GeneratedSite c S v)
    (hx : LanguageContained x c) (hy : LanguageContained y c) (ell : Site →+ ℝ)
    (hstrict : ∀ u ∈ S, u ≠ v → ell v < ell u) (b : ℝ)
    (hagree : ∀ g : Site, b ≤ ell g → x g = y g) : x = y := by
  obtain ⟨δ, hδ, hgap⟩ := exists_positive_normal_gap S v ell hstrict
  have hband (n : ℕ) : ∀ g : Site, b - (n : ℝ) * δ ≤ ell g → x g = y g := by
    induction n with
    | zero => simpa only [Nat.cast_zero, zero_mul, sub_zero] using hagree
    | succ n ih =>
      intro g hg
      apply generated_halfplane_agreement_step c x y S v hv hgen hx hy ell δ
        (b - (n : ℝ) * δ) hgap ih g
      rw [Nat.cast_add, Nat.cast_one] at hg
      linarith
  funext g
  obtain ⟨N, hN⟩ := exists_nat_gt ((b - ell g) / δ)
  have hbound := (div_lt_iff₀ hδ).mp hN
  exact hband N g (by linarith)

-- one-sided nonexpansiveness uses distinct points of the same product-topology orbit closure.
def OneSidedNonexpansive {A : Type*} [TopologicalSpace A]
    (c : Site → A) (ell : Site →+ ℝ) : Prop :=
  ell ≠ 0 ∧ ∃ x y : Site → A, x ∈ orbitClosure c ∧ y ∈ orbitClosure c ∧ x ≠ y ∧
    ∀ g : Site, 0 ≤ ell g → x g = y g

-- such a direction cannot have a unique generated minimizing vertex.
theorem not_oneSidedNonexpansive_of_generated_unique_minimum {A : Type*}
    [TopologicalSpace A] [DiscreteTopology A] (c : Site → A) (S : Finset Site)
    (v : Site) (hv : v ∈ S) (hgen : GeneratedSite c S v) (ell : Site →+ ℝ)
    (hstrict : ∀ u ∈ S, u ≠ v → ell v < ell u) : ¬ OneSidedNonexpansive c ell := by
  rintro ⟨_hell, x, y, hx, hy, hxy, hagree⟩
  exact hxy (generated_unique_minimum_forces_global_agreement c x y S v hv hgen
    (languageContained_of_mem_orbitClosure c x hx) (languageContained_of_mem_orbitClosure c y hy)
    ell hstrict 0 hagree)

end KumarNivat
