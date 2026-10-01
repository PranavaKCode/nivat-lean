import KumarNivat.PolyhedralRays
import Mathlib.Data.Nat.Find

namespace KumarNivat

-- a first failing integer level exists inside any fixed region once its inward tail agrees.
theorem first_disagreement_level_in_region {A : Type*} (x y : Site → A) (D : Set Site)
    (ν : Site →+ ℤ) (cut : ℤ)
    (hagree : ∀ g ∈ D, cut ≤ ν g → x g = y g)
    (hfail : ∃ g ∈ D, x g ≠ y g) :
    ∃ β : ℤ, ∃ g : Site, β < cut ∧ g ∈ D ∧ ν g = β ∧ x g ≠ y g ∧
      ∀ u ∈ D, β + 1 ≤ ν u → x u = y u := by
  classical
  let P : ℕ → Prop := fun n => ∃ g ∈ D, ν g = cut - ((n : ℤ) + 1) ∧ x g ≠ y g
  have hex : ∃ n : ℕ, P n := by
    obtain ⟨g, hg, hn⟩ := hfail
    have hlt : ν g < cut := by by_contra hnot; exact hn (hagree g hg (by omega))
    let n := (cut - ν g - 1).toNat
    exact ⟨n, g, hg, by dsimp [n]; omega, hn⟩
  let n := Nat.find hex
  obtain ⟨g, hg, hlevel, hn⟩ := Nat.find_spec hex
  refine ⟨cut - ((n : ℤ) + 1), g, by omega, hg, hlevel, hn, ?_⟩
  intro u hu hνu
  by_cases hcut : cut ≤ ν u
  · exact hagree u hu hcut
  · by_contra hne
    let k := (cut - ν u - 1).toNat
    have hk : ν u = cut - ((k : ℤ) + 1) := by dsimp [k]; omega
    have hkn : k < n := by omega
    exact Nat.find_min hex hkn ⟨u, hu, hk, hne⟩

-- dropping one facet is exactly exhausted by its outward integer relaxations at lattice sites.
theorem exists_inward_relaxation_containing_site {I : Type*} (ν : Site →+ ℤ) (cut : ℤ)
    (J : Finset I) (μ : I → Site →+ ℤ) (z : I → ℤ) (g : Site)
    (hg : ∀ i ∈ J, z i ≤ μ i g) :
    ∃ n : ℕ, latticeEmbedding g ∈ inwardLayerRegion ν (cut - (n : ℤ)) J μ z := by
  refine ⟨(cut - ν g).toNat, ?_⟩
  apply (mem_inwardLayerRegion_lattice ν _ J μ z g).mpr
  exact ⟨by omega, hg⟩

-- the actual failed enlargement chooses a last agreement region and a witness on precisely its next layer.
theorem first_failed_inward_layer {A I : Type*} (x y : Site → A) (ν : Site →+ ℤ) (cut : ℤ)
    (J : Finset I) (μ : I → Site →+ ℤ) (z : I → ℤ)
    (hagree : ∀ g : Site, latticeEmbedding g ∈ inwardLayerRegion ν cut J μ z → x g = y g)
    (hfail : ∃ g : Site, (∀ i ∈ J, z i ≤ μ i g) ∧ x g ≠ y g) :
    ∃ β : ℤ, ∃ g : Site, β < cut ∧ ν g = β ∧
      latticeEmbedding g ∈ inwardLayerRegion ν β J μ z ∧ x g ≠ y g ∧
      ∀ u : Site, latticeEmbedding u ∈ inwardLayerRegion ν (β + 1) J μ z → x u = y u := by
  let D : Set Site := {g | ∀ i ∈ J, z i ≤ μ i g}
  obtain ⟨β, g, hβ, hg, hlevel, hneq, htail⟩ := first_disagreement_level_in_region x y D ν cut
    (fun g hg hν => hagree g ((mem_inwardLayerRegion_lattice ν cut J μ z g).mpr ⟨hν, hg⟩)) hfail
  refine ⟨β, g, hβ, hlevel, (mem_inwardLayerRegion_lattice ν β J μ z g).mpr ⟨le_of_eq hlevel.symm, hg⟩,
    hneq, ?_⟩
  intro u hu
  have h := (mem_inwardLayerRegion_lattice ν (β + 1) J μ z u).mp hu
  exact htail u h.2 h.1

end KumarNivat
