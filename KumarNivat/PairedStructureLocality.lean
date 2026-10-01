import KumarNivat.PairedStructureLimits
import KumarNivat.PairedStructureBalls

open Filter Topology

namespace KumarNivat

-- expansive half-plane agreement determines each chosen output from a finite subset of that side.
theorem finite_halfplane_determines_site_of_not_nonexpansive {A : Type*}
    [TopologicalSpace A] [DiscreteTopology A] (c : Site → A) (hc : (Set.range c).Finite)
    (ell : Site →+ ℝ) (hell : ell ≠ 0) (hnoNE : ¬ OneSidedNonexpansive c ell) (e : Site) :
    ∃ D : Finset Site, (∀ g ∈ D, 0 ≤ ell g) ∧
      ∀ x ∈ orbitClosure c, ∀ y ∈ orbitClosure c,
        (∀ g ∈ D, x g = y g) → x e = y e := by
  classical
  by_contra hnone
  have hbad (D : Finset Site) (hD : ∀ g ∈ D, 0 ≤ ell g) :
      ∃ x ∈ orbitClosure c, ∃ y ∈ orbitClosure c, (∀ g ∈ D, x g = y g) ∧ x e ≠ y e := by
    by_contra hgood
    apply hnone
    refine ⟨D, hD, ?_⟩
    intro x hx y hy hagree
    by_contra hne
    exact hgood ⟨x, hx, y, hy, hagree, hne⟩
  let D : ℕ → Finset Site := fun n =>
    ((Finset.Icc (-(n : ℤ)) n).product (Finset.Icc (-(n : ℤ)) n)).filter (fun g => 0 ≤ ell g)
  choose x hx y hy hagree hfail using
    (fun n : ℕ => hbad (D n) (fun g hg => (Finset.mem_filter.mp hg).2))
  apply hnoNE
  apply oneSidedNonexpansive_of_growing_halfplane_pairs c hc ell hell x y hx hy {e}
    (fun n => ⟨e, Finset.mem_singleton_self e, hfail n⟩)
  intro g hg
  filter_upwards [eventually_ge_atTop (latticeEnergy g + 1)] with n hn
  apply hagree n g
  apply Finset.mem_filter.mpr
  refine ⟨mem_lattice_square_of_energy_le n g (by nlinarith), hg⟩

end KumarNivat
