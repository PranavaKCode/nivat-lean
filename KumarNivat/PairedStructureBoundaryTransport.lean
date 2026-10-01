import KumarNivat.PolyhedralRays
import KumarNivat.AnchoredCompactness

open Filter Topology

namespace KumarNivat

-- a nonzero integer normal has an inward lattice step for the final agreement argument.
theorem exists_positive_integer_normal_vector (ν : Site →+ ℤ) (hν : ν ≠ 0) :
    ∃ v : Site, 0 < ν v := by
  have hsome : ∃ v : Site, ν v ≠ 0 := by
    by_contra! hz
    apply hν
    ext v
    exact hz v
  obtain ⟨v, hv⟩ := hsome
  rcases lt_or_gt_of_ne hv with hneg | hpos
  · exact ⟨-v, by simpa only [map_neg] using neg_pos.mpr hneg⟩
  · exact ⟨v, hpos⟩

-- tangential motion exhausts all the other positive inward inequalities at every fixed half-plane site.
theorem eventually_shifted_polyhedral_interior_agreement {A I : Type*}
    (x B : Site → A) (ν : Site →+ ℤ) (β : ℤ) (J : Finset I)
    (μ : I → Site →+ ℤ) (cut : I → ℤ) (h : Site) (hνh : ν h = 0)
    (hμh : ∀ i ∈ J, 0 < μ i h) (hperiod : IsPeriod B h)
    (hagree : ∀ g : Site, latticeEmbedding g ∈ inwardLayerRegion ν β J μ cut →
      β + 1 ≤ ν g → x g = B g) :
    ∀ g : Site, β + 1 ≤ ν g → ∀ᶠ n : ℕ in atTop, shift ((n : ℤ) • h) x g = B g := by
  intro g hg
  obtain ⟨N, _hN, hfit⟩ := eventually_translated_window_in_fixed_halfplanes
    J μ cut {0} g h hμh
  filter_upwards [eventually_ge_atTop N.toNat] with n hn
  have hn' : N ≤ (n : ℤ) := by omega
  have hnormal : ν (g + (n : ℤ) • h) = ν g := by
    rw [map_add, map_zsmul, hνh, smul_zero, add_zero]
  have hmem : latticeEmbedding (g + (n : ℤ) • h) ∈ inwardLayerRegion ν β J μ cut := by
    apply (mem_inwardLayerRegion_lattice ν β J μ cut _).mpr
    refine ⟨by rw [hnormal]; omega, ?_⟩
    intro i hi
    simpa only [add_zero] using hfit (n : ℤ) hn' 0 (Finset.mem_singleton_self 0) i hi
  change x (g + (n : ℤ) • h) = B g
  exact (hagree _ hmem (by rw [hnormal]; exact hg)).trans (hperiod.zsmul (n : ℤ) g)

-- translating by a reference period keeps every late degree block in the same fixed boundary window.
theorem directional_disagreement_blocks_retain_fixed_window {A : Type*}
    (x B : Site → A) (A₀ b : Site) (t q : ℕ) (hperiod : IsPeriod B ((q : ℤ) • b))
    (hblocks : ∀ n : ℤ, 0 ≤ n → ∃ i : Fin t,
      x (A₀ + (n + (i.val : ℤ)) • b) ≠ B (A₀ + (n + (i.val : ℤ)) • b)) :
    ∀ n : ℕ, ∃ g ∈ Finset.univ.image (fun i : Fin t => A₀ + (i.val : ℤ) • b),
      shift ((n : ℤ) • ((q : ℤ) • b)) x g ≠ B g := by
  intro n
  obtain ⟨i, hi⟩ := hblocks ((n : ℤ) * (q : ℤ)) (mul_nonneg (Int.natCast_nonneg n) (Int.natCast_nonneg q))
  refine ⟨A₀ + (i.val : ℤ) • b, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, ?_⟩
  have hsite : (A₀ + (i.val : ℤ) • b) + (n : ℤ) • ((q : ℤ) • b) =
      A₀ + ((n : ℤ) * (q : ℤ) + (i.val : ℤ)) • b := by
    rw [smul_smul, add_smul]
    abel
  intro he
  apply hi
  rw [← hsite]
  exact he.trans (hperiod.zsmul (n : ℤ) (A₀ + (i.val : ℤ) • b)).symm

end KumarNivat
