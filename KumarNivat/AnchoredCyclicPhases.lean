module

public import KumarNivat.AnchoredEnvelopeTranslation
public import KumarNivat.AnchoredChainWalk
public import KumarNivat.AnchoredSubsequences
public import KumarNivat.AnchoredMaximalGeometry

@[expose] public section

open Filter Topology

namespace KumarNivat

-- phase selection and dickson's lemma reindex the same actual polygons and edge witnesses.
theorem anchored_cyclic_constant_phase_monotone_subsequence {A : Type*} {n : ℕ} [NeZero n]
    (w : Site → A) (a : Site) (l : ℕ) (hl : 0 < l) (hw : IsPeriod w ((l : ℤ) • a))
    (k : ℕ → ℤ) (e : ZMod n → Site) (horder : CyclicEdgeOrder e)
    (F : ℕ → Finset Site) (P : ∀ N, OrderedCyclicLatticePolygon e (F N))
    (hF : ∀ N, LatticeConvex (F N)) (G : Site) (hanchor : ∀ N, (P N).vertex 1 = G) :
    ∃ r : ℤ, 0 ≤ r ∧ r < (l : ℤ) ∧ ∃ ρ : ℕ → ℕ, StrictMono ρ ∧
      (∀ N, shift (k (ρ N) • a) w = shift (r • a) w) ∧
      Monotone (fun N => (P (ρ N)).edgeLength) ∧
      Monotone (fun N => latticeHull (F (ρ N))) ∧ Monotone (F ∘ ρ) := by
  obtain ⟨r, hr₀, hr₁, φ, hφ, hphase⟩ := periodic_reference_constant_phase w a l hl hw k
  let lengths : ℕ → ZMod n → ℕ := fun N i => ((P (φ N)).edgeLength i).toNat
  obtain ⟨ψ, hψ, hmono⟩ := anchored_lengths_monotone_subsequence lengths
  let ρ := φ ∘ ψ
  have hρ : StrictMono ρ := hφ.comp hψ
  have hlengths : Monotone (fun N => (P (ρ N)).edgeLength) := by
    intro N M hNM i
    change (P (ρ N)).edgeLength i ≤ (P (ρ M)).edgeLength i
    have hnat := hmono hNM i
    change ((P (ρ N)).edgeLength i).toNat ≤ ((P (ρ M)).edgeLength i).toNat at hnat
    have hN := (P (ρ N)).length_pos i
    have hM := (P (ρ M)).length_pos i
    have hNcast : (((P (ρ N)).edgeLength i).toNat : ℤ) = (P (ρ N)).edgeLength i := by omega
    have hMcast : (((P (ρ M)).edgeLength i).toNat : ℤ) = (P (ρ M)).edgeLength i := by omega
    have hz : (((P (ρ N)).edgeLength i).toNat : ℤ) ≤ (((P (ρ M)).edgeLength i).toNat : ℤ) := by
      exact_mod_cast hnat
    rwa [hNcast, hMcast] at hz
  have hhull : Monotone (fun N => latticeHull (F (ρ N))) :=
    anchored_cyclic_sequence_hulls_monotone e horder (F ∘ ρ) (fun N => P (ρ N)) G
      (fun N => hanchor (ρ N)) (fun N M hNM i => hlengths hNM i)
  have hsites : Monotone (F ∘ ρ) := by
    intro N M hNM
    exact (latticeConvex_hull_inclusion_iff (F (ρ N)) (F (ρ M)) (hF (ρ M))).mpr (hhull hNM)
  exact ⟨r, hr₀, hr₁, ρ, hρ, fun N => hphase (ψ N), hlengths, hhull, hsites⟩

-- the same inherited integer edge lengths keep their divergence along every selected increasing subsequence.
theorem anchored_cyclic_edge_divergence_subsequence {n : ℕ} [NeZero n]
    (e : ZMod n → Site) (F : ℕ → Finset Site) (P : ∀ N, OrderedCyclicLatticePolygon e (F N))
    (i : ZMod n) (hdiv : Tendsto (fun N => ((P N).edgeLength i).toNat) atTop atTop)
    (ρ : ℕ → ℕ) (hρ : StrictMono ρ) :
    Tendsto (fun N => ((P (ρ N)).edgeLength i).toNat) atTop atTop :=
  hdiv.comp hρ.tendsto_atTop

-- the original tangent-normal heights keep their divergence through the same reindexing.
theorem anchored_cyclic_width_divergence_subsequence {n : ℕ} [NeZero n]
    (e : ZMod n → Site) (F : ℕ → Finset Site) (P : ∀ N, OrderedCyclicLatticePolygon e (F N))
    (i : ZMod n) (G : Site)
    (hdiv : Tendsto (fun N => ((directionNormal (e 0) ((P N).vertex i) -
      directionNormal (e 0) G : ℤ) : ℝ)) atTop atTop)
    (ρ : ℕ → ℕ) (hρ : StrictMono ρ) :
    Tendsto (fun N => ((directionNormal (e 0) ((P (ρ N)).vertex i) -
      directionNormal (e 0) G : ℤ) : ℝ)) atTop atTop :=
  hdiv.comp hρ.tendsto_atTop

end KumarNivat
