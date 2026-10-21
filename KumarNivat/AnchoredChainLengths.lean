module

public import KumarNivat.AnchoredSubsequences
public import Mathlib.Topology.Algebra.Order.Archimedean

@[expose] public section

open Filter Topology

namespace KumarNivat

-- an unbounded finite weighted width cannot have every nondecreasing edge length stabilize.
theorem unbounded_width_has_unbounded_chain_length (J : Finset ℕ)
    (lengths : ℕ → ℕ → ℕ) (hmono : ∀ j, Monotone (fun N => lengths N j))
    (weight : ℕ → ℤ)
    (hwidth : Tendsto (fun N => ((∑ j ∈ J, (lengths N j : ℤ) * weight j : ℤ) : ℝ))
      atTop atTop) :
    ∃ j ∈ J, Tendsto (fun N => lengths N j) atTop atTop := by
  classical
  by_contra hnot
  have hstabilize : ∀ j : ℕ, ∃ v : ℕ, j ∈ J → ∀ᶠ N in atTop, lengths N j = v := by
    intro j
    by_cases hj : j ∈ J
    · obtain hstable | hdiv := anchored_monotone_length_dichotomy (fun N => lengths N j) (hmono j)
      · obtain ⟨v, hv⟩ := hstable
        exact ⟨v, fun _ => hv⟩
      · exact False.elim (hnot ⟨j, hj, hdiv⟩)
    · exact ⟨0, fun h => False.elim (hj h)⟩
  choose v hv using hstabilize
  let C : ℤ := ∑ j ∈ J, (v j : ℤ) * weight j
  have hconstant : ∀ᶠ N in atTop, (∑ j ∈ J, (lengths N j : ℤ) * weight j) = C := by
    have hevent := J.eventually_all.mpr (fun j hj => hv j hj)
    exact hevent.mono (fun N hN => Finset.sum_congr rfl (fun j hj => by rw [hN j hj]))
  have hlarge := (tendsto_atTop.mp hwidth) ((C : ℝ) + 1)
  obtain ⟨N, hNconstant, hNlarge⟩ := (hconstant.and hlarge).exists
  rw [hNconstant] at hNlarge
  linarith

-- the first unbounded first-half edge has only stabilized primitive lengths before it.
theorem first_unbounded_anchored_chain_length (q : ℕ)
    (lengths : ℕ → ℕ → ℕ) (hmono : ∀ j, Monotone (fun N => lengths N j))
    (weight : ℕ → ℤ)
    (hwidth : Tendsto (fun N =>
      ((∑ j ∈ Finset.Icc 1 (q - 1), (lengths N j : ℤ) * weight j : ℤ) : ℝ)) atTop atTop) :
    ∃ b : ℕ, 0 < b ∧ b < q ∧ Tendsto (fun N => lengths N b) atTop atTop ∧
      ∀ j : ℕ, 0 < j → j < b → ∃ r : ℕ, ∀ᶠ N in atTop, lengths N j = r := by
  classical
  obtain ⟨j, hj, hdiv⟩ := unbounded_width_has_unbounded_chain_length
    (Finset.Icc 1 (q - 1)) lengths hmono weight hwidth
  obtain ⟨hj₀, hjq⟩ := Finset.mem_Icc.mp hj
  let test : ℕ → Prop := fun b => 0 < b ∧ b < q ∧ Tendsto (fun N => lengths N b) atTop atTop
  have hex : ∃ b, test b := ⟨j, by omega, by omega, hdiv⟩
  let b := Nat.find hex
  obtain ⟨hb₀, hbq, hbdiv⟩ := Nat.find_spec hex
  refine ⟨b, hb₀, hbq, hbdiv, ?_⟩
  intro i hi₀ hib
  obtain hstable | hdivi := anchored_monotone_length_dichotomy (fun N => lengths N i) (hmono i)
  · exact hstable
  · exact False.elim (Nat.find_min hex hib ⟨hi₀, by omega, hdivi⟩)

end KumarNivat
