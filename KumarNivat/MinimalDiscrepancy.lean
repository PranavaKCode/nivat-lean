import KumarNivat.LatticeConvexity
import KumarNivat.PatternRestriction
import Mathlib.Data.Finset.Powerset

namespace KumarNivat

-- an inclusion-minimal discrepancy minimizer compares against every proper convex subwindow.
def MinimalDiscrepancyWindow {A : Type*} (c : Site → A) (R S : Finset Site) : Prop :=
  S ⊆ R ∧ S.Nonempty ∧ LatticeConvex S ∧ discrepancy c S ≤ 0 ∧
    ∀ T : Finset Site, T ⊂ S → T.Nonempty → LatticeConvex T → discrepancy c S < discrepancy c T

-- the finite powerset supplies the actual minimizing set; no extremality premise is assumed.
theorem exists_minimal_discrepancy_window {A : Type*} (c : Site → A)
    (R : Finset Site) (hR : R.Nonempty) (hconv : LatticeConvex R)
    (hlow : complexity c R ≤ R.card) :
    ∃ S : Finset Site, MinimalDiscrepancyWindow c R S := by
  classical
  let F := R.powerset.filter (fun T => T.Nonempty ∧ LatticeConvex T)
  have hRF : R ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr Finset.Subset.rfl, hR, hconv⟩
  obtain ⟨M, hMF, hMmin⟩ := F.exists_min_image (discrepancy c) ⟨R, hRF⟩
  let G := F.filter (fun T => discrepancy c T = discrepancy c M)
  have hMG : M ∈ G := Finset.mem_filter.mpr ⟨hMF, rfl⟩
  obtain ⟨S, hSG, hScard⟩ := G.exists_min_image Finset.card ⟨M, hMG⟩
  obtain ⟨hSF, hδ⟩ := Finset.mem_filter.mp hSG
  obtain ⟨hSpower, hSne, hSconv⟩ := Finset.mem_filter.mp hSF
  have hSR : S ⊆ R := Finset.mem_powerset.mp hSpower
  have hδR : discrepancy c R ≤ 0 := by unfold discrepancy; omega
  have hδS : discrepancy c S ≤ discrepancy c R := by rw [hδ]; exact hMmin R hRF
  refine ⟨S, hSR, hSne, hSconv, hδS.trans hδR, ?_⟩
  intro T hTS hTne hTconv
  have hTF : T ∈ F := Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (hTS.1.trans hSR), hTne, hTconv⟩
  have hle : discrepancy c S ≤ discrepancy c T := by rw [hδ]; exact hMmin T hTF
  apply lt_of_le_of_ne hle
  intro he
  have hTG : T ∈ G := Finset.mem_filter.mpr ⟨hTF, he.symm.trans hδ⟩
  have hcard₁ := hScard T hTG
  have hcard₂ := Finset.card_lt_card hTS
  omega

end KumarNivat
