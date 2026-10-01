import KumarNivat.OrientedNormals
import KumarNivat.AnnihilatorDirections

namespace KumarNivat

-- this is the paired-direction conclusion of the quoted structural theorem.
def HasPairedOneSidedDirection {A : Type*} [TopologicalSpace A] (c : Site → A) : Prop :=
  ∃ ell : Site →+ ℝ, OneSidedNonexpansive c ell ∧ OneSidedNonexpansive c (-ell)

-- identical inward half-planes preserve the actual two distinct orbit-closure witnesses.
theorem OneSidedNonexpansive.congr_halfplanes {A : Type*} [TopologicalSpace A]
    {c : Site → A} {ell μ : Site →+ ℝ} (hNE : OneSidedNonexpansive c ell)
    (hhalf : ∀ g : Site, 0 ≤ ell g ↔ 0 ≤ μ g) : OneSidedNonexpansive c μ := by
  obtain ⟨_hell, x, y, hx, hy, hxy, hagree⟩ := hNE
  have hμ : μ ≠ 0 := by
    intro hz
    apply hxy
    funext g
    exact hagree g ((hhalf g).mpr (by rw [hz]; exact le_rfl))
  exact ⟨hμ, x, y, hx, hy, hxy, fun g hg => hagree g ((hhalf g).mpr hg)⟩

-- a positive scalar changes normal units without changing the side of the boundary.
theorem positive_scalar_same_halfplane (ell μ : Site →+ ℝ) (κ : ℝ) (hκ : 0 < κ)
    (hrep : ∀ g : Site, ell g = κ * μ g) : ∀ g : Site, 0 ≤ ell g ↔ 0 ≤ μ g := by
  intro g
  rw [hrep g]
  constructor
  · intro hg
    by_contra! hn
    have hneg := mul_neg_of_pos_of_neg hκ hn
    exact not_lt_of_ge hg hneg
  · intro hg
    exact mul_nonneg (le_of_lt hκ) hg

-- the integer face is exactly the lattice points of the corresponding real hull slice.
theorem mem_lowerLatticeFace_iff_hull_slice (S : Finset Site) (hS : LatticeConvex S)
    (ν : Site →+ ℤ) (m : ℤ) (u : Site) :
    u ∈ lowerLatticeFace S ν m ↔ latticeEmbedding u ∈ latticeHull S ∧
      latticeNormal ν (latticeEmbedding u) = (m : ℝ) := by
  constructor
  · intro hu
    obtain ⟨hum, he⟩ := Finset.mem_filter.mp hu
    refine ⟨subset_convexHull ℝ _ ⟨u, hum, rfl⟩, ?_⟩
    rw [latticeNormal_embedding, he]
  · rintro ⟨hu, he⟩
    apply Finset.mem_filter.mpr
    rw [latticeNormal_embedding] at he
    exact ⟨hS u hu, Int.cast_injective he⟩

-- a supporting bound on all lattice generators holds on the entire real polygon.
theorem lower_face_hull_bound (S : Finset Site) (ν : Site →+ ℤ) (m : ℤ)
    (hmin : ∀ u ∈ S, m ≤ ν u) :
    ∀ x ∈ latticeHull S, (m : ℝ) ≤ latticeNormal ν x := by
  have hsub : latticeEmbedding '' (S : Set Site) ⊆ {x : RealPlane | (m : ℝ) ≤ latticeNormal ν x} := by
    rintro _ ⟨u, hu, rfl⟩
    change (m : ℝ) ≤ latticeNormal ν (latticeEmbedding u)
    rw [latticeNormal_embedding]
    exact_mod_cast hmin u hu
  exact convexHull_min hsub ((convex_Ici (m : ℝ)).linear_preimage (latticeNormal ν))

-- a supporting pair occupies two distinct sites of its corresponding integer face.
theorem supporting_pair_two_le_face_card (S : Finset Site) (ν : Site →+ ℤ)
    (u v : Site) (hu : u ∈ S) (hv : v ∈ S) (huv : u ≠ v) (he : ν u = ν v) :
    2 ≤ (lowerLatticeFace S ν (ν u)).card := by
  have huf : u ∈ lowerLatticeFace S ν (ν u) := Finset.mem_filter.mpr ⟨hu, rfl⟩
  have hvf : v ∈ lowerLatticeFace S ν (ν u) := Finset.mem_filter.mpr ⟨hv, he.symm⟩
  have hcard := Finset.one_lt_card.mpr ⟨u, huf, v, hvf, huv⟩
  omega

-- the paired input now supplies the paper's actual primitive factor direction and opposite edges.
theorem paired_direction_supporting_data (c : Site → ℤ) (R S : Finset Site)
    (hgen : GeneratingPolygon c R S) (hs : List Site) (hdirs : ∀ h ∈ hs, h ≠ 0)
    (hann : laurentAct (differenceProduct hs) c = 0) (hpair : HasPairedOneSidedDirection c) :
    ∃ p h : Site, p ≠ 0 ∧ Int.gcd p.1 p.2 = 1 ∧ h ∈ hs ∧ h ≠ 0 ∧ determinant p h = 0 ∧
      OneSidedNonexpansive c (integerNormalAsReal (directionNormal p)) ∧
      OneSidedNonexpansive c (-integerNormalAsReal (directionNormal p)) ∧
      ∃ m M : ℤ, (∀ u ∈ S, m ≤ directionNormal p u ∧ directionNormal p u ≤ M) ∧
        2 ≤ (lowerLatticeFace S (directionNormal p) m).card ∧
        2 ≤ (lowerLatticeFace S (-directionNormal p) (-M)).card := by
  obtain ⟨ell, hNE, hNEneg⟩ := hpair
  obtain ⟨p, hp, hprimitive, κ, hκ, hrep⟩ :=
    oneSidedNonexpansive_oriented_primitive_normal c R S hgen ell hNE
  let ν := directionNormal p
  let μ := integerNormalAsReal ν
  have hrep' (g : Site) : ell g = κ * μ g := hrep g
  have hhalf := positive_scalar_same_halfplane ell μ κ hκ hrep'
  have hμNE := hNE.congr_halfplanes hhalf
  have hrepneg (g : Site) : (-ell) g = κ * (-μ) g := by
    change -ell g = κ * (-μ g)
    rw [hrep' g]
    ring
  have hμNEneg := hNEneg.congr_halfplanes (positive_scalar_same_halfplane (-ell) (-μ) κ hκ hrepneg)
  obtain ⟨h, hh, hhtangent⟩ := oneSidedNonexpansive_difference_product_direction c hs hann μ hμNE
  have hdet : determinant p h = 0 := by
    change (directionNormal p h : ℝ) = 0 at hhtangent
    exact Int.cast_eq_zero.mp hhtangent
  obtain ⟨u, hu, v, hv, huv, he, hmin⟩ := oneSidedNonexpansive_supporting_pair c R S hgen μ hμNE
  obtain ⟨U, hU, V, hV, hUV, hE, hmax⟩ :=
    oneSidedNonexpansive_supporting_pair c R S hgen (-μ) hμNEneg
  have heInt : ν u = ν v := by
    change (ν u : ℝ) = (ν v : ℝ) at he
    exact_mod_cast he
  have hEInt : (-ν) U = (-ν) V := by
    change -(ν U : ℝ) = -(ν V : ℝ) at hE
    exact_mod_cast hE
  have hminInt (w : Site) (hw : w ∈ S) : ν u ≤ ν w := by
    have hb := hmin w hw
    change (ν u : ℝ) ≤ (ν w : ℝ) at hb
    exact_mod_cast hb
  have hmaxInt (w : Site) (hw : w ∈ S) : ν w ≤ ν U := by
    have hb := hmax w hw
    change -(ν U : ℝ) ≤ -(ν w : ℝ) at hb
    exact_mod_cast (neg_le_neg_iff.mp hb)
  exact ⟨p, h, hp, hprimitive, hh, hdirs h hh, hdet, hμNE, hμNEneg,
    ν u, ν U, fun w hw => ⟨hminInt w hw, hmaxInt w hw⟩,
    supporting_pair_two_le_face_card S ν u v hu hv huv heInt,
    supporting_pair_two_le_face_card S (-ν) U V hU hV hUV hEInt⟩

end KumarNivat
