module

public import KumarNivat.LineFaceGeometry

@[expose] public section

namespace KumarNivat

-- the coefficient block and the real newton face come from the same actual exposed support.
theorem exists_actual_exposed_geometric_face_data {K : Type*} [CommRing K]
    (f : Laurent K) (ν : Site →+ ℤ) (hν : ν ≠ 0) (m : ℤ)
    (hmin : ∀ u ∈ f.coeff.support, m ≤ ν u) (E p : Site) (hp : p ≠ 0)
    (hprimitive : Int.gcd p.1 p.2 = 1) (htangent : ν p = 0)
    (hE : E ∈ f.coeff.support) (hlevel : ν E = m) :
    ∃ q₀ : Site, ∃ t : ℕ, ∃ α : Fin (t + 1) → K,
      α 0 ≠ 0 ∧ α (Fin.last t) ≠ 0 ∧ ν q₀ = m ∧
        q₀ ∈ f.coeff.support ∧ q₀ + (t : ℤ) • p ∈ f.coeff.support ∧
        exposedOperator f ν m = lineOperator q₀ p t α ∧
        f = lineOperator q₀ p t α + (f - exposedOperator f ν m) ∧
        normalFace (latticeHull f.coeff.support) (latticeNormal ν) (m : ℝ) =
          lineInterval (latticeEmbedding q₀) (latticeEmbedding p) 0 (t : ℝ) := by
  obtain ⟨q₀, t, α, hfirst, hlast, hq₀, hq₀mem, hq₁mem, hface, hpoints, hdecomp, _hstrict⟩ :=
    exists_actual_exposed_face_data f ν hν m hmin E p hp hprimitive htangent hE hlevel
  exact ⟨q₀, t, α, hfirst, hlast, hq₀, hq₀mem, hq₁mem, hface, hdecomp,
    normalFace_latticeHull_eq_lineInterval f.coeff.support ν m hmin q₀ p t hq₀mem hq₁mem hq₀ htangent hpoints⟩

end KumarNivat
