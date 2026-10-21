module

public import KumarNivat.TuplePatternPeriods
public import KumarNivat.GeneratedHalfplanes

@[expose] public section

namespace KumarNivat

-- a single legal extension forces agreement on the full window for both inherited configurations.
theorem agreement_of_unique_observed_extension {A : Type*} (c x y : Site → A)
    (hx : LanguageContained x c) (hy : LanguageContained y c)
    (S T : Finset Site) (hTS : T ⊆ S) (g : Site)
    (hbase : ∀ u ∈ T, x (g + u) = y (g + u))
    (hunique : extensionCount c S T hTS (legalTranslatedPattern c x hx T g) = 1) :
    ∀ u ∈ S, x (g + u) = y (g + u) := by
  let base := legalTranslatedPattern c x hx T g
  let qx := legalTranslatedPattern c x hx S g
  let qy := legalTranslatedPattern c y hy S g
  have hqx : legalPatternRestriction c S T hTS qx = base := by
    apply Subtype.ext
    rfl
  have hqy : legalPatternRestriction c S T hTS qy = base := by
    apply Subtype.ext
    funext u
    exact (hbase u.val u.property).symm
  have hcount : {q : patterns c S | legalPatternRestriction c S T hTS q = base}.ncard = 1 := hunique
  obtain ⟨q, hfiber⟩ := Set.ncard_eq_one.mp hcount
  have hqx' : qx = q := Set.mem_singleton_iff.mp (hfiber ▸ hqx)
  have hqy' : qy = q := Set.mem_singleton_iff.mp (hfiber ▸ hqy)
  have he := congrArg Subtype.val (hqx'.trans hqy'.symm)
  intro u hu
  exact congrFun he ⟨u, hu⟩

-- a generated final endpoint propagates an edge-block seed along every fitting forward translate.
theorem generated_endpoint_agreement_tail {A : Type*} (c x y : Site → A)
    (hx : LanguageContained x c) (hy : LanguageContained y c)
    (S F : Finset Site) (q₀ p E : Site) (t : ℕ)
    (hendpoint : q₀ + (t : ℤ) • p ∈ S)
    (hgen : GeneratedSite c S (q₀ + (t : ℤ) • p))
    (hface : ∀ u ∈ F, ∃ i : Fin (t + 1), u = q₀ + (i.val : ℤ) • p)
    (n₀ : ℤ)
    (hinterior : ∀ n : ℤ, n₀ ≤ n → ∀ u ∈ S \ F, x (E + n • p + u) = y (E + n • p + u))
    (hseed : ∀ i : Fin t, x (E + q₀ + (n₀ + (i.val : ℤ)) • p) =
      y (E + q₀ + (n₀ + (i.val : ℤ)) • p)) :
    ∀ n : ℤ, n₀ ≤ n → x (E + q₀ + n • p) = y (E + q₀ + n • p) := by
  have hforward (k : ℕ) : x (E + q₀ + (n₀ + (k : ℤ)) • p) =
      y (E + q₀ + (n₀ + (k : ℤ)) • p) := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      by_cases hkt : k < t
      · exact hseed ⟨k, hkt⟩
      · have htk : t ≤ k := by omega
        let base : ℤ := n₀ + ((k - t : ℕ) : ℤ)
        have hagree : ∀ u ∈ S.erase (q₀ + (t : ℤ) • p),
            x (E + base • p + u) = y (E + base • p + u) := by
          intro u hu
          obtain ⟨hune, hum⟩ := Finset.mem_erase.mp hu
          by_cases huf : u ∈ F
          · obtain ⟨i, he⟩ := hface u huf
            have hit : i.val < t := by
              have hi := i.isLt
              have hne : i.val ≠ t := by
                intro hei
                exact hune (he.trans (by rw [hei]))
              omega
            have hindex : k - t + i.val < k := by omega
            have hsite : E + base • p + u = E + q₀ + (n₀ + ((k - t + i.val : ℕ) : ℤ)) • p := by
              rw [he]
              dsimp [base]
              simp only [add_smul]
              abel
            rw [hsite]
            exact ih _ hindex
          · exact hinterior base (by dsimp [base]; omega) u (Finset.mem_sdiff.mpr ⟨hum, huf⟩)
        have he := generatedSite_inherited c x y S (q₀ + (t : ℤ) • p) hendpoint hgen hx hy
          (E + base • p) hagree
        have hbase : base + (t : ℤ) = n₀ + (k : ℤ) := by dsimp [base]; omega
        have hsite : (E + base • p) + (q₀ + (t : ℤ) • p) = E + q₀ + (n₀ + (k : ℤ)) • p := by
          rw [← hbase, add_smul base (t : ℤ) p]
          ac_rfl
        simpa only [hsite] using he
  intro n hn
  have he : n₀ + (((n - n₀).toNat : ℕ) : ℤ) = n := by omega
  simpa only [he] using hforward (n - n₀).toNat

end KumarNivat
