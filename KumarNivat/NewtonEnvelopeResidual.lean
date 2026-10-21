module

public import KumarNivat.NewtonEnvelopeSaturation

@[expose] public section

namespace KumarNivat

open scoped Pointwise

-- every dilation of at least one retains the original hull as an explicit minkowski summand.
theorem convex_dilate_translate_minkowski_residual (P : Set RealPlane) (hP : Convex ℝ P)
    (n : ℝ) (hn : 1 ≤ n) (E : RealPlane) :
    (fun z => E + n • z) '' P = P + (fun z => E + (n - 1) • z) '' P := by
  have hscalar : n • P = P + (n - 1) • P := by
    calc
      n • P = (1 + (n - 1)) • P := by congr 1; ring
      _ = P + (n - 1) • P := by
        rw [hP.add_smul zero_le_one (by linarith : 0 ≤ n - 1), one_smul]
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hpoint : n • z ∈ P + (n - 1) • P := by
      rw [← hscalar]
      exact Set.smul_mem_smul_set hz
    obtain ⟨x, hx, _y, ⟨y, hy, rfl⟩, he⟩ := Set.mem_add.mp hpoint
    refine Set.mem_add.mpr ⟨x, hx, E + (n - 1) • y, ⟨y, hy, rfl⟩, ?_⟩
    change x + (E + (n - 1) • y) = E + n • z
    change x + (n - 1) • y = n • z at he
    rw [← he]
    abel
  · intro hw
    obtain ⟨x, hx, _y, ⟨y, hy, rfl⟩, rfl⟩ := Set.mem_add.mp hw
    have hpoint : x + (n - 1) • y ∈ n • P := by
      rw [hscalar]
      exact Set.add_mem_add hx (Set.smul_mem_smul_set hy)
    obtain ⟨z, hz, he⟩ := hpoint
    refine ⟨z, hz, ?_⟩
    change E + n • z = x + (E + (n - 1) • y)
    change n • z = x + (n - 1) • y at he
    rw [he]
    abel

end KumarNivat
