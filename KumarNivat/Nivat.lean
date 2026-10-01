import KumarNivat.IntegerWedgeSelectionProof

namespace KumarNivat

universe u

-- the manuscript's selection theorem closes the full finite-alphabet conjecture on the original integer lattice.
theorem nivat : FullNivat.{u} :=
  fullNivat_of_integer_wedge_selection integer_wedge_selection

end KumarNivat
