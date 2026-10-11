import Proposition14SparseBounds

/-! Corollary 15 (`cor:cubic-sparse`). -/
namespace Paper
variable {V : Type*} [DecidableEq V] {S : Finset V}

/-- For subcubic graphs with twin-width at least five the two widths coincide. -/
theorem cubic_sparse_of_twinWidth (G : SimpleGraph V) (hdeg : MaxDegree G S 3)
    (hw : 5 ≤ twinWidth (.ofGraph G) S) :
    sparseTwinWidth (.ofGraph G) S = twinWidth (.ofGraph G) S := by
  have hbound := (sparse_bounds G (by omega : 3 ≤ 3) hdeg).2
  have hle := twinWidth_le_sparseTwinWidth (.ofGraph G) S
  norm_num at hbound
  omega

/-- The equivalent sparse-width formulation in Corollary 15. -/
theorem cubic_sparse_of_sparseTwinWidth (G : SimpleGraph V) (hdeg : MaxDegree G S 3)
    (hw : 6 ≤ sparseTwinWidth (.ofGraph G) S) :
    sparseTwinWidth (.ofGraph G) S = twinWidth (.ofGraph G) S := by
  have hbound := (sparse_bounds G (by omega : 3 ≤ 3) hdeg).2
  have hle := twinWidth_le_sparseTwinWidth (.ofGraph G) S
  norm_num at hbound
  omega

end Paper
