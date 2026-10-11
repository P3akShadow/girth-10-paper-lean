import SparseNormalization

/-! Proposition 14 (`prop:sparse-bounds`). The proof follows the paper's
counting inequality, twin-class preparation, critical-bag normalization,
five degree cases, and the final two-merge swap, in that order. -/
namespace Paper
open Finset
variable {V : Type*} [DecidableEq V] {S : Finset V}

lemma degree_le_sparse_threshold {d : ℕ} (hd : 3 ≤ d) : d ≤ (d - 1)^2 := by
  have h1 : d - 1 + 1 = d := by omega
  have h2 : d - 1 ≥ 2 := by omega
  nlinarith [Nat.zero_le ((d - 1) * (d - 3))]

/-- Proposition 14, with a supplied witnessing sequence of width w. -/
theorem sparse_bounds_of_sequence (G : SimpleGraph V) {d w s : ℕ} (hd : 3 ≤ d)
    (hdeg : MaxDegree G S d) (hseq : HasWidths (.ofGraph G) S w s) :
    sparseTwinWidth (.ofGraph G) S ≤ max (w + 1) ((d - 1)^2) ∧
    sparseTwinWidth (.ofGraph G) S ≤ max w ((d - 1)^2 + 1) := by
  -- Merge all original twin classes first (Lemma 13); the prefix has no red edges.
  obtain ⟨P,hpre,hmono,hsat,hcont⟩ := prepare_twins G hdeg ⊥ (monoTwinBags_bot G) hseq
  -- The remaining critical bags in this prefix are isolated two-vertex components.
  obtain ⟨Q,hpre',hsatQ,hncQ,hcontQ⟩ := prepare_critical G hdeg P hsat (hmono.bounded hdeg) hcont
  have hprefix := hpre.trans hpre'
  -- Eliminate every newly created critical bag at the following step.
  -- For the second bound, interchange exactly the two merges specified in the paper.
  obtain ⟨hfirst,hsecond⟩ := normalize_sparse G hd hdeg Q hsatQ hncQ hcontQ
  have hd1 : d ≤ max (w + 1) ((d - 1)^2) := (degree_le_sparse_threshold hd).trans (le_max_right _ _)
  have hd2 : d ≤ max w ((d - 1)^2 + 1) :=
    ((degree_le_sparse_threshold hd).trans (Nat.le_succ _)).trans (le_max_right _ _)
  exact ⟨sparseTwinWidth_le (hprefix.append (Nat.zero_le _) hd1 hfirst),
    sparseTwinWidth_le (hprefix.append (Nat.zero_le _) hd2 hsecond)⟩

/-- Proposition 14: both bounds for a graph of maximum degree at most d ≥ 3. -/
theorem sparse_bounds (G : SimpleGraph V) {d : ℕ} (hd : 3 ≤ d) (hdeg : MaxDegree G S d) :
    sparseTwinWidth (.ofGraph G) S ≤ max (twinWidth (.ofGraph G) S + 1) ((d - 1)^2) ∧
    sparseTwinWidth (.ofGraph G) S ≤ max (twinWidth (.ofGraph G) S) ((d - 1)^2 + 1) := by
  obtain ⟨s,hs⟩ := twinWidth_witness (.ofGraph G) S
  exact sparse_bounds_of_sequence G hd hdeg hs

end Paper
