import Corollary15CubicSparse
import SubcubicReductions

/-! Corollary 16: minimum-order subcubic graphs of twin-width at least six
are cubic and have girth at least five. Minimality is over all smaller
finite simple graphs, not just induced subgraphs of the given graph. -/

namespace Paper
open Finset
universe u
variable {V : Type u} [DecidableEq V] {S : Finset V}

/-- Forget the edge colors of a trigraph. -/
def Trigraph.underlying (T : Trigraph V) : SimpleGraph V := T.black ⊔ T.red

omit [DecidableEq V] in
lemma underlying_supported (T : Trigraph V) (S : Finset V) :
    SupportedBy T (.ofGraph T.underlying) S := by
  intro a _ b _ hab
  exact Or.inl hab

lemma sparseTwinWidth_underlying (T : Trigraph V) (S : Finset V) :
    sparseTwinWidth (.ofGraph T.underlying) S = sparseTwinWidth T S := by
  apply le_antisymm
  · apply sparseTwinWidth_supported
    intro a _ b _ hab
    simpa [Trigraph.ofGraph, Trigraph.underlying] using hab
  · exact sparseTwinWidth_supported (underlying_supported T S)

lemma quotient_underlying_degree (T : Trigraph V) (P : Partition S)
    {A : Finset V} (hA : A ∈ P.parts) :
    (graphNeighbors ((partitionExpansion P).quotient T).underlying P.parts A).card =
      totalDegree T P A := by
  classical
  congr 1
  ext B
  simp only [graphNeighbors, neighbors, mem_filter]
  constructor
  · rintro ⟨hB, hadj⟩
    have hne : A ≠ B := hadj.ne
    exact ⟨hB, hne.symm,
      ((partitionExpansion P).quotient_adjacent T hA hB hne).mp hadj⟩
  · rintro ⟨hB, hne, hadj⟩
    exact ⟨hB, ((partitionExpansion P).quotient_adjacent T hA hB hne.symm).mpr hadj⟩

/-- Continue a bounded prefix using a sparse-width witness of the underlying
simple quotient. This justifies the final inequality in the paper proof. -/
lemma sparseTwinWidth_le_prefix_quotient (T : Trigraph V) {P : Partition S} {b : ℕ}
    (hp : Prefix T b b ⊥ P) :
    sparseTwinWidth T S ≤
      max b (sparseTwinWidth (.ofGraph ((partitionExpansion P).quotient T).underlying) P.parts) := by
  let Q := (partitionExpansion P).quotient T
  let s := sparseTwinWidth (.ofGraph Q.underlying) P.parts
  obtain ⟨w, hw⟩ := sparseTwinWidth_witness (.ofGraph Q.underlying) P.parts
  have hc : Continuation T s s P := by
    have h := (partitionExpansion P).continuation T ((underlying_supported Q P.parts).continuation hw)
    simpa only [partitionExpansion_bot] using h
  exact sparseTwinWidth_le (hp.append (le_max_left _ _) (le_max_left _ _)
    (hc.monoBounds (le_max_right _ _) (le_max_right _ _)))

/-- Every smaller subcubic graph has twin-width below the specified threshold.
The finite set is its vertex set, so the ambient type need not be finite. -/
def SubcubicOrderMinimal (S : Finset V) (k : ℕ) : Prop :=
  ∀ (W : Type u) [DecidableEq W] (H : SimpleGraph W) (U : Finset W),
    U.card < S.card → MaxDegree H U 3 → twinWidth (.ofGraph H) U < k

lemma no_subcubicReduction_of_minimal (G : SimpleGraph V) {k : ℕ}
    (hk : 6 ≤ k) (hw : k ≤ twinWidth (.ofGraph G) S)
    (hmin : SubcubicOrderMinimal S k) : ¬ SubcubicReduction G S := by
  rintro ⟨P, hp, hb, hcard⟩
  let H := ((partitionExpansion P).quotient (.ofGraph G)).underlying
  have hdeg : MaxDegree H P.parts 3 := by
    intro A hA
    rw [quotient_underlying_degree (.ofGraph G) P hA]
    exact (hb A hA).2
  have hsmall := hmin (Finset V) H P.parts hcard hdeg
  have hprefix := sparseTwinWidth_le_prefix_quotient (.ofGraph G) hp
  have hle := twinWidth_le_sparseTwinWidth (.ofGraph G) S
  have hbound := (sparse_bounds H (by omega : 3 ≤ 3) hdeg).2
  norm_num at hbound
  change sparseTwinWidth (.ofGraph G) S ≤ max 5 (sparseTwinWidth (.ofGraph H) P.parts) at hprefix
  omega

lemma minimum_subcubic_regular (G : SimpleGraph V) {k : ℕ}
    (hdeg : MaxDegree G S 3) (hk : 6 ≤ k) (hw : k ≤ twinWidth (.ofGraph G) S)
    (hmin : SubcubicOrderMinimal S k) : Regular G S 3 := by
  have hcard : 1 < S.card := by
    have hbound := twinWidth_le (widths_exist (.ofGraph G) S)
    omega
  intro v hv
  have hvle := hdeg v hv
  by_contra hne
  exact no_subcubicReduction_of_minimal G hk hw hmin
    (subcubicReduction_low_degree G hdeg hcard hv (by omega))

lemma minimum_subcubic_cycle_length [Fintype V] (G : SimpleGraph V) {k : ℕ}
    (hdeg : MaxDegree G univ 3) (hk : 6 ≤ k) (hw : k ≤ twinWidth (.ofGraph G) univ)
    (hmin : SubcubicOrderMinimal (univ : Finset V) k)
    {v : V} (p : G.Walk v v) (hp : p.IsCycle) : 5 ≤ p.length := by
  have hno := no_subcubicReduction_of_minimal G hk hw hmin
  by_contra hshort
  have hthree := hp.three_le_length
  have hab := p.adj_getVert_succ (by omega : 0 < p.length)
  have hbc := p.adj_getVert_succ (by omega : 1 < p.length)
  rcases (show p.length = 3 ∨ p.length = 4 by omega) with hlen | hlen
  · have hca : G.Adj (p.getVert 2) (p.getVert 0) := by
      have h := p.adj_getVert_succ (by omega : 2 < p.length)
      simpa only [show 2 + 1 = p.length by omega,
        SimpleGraph.Walk.getVert_length, SimpleGraph.Walk.getVert_zero] using h
    exact hno (subcubicReduction_triangle G hdeg
      (mem_univ _) (mem_univ _) (mem_univ _) hab hbc hca)
  · have hcd := p.adj_getVert_succ (by omega : 2 < p.length)
    have hda : G.Adj (p.getVert 3) (p.getVert 0) := by
      have h := p.adj_getVert_succ (by omega : 3 < p.length)
      simpa only [show 3 + 1 = p.length by omega,
        SimpleGraph.Walk.getVert_length, SimpleGraph.Walk.getVert_zero] using h
    have hac : p.getVert 0 ≠ p.getVert 2 := by
      intro he
      have := hp.getVert_injOn' (by simp only [Set.mem_ofPred_eq]; omega)
        (by simp only [Set.mem_ofPred_eq]; omega) he
      omega
    have hbd : p.getVert 1 ≠ p.getVert 3 := by
      intro he
      have := hp.getVert_injOn' (by simp only [Set.mem_ofPred_eq]; omega)
        (by simp only [Set.mem_ofPred_eq]; omega) he
      omega
    exact hno (subcubicReduction_four_cycle G hdeg
      (mem_univ _) (mem_univ _) (mem_univ _) (mem_univ _) hab hbc hcd hda hac hbd)

/-- Corollary 16, with the same proof for every threshold k >= 6.
Extended girth uses infinity for acyclic graphs, matching the graph-theoretic
convention. No connectedness assumption is required. -/
theorem minimum_subcubic_cubic_girth [Fintype V] (G : SimpleGraph V) {k : ℕ}
    (hdeg : MaxDegree G univ 3) (hk : 6 ≤ k) (hw : k ≤ twinWidth (.ofGraph G) univ)
    (hmin : SubcubicOrderMinimal (univ : Finset V) k) :
    5 ≤ G.egirth ∧ Regular G univ 3 := by
  refine ⟨SimpleGraph.le_egirth.mpr ?_, minimum_subcubic_regular G hdeg hk hw hmin⟩
  intro v p hp
  exact_mod_cast minimum_subcubic_cycle_length G hdeg hk hw hmin p hp

end Paper
