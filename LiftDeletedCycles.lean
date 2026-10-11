import LiftCycles
import RegularSeed

/-! Deleting an edge of a shortest cycle removes at least one of the cycles
counted in Lemma 8. The count uses all roots and orientations uniformly. -/
namespace Paper
open Finset SimpleGraph
variable {V : Type*} [DecidableEq V] [Fintype V]

omit [DecidableEq V] in
lemma rootedCycles_mono {G H : SimpleGraph V} (hsub : H ≤ G) (n : ℕ) :
    rootedCycles H n ⊆ rootedCycles G n := by
  intro c hc
  have hh := (mem_rootedCycles H).mp hc
  exact (mem_rootedCycles G).mpr ⟨hh.1,fun i j hij => hsub (hh.2 i j hij)⟩

omit [DecidableEq V] in
lemma rootedCycles_nonempty_of_cycle (G : SimpleGraph V) {n : ℕ}
    (hp : ∃ a, ∃ p : G.Walk a a, p.IsCycle ∧ p.length = n+3) :
    (rootedCycles G n).Nonempty := by
  obtain ⟨f⟩ := (cycleGraph_isContained_iff (by omega : 2 < n+3)).mpr hp
  exact ⟨f.toHom,(mem_rootedCycles G).mpr ⟨f.injective,fun _ _ hij => f.toHom.map_rel hij⟩⟩

omit [DecidableEq V] in
lemma shortest_rootedCycles_nonempty (G : SimpleGraph V) (hcyc : ¬ G.IsAcyclic) :
    (rootedCycles G (G.girth-3)).Nonempty := by
  have hg := three_le_girth hcyc
  obtain ⟨a,p,hp,hlen⟩ := exists_girth_eq_length.mpr hcyc
  apply rootedCycles_nonempty_of_cycle G
  exact ⟨a,p,hp,by omega⟩

lemma deleting_cycle_edge_reduces_count (G : SimpleGraph V) {n : ℕ} {c : Fin (n+3) → V}
    (hc : RootedCycle G n c) (x y : V)
    (he : s(x,y) ∈ ((cycleGraph.cycle n).map hc.hom).edges) :
    (rootedCycles (edgeDeleted G x y) n).card < (rootedCycles G n).card := by
  classical
  apply card_lt_card
  apply ssubset_iff_subset_ne.mpr
  have hsub : edgeDeleted G x y ≤ G := fun _ _ hh => hh.1
  refine ⟨rootedCycles_mono hsub n,?_⟩
  intro heq
  have hcH := (mem_rootedCycles (edgeDeleted G x y)).mp (heq ▸ (mem_rootedCycles G).mpr hc)
  let pH := (cycleGraph.cycle n).map hcH.hom
  have hedges : pH.edges = ((cycleGraph.cycle n).map hc.hom).edges := by
    simp only [pH,Walk.edges_map]
    rfl
  have hxy : (edgeDeleted G x y).Adj x y := pH.adj_of_mem_edges (hedges ▸ he)
  exact hxy.2 (Or.inl ⟨rfl,rfl⟩)

/-- Choose an edge on a shortest cycle. Deletion strictly reduces the number
of cycles at the old girth, before the paper's signing average is applied. -/
theorem exists_shortest_edge_fewer_cycles (G : SimpleGraph V) (hcyc : ¬ G.IsAcyclic) :
    ∃ x y, (∃ a, ∃ p : G.Walk a a,
      p.IsCycle ∧ s(x,y) ∈ p.edges ∧ p.length = G.girth) ∧
      (rootedCycles (edgeDeleted G x y) (G.girth-3)).card < shortestCycleCount G := by
  obtain ⟨c,hc⟩ := shortest_rootedCycles_nonempty G hcyc
  have hroot := (mem_rootedCycles G).mp hc
  let p := (cycleGraph.cycle (G.girth-3)).map hroot.hom
  have hp : p.IsCycle := hroot.isCycle
  have hlen : p.length = G.girth := by
    have hg := three_le_girth hcyc
    simp only [p,Walk.length_map,cycleGraph.length_cycle]
    omega
  have hne : p.edges ≠ [] := by
    intro hh
    have hzero := congrArg List.length hh
    have hthree := hp.isCircuit.three_le_length
    simp only [Walk.length_edges,List.length_nil] at hzero
    omega
  obtain ⟨e,he⟩ := List.exists_mem_of_ne_nil _ hne
  induction e using Sym2.inductionOn with | _ x y =>
    exact ⟨x,y,⟨_,p,hp,he,hlen⟩,deleting_cycle_edge_reduces_count G hroot x y he⟩

end Paper
