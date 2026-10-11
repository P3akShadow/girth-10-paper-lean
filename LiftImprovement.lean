import LiftCycleDecomposition
import LiftDeletedCycles
import LiftIteration

/-! Lemma 8: choose a signing by the paper's shortest-cycle expectation,
then iterate the strict decrease of the finite shortest-cycle count. -/

namespace Paper
open Finset SimpleGraph
variable {V : Type*} [DecidableEq V] [Fintype V]

lemma girthLift_rooted_count_le (G : SimpleGraph V) {x y : V} (hxy : G.Adj x y)
    (ε : Sym2 V → Bool) (n : ℕ) (hlen : n+3 = G.girth) :
    (rootedCycles (girthLift G x y (Signing.ofEdges ε)) n).card ≤
      2 * ((rootedCycles (edgeDeleted G x y) n).filter
        (fun c => signingParity ε (rootedCycleEdges c) = false)).card := by
  classical
  have hs : rootedCycles (girthLift G x y (Signing.ofEdges ε)) n ⊆
      rootedCycles (signedCover (edgeDeleted G x y) (Signing.ofEdges ε)) n := by
    intro c hc
    have hc' := (mem_rootedCycles _).mp hc
    have hcycle := girthLift_cycle_length G hxy (Signing.ofEdges ε) hc'.isCycle
    have hh := hcycle.2 (by simpa only [Walk.length_map,cycleGraph.length_cycle] using hlen)
    exact (mem_rootedCycles _).mpr (horizontal_rooted_cycle G x y (Signing.ofEdges ε) hc' hh)
  exact (card_le_card hs).trans (cover_rooted_count_le G (edgeDeleted G x y)
    (fun _ _ h => h.1) ε n hlen.le)

/-- With the selected edge lying on a shortest cycle, every signing preserves
the girth; only the number of shortest cycles depends on the signing. -/
lemma girthLift_girth_le (G : SimpleGraph V) {d : ℕ} (hd : 2 ≤ d)
    (hr : Regular G univ d) (hc : G.Connected) {x y : V}
    (hshort : ∃ a, ∃ p : G.Walk a a,
      p.IsCycle ∧ s(x,y) ∈ p.edges ∧ p.length = G.girth) (σ : Signing V) :
    G.girth ≤ (girthLift G x y σ).girth := by
  obtain ⟨a,p,hp,he,_⟩ := hshort
  have hxy := p.adj_of_mem_edges he
  have hreg : Regular (girthLift G x y σ) univ d := by
    simpa only [liftVertices_univ] using
      girthLift_regular G univ x y (mem_univ _) (mem_univ _) hxy σ hr
  have hconn := girthLift_connected G x y σ (edgeDeleted_connected G hc hp he)
  obtain ⟨b,q,hq,hlen⟩ := regular_shortest_cycle _ hd hreg hconn
  exact hlen ▸ (girthLift_cycle_length G hxy σ hq).1

/-- The expected surviving count is at most the number of shortest cycles
after deleting xy, which is strictly smaller than the original count. -/
theorem exists_improvingLift (G : SimpleGraph V) {d : ℕ} (hd : 2 ≤ d)
    (hr : Regular G univ d) (hc : G.Connected) : Nonempty (ImprovingLift G) := by
  classical
  obtain ⟨x,y,hshort,hfewer⟩ := exists_shortest_edge_fewer_cycles G
    (regular_not_acyclic G hd hr hc)
  obtain ⟨a,p,hp,he,hlen⟩ := hshort
  have hxy := p.adj_of_mem_edges he
  have hg : 3 ≤ G.girth := hlen ▸ hp.isCircuit.three_le_length
  obtain ⟨ε,hε⟩ := exists_signing_few_surviving_indexed
    (rootedCycles (edgeDeleted G x y) (G.girth-3)) rootedCycleEdges
    (fun c _ => rootedCycleEdges_nonempty c)
  refine ⟨{
    x := x
    y := y
    signing := Signing.ofEdges ε
    shortest := ⟨a,p,hp,he,hlen⟩
    progress := ⟨girthLift_girth_le G hd hr hc ⟨a,p,hp,he,hlen⟩ _,?_⟩ }⟩
  intro heq
  unfold shortestCycleCount
  rw [heq]
  exact ((girthLift_rooted_count_le G hxy ε (G.girth-3) (by omega)).trans hε).trans_lt hfewer

/-- Lemma 8. Signings and shortest-cycle edges can be chosen so that the
resulting TWNGE sequence has unbounded girth. -/
theorem lift_girth (G₀ : SimpleGraph V) {d : ℕ} (hd : 2 ≤ d)
    (hr : Regular G₀ univ d) (hc : G₀.Connected) :
    ∃ F : TWNGE V, F.graph 0 = G₀ ∧ ∀ g : ℕ, ∃ n, g ≤ (F.graph n).girth := by
  exact exists_unbounded_tower_of_step G₀ hr hc
    (fun _ G hreg hconn => exists_improvingLift G hd hreg hconn)

end Paper
