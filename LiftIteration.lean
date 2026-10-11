import LiftCycles
import RegularSeed

/-! The finite-descent iteration in Lemma 8. At fixed girth the number of
shortest cycles strictly decreases; consequently the girth must increase. -/
namespace Paper
open Finset
universe u
variable {V : Type u} [DecidableEq V] [Fintype V]

/-- The one-step output of the cycle-classification and signing argument.
This is construction data, subsequently supplied by the proved signing lemma. -/
structure ImprovingLift (G : SimpleGraph V) where
  x : V
  y : V
  signing : Signing V
  shortest : ∃ a, ∃ p : G.Walk a a,
    p.IsCycle ∧ s(x,y) ∈ p.edges ∧ p.length = G.girth
  progress : G.girth ≤ (girthLift G x y signing).girth ∧
    ((girthLift G x y signing).girth = G.girth →
      shortestCycleCount (girthLift G x y signing) < shortestCycleCount G)

def ImprovingLift.graph {G : SimpleGraph V} (L : ImprovingLift G) : SimpleGraph (V × Bool) :=
  girthLift G L.x L.y L.signing

lemma ImprovingLift.adj {G : SimpleGraph V} (L : ImprovingLift G) : G.Adj L.x L.y := by
  obtain ⟨_,p,_,he,_⟩ := L.shortest
  exact p.adj_of_mem_edges he

lemma ImprovingLift.regular {G : SimpleGraph V} (L : ImprovingLift G) {d : ℕ}
    (hr : Regular G univ d) : Regular L.graph univ d := by
  have hh := girthLift_regular G univ L.x L.y (mem_univ _) (mem_univ _) L.adj L.signing hr
  simpa only [ImprovingLift.graph,liftVertices_univ] using hh

lemma ImprovingLift.connected {G : SimpleGraph V} (L : ImprovingLift G)
    (hc : G.Connected) : L.graph.Connected := by
  obtain ⟨_,p,hp,he,_⟩ := L.shortest
  exact girthLift_connected G L.x L.y L.signing (edgeDeleted_connected G hc hp he)

/-- The count cannot decrease forever while the girth stays fixed. -/
lemma progress_eventually_increases (g c : ℕ → ℕ)
    (hmono : ∀ n, g n ≤ g (n+1))
    (hdec : ∀ n, g (n+1) = g n → c (n+1) < c n) (n : ℕ) :
    ∃ m, n ≤ m ∧ g n < g m := by
  generalize hk : c n = k
  induction k using Nat.strong_induction_on generalizing n with | h k ih =>
    by_cases heq : g (n+1) = g n
    · have hc := hdec n heq
      obtain ⟨m,hnm,hm⟩ := ih (c (n+1)) (by omega) (n+1) rfl
      exact ⟨m,by omega,by omega⟩
    · exact ⟨n+1,by omega,by have := hmono n; omega⟩

lemma progress_unbounded (g c : ℕ → ℕ)
    (hmono : ∀ n, g n ≤ g (n+1))
    (hdec : ∀ n, g (n+1) = g n → c (n+1) < c n) : ∀ k, ∃ n, k ≤ g n := by
  intro k
  induction k with
  | zero => exact ⟨0,Nat.zero_le _⟩
  | succ k ih =>
    obtain ⟨n,hn⟩ := ih
    obtain ⟨m,_,hm⟩ := progress_eventually_increases g c hmono hdec n
    exact ⟨m,by omega⟩

/-- Apply finite cycle-count descent to an actual sequence of lifts. -/
lemma TWNGE.unbounded_of_progress (F : TWNGE V)
    (hm : ∀ n, (F.graph n).girth ≤ (F.graph (n+1)).girth)
    (hd : ∀ n, (F.graph (n+1)).girth = (F.graph n).girth →
      shortestCycleCount (F.graph (n+1)) < shortestCycleCount (F.graph n)) :
    ∀ g : ℕ, ∃ n, g ≤ (F.graph n).girth :=
  progress_unbounded (fun n => (F.graph n).girth) (fun n => shortestCycleCount (F.graph n)) hm hd

/-- Build all stages, retaining regularity and connectivity at every step. -/
noncomputable def progressStages (G₀ : SimpleGraph V) {d : ℕ}
    (hr : Regular G₀ univ d) (hc : G₀.Connected)
    (step : ∀ (n : ℕ) (G : SimpleGraph (TowerVertex V n)),
      Regular G univ d → G.Connected → Nonempty (ImprovingLift G)) :
    (n : ℕ) → {G : SimpleGraph (TowerVertex V n) // Regular G univ d ∧ G.Connected}
  | 0 => ⟨G₀,hr,hc⟩
  | n+1 =>
    let prev := progressStages G₀ hr hc step n
    let L := Classical.choice (step n prev.val prev.property.1 prev.property.2)
    ⟨L.graph,L.regular prev.property.1,L.connected prev.property.2⟩

/-- Choose a signing at every stage and concatenate the resulting lift steps. -/
lemma exists_unbounded_tower_of_step (G₀ : SimpleGraph V) {d : ℕ}
    (hr : Regular G₀ univ d) (hc : G₀.Connected)
    (step : ∀ (n : ℕ) (G : SimpleGraph (TowerVertex V n)),
      Regular G univ d → G.Connected → Nonempty (ImprovingLift G)) :
    ∃ F : TWNGE V, F.graph 0 = G₀ ∧ ∀ g : ℕ, ∃ n, g ≤ (F.graph n).girth := by
  classical
  let stages := progressStages G₀ hr hc step
  let choices := fun n => Classical.choice (step n (stages n).val (stages n).property.1 (stages n).property.2)
  let F : TWNGE V := {
    graph := fun n => (stages n).val
    x := fun n => (choices n).x
    y := fun n => (choices n).y
    signing := fun n => (choices n).signing
    shortest := fun n => (choices n).shortest
    step := fun _ => rfl }
  refine ⟨F,rfl,F.unbounded_of_progress ?_ ?_⟩
  · intro n
    exact (choices n).progress.1
  · intro n heq
    exact (choices n).progress.2 heq

end Paper
