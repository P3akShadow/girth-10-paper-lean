import LiftFiberState
import LiftConstruction
import LiftBreadthFirst

/-! Lemma 9. The fibers are merged in breadth-first order in H. At every
stage the next fiber minimizes distance from x among uncontracted fibers;
all smaller-distance fibers, including its parent, are already contracted. -/

namespace Paper
open Finset
variable {V : Type*} [DecidableEq V] [Fintype V]

lemma girthLift_fiber_completion (G : SimpleGraph V) (x y : V) (hxy : G.Adj x y)
    (σ : Signing V) {d : ℕ} (hd : 2 ≤ d) (hreg : Regular G univ d)
    (hconn : (edgeDeleted G x y).Connected)
    (htail : Continuation (.ofGraph (girthLift G x y σ)) (2*d-1) (2*d-1)
      ((fiberExpansion univ).partition ⊥))
    (P : Partition (liftVertices (univ : Finset V)))
    (hstate : FiberState P)
    (hbound : Bounded (.ofGraph (girthLift G x y σ)) (2*d-1) (2*d-1) P) :
    Continuation (.ofGraph (girthLift G x y σ)) (2*d-1) (2*d-1) P := by
  classical
  let T := Trigraph.ofGraph (girthLift G x y σ)
  have hdeg : Regular (girthLift G x y σ) (liftVertices univ) d :=
    girthLift_regular G univ x y (mem_univ _) (mem_univ _) hxy σ hreg
  induction hn : P.parts.card using Nat.strong_induction_on generalizing P with
  | h n ih =>
    by_cases hall : ∀ u, fiber u ∈ P.parts
    · have heq := fiberState_complete (P := P) (fun u _ => hall u)
      exact heq ▸ htail
    · push Not at hall
      obtain ⟨v,hv⟩ := hall
      -- Choose the next BFS fiber, retaining the minimum-distance and
      -- earlier-level facts even though only the parent is needed below.
      obtain ⟨u,hu,_hminimum,_hearlier,hparent⟩ := breadth_first_next
        (edgeDeleted G x y) hconn x (fun u => fiber u ∈ P.parts) ⟨v,hv⟩
      obtain ⟨h0,h1⟩ := (hstate u (mem_univ _)).resolve_left hu
      let A : Finset (V × Bool) := {(u,false)}
      let B : Finset (V × Bool) := {(u,true)}
      have hAB : A ≠ B := by simp [A,B]
      have hABfiber : A ∪ B = fiber u := by simp [A,B,fiber]
      let Q := mergePartition P A B h0 h1
      have hQ : Q.parts = insert (A ∪ B) (P.parts \ {A,B}) := rfl
      have hmerge : Merge P Q := ⟨A,h0,B,h1,hAB,hQ⟩
      have hAdeg : totalDegree T P A ≤ d :=
        (singleton_totalDegree_le _ P (u,false)).trans (le_of_eq (hdeg _ (by simp [liftVertices])))
      have hBdeg : totalDegree T P B ≤ d :=
        (singleton_totalDegree_le _ P (u,true)).trans (le_of_eq (hdeg _ (by simp [liftVertices])))
      have hnew : totalDegree T Q (A ∪ B) ≤ 2*d-1 := by
        rcases hparent with hux | ⟨p,hp,hup,_hparentLevel⟩
        · have hadj : Adjacent T A B := ⟨(u,false),by simp [A],(u,true),by simp [B],
            Or.inl (girthLift_vertical G x y σ (Or.inl hux) false)⟩
          have hcount := adjacent_merge_totalDegree T h0 h1 hAB hQ hadj
          change totalDegree T Q (A ∪ B) + 2 ≤ totalDegree T P A + totalDegree T P B at hcount
          omega
        · have hac : Adjacent T A (fiber p) :=
            ⟨(u,false),by simp [A],(p,false ^^ σ.value u p),mem_fiber.mpr rfl,
              Or.inl (girthLift_horizontal G x y σ hup false)⟩
          have hbc : Adjacent T B (fiber p) :=
            ⟨(u,true),by simp [B],(p,true ^^ σ.value u p),mem_fiber.mpr rfl,
              Or.inl (girthLift_horizontal G x y σ hup true)⟩
          have hcount := common_neighbor_merge_totalDegree T hQ hp
            (fiber_ne_singleton p (u,false)) (fiber_ne_singleton p (u,true)) hac hbc
          omega
      have hQstate : FiberState Q := hstate.merge (hABfiber ▸ hQ)
      have hQbound : Bounded T (2*d-1) (2*d-1) Q :=
        bounded_merge_total T h0 h1 hAB hQ hbound hnew
      exact .step hbound hmerge (ih Q.parts.card (hn ▸ hmerge.card_lt) Q hQstate hQbound rfl)

/-- Lemma 9's one-step assertion. The inherited sequence is appended to the
fiber merges, whose new bags have degree at most 2d-2 at the root and 2d-1
thereafter. Every other bag's total degree can only decrease. -/
theorem girthLift_hasWidths (G : SimpleGraph V) (x y : V) (hxy : G.Adj x y)
    (σ : Signing V) {d w : ℕ} (hd : 2 ≤ d) (hreg : Regular G univ d)
    (hconn : (edgeDeleted G x y).Connected)
    (h : HasWidths (.ofGraph G) univ w (2*d-1)) :
    HasWidths (.ofGraph (girthLift G x y σ)) (liftVertices univ) (2*d-1) (2*d-1) := by
  apply girthLift_fiber_completion G x y hxy σ hd hreg hconn
    (girthLift_fiber_continuation G x y σ h) ⊥ FiberState.bot
  intro A hA
  obtain ⟨a,ha,rfl⟩ := Finpartition.mem_bot_iff.mp hA
  have hr := girthLift_regular G univ x y (mem_univ _) (mem_univ _) hxy σ hreg
  have ht : totalDegree (S := liftVertices (univ : Finset V)) (.ofGraph (girthLift G x y σ)) ⊥ {a} ≤ 2*d-1 := by
    have hc := (singleton_totalDegree_le (girthLift G x y σ) ⊥ a).trans (le_of_eq (hr a ha))
    omega
  exact ⟨(redDegree_le_totalDegree _ _ _).trans ht,ht⟩

theorem girthLift_sparseTwinWidth (G : SimpleGraph V) (x y : V) (hxy : G.Adj x y)
    (σ : Signing V) {d : ℕ} (hd : 2 ≤ d) (hreg : Regular G univ d)
    (hconn : (edgeDeleted G x y).Connected)
    (h : sparseTwinWidth (.ofGraph G) univ ≤ 2*d-1) :
    sparseTwinWidth (.ofGraph (girthLift G x y σ)) (liftVertices univ) ≤ 2*d-1 := by
  obtain ⟨w,hw⟩ := sparseTwinWidth_witness (.ofGraph G) univ
  exact sparseTwinWidth_le (girthLift_hasWidths G x y hxy σ hd hreg hconn
    (hw.monoBounds (le_refl _) h))

universe u

def TowerVertex (V : Type u) : ℕ → Type u
  | 0 => V
  | n+1 => TowerVertex V n × Bool

instance towerFintype (V : Type u) [Fintype V] : (n : ℕ) → Fintype (TowerVertex V n)
  | 0 => inferInstanceAs (Fintype V)
  | n+1 => by
    letI := towerFintype V n
    exact inferInstanceAs (Fintype (TowerVertex V n × Bool))

instance towerDecidableEq (V : Type u) [DecidableEq V] : (n : ℕ) → DecidableEq (TowerVertex V n)
  | 0 => inferInstanceAs (DecidableEq V)
  | n+1 => @instDecidableEqProd _ _ (towerDecidableEq V n) inferInstance

/-- The sequence in Definition 7: each step chooses an edge on a shortest
cycle and an arbitrary signing, and applies the stated lift operation. -/
structure TWNGE (V : Type u) [DecidableEq V] where
  graph : (n : ℕ) → SimpleGraph (TowerVertex V n)
  x : (n : ℕ) → TowerVertex V n
  y : (n : ℕ) → TowerVertex V n
  signing : (n : ℕ) → Signing (TowerVertex V n)
  shortest : ∀ n, ∃ (a : TowerVertex V n) (p : (graph n).Walk a a),
    p.IsCycle ∧ s(x n,y n) ∈ p.edges ∧ p.length = (graph n).girth
  step : ∀ n, graph (n+1) = girthLift (graph n) (x n) (y n) (signing n)

omit [Fintype V] in
lemma TWNGE.adj (F : TWNGE V) (n : ℕ) : (F.graph n).Adj (F.x n) (F.y n) := by
  obtain ⟨_,p,_,he,_⟩ := F.shortest n
  exact p.adj_of_mem_edges he

omit [Fintype V] in
lemma TWNGE.connected (F : TWNGE V) (h0 : (F.graph 0).Connected) (n : ℕ) :
    (F.graph n).Connected := by
  induction n with
  | zero => exact h0
  | succ n ih =>
    obtain ⟨_,p,hp,he,_⟩ := F.shortest n
    rw [F.step n]
    exact girthLift_connected _ _ _ _ (edgeDeleted_connected _ ih hp he)

lemma TWNGE.regular (F : TWNGE V) {d : ℕ} (h0 : Regular (F.graph 0) univ d) (n : ℕ) :
    Regular (F.graph n) univ d := by
  induction n with
  | zero => exact h0
  | succ n ih =>
    rw [F.step n]
    convert girthLift_regular (F.graph n) univ (F.x n) (F.y n)
      (mem_univ _) (mem_univ _) (F.adj n) (F.signing n) ih using 1
    simp only [liftVertices_univ]
    rfl

/-- Lemma 9, including induction over all graphs in the TWNGE. -/
theorem TWNGE.sparseTwinWidth_le (F : TWNGE V) {d : ℕ} (hd : 2 ≤ d)
    (hreg : Regular (F.graph 0) univ d) (hconn : (F.graph 0).Connected)
    (hwidth : sparseTwinWidth (.ofGraph (F.graph 0)) univ ≤ 2*d-1) (n : ℕ) :
    sparseTwinWidth (.ofGraph (F.graph n)) univ ≤ 2*d-1 := by
  induction n with
  | zero => exact hwidth
  | succ n ih =>
    obtain ⟨_,p,hp,he,_⟩ := F.shortest n
    have hc := edgeDeleted_connected (F.graph n) (F.connected hconn n) hp he
    rw [F.step n]
    convert girthLift_sparseTwinWidth (F.graph n)
      (F.x n) (F.y n) (F.adj n) (F.signing n) hd (F.regular hreg n) hc ih using 1
    congr 1

end Paper
