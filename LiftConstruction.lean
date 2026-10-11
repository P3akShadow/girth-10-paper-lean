import GraphDegrees
import Expansion

/-! The signed double cover with the chosen edge replaced by the two vertical
edges, exactly as in the TWNGE construction in Section 4. -/

namespace Paper
open Finset
variable {V : Type*} [DecidableEq V]

/-- A signing has the same value in either orientation of an edge. -/
structure Signing (V : Type*) where
  value : V → V → Bool
  symmetric : ∀ u v, value u v = value v u

def DeletedEdge (x y u v : V) : Prop := (u = x ∧ v = y) ∨ (u = y ∧ v = x)

lemma deletedEdge_symm {x y u v : V} : DeletedEdge x y u v ↔ DeletedEdge x y v u := by
  unfold DeletedEdge
  tauto

def edgeDeleted (G : SimpleGraph V) (x y : V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ ¬ DeletedEdge x y u v
  symm := ⟨fun _ _ h => ⟨h.1.symm, fun hd => h.2 (deletedEdge_symm.mpr hd)⟩⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

def girthLift (G : SimpleGraph V) (x y : V) (σ : Signing V) : SimpleGraph (V × Bool) where
  Adj a b := ((edgeDeleted G x y).Adj a.1 b.1 ∧ (a.2 ^^ b.2) = σ.value a.1 b.1) ∨
    (a.1 = b.1 ∧ (a.1 = x ∨ a.1 = y) ∧ a.2 ≠ b.2)
  symm := ⟨by
    intro a b h
    rcases h with h | h
    · exact Or.inl ⟨h.1.symm, by simpa [Bool.xor_comm, σ.symmetric b.1 a.1] using h.2⟩
    · exact Or.inr ⟨h.1.symm, h.1 ▸ h.2.1, h.2.2.symm⟩⟩
  loopless := ⟨by
    intro a h
    rcases h with h | h
    · exact h.1.ne rfl
    · exact h.2.2 rfl⟩

def liftVertices (S : Finset V) : Finset (V × Bool) := S ×ˢ univ

omit [DecidableEq V] in
lemma mem_liftVertices {S : Finset V} {a : V × Bool} : a ∈ liftVertices S ↔ a.1 ∈ S := by
  simp [liftVertices]

lemma girthLift_horizontal (G : SimpleGraph V) (x y : V) (σ : Signing V)
    {u v : V} (h : (edgeDeleted G x y).Adj u v) (i : Bool) :
    (girthLift G x y σ).Adj (u,i) (v,i ^^ σ.value u v) := by
  apply Or.inl
  refine ⟨h, ?_⟩
  cases i <;> cases σ.value u v <;> rfl

lemma girthLift_vertical (G : SimpleGraph V) (x y : V) (σ : Signing V)
    {u : V} (h : u = x ∨ u = y) (i : Bool) :
    (girthLift G x y σ).Adj (u,i) (u,!i) := by
  exact Or.inr ⟨rfl, h, by cases i <;> simp⟩

noncomputable def liftNeighbor (x y : V) (σ : Signing V) (u : V) (i : Bool) (v : V) : V × Bool := by
  classical
  exact if DeletedEdge x y u v then (u,!i) else (v,i ^^ σ.value u v)

omit [DecidableEq V] in
lemma deletedEdge_adj {G : SimpleGraph V} {x y u v : V} (hxy : G.Adj x y)
    (h : DeletedEdge x y u v) : G.Adj u v := by
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact hxy
  · exact hxy.symm

omit [DecidableEq V] in
lemma deletedEdge_unique {x y u v w : V} (hxy : x ≠ y)
    (hv : DeletedEdge x y u v) (hw : DeletedEdge x y u w) : v = w := by
  unfold DeletedEdge at *
  aesop

/-- The construction replaces exactly one neighbor at each endpoint by its
vertical copy; all other neighbors have one signed lift. -/
lemma girthLift_degree (G : SimpleGraph V) (S : Finset V) (x y : V)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : G.Adj x y) (σ : Signing V)
    {u : V} (hu : u ∈ S) (i : Bool) :
    (graphNeighbors (girthLift G x y σ) (liftVertices S) (u,i)).card =
      (graphNeighbors G S u).card := by
  classical
  symm
  apply card_bij (fun v _ => liftNeighbor x y σ u i v)
  · intro v hv
    obtain ⟨hvS, huv⟩ := mem_filter.mp hv
    by_cases hdel : DeletedEdge x y u v
    · rw [liftNeighbor, ite_eq_left hdel]
      apply mem_filter.mpr
      refine ⟨mem_liftVertices.mpr hu, girthLift_vertical G x y σ ?_ i⟩
      rcases hdel with h | h
      · exact Or.inl h.1
      · exact Or.inr h.1
    · rw [liftNeighbor, ite_eq_right hdel]
      exact mem_filter.mpr ⟨mem_liftVertices.mpr hvS,
        girthLift_horizontal G x y σ ⟨huv,hdel⟩ i⟩
  · intro v hv w hw heq
    have huv := (mem_filter.mp hv).2
    have huw := (mem_filter.mp hw).2
    by_cases hvd : DeletedEdge x y u v <;> by_cases hwd : DeletedEdge x y u w
    · exact deletedEdge_unique hxy.ne hvd hwd
    · have heq' : u = w := by simpa [liftNeighbor, hvd, hwd] using congrArg Prod.fst heq
      exact False.elim (huw.ne heq')
    · have heq' : v = u := by simpa [liftNeighbor, hvd, hwd] using congrArg Prod.fst heq
      exact False.elim (huv.ne heq'.symm)
    · simpa [liftNeighbor, hvd, hwd] using congrArg Prod.fst heq
  · intro a ha
    rcases a with ⟨a,j⟩
    obtain ⟨haS, hadj⟩ := mem_filter.mp ha
    rcases hadj with ⟨⟨hua, hdel⟩, hsign⟩ | ⟨hua, hend, hbit⟩
    · refine ⟨a, mem_filter.mpr ⟨mem_liftVertices.mp haS, hua⟩, ?_⟩
      rw [liftNeighbor, ite_eq_right hdel]
      refine Prod.ext (by rfl) ?_
      change (i ^^ σ.value u a) = j
      change (i ^^ j) = σ.value u a at hsign
      rw [← hsign]
      cases i <;> cases j <;> rfl
    · change u = a at hua
      change u = x ∨ u = y at hend
      have hab : (!i) = j := by
        change i ≠ j at hbit
        cases i <;> cases j <;> simp_all
      rcases hend with hux | huy
      · refine ⟨y, mem_filter.mpr ⟨hy, by simpa only [hux] using hxy⟩, ?_⟩
        have hdel : DeletedEdge x y u y := Or.inl ⟨hux,rfl⟩
        rw [liftNeighbor, ite_eq_left hdel]
        exact Prod.ext hua hab
      · refine ⟨x, mem_filter.mpr ⟨hx, by simpa only [huy] using hxy.symm⟩, ?_⟩
        have hdel : DeletedEdge x y u x := Or.inr ⟨huy,rfl⟩
        rw [liftNeighbor, ite_eq_left hdel]
        exact Prod.ext hua hab

theorem girthLift_regular (G : SimpleGraph V) (S : Finset V) (x y : V)
    (hx : x ∈ S) (hy : y ∈ S) (hxy : G.Adj x y) (σ : Signing V) {d : ℕ}
    (hreg : Regular G S d) : Regular (girthLift G x y σ) (liftVertices S) d := by
  intro a ha
  exact (girthLift_degree G S x y hx hy hxy σ (mem_liftVertices.mp ha) a.2).trans
    (hreg a.1 (mem_liftVertices.mp ha))

/-- Follow a base walk, with the sign determining the next sheet at each step. -/
lemma girthLift_walk (G : SimpleGraph V) (x y : V) (σ : Signing V)
    {u v : V} (p : (edgeDeleted G x y).Walk u v) (i : Bool) :
    ∃ j, (girthLift G x y σ).Reachable (u,i) (v,j) := by
  induction p generalizing i with
  | nil => exact ⟨i, .refl _⟩
  | @cons u v w huv p ih =>
    obtain ⟨j,hj⟩ := ih (i ^^ σ.value u v)
    exact ⟨j, (girthLift_horizontal G x y σ huv i).reachable.trans hj⟩

/-- The two copies of the root are joined by the vertical edge. -/
lemma girthLift_root_reachable (G : SimpleGraph V) (x y : V) (σ : Signing V)
    (i j : Bool) : (girthLift G x y σ).Reachable (x,i) (x,j) := by
  by_cases h : i = j
  · subst j
    exact .refl _
  · apply SimpleGraph.Adj.reachable
    exact Or.inr ⟨rfl,Or.inl rfl,h⟩

/-- Connectivity argument preceding Lemma 8: lift a walk from each vertex to
the root and, if necessary, cross the root's vertical edge. -/
theorem girthLift_connected (G : SimpleGraph V) (x y : V) (σ : Signing V)
    (hconn : (edgeDeleted G x y).Connected) : (girthLift G x y σ).Connected := by
  let : Nonempty (V × Bool) := ⟨(x,false)⟩
  apply SimpleGraph.Connected.mk
  intro a b
  obtain ⟨p⟩ := hconn.preconnected a.1 x
  obtain ⟨q⟩ := hconn.preconnected b.1 x
  obtain ⟨i,hi⟩ := girthLift_walk G x y σ p a.2
  obtain ⟨j,hj⟩ := girthLift_walk G x y σ q b.2
  exact (hi.trans (girthLift_root_reachable G x y σ i j)).trans hj.symm

lemma edgeDeleted_eq_deleteEdges (G : SimpleGraph V) (x y : V) :
    edgeDeleted G x y = G.deleteEdges {s(x,y)} := by
  ext u v
  simp only [edgeDeleted,SimpleGraph.deleteEdges_adj,Set.mem_singleton_iff,
    Sym2.eq_iff,DeletedEdge]

/-- Deleting an edge on a cycle leaves a connected graph connected. -/
lemma edgeDeleted_connected (G : SimpleGraph V) (hG : G.Connected)
    {x y a : V} {p : G.Walk a a} (hp : p.IsCycle) (hxy : s(x,y) ∈ p.edges) :
    (edgeDeleted G x y).Connected := by
  rw [edgeDeleted_eq_deleteEdges]
  exact hG.connected_delete_edge_of_not_isBridge
    (fun hbridge => hbridge.notMem_edges_of_isCycle hp hxy)

omit [DecidableEq V] in
lemma liftVertices_univ [Fintype V] : liftVertices (univ : Finset V) = univ := by
  ext a
  simp [mem_liftVertices]

end Paper
