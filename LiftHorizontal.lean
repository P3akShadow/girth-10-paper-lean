import LiftWalks

/-! Removing the vertical edges from the walks considered in Lemma 8. -/

namespace Paper
open SimpleGraph
variable {V : Type*} [DecidableEq V]

abbrev HorizontalWalk {L : SimpleGraph (V × Bool)} {a b : V × Bool} (p : L.Walk a b) : Prop :=
  ∀ u v, s(u,v) ∈ p.edges → u.1 ≠ v.1

omit [DecidableEq V] in
lemma HorizontalWalk.subwalk {L : SimpleGraph (V × Bool)} {a b c d : V × Bool}
    {p : L.Walk a b} {q : L.Walk c d} (hp : HorizontalWalk p) (hq : q.IsSubwalk p) :
    HorizontalWalk q := by
  intro u v huv
  exact hp u v (hq.edges_subset huv)

omit [DecidableEq V] in
lemma HorizontalWalk.reverse {L : SimpleGraph (V × Bool)} {a b : V × Bool}
    {p : L.Walk a b} (hp : HorizontalWalk p) : HorizontalWalk p.reverse := by
  intro u v huv
  apply hp u v
  simpa using huv

def toHorizontal {G : SimpleGraph V} {x y : V} {σ : Signing V} {a b : V × Bool}
    (p : (girthLift G x y σ).Walk a b) (hp : HorizontalWalk p) :
    (signedCover (edgeDeleted G x y) σ).Walk a b :=
  match p with
  | .nil => .nil
  | @Walk.cons _ _ a c b h p =>
    .cons (h.resolve_right (fun hv => hp a c (by simp) hv.1))
      (toHorizontal p (fun u v he => hp u v (by simp [he])))

@[simp] lemma toHorizontal_length {G : SimpleGraph V} {x y : V} {σ : Signing V} {a b : V × Bool}
    (p : (girthLift G x y σ).Walk a b) (hp : HorizontalWalk p) :
    (toHorizontal p hp).length = p.length := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    change (toHorizontal p _).length + 1 = p.length + 1
    rw [ih]

@[simp] lemma toHorizontal_support {G : SimpleGraph V} {x y : V} {σ : Signing V} {a b : V × Bool}
    (p : (girthLift G x y σ).Walk a b) (hp : HorizontalWalk p) :
    (toHorizontal p hp).support = p.support := by
  induction p with
  | nil => rfl
  | @cons a c b h p ih =>
    change a :: (toHorizontal p _).support = a :: p.support
    rw [ih]

@[simp] lemma toHorizontal_edges {G : SimpleGraph V} {x y : V} {σ : Signing V} {a b : V × Bool}
    (p : (girthLift G x y σ).Walk a b) (hp : HorizontalWalk p) :
    (toHorizontal p hp).edges = p.edges := by
  induction p with
  | nil => rfl
  | @cons a c b h p ih =>
    change s(a,c) :: (toHorizontal p _).edges = s(a,c) :: p.edges
    rw [ih]

lemma toHorizontal_isPath {G : SimpleGraph V} {x y : V} {σ : Signing V} {a b : V × Bool}
    (p : (girthLift G x y σ).Walk a b) (hp : HorizontalWalk p) (hpath : p.IsPath) :
    (toHorizontal p hp).IsPath := by
  apply (Walk.isPath_def _).mpr
  simpa using hpath.support_nodup

lemma toHorizontal_isCycle {G : SimpleGraph V} {x y : V} {σ : Signing V} {a : V × Bool}
    (p : (girthLift G x y σ).Walk a a) (hp : HorizontalWalk p) (hcycle : p.IsCycle) :
    (toHorizontal p hp).IsCycle := by
  apply (Walk.isCycle_def _).mpr
  refine ⟨⟨?_,⟩,?_,?_⟩
  · simpa using hcycle.isCircuit.isTrail.edges_nodup
  · intro hnil
    have hlen := congrArg Walk.length hnil
    have hmin := hcycle.isCircuit.three_le_length
    have hz : p.length = 0 := by simpa only [toHorizontal_length,Walk.length_nil] using hlen
    omega
  · simpa using hcycle.support_nodup

/-- Rotation at a displayed split of a cycle. -/
lemma cycle_append_comm {W : Type*} {H : SimpleGraph W} {u v : W}
    {p : H.Walk u v} {q : H.Walk v u} (h : (p.append q).IsCycle) :
    (q.append p).IsCycle := by
  apply (Walk.isCycle_def _).mpr
  have he := h.isCircuit.isTrail.edges_nodup
  have hs := h.support_nodup
  rw [Walk.edges_append] at he
  rw [Walk.tail_support_append] at hs
  refine ⟨⟨?_,⟩,?_,?_⟩
  · rw [Walk.edges_append]
    exact (List.perm_append_comm.nodup_iff).mp he
  · intro hn
    have hlen := congrArg Walk.length hn
    have hmin := h.isCircuit.three_le_length
    simp only [Walk.length_append,Walk.length_nil] at hlen hmin
    omega
  · rw [Walk.tail_support_append]
    exact (List.perm_append_comm.nodup_iff).mp hs

end Paper
