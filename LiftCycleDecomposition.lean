import LiftHorizontal

/-! The zero-, one-, and two-vertical-edge classification of cycles in the
TWNGE lift, as used in Lemma 8. -/
namespace Paper
open SimpleGraph
variable {V : Type*} [DecidableEq V]

lemma vertical_adj_endpoints {G : SimpleGraph V} {x y : V} {σ : Signing V}
    {a b : V × Bool} (h : (girthLift G x y σ).Adj a b) (he : a.1 = b.1) :
    (a.1 = x ∨ a.1 = y) ∧ a.2 ≠ b.2 := by
  rcases h with h | h
  · exact False.elim (h.1.1.ne he)
  · exact h.2

lemma vertical_edges_eq {G : SimpleGraph V} {x y : V} {σ : Signing V}
    {a b c d : V × Bool} (hab : (girthLift G x y σ).Adj a b)
    (hcd : (girthLift G x y σ).Adj c d)
    (habv : a.1 = b.1) (hcdv : c.1 = d.1) (hac : a.1 = c.1) :
    s(a,b) = s(c,d) := by
  have hi := (vertical_adj_endpoints hab habv).2
  have hj := (vertical_adj_endpoints hcd hcdv).2
  rcases a with ⟨a, i⟩
  rcases b with ⟨b, j⟩
  rcases c with ⟨c, k⟩
  rcases d with ⟨d, l⟩
  dsimp at habv hcdv hac hi hj
  subst b; subst c; subst d
  cases i <;> cases j <;> cases k <;> cases l <;> simp_all

lemma vertical_edge_two_choices {G : SimpleGraph V} {x y : V} {σ : Signing V}
    {a b c d e f : V × Bool} (hab : (girthLift G x y σ).Adj a b)
    (hcd : (girthLift G x y σ).Adj c d) (hef : (girthLift G x y σ).Adj e f)
    (habv : a.1 = b.1) (hcdv : c.1 = d.1) (hefv : e.1 = f.1)
    (hneq : s(a,b) ≠ s(c,d)) : s(e,f) = s(a,b) ∨ s(e,f) = s(c,d) := by
  have hac : a.1 ≠ c.1 := fun h => hneq (vertical_edges_eq hab hcd habv hcdv h)
  have ha := (vertical_adj_endpoints hab habv).1
  have hc := (vertical_adj_endpoints hcd hcdv).1
  have he := (vertical_adj_endpoints hef hefv).1
  have hh : e.1 = a.1 ∨ e.1 = c.1 := by aesop
  exact hh.elim (fun h => Or.inl (vertical_edges_eq hef hab hefv habv h))
    (fun h => Or.inr (vertical_edges_eq hef hcd hefv hcdv h))

/-- Every horizontal path between the two vertical fibers has at least
`girth(G)-1` edges, since the deleted edge closes its projection. -/
lemma horizontal_between_endpoints_length (G : SimpleGraph V) {x y : V}
    (hxy : G.Adj x y) (σ : Signing V) {a b : V × Bool}
    (p : (girthLift G x y σ).Walk a b) (hp : HorizontalWalk p)
    (ha : a.1 = x ∨ a.1 = y) (hb : b.1 = x ∨ b.1 = y) (hab : a.1 ≠ b.1) :
    G.girth ≤ p.length + 1 := by
  let q := (toHorizontal p hp).map (coverProjection (edgeDeleted G x y) σ)
  have hql : q.length = p.length := by simp [q]
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact False.elim (hab (ha.trans hb.symm))
  · have h := deleted_edge_walk_length G hxy (q.copy ha hb)
    have hcopy := Walk.length_copy q ha hb
    omega
  · have h := deleted_edge_walk_length G hxy (q.reverse.copy hb ha)
    have hcopy := Walk.length_copy q.reverse hb ha
    have hrev := q.length_reverse
    omega
  · exact False.elim (hab (ha.trans hb.symm))

/-- A cycle displayed with its two distinct vertical edges has horizontal
pieces between them: a third vertical occurrence would repeat an edge. -/
lemma vertical_pieces_horizontal {G : SimpleGraph V} {x y : V} {σ : Signing V}
    {a b c d : V × Bool} (hab : (girthLift G x y σ).Adj a b)
    (hcd : (girthLift G x y σ).Adj c d)
    (r : (girthLift G x y σ).Walk b c) (s : (girthLift G x y σ).Walk d a)
    (habv : a.1 = b.1) (hcdv : c.1 = d.1)
    (hc : (Walk.cons hab ((r.append hcd.toWalk).append s)).IsCycle) :
    HorizontalWalk r ∧ HorizontalWalk s := by
  have hn := hc.isCircuit.isTrail.edges_nodup
  have hn' : (s(a,b) :: (r.edges ++ s(c,d) :: s.edges)).Nodup := by
    simpa [Walk.edges_append, Adj.toWalk] using hn
  obtain ⟨habnot, hrest⟩ := List.nodup_cons.mp hn'
  have hneq : s(a,b) ≠ s(c,d) := fun he => habnot (by simp [he])
  have hrnot : s(c,d) ∉ r.edges := by
    intro he
    have hnd := (List.nodup_append.mp hrest).2.2
    exact hnd _ he _ (by simp) rfl
  have hsnot : s(c,d) ∉ s.edges := (List.nodup_cons.mp (List.nodup_append.mp hrest).2.1).1
  constructor
  · intro e f hef hefv
    have haef := r.adj_of_mem_edges hef
    rcases vertical_edge_two_choices hab hcd haef habv hcdv hefv hneq with hh | hh
    · exact habnot (by simp [← hh, hef])
    · exact hrnot (hh ▸ hef)
  · intro e f hef hefv
    have haef := s.adj_of_mem_edges hef
    rcases vertical_edge_two_choices hab hcd haef habv hcdv hefv hneq with hh | hh
    · exact habnot (by simp [← hh, hef])
    · exact hsnot (hh ▸ hef)

lemma two_vertical_cycle_girth_lt (G : SimpleGraph V) {x y : V}
    (hxy : G.Adj x y) (σ : Signing V) {a b c d : V × Bool}
    (hab : (girthLift G x y σ).Adj a b) (hcd : (girthLift G x y σ).Adj c d)
    (r : (girthLift G x y σ).Walk b c) (s : (girthLift G x y σ).Walk d a)
    (habv : a.1 = b.1) (hcdv : c.1 = d.1)
    (hc : (Walk.cons hab ((r.append hcd.toWalk).append s)).IsCycle) :
    G.girth < (Walk.cons hab ((r.append hcd.toWalk).append s)).length := by
  obtain ⟨hr, hs⟩ := vertical_pieces_horizontal hab hcd r s habv hcdv hc
  have hn := hc.isCircuit.isTrail.edges_nodup
  have hneq : s(a,b) ≠ s(c,d) := by
    intro he
    have hh := (List.nodup_cons.mp hn).1
    exact hh (by simp [Adj.toWalk, he])
  have hac : a.1 ≠ c.1 := fun he => hneq (vertical_edges_eq hab hcd habv hcdv he)
  have ha := (vertical_adj_endpoints hab habv).1
  have hc' := (vertical_adj_endpoints hcd hcdv).1
  have hbc : b.1 ≠ c.1 := fun he => hac (habv.trans he)
  have hda : d.1 ≠ a.1 := fun he => hac (hcdv.trans he).symm
  have hrlen := horizontal_between_endpoints_length G hxy σ r hr (habv ▸ ha) hc' hbc
  have hslen := horizontal_between_endpoints_length G hxy σ s hs (hcdv ▸ hc') ha hda
  have hlen := hc.isCircuit.three_le_length
  simp only [Walk.length_cons, Walk.length_append, Adj.toWalk, Walk.length_nil] at hlen ⊢
  omega

/-- A cycle starting with a vertical edge is strictly longer than the base
shortest cycle. Its tail either is horizontal, or contains the other vertical
edge and splits into two horizontal paths. -/
lemma vertical_start_cycle_girth_lt (G : SimpleGraph V) {x y : V}
    (hxy : G.Adj x y) (σ : Signing V) {a b : V × Bool}
    (hab : (girthLift G x y σ).Adj a b) (habv : a.1 = b.1)
    (q : (girthLift G x y σ).Walk b a) (hc : (Walk.cons hab q).IsCycle) :
    G.girth < (Walk.cons hab q).length := by
  classical
  by_cases hq : HorizontalWalk q
  · rcases a with ⟨a, i⟩
    rcases b with ⟨b, j⟩
    dsimp at habv
    subst b
    have hij := (vertical_adj_endpoints hab rfl).2
    have hpq : q.IsPath := by simpa using hc.isPath_tail
    have hh := same_fiber_path_girth_le G x y σ hij.symm (toHorizontal q hq)
      (toHorizontal_isPath q hq hpq)
    simpa only [toHorizontal_length, Walk.length_cons] using hh
  · unfold HorizontalWalk at hq
    push Not at hq
    obtain ⟨c, d, hmem, hcdv⟩ := hq
    have hcd := q.adj_of_mem_edges hmem
    rcases (Walk.isSubwalk_toWalk_iff_mem_edges hcd).mpr hmem with hsub | hsub
    · obtain ⟨r, s, rfl⟩ := hsub
      exact two_vertical_cycle_girth_lt G hxy σ hab hcd r s habv hcdv hc
    · obtain ⟨r, s, rfl⟩ := hsub
      exact two_vertical_cycle_girth_lt G hxy σ hab hcd.symm r s habv hcdv.symm hc

lemma cycle_with_vertical_girth_lt (G : SimpleGraph V) {x y : V}
    (hxy : G.Adj x y) (σ : Signing V) {u : V × Bool}
    {p : (girthLift G x y σ).Walk u u} (hp : p.IsCycle) (hv : ¬ HorizontalWalk p) :
    G.girth < p.length := by
  classical
  unfold HorizontalWalk at hv
  push Not at hv
  obtain ⟨a, b, hmem, habv⟩ := hv
  have hab := p.adj_of_mem_edges hmem
  have rotate_bound : ∀ {a b : V × Bool} (hab : (girthLift G x y σ).Adj a b),
      a.1 = b.1 → hab.toWalk.IsSubwalk p → G.girth < p.length := by
    intro a b hab habv hsub
    obtain ⟨r, s, heq⟩ := hsub
    have hrot : (Walk.cons hab (s.append r)).IsCycle := by
      have hh : (r.append (hab.toWalk.append s)).IsCycle := by
        rw [Walk.append_assoc, ← heq]
        exact hp
      have hh' := cycle_append_comm hh
      simpa [Adj.toWalk, ← Walk.append_assoc] using hh'
    have hbound := vertical_start_cycle_girth_lt G hxy σ hab habv (s.append r) hrot
    have hlen : (Walk.cons hab (s.append r)).length = p.length := by
      rw [heq]
      simp [Walk.length_append, Adj.toWalk]
      omega
    simpa only [hlen] using hbound
  rcases (Walk.isSubwalk_toWalk_iff_mem_edges hab).mpr hmem with hsub | hsub
  · exact rotate_bound hab habv hsub
  · exact rotate_bound hab.symm habv.symm hsub

/-- The cycle classification in Lemma 8: no cycle becomes shorter, and a
cycle of the old girth uses no vertical edge. -/
theorem girthLift_cycle_length (G : SimpleGraph V) {x y : V}
    (hxy : G.Adj x y) (σ : Signing V) {u : V × Bool}
    {p : (girthLift G x y σ).Walk u u} (hp : p.IsCycle) :
    G.girth ≤ p.length ∧ (p.length = G.girth → HorizontalWalk p) := by
  classical
  by_cases hh : HorizontalWalk p
  · exact ⟨by simpa only [toHorizontal_length] using
      horizontal_cycle_girth_le G x y σ (toHorizontal_isCycle p hh hp), fun _ => hh⟩
  · have hlt := cycle_with_vertical_girth_lt G hxy σ hp hh
    exact ⟨hlt.le, fun he => False.elim (by omega)⟩

end Paper
