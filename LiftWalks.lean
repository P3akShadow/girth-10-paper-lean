import LiftConstruction

/-! The nonbacktracking observation in Lemma 8. -/

namespace Paper
open SimpleGraph
variable {V W : Type*} {G : SimpleGraph V}

/-- No immediate traversal of an edge followed by the reverse traversal. -/
def NoBacktrack {u v : V} (p : G.Walk u v) : Prop :=
  ∀ a (q : G.Walk a a), q.IsSubwalk p → q.length ≠ 2

lemma NoBacktrack.subwalk {u v a b : V} {p : G.Walk u v} {q : G.Walk a b}
    (hp : NoBacktrack p) (hq : q.IsSubwalk p) : NoBacktrack q := by
  intro x r hr
  exact hp x r (hr.trans hq)

lemma noBacktrack_of_getVert {u v : V} (p : G.Walk u v)
    (h : ∀ i, i+2 ≤ p.length → p.getVert i ≠ p.getVert (i+2)) : NoBacktrack p := by
  intro a q hq htwo
  obtain ⟨r,t,rfl⟩ := hq
  have hlen : r.length+2 ≤ ((r.append q).append t).length := by
    simp only [Walk.length_append,htwo]
    omega
  have hqend : q.getVert 2 = a := htwo ▸ q.getVert_length
  have hstart : ((r.append q).append t).getVert r.length = a := by
    simp [Walk.getVert_append',htwo]
  have hend : ((r.append q).append t).getVert (r.length+2) = a := by
    simp [Walk.getVert_append',htwo,hqend]
  exact h r.length hlen (hstart.trans hend.symm)

/-- A nonempty closed nonbacktracking walk contains a cycle no longer than
itself. This is the precise walk fact used after projecting horizontal edges. -/
theorem cycle_of_noBacktrack {u : V} (p : G.Walk u u) (hp : ¬ p.Nil)
    (hnb : NoBacktrack p) : ∃ (a : V) (c : G.Walk a a), c.IsCycle ∧ c.length ≤ p.length := by
  classical
  induction hn : p.length using Nat.strong_induction_on generalizing u p with
  | h n ih =>
    by_cases ht : p.tail.IsPath
    · have h0 : 0 < p.length := Walk.not_nil_iff_lt_length.mp hp
      have h1 : p.length ≠ 1 := fun he => (Walk.adj_of_length_eq_one he).ne rfl
      have h2 : p.length ≠ 2 := hnb u p p.isSubwalk_rfl
      have h3 : 3 ≤ p.length := by omega
      exact ⟨u,p,Walk.isCycle_iff_isPath_tail_and_le_length.mpr ⟨ht,h3⟩,le_of_eq hn⟩
    · rw [Walk.isPath_iff_isSubwalk_imp_nil] at ht
      push Not at ht
      obtain ⟨a,q,hq,hqnil⟩ := ht
      have hqle := Walk.length_le_of_isSubwalk hq
      have htail := p.length_tail_add_one hp
      have hqsub := hq.trans p.isSubwalk_rfl.tail
      obtain ⟨b,c,hc,hcle⟩ := ih q.length (by omega) q hqnil (hnb.subwalk hqsub) rfl
      exact ⟨b,c,hc,hcle.trans (by omega)⟩

lemma cycle_subwalk_of_noBacktrack {u : V} (p : G.Walk u u) (hp : ¬ p.Nil)
    (hnb : NoBacktrack p) : ∃ (a : V) (c : G.Walk a a), c.IsCycle ∧ c.IsSubwalk p := by
  classical
  induction hn : p.length using Nat.strong_induction_on generalizing u p with
  | h n ih =>
    by_cases ht : p.tail.IsPath
    · have h0 : 0 < p.length := Walk.not_nil_iff_lt_length.mp hp
      have h1 : p.length ≠ 1 := fun he => (Walk.adj_of_length_eq_one he).ne rfl
      have h2 : p.length ≠ 2 := hnb u p p.isSubwalk_rfl
      exact ⟨u,p,Walk.isCycle_iff_isPath_tail_and_le_length.mpr ⟨ht,by omega⟩,p.isSubwalk_rfl⟩
    · rw [Walk.isPath_iff_isSubwalk_imp_nil] at ht
      push Not at ht
      obtain ⟨a,q,hq,hqnil⟩ := ht
      have hqle := Walk.length_le_of_isSubwalk hq
      have htail := p.length_tail_add_one hp
      have hqsub := hq.trans p.isSubwalk_rfl.tail
      obtain ⟨b,c,hc,hcsub⟩ := ih q.length (by omega) q hqnil (hnb.subwalk hqsub) rfl
      exact ⟨b,c,hc,hcsub.trans hqsub⟩

/-- At the girth, the projected nonbacktracking closed walk is itself simple. -/
lemma noBacktrack_at_girth_isCycle {u : V} (p : G.Walk u u) (hp : ¬ p.Nil)
    (hnb : NoBacktrack p) (hlen : p.length ≤ G.girth) : p.IsCycle := by
  obtain ⟨a,c,hc,hsub⟩ := cycle_subwalk_of_noBacktrack p hp hnb
  have hcle := hc.girth_le_length
  obtain ⟨r,t,rfl⟩ := hsub
  have hrlen : r.length = 0 := by simp only [Walk.length_append] at hlen; omega
  have htlen : t.length = 0 := by simp only [Walk.length_append] at hlen; omega
  cases r with
  | nil =>
    cases t with
    | nil => simpa using hc
    | cons h t => simp at htlen
  | cons h r => simp at hrlen

def LocallyInjective {H : SimpleGraph W} (f : G →g H) : Prop :=
  ∀ u v w, G.Adj u v → G.Adj u w → f v = f w → v = w

lemma cycle_map_noBacktrack {H : SimpleGraph W} (f : G →g H)
    (hf : LocallyInjective f) {u : V} {p : G.Walk u u} (hp : p.IsCycle) :
    NoBacktrack (p.map f) := by
  apply noBacktrack_of_getVert
  intro i hi heq
  simp only [Walk.length_map] at hi
  simp only [Walk.getVert_map] at heq
  have hleft := (p.adj_getVert_succ (i := i) (by omega)).symm
  have hright := p.adj_getVert_succ (i := i+1) (by omega)
  have hneq := hp.getVert_sub_one_ne_getVert_add_one (i := i+1) (by omega)
  simp only [Nat.add_sub_cancel,Nat.add_assoc] at hneq
  exact hneq (hf _ _ _ hleft hright heq)

lemma path_map_noBacktrack {H : SimpleGraph W} (f : G →g H)
    (hf : LocallyInjective f) {u v : V} {p : G.Walk u v} (hp : p.IsPath) :
    NoBacktrack (p.map f) := by
  apply noBacktrack_of_getVert
  intro i hi heq
  simp only [Walk.length_map] at hi
  simp only [Walk.getVert_map] at heq
  have hleft := (p.adj_getVert_succ (i := i) (by omega)).symm
  have hright := p.adj_getVert_succ (i := i+1) (by omega)
  have hEq := hf _ _ _ hleft hright heq
  have hh := hp.getVert_injOn (by dsimp; omega) (by dsimp; omega) hEq
  omega

/-- Projecting a cycle along a locally injective graph map cannot create a
walk shorter than the girth of the base graph. -/
theorem cycle_map_girth_le {H : SimpleGraph W} (f : G →g H)
    (hf : LocallyInjective f) {u : V} {p : G.Walk u u} (hp : p.IsCycle) :
    H.girth ≤ p.length := by
  have hnonempty : ¬ (p.map f).Nil := by
    apply Walk.not_nil_iff_lt_length.mpr
    simpa using Walk.not_nil_iff_lt_length.mp hp.not_nil
  obtain ⟨_,c,hc,hle⟩ := cycle_of_noBacktrack (p.map f) hnonempty (cycle_map_noBacktrack f hf hp)
  exact hc.girth_le_length.trans (by simpa using hle)

def signedCover (H : SimpleGraph V) (σ : Signing V) : SimpleGraph (V × Bool) where
  Adj a b := H.Adj a.1 b.1 ∧ (a.2 ^^ b.2) = σ.value a.1 b.1
  symm := ⟨by
    intro a b h
    exact ⟨h.1.symm,by simpa [Bool.xor_comm,σ.symmetric b.1 a.1] using h.2⟩⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

def coverProjection (H : SimpleGraph V) (σ : Signing V) : signedCover H σ →g H where
  toFun := Prod.fst
  map_rel' := fun h => h.1

lemma coverProjection_locallyInjective (H : SimpleGraph V) (σ : Signing V) :
    LocallyInjective (coverProjection H σ) := by
  intro a b c hab hac hbc
  change b.1 = c.1 at hbc
  apply Prod.ext hbc
  have hh : (a.2 ^^ b.2) = (a.2 ^^ c.2) := hab.2.trans (by simpa only [hbc] using hac.2.symm)
  exact Bool.xor_right_inj.mp hh

theorem horizontal_cycle_girth_le [DecidableEq V] (G : SimpleGraph V) (x y : V)
    (σ : Signing V) {u : V × Bool} {p : (signedCover (edgeDeleted G x y) σ).Walk u u}
    (hp : p.IsCycle) : G.girth ≤ p.length := by
  let f : signedCover (edgeDeleted G x y) σ →g G := {
    toFun := Prod.fst
    map_rel' := fun h => h.1.1 }
  exact cycle_map_girth_le f (coverProjection_locallyInjective (edgeDeleted G x y) σ) hp

/-- The one-vertical case of Lemma 8, after deleting its vertical edge. -/
theorem same_fiber_path_girth_le [DecidableEq V] (G : SimpleGraph V) (x y : V)
    (σ : Signing V) {u : V} {i j : Bool} (hij : i ≠ j)
    (p : (signedCover (edgeDeleted G x y) σ).Walk (u,i) (u,j)) (hp : p.IsPath) :
    G.girth < p.length + 1 := by
  let f : signedCover (edgeDeleted G x y) σ →g G := {
    toFun := Prod.fst
    map_rel' := fun h => h.1.1 }
  have hnonempty : ¬ (p.map f).Nil := by
    rw [← Walk.length_eq_zero_iff,Walk.length_map]
    intro hz
    have hn := (Walk.length_eq_zero_iff.mp hz).eq
    exact hij (congrArg Prod.snd hn)
  obtain ⟨_,c,hc,hle⟩ := cycle_of_noBacktrack (p.map f) hnonempty
    (path_map_noBacktrack f (coverProjection_locallyInjective (edgeDeleted G x y) σ) hp)
  have hh := hc.girth_le_length.trans hle
  simpa only [Walk.length_map] using Nat.lt_succ_of_le hh

/-- The removed edge closes every x-y path in H to a cycle. -/
lemma deleted_edge_walk_length [DecidableEq V] (G : SimpleGraph V) {x y : V}
    (hxy : G.Adj x y) (p : (edgeDeleted G x y).Walk x y) :
    G.girth ≤ p.length + 1 := by
  let q := p.bypass
  have hq0 : q.length ≠ 0 := by
    intro hz
    exact hxy.ne ((Walk.length_eq_zero_iff.mp hz).eq)
  have hq1 : q.length ≠ 1 := by
    intro ho
    have hh := Walk.adj_of_length_eq_one ho
    exact hh.2 (Or.inl ⟨rfl,rfl⟩)
  have hq2 : 2 ≤ q.length := by omega
  have hsub : edgeDeleted G x y ≤ G := fun _ _ h => h.1
  let c := Walk.cons hxy (q.reverse.mapLe hsub)
  have hc : c.IsCycle := by
    apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
    constructor
    · simpa [c,q] using Walk.IsPath.mapLe hsub (p.bypass_isPath.reverse)
    · simpa [c] using Nat.add_le_add_right hq2 1
  have hbound := hc.girth_le_length
  have hqle := p.length_bypass_le_length
  simp only [c,Walk.length_cons,Walk.length_mapLe,Walk.length_reverse] at hbound
  exact hbound.trans (Nat.add_le_add_right hqle 1)

/-- The two-vertical case, after removing the vertical edges: each remaining
horizontal x-y walk has length at least girth(G)-1. -/
theorem two_vertical_walks_length [DecidableEq V] (G : SimpleGraph V) {x y : V}
    (hxy : G.Adj x y) (σ : Signing V) {i j i' j' : Bool}
    (p : (signedCover (edgeDeleted G x y) σ).Walk (x,i) (y,j))
    (q : (signedCover (edgeDeleted G x y) σ).Walk (x,i') (y,j')) :
    2 * G.girth ≤ p.length + q.length + 2 := by
  have hp := deleted_edge_walk_length G hxy (p.map (coverProjection (edgeDeleted G x y) σ))
  have hq := deleted_edge_walk_length G hxy (q.map (coverProjection (edgeDeleted G x y) σ))
  have hp' : G.girth ≤ p.length + 1 := (Walk.length_map _ p) ▸ hp
  have hq' : G.girth ≤ q.length + 1 := (Walk.length_map _ q) ▸ hq
  omega

end Paper
