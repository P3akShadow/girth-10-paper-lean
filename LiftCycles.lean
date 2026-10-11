import LiftWalks
import LiftParity
import LiftHorizontal

/-! Cycle encodings and the parity averaging argument in Lemma 8. -/

namespace Paper
open Finset SimpleGraph
variable {V : Type*} [DecidableEq V] [Fintype V]

noncomputable def cycleEdgeSets (G : SimpleGraph V) (g : ℕ) : Finset (Finset (Sym2 V)) := by
  classical
  exact univ.filter fun C => ∃ (u : V) (p : G.Walk u u),
    p.IsCycle ∧ p.length = g ∧ p.edges.toFinset = C

lemma mem_cycleEdgeSets (G : SimpleGraph V) {g : ℕ} {C : Finset (Sym2 V)} :
    C ∈ cycleEdgeSets G g ↔ ∃ (u : V) (p : G.Walk u u),
      p.IsCycle ∧ p.length = g ∧ p.edges.toFinset = C := by
  classical
  simp [cycleEdgeSets]

lemma cycleEdgeSets_nonempty_edges (G : SimpleGraph V) {g : ℕ} {C : Finset (Sym2 V)}
    (hC : C ∈ cycleEdgeSets G g) : C.Nonempty := by
  obtain ⟨u,p,hp,_,rfl⟩ := (mem_cycleEdgeSets G).mp hC
  have hlen := hp.isCircuit.three_le_length
  cases p with
  | nil => simp at hlen
  | @cons u v w h p => exact ⟨s(u,v),by simp⟩

/-- A chosen root and orientation, represented by an injective map from the
standard cycle. Averaging over these maps counts every choice uniformly. -/
def RootedCycle (G : SimpleGraph V) (n : ℕ) (c : Fin (n+3) → V) : Prop :=
  Function.Injective c ∧ ∀ i j, (cycleGraph (n+3)).Adj i j → G.Adj (c i) (c j)

abbrev RootedCycle.hom {G : SimpleGraph V} {n : ℕ} {c : Fin (n+3) → V}
    (hc : RootedCycle G n c) : cycleGraph (n+3) →g G where
  toFun := c
  map_rel' := hc.2 _ _

noncomputable def rootedCycles (G : SimpleGraph V) (n : ℕ) : Finset (Fin (n+3) → V) := by
  classical
  exact univ.filter (RootedCycle G n)

/-- The descent count sums over roots and orientations. At a fixed girth this
weights all ordinary cycles equally, and the paper's expectation argument
applies to each rooted cycle separately. -/
noncomputable def shortestCycleCount (G : SimpleGraph V) : ℕ :=
  (rootedCycles G (G.girth-3)).card

omit [DecidableEq V] in
lemma mem_rootedCycles (G : SimpleGraph V) {n : ℕ} {c : Fin (n+3) → V} :
    c ∈ rootedCycles G n ↔ RootedCycle G n c := by
  classical
  simp [rootedCycles]

omit [DecidableEq V] [Fintype V] in
lemma RootedCycle.isCycle {G : SimpleGraph V} {n : ℕ} {c : Fin (n+3) → V}
    (hc : RootedCycle G n c) : ((cycleGraph.cycle n).map hc.hom).IsCycle :=
  cycleGraph.isCycle_cycle.map hc.1

lemma cycleGraph_tail_support_all (n : ℕ) (i : Fin (n+3)) :
    i ∈ (cycleGraph.cycle n).support.tail := by
  have hn := (cycleGraph.isCycle_cycle (n := n)).support_nodup
  have hfull : (cycleGraph.cycle n).support.tail.toFinset = univ := by
    apply eq_univ_of_card
    rw [List.toFinset_card_of_nodup hn]
    simp
  exact List.mem_toFinset.mp (hfull ▸ mem_univ i)

lemma cycleGraph_edges_all (n : ℕ) :
    (cycleGraph.cycle n).edges.toFinset = (cycleGraph (n+3)).edgeFinset := by
  classical
  have hc : (cycleGraph (n+3)).edgeFinset.card = n+3 := by
    have h := (cycleGraph (n+3)).sum_degrees_eq_twice_card_edges
    simp only [cycleGraph_degree_three_le,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,smul_eq_mul] at h
    omega
  apply eq_of_subset_of_card_le
  · intro e he
    exact mem_edgeFinset.mpr ((cycleGraph.cycle n).edges_subset_edgeSet (List.mem_toFinset.mp he))
  · rw [hc,List.toFinset_card_of_nodup cycleGraph.isCycle_cycle.isCircuit.isTrail.edges_nodup]
    simp

lemma cycleGraph_adj_mem_edges {n : ℕ} {i j : Fin (n+3)}
    (hij : (cycleGraph (n+3)).Adj i j) : s(i,j) ∈ (cycleGraph.cycle n).edges := by
  apply List.mem_toFinset.mp
  rw [cycleGraph_edges_all]
  exact mem_edgeFinset.mpr hij

omit [Fintype V] in
lemma horizontal_rooted_cycle (G : SimpleGraph V) (x y : V) (σ : Signing V)
    {n : ℕ} {c : Fin (n+3) → V × Bool}
    (hc : RootedCycle (girthLift G x y σ) n c)
    (hh : HorizontalWalk ((cycleGraph.cycle n).map hc.hom)) :
    RootedCycle (signedCover (edgeDeleted G x y) σ) n c := by
  refine ⟨hc.1,?_⟩
  intro i j hij
  have hmem : s(c i,c j) ∈ ((cycleGraph.cycle n).map hc.hom).edges := by
    rw [Walk.edges_map]
    exact List.mem_map.mpr ⟨s(i,j),cycleGraph_adj_mem_edges hij,rfl⟩
  rcases hc.2 i j hij with h | h
  · exact h
  · exact False.elim (hh (c i) (c j) hmem h.1)

omit [DecidableEq V] [Fintype V] in
lemma rootedCycle_of_cycle_map (G : SimpleGraph V) {n : ℕ}
    (f : cycleGraph (n+3) →g G) (h : ((cycleGraph.cycle n).map f).IsCycle) :
    RootedCycle G n f := by
  refine ⟨?_,fun _ _ hij => f.map_rel hij⟩
  have hn : ((cycleGraph.cycle n).support.tail.map f).Nodup := by
    simpa only [Walk.support_map,← List.map_tail] using h.support_nodup
  intro i j heq
  exact List.inj_on_of_nodup_map hn (cycleGraph_tail_support_all n i)
    (cycleGraph_tail_support_all n j) heq

def rootedCycleEdges {n : ℕ} (c : Fin (n+3) → V) : Finset (Sym2 V) :=
  ((cycleGraph.cycle n).edges.map (Sym2.map c)).toFinset

omit [Fintype V] in
lemma rootedCycleEdges_nonempty {n : ℕ} (c : Fin (n+3) → V) :
    (rootedCycleEdges c).Nonempty := by
  have hp := (cycleGraph.isCycle_cycle (n := n)).not_nil
  have hh : (cycleGraph.cycle n).edges ≠ [] := by
    intro he
    have hlen := congrArg List.length he
    simp at hlen
  obtain ⟨e,he⟩ := List.exists_mem_of_ne_nil _ hh
  exact ⟨Sym2.map c e,List.mem_toFinset.mpr (List.mem_map.mpr ⟨e,he,rfl⟩)⟩

omit [DecidableEq V] [Fintype V] in
lemma cover_rooted_project (G H : SimpleGraph V) (hsub : H ≤ G) (σ : Signing V)
    {n : ℕ} {c : Fin (n+3) → V × Bool} (hc : RootedCycle (signedCover H σ) n c)
    (hlen : n+3 ≤ G.girth) : RootedCycle H n (Prod.fst ∘ c) := by
  let f : signedCover H σ →g G := {
    toFun := Prod.fst
    map_rel' := fun h => hsub h.1 }
  let p := (cycleGraph.cycle n).map hc.hom
  have hp := hc.isCycle
  have hn : ¬ (p.map f).Nil := by
    apply Walk.not_nil_iff_lt_length.mpr
    simp only [p,Walk.length_map,cycleGraph.length_cycle]
    omega
  have hcycle := noBacktrack_at_girth_isCycle (p.map f) hn
    (cycle_map_noBacktrack f (coverProjection_locallyInjective H σ) hp) (by simpa only [p,Walk.length_map,cycleGraph.length_cycle] using hlen)
  have hcycle' : ((cycleGraph.cycle n).map (f.comp hc.hom)).IsCycle := by
    rw [Walk.map_map] at hcycle
    exact hcycle
  have hinj := (rootedCycle_of_cycle_map G (f.comp hc.hom) hcycle').1
  exact ⟨hinj,fun i j hij => (hc.2 i j hij).1⟩

def Signing.ofEdges (ε : Sym2 V → Bool) : Signing V where
  value u v := ε s(u,v)
  symmetric := by intro u v; rw [Sym2.eq_swap]

local instance : Std.Commutative Bool.xor := ⟨Bool.xor_comm⟩

lemma signingParity_list {E : Type*} [DecidableEq E] (ε : E → Bool) (l : List E)
    (hn : l.Nodup) : signingParity ε l.toFinset = (l.map ε).foldr Bool.xor false := by
  induction l with
  | nil => simp [signingParity]
  | cons e l ih =>
    have he : e ∉ l.toFinset := by simpa using (List.nodup_cons.mp hn).1
    simp only [List.toFinset_cons,signingParity,Finset.fold_insert he,List.map_cons,List.foldr_cons]
    rw [← ih (List.nodup_cons.mp hn).2]
    rfl

omit [DecidableEq V] [Fintype V] in
lemma cover_walk_signingParity (H : SimpleGraph V) (ε : Sym2 V → Bool)
    {a b : V × Bool} (p : (signedCover H (Signing.ofEdges ε)).Walk a b) :
    (((p.map (coverProjection H (Signing.ofEdges ε))).edges.map ε).foldr Bool.xor false) =
      (a.2 ^^ b.2) := by
  induction p with
  | nil => simp
  | @cons a c b hac p ih =>
    simp only [Walk.map_cons,Walk.edges_cons,List.map_cons,List.foldr_cons,ih]
    have he : ε s(a.1,c.1) = (a.2 ^^ c.2) := hac.2.symm
    change (ε s(a.1,c.1) ^^ (c.2 ^^ b.2)) = (a.2 ^^ b.2)
    rw [he]
    cases a.2 <;> cases c.2 <;> cases b.2 <;> rfl

omit [Fintype V] in
lemma cover_rooted_even (H : SimpleGraph V) (ε : Sym2 V → Bool)
    {n : ℕ} {c : Fin (n+3) → V × Bool}
    (hc : RootedCycle (signedCover H (Signing.ofEdges ε)) n c)
    (hbase : RootedCycle H n (Prod.fst ∘ c)) :
    signingParity ε (rootedCycleEdges (Prod.fst ∘ c)) = false := by
  let p := (cycleGraph.cycle n).map hc.hom
  let q := (cycleGraph.cycle n).map hbase.hom
  have hq : q = p.map (coverProjection H (Signing.ofEdges ε)) := by
    rw [Walk.map_map]
    rfl
  have heq : q.edges.toFinset = rootedCycleEdges (Prod.fst ∘ c) := by
    simp only [q,Walk.edges_map]
    rfl
  rw [← heq,signingParity_list ε q.edges hbase.isCycle.isCircuit.isTrail.edges_nodup,hq]
  exact (cover_walk_signingParity H ε p).trans (Bool.xor_self _)

omit [DecidableEq V] [Fintype V] in
lemma cover_hom_eq_of_root {I : Type*} (K : SimpleGraph I) (H : SimpleGraph V)
    (σ : Signing V) (f g : K →g signedCover H σ) (hbase : ∀ i, (f i).1 = (g i).1)
    {u v : I} (p : K.Walk u v) (hu : f u = g u) : f v = g v := by
  induction p with
  | nil => exact hu
  | @cons u w v huw p ih =>
    apply ih
    have hleft := f.map_rel huw
    have hright := g.map_rel huw
    rw [← hu] at hright
    exact coverProjection_locallyInjective H σ _ _ _ hleft hright (hbase w)

omit [DecidableEq V] [Fintype V] in
/-- A projected rooted cycle and its root's bit determine its entire lift. -/
lemma cover_rooted_injective (H : SimpleGraph V) (σ : Signing V) {n : ℕ}
    {c e : Fin (n+3) → V × Bool}
    (hc : RootedCycle (signedCover H σ) n c) (he : RootedCycle (signedCover H σ) n e)
    (hbase : Prod.fst ∘ c = Prod.fst ∘ e) (hroot : (c 0).2 = (e 0).2) : c = e := by
  have hr : hc.hom 0 = he.hom 0 := Prod.ext (congrFun hbase 0) hroot
  funext i
  obtain ⟨p⟩ := (cycleGraph_connected (n := n+2)).preconnected 0 i
  exact cover_hom_eq_of_root _ H σ hc.hom he.hom (fun i => congrFun hbase i) p hr

/-- Each even base cycle contributes at most its two choices of root sheet.
This is the counting direction needed by the expectation argument. -/
theorem cover_rooted_count_le (G H : SimpleGraph V) (hsub : H ≤ G) (ε : Sym2 V → Bool)
    (n : ℕ) (hlen : n+3 ≤ G.girth) :
    (rootedCycles (signedCover H (Signing.ofEdges ε)) n).card ≤
      2 * ((rootedCycles H n).filter (fun c => signingParity ε (rootedCycleEdges c) = false)).card := by
  classical
  let source := rootedCycles (signedCover H (Signing.ofEdges ε)) n
  let target := ((rootedCycles H n).filter (fun c => signingParity ε (rootedCycleEdges c) = false)) ×ˢ
    (univ : Finset Bool)
  let f := fun c : Fin (n+3) → V × Bool => (Prod.fst ∘ c,(c 0).2)
  have himage : source.image f ⊆ target := by
    intro b hb
    obtain ⟨c,hc,rfl⟩ := mem_image.mp hb
    have hc' := (mem_rootedCycles _).mp hc
    have hbase := cover_rooted_project G H hsub (Signing.ofEdges ε) hc' hlen
    exact mem_product.mpr ⟨mem_filter.mpr ⟨(mem_rootedCycles H).mpr hbase,
      cover_rooted_even H ε hc' hbase⟩,mem_univ _⟩
  have hinj : Set.InjOn f source := by
    intro c hc e he heq
    exact cover_rooted_injective H (Signing.ofEdges ε) ((mem_rootedCycles _).mp hc)
      ((mem_rootedCycles _).mp he) (congrArg (fun z : (Fin (n+3) → V) × Bool => z.1) heq)
      (congrArg (fun z : (Fin (n+3) → V) × Bool => z.2) heq)
  have hcard := (card_image_of_injOn hinj).symm.trans_le (card_le_card himage)
  simpa [source,target,Nat.mul_comm] using hcard

end Paper
