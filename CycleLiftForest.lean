import PaperDefinitions
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! The tree-identification observation used in the proof of Lemma 2. -/
namespace Paper.CycleLift
open SimpleGraph
variable {V : Type*} [DecidableEq V]

/-- Identify `v` with `u`, retaining `u` as representative. -/
def identify (u v x : V) : V := if x = v then u else x

lemma identify_self (u v : V) : identify u v v = u := by simp [identify]
lemma identify_left (u v : V) : identify u v u = u := by simp [identify]
lemma identify_eq_of_ne {u v x y : V} (h : identify u v x = y) (hy : y ≠ u) :
    x = y ∧ y ≠ v := by
  unfold identify at h
  split_ifs at h with hx
  · exact False.elim (hy h.symm)
  · exact ⟨h, h ▸ hx⟩

lemma identify_adj_away {G : SimpleGraph V} {u v x y : V}
    (h : (G.map (identify u v)).Adj x y) (hx : x ≠ u) (hy : y ≠ u) :
    G.Adj x y := by
  obtain ⟨_, a, b, hab, ha, hb⟩ := (SimpleGraph.map_adj' _ _ _ _).mp h
  obtain ⟨rfl, _⟩ := identify_eq_of_ne ha hx
  obtain ⟨rfl, _⟩ := identify_eq_of_ne hb hy
  exact hab

lemma identify_adj_left {G : SimpleGraph V} {u v y : V}
    (h : (G.map (identify u v)).Adj u y) :
    ∃ x, (x = u ∨ x = v) ∧ G.Adj x y := by
  obtain ⟨hne, a, b, hab, ha, hb⟩ := (SimpleGraph.map_adj' _ _ _ _).mp h
  obtain ⟨rfl, _⟩ := identify_eq_of_ne hb hne.symm
  refine ⟨a, ?_, hab⟩
  by_cases hav : a = v
  · exact Or.inr hav
  · exact Or.inl (by simpa [identify, hav] using ha)

lemma identify_adj_not_right {G : SimpleGraph V} {u v x y : V}
    (huv : u ≠ v) (h : (G.map (identify u v)).Adj x y) : x ≠ v ∧ y ≠ v := by
  obtain ⟨_, a, b, _, ha, hb⟩ := (SimpleGraph.map_adj' _ _ _ _).mp h
  constructor <;> intro heq
  · have hh := ha.trans heq
    unfold identify at hh
    split_ifs at hh with h <;> aesop
  · have hh := hb.trans heq
    unfold identify at hh
    split_ifs at hh with h <;> aesop

/-- Walks avoiding the identified vertex retain their edges and vertices. -/
def liftAway {G : SimpleGraph V} {u v x y : V}
    (p : (G.map (identify u v)).Walk x y)
    (hp : u ∉ p.support) : G.Walk x y :=
  match p with
  | .nil => .nil
  | .cons h p =>
    .cons (identify_adj_away h
      (fun heq => hp (by simp [heq]))
      (fun heq => hp (by simp [← heq, p.start_mem_support])))
      (liftAway p (fun hm => hp (by simp [hm])))

@[simp] lemma liftAway_support {G : SimpleGraph V} {u v x y : V}
    (p : (G.map (identify u v)).Walk x y) (hp : u ∉ p.support) :
    (liftAway p hp).support = p.support := by
  induction p with
  | nil => rfl
  | cons h p ih => simp [liftAway, ih]

@[simp] lemma liftAway_length {G : SimpleGraph V} {u v x y : V}
    (p : (G.map (identify u v)).Walk x y) (hp : u ∉ p.support) :
    (liftAway p hp).length = p.length := by
  induction p with
  | nil => rfl
  | cons h p ih => simp [liftAway, ih]

lemma map_walk_not_mem_right {G : SimpleGraph V} {u v x y : V}
    (huv : u ≠ v) (p : (G.map (identify u v)).Walk x y) (hx : x ≠ v) :
    v ∉ p.support := by
  induction p with
  | nil => simpa using hx.symm
  | cons h p ih =>
    simp only [Walk.support_cons, List.mem_cons, not_or]
    exact ⟨hx.symm, ih (identify_adj_not_right huv h).2⟩

/-- Graph distance at most two, phrased without the disconnected-distance convention. -/
def Near (G : SimpleGraph V) (u v : V) : Prop :=
  u = v ∨ G.Adj u v ∨ ∃ w, G.Adj u w ∧ G.Adj w v

omit [DecidableEq V] in
lemma Near.symm {G : SimpleGraph V} {u v : V} (h : Near G u v) : Near G v u := by
  rcases h with rfl | h | ⟨w, h₁, h₂⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl h.symm)
  · exact Or.inr (Or.inr ⟨w, h₂.symm, h₁.symm⟩)

lemma Near.exists_path {G : SimpleGraph V} {u v : V} (h : Near G u v) :
    ∃ p : G.Walk u v, p.IsPath ∧ p.length ≤ 2 := by
  rcases h with rfl | h | ⟨w, h₁, h₂⟩
  · exact ⟨.nil, by simp, by simp⟩
  · exact ⟨.cons h .nil, by simpa [Walk.isPath_def] using h.ne, by simp⟩
  · by_cases huv : u = v
    · subst v; exact ⟨.nil, by simp, by simp⟩
    · refine ⟨.cons h₁ (.cons h₂ .nil), ?_, by simp⟩
      simp [Walk.isPath_def, h₁.ne, h₂.ne, huv]

lemma Near.path_length_le {G : SimpleGraph V} {u v : V} (h : Near G u v)
    (hG : G.IsAcyclic) {p : G.Walk u v} (hp : p.IsPath) : p.length ≤ 2 := by
  obtain ⟨q, hq, hl⟩ := h.exists_path
  have heq : p = q := congrArg Subtype.val ((hG.subsingleton_path _ _).elim ⟨p, hp⟩ ⟨q, hq⟩)
  simpa [heq] using hl

omit [DecidableEq V] in
lemma near_of_walk {G : SimpleGraph V} {u v : V} (p : G.Walk u v)
    (hp : p.length ≤ 2) : Near G u v := by
  cases p with
  | nil => exact Or.inl rfl
  | cons h p =>
    cases p with
    | nil => exact Or.inr (Or.inl h)
    | cons h' p =>
      cases p with
      | nil => exact Or.inr (Or.inr ⟨_, h, h'⟩)
      | cons h'' p => simp at hp

omit [DecidableEq V] in
lemma Near.map {W : Type*} {G : SimpleGraph V} {u v : V}
    (h : Near G u v) (f : V → W) : Near (G.map f) (f u) (f v) := by
  rcases h with rfl | h | ⟨w, h₁, h₂⟩
  · exact Or.inl rfl
  · by_cases he : f u = f v
    · exact Or.inl he
    · exact Or.inr (Or.inl (SimpleGraph.map_adj_apply' h he))
  · by_cases hu : f u = f w
    · by_cases hv : f w = f v
      · exact Or.inl (hu.trans hv)
      · exact Or.inr (Or.inl (hu ▸ SimpleGraph.map_adj_apply' h₂ hv))
    · by_cases hv : f w = f v
      · exact Or.inr (Or.inl (hv ▸ SimpleGraph.map_adj_apply' h₁ hu))
      · exact Or.inr (Or.inr ⟨f w, SimpleGraph.map_adj_apply' h₁ hu,
          SimpleGraph.map_adj_apply' h₂ hv⟩)

omit [DecidableEq V] in
lemma cycle_of_tail_support {G : SimpleGraph V} {u : V} {p : G.Walk u u}
    (hn : p.support.tail.Nodup) (hl : 3 ≤ p.length) : p.IsCycle := by
  apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
  refine ⟨(Walk.isPath_def _).mpr ?_, hl⟩
  rw [p.support_tail_of_not_nil (Walk.not_nil_iff_lt_length.mpr (by omega))]
  exact hn

lemma no_cycle_at_identified {G : SimpleGraph V} {u v : V}
    (huv : u ≠ v) (hG : G.IsAcyclic) (hd : Near G u v)
    (c : (G.map (identify u v)).Walk u u) : ¬ c.IsCycle := by
  intro hc
  have hcl := hc.isCircuit.three_le_length
  have htn : ¬ c.tail.Nil := Walk.not_nil_iff_lt_length.mpr (by rw [Walk.length_tail]; omega)
  let q := c.tail.dropLast
  have hq : q.IsPath := hc.isPath_tail.dropLast
  have hql : 1 ≤ q.length := by dsimp [q]; rw [Walk.length_dropLast, Walk.length_tail]; omega
  have huq : u ∉ q.support := by
    have hn := hc.isPath_tail.support_nodup
    rw [← Walk.support_dropLast_concat htn] at hn
    have hh := (List.nodup_append.mp hn).2.2
    exact fun hmem => hh u hmem u (by simp) rfl
  obtain ⟨x, hx, hxs⟩ := identify_adj_left (c.adj_snd hc.not_nil)
  obtain ⟨y, hy, hyt⟩ := identify_adj_left (c.tail.adj_penultimate htn).symm
  have hvq : v ∉ q.support := map_walk_not_mem_right huv q
    (identify_adj_not_right huv (c.adj_snd hc.not_nil)).2
  let r := liftAway q huq
  have hr : r.IsPath := (Walk.isPath_def _).mpr (by simpa [r] using hq.support_nodup)
  have hxr : x ∉ r.support := by
    simp only [r, liftAway_support]
    rcases hx with rfl | rfl <;> assumption
  have hyr : y ∉ r.support := by
    simp only [r, liftAway_support]
    rcases hy with rfl | rfl <;> assumption
  let t := r.concat hyt.symm
  have ht : t.IsPath := hr.concat hyr hyt.symm
  have htl : 2 ≤ t.length := by simpa [t, r] using Nat.add_le_add_right hql 1
  by_cases hxy : x = y
  · subst y
    have hh : (Walk.cons hxs t).IsCycle := by
      apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
      exact ⟨by simpa using ht, by simp only [Walk.length_cons]; omega⟩
    exact hG _ hh
  · have hxt : x ∉ t.support := by simp [t, Walk.support_concat, hxr, hxy]
    have hpath := ht.cons hxt (h := hxs)
    have hnear : Near G x y := by
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact Or.inl rfl
      · exact hd
      · exact hd.symm
      · exact Or.inl rfl
    have hh := hnear.path_length_le hG hpath
    simp only [Walk.length_cons] at hh
    omega

/-- Identifying two vertices at distance at most two preserves a simple forest.
Loops and parallel edges disappear in `SimpleGraph.map`, as in the paper. -/
lemma identify_isAcyclic {G : SimpleGraph V} {u v : V}
    (hG : G.IsAcyclic) (hd : Near G u v) : (G.map (identify u v)).IsAcyclic := by
  by_cases huv : u = v
  · subst v
    have he : identify u u = id := by ext x; simp [identify]; exact Eq.symm
    simpa [he] using hG
  intro w c hc
  by_cases hu : u ∈ c.support
  · exact no_cycle_at_identified huv hG hd (c.rotate u hu) (hc.rotate hu)
  · let q := liftAway c hu
    have hql : 3 ≤ q.length := by simpa [q] using hc.isCircuit.three_le_length
    have hqn : q.support.tail.Nodup := by simpa [q] using hc.support_nodup
    exact hG q (cycle_of_tail_support hqn hql)

/-- The selected endpoint pairs of distinct quotient bags are disjoint. -/
def Separated {I : Type*} (a b : I → V) : Prop :=
  ∀ i j, i ≠ j → a i ≠ a j ∧ a i ≠ b j ∧ b i ≠ a j ∧ b i ≠ b j

lemma identify_many {I : Type*} [DecidableEq I] {G : SimpleGraph V}
    (hG : G.IsAcyclic) (a b : I → V) (hs : Separated a b)
    (hd : ∀ i, Near G (a i) (b i)) (s : Finset I) :
    ∃ f : V → V, (G.map f).IsAcyclic ∧
      (∀ i, f (a i) = a i) ∧ (∀ i, f (b i) = if i ∈ s then a i else b i) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨id, by simpa using hG, by simp, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨f, hf, ha, hb⟩ := ih
    have hbi : f (b i) = b i := by simpa [hi] using hb i
    have hnear : Near (G.map f) (a i) (b i) := by simpa [ha i, hbi] using (hd i).map f
    refine ⟨identify (a i) (b i) ∘ f, ?_, ?_, ?_⟩
    · rw [← SimpleGraph.map_map]
      exact identify_isAcyclic hf hnear
    · intro j
      simp only [Function.comp_apply, ha]
      by_cases hji : j = i
      · subst j; exact identify_left _ _
      · simp [identify, (hs j i hji).2.1]
    · intro j
      simp only [Function.comp_apply, hb]
      by_cases hji : j = i
      · subst j; simp [hi, identify_self]
      · have hjb : b j ≠ b i := (hs j i hji).2.2.2
        have hja : a j ≠ b i := (hs j i hji).2.1
        by_cases hjs : j ∈ s <;> simp [hjs, hji, identify, hjb, hja]

lemma cycle_crossing_not_isAcyclic {G : SimpleGraph V} (n : ℕ)
    (a b : Fin (n + 3) → V) (hs : Separated a b)
    (hd : ∀ i, Near G (a i) (b i))
    (he : ∀ i, G.Adj (b i) (a (i + 1))) : ¬ G.IsAcyclic := by
  intro hG
  obtain ⟨f, hf, ha, hb⟩ := identify_many hG a b hs hd Finset.univ
  have hab : ∀ i, f (b i) = a i := by simpa using hb
  have hainj : Function.Injective a := fun i j heq => by
    by_contra hne
    exact (hs i j hne).1 heq
  have hcross : ∀ i, (G.map f).Adj (a i) (a (i + 1)) := by
    intro i
    have hne : i ≠ i + 1 := by
      intro hh
      have hh' : (0 : Fin (n + 3)) = 1 := by simpa using congrArg (fun z => z - i) hh
      have hv := congrArg Fin.val hh'
      simp at hv
    have hff : f (b i) ≠ f (a (i + 1)) := by rw [hab, ha]; exact hainj.ne hne
    simpa [hab, ha] using SimpleGraph.map_adj_apply' (he i) hff
  let F : cycleGraph (n + 3) →g G.map f := {
    toFun := a
    map_rel' := by
      intro i j hij
      rw [cycleGraph_adj] at hij
      rcases hij with hij | hji
      · have hh : i = j + 1 := by simpa [add_comm] using (sub_eq_iff_eq_add).mp hij
        simpa [hh] using (hcross j).symm
      · have hh : j = i + 1 := by simpa [add_comm] using (sub_eq_iff_eq_add).mp hji
        simpa [hh] using hcross i }
  exact hf _ ((cycleGraph.isCycle_cycle (n := n)).map (f := F) hainj)

end Paper.CycleLift
