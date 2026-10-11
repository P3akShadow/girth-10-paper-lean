import LiftContraction
import MergeDegrees

/-! Intermediate partitions in the proof of Lemma 9. A base fiber is either
already contracted or consists of its two singleton bags. -/

namespace Paper
open Finset
variable {V : Type*} [DecidableEq V] {S : Finset V}

lemma singleton_totalDegree_le (G : SimpleGraph V) (P : Partition S) (a : V) :
    totalDegree (.ofGraph G) P {a} ≤ (graphNeighbors G S a).card := by
  classical
  have hsub : neighbors (Adjacent (.ofGraph G)) P {a} ⊆
      (graphNeighbors G S a).image P.part := by
    intro B hB
    obtain ⟨hBP,_,a',ha',b,hb,hab⟩ := mem_filter.mp hB
    have haa : a' = a := mem_singleton.mp ha'
    have hab' : G.Adj a b := by simpa [Trigraph.ofGraph,haa] using hab
    exact mem_image.mpr ⟨b,mem_filter.mpr ⟨P.subset hBP hb,hab'⟩,
      P.part_eq_of_mem hBP hb⟩
  exact (card_le_card hsub).trans card_image_le

def FiberState (P : Partition (liftVertices S)) : Prop :=
  ∀ u ∈ S, fiber u ∈ P.parts ∨ ({(u,false)} ∈ P.parts ∧ {(u,true)} ∈ P.parts)

lemma fiber_ne_singleton (u : V) (a : V × Bool) : fiber u ≠ {a} := by
  intro h
  have hh := congrArg card h
  have hne : (u,false) ≠ (u,true) := by simp
  simp [fiber,card_pair hne] at hh

lemma FiberState.bot : FiberState (⊥ : Partition (liftVertices S)) := by
  intro u hu
  right
  constructor <;> apply Finpartition.mem_bot_iff.mpr
  · exact ⟨(u,false),mem_liftVertices.mpr hu,rfl⟩
  · exact ⟨(u,true),mem_liftVertices.mpr hu,rfl⟩

lemma FiberState.merge {P Q : Partition (liftVertices S)} (hP : FiberState P)
    {u : V} (hQ : Q.parts = insert (fiber u) (P.parts \ {{(u,false)},{(u,true)}})) :
    FiberState Q := by
  intro v hv
  by_cases hvu : v = u
  · subst v
    exact Or.inl (hQ ▸ mem_insert_self _ _)
  · have hs : ∀ i j : Bool, ({(v,i)} : Finset (V × Bool)) ≠ {(u,j)} := by
      intro i j heq
      exact hvu (congrArg Prod.fst (singleton_inj.mp heq))
    rcases hP v hv with h | ⟨h0,h1⟩
    · left
      rw [hQ]
      exact mem_insert_of_mem (mem_sdiff.mpr ⟨h,by simp [fiber_ne_singleton]⟩)
    · right
      rw [hQ]
      constructor
      · exact mem_insert_of_mem (mem_sdiff.mpr ⟨h0,by simp [hs]⟩)
      · exact mem_insert_of_mem (mem_sdiff.mpr ⟨h1,by simp [hs]⟩)

lemma fiberExpansion_bot_parts :
    ((fiberExpansion S).partition ⊥).parts = S.image fiber := by
  ext A
  simp only [Expansion.partition_parts,mem_image,Finpartition.mem_bot_iff]
  constructor
  · rintro ⟨B,⟨u,hu,rfl⟩,hBA⟩
    exact ⟨u,hu,by simpa [Expansion.bag,fiberExpansion] using hBA⟩
  · rintro ⟨u,hu,rfl⟩
    exact ⟨{u},⟨u,hu,rfl⟩,by simp [Expansion.bag,fiberExpansion]⟩

lemma fiberState_complete {P : Partition (liftVertices S)}
    (h : ∀ u ∈ S, fiber u ∈ P.parts) : P = (fiberExpansion S).partition ⊥ := by
  apply Finpartition.ext
  rw [fiberExpansion_bot_parts]
  apply Subset.antisymm
  · intro A hA
    obtain ⟨a,ha⟩ := P.nonempty_of_mem_parts hA
    have haS : a.1 ∈ S := mem_liftVertices.mp (P.subset hA ha)
    exact mem_image.mpr ⟨a.1,haS,(P.eq_of_mem_parts (h a.1 haS) hA
      (mem_fiber.mpr rfl) ha)⟩
  · intro A hA
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hA
    exact h u hu

omit [DecidableEq V] in
/-- A walk leaving the set of already contracted fibers has a first edge
from a contracted fiber to an uncontracted fiber. -/
lemma walk_crosses (H : SimpleGraph V) (D : V → Prop) {u v : V}
    (p : H.Walk u v) (hu : D u) (hv : ¬ D v) :
    ∃ a b, D a ∧ ¬ D b ∧ H.Adj a b := by
  classical
  induction p with
  | nil => exact False.elim (hv hu)
  | @cons u w v huw p ih =>
    by_cases hw : D w
    · exact ih hw hv
    · exact ⟨u,w,hu,hw,huw⟩

lemma bounded_merge_total (T : Trigraph V) {P Q : Partition S} {A B : Finset V}
    {s : ℕ} (hA : A ∈ P.parts) (hB : B ∈ P.parts) (hAB : A ≠ B)
    (hQ : Q.parts = insert (A ∪ B) (P.parts \ {A,B}))
    (hP : Bounded T s s P) (hnew : totalDegree T Q (A ∪ B) ≤ s) :
    Bounded T s s Q := by
  intro X hX
  have ht : totalDegree T Q X ≤ s := by
    rw [hQ] at hX
    rcases mem_insert.mp hX with rfl | hX
    · exact hnew
    · obtain ⟨hXP,hXAB⟩ := mem_sdiff.mp hX
      have hXA : X ≠ A := fun h => hXAB (by simp [h])
      have hXB : X ≠ B := fun h => hXAB (by simp [h])
      exact (outside_totalDegree_le T hA hB hAB hQ hXP hXA hXB).trans (hP X hXP).2
  exact ⟨(redDegree_le_totalDegree T Q X).trans ht,ht⟩

lemma Continuation.monoBounds {T : Trigraph V} {P : Partition S} {w s w' s' : ℕ}
    (h : Continuation T w s P) (hw : w ≤ w') (hs : s ≤ s') :
    Continuation T w' s' P := by
  have hb : ∀ P : Partition S, Bounded T w s P → Bounded T w' s' P := by
    intro P hP A hA
    exact ⟨(hP A hA).1.trans hw,(hP A hA).2.trans hs⟩
  induction h with
  | done hP hf => exact .done (hb _ hP) hf
  | step hP hm _ ih => exact .step (hb _ hP) hm ih

end Paper
