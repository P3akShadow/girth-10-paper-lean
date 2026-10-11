import TwinPartition

/-! The preparatory twin-class merges in Proposition 14. -/
namespace Paper
open Finset
variable {V : Type*} [DecidableEq V] {S : Finset V}

inductive Prefix (T : Trigraph V) (w s : ℕ) : Partition S → Partition S → Prop
  | refl (P) : Prefix T w s P P
  | step {P Q R} : Bounded T w s P → Merge P Q → Prefix T w s Q R → Prefix T w s P R

lemma Prefix.append {T : Trigraph V} {w s w' s' : ℕ} {P Q : Partition S}
    (h : Prefix T w s P Q) (hw : w ≤ w') (hs : s ≤ s')
    (hq : Continuation T w' s' Q) : Continuation T w' s' P := by
  induction h with
  | refl => exact hq
  | step hb hm _ ih => exact .step (fun A hA => ⟨(hb A hA).1.trans hw,
      (hb A hA).2.trans hs⟩) hm (ih hq)

lemma Prefix.trans {T : Trigraph V} {w s : ℕ} {P Q R : Partition S}
    (h : Prefix T w s P Q) (h' : Prefix T w s Q R) : Prefix T w s P R := by
  induction h with
  | refl => exact h'
  | step hb hm _ ih => exact .step hb hm (ih h')

lemma merge_contains {P Q : Partition S} (h : Merge P Q) {A : Finset V}
    (hA : A ∈ P.parts) : ∃ B ∈ Q.parts, A ⊆ B := by
  classical
  obtain ⟨B,hB,C,hC,hBC,hQ⟩ := h
  by_cases hAB : A = B
  · subst A; exact ⟨B ∪ C, by rw [hQ]; simp, subset_union_left⟩
  by_cases hAC : A = C
  · subst A; exact ⟨B ∪ C, by rw [hQ]; simp, subset_union_right⟩
  exact ⟨A, by rw [hQ]; simp [hA,hAB,hAC], Subset.rfl⟩

lemma TwinSaturated.merge {G : SimpleGraph V} {P Q : Partition S}
    (h : TwinSaturated G P) (hm : Merge P Q) : TwinSaturated G Q := by
  intro a ha b hb hab
  obtain ⟨C,hC,hsub⟩ := merge_contains hm (P.part_mem.mpr ha)
  have hca := hsub (P.mem_part ha)
  have hcb := hsub (by rw [h a ha b hb hab]; exact P.mem_part hb)
  exact (Q.part_eq_of_mem hC hca).trans (Q.part_eq_of_mem hC hcb).symm

def MonoTwinBags (G : SimpleGraph V) (P : Partition S) : Prop :=
  ∀ A ∈ P.parts, ∀ a ∈ A, ∀ b ∈ A, GraphTwins G S a b

omit [DecidableEq V] in
lemma GraphTwins.adj {G : SimpleGraph V} {a b x : V}
    (h : GraphTwins G S a b) (hx : x ∈ S) : G.Adj a x ↔ G.Adj b x := by
  classical
  have hmem : x ∈ graphNeighbors G S a ↔ x ∈ graphNeighbors G S b := by rw [h]
  simpa [graphNeighbors,hx] using hmem

lemma monoTwinBags_bot (G : SimpleGraph V) : MonoTwinBags G (⊥ : Partition S) := by
  rintro A hA a ha b hb
  obtain ⟨x,_,rfl⟩ := Finpartition.mem_bot_iff.mp hA
  have := mem_singleton.mp ha
  have := mem_singleton.mp hb
  subst a; subst b; rfl

lemma MonoTwinBags.black {G : SimpleGraph V} {P : Partition S}
    (h : MonoTwinBags G P) {A B : Finset V} (hA : A ∈ P.parts) (hB : B ∈ P.parts)
    (hab : Adjacent (.ofGraph G) A B) : Black (.ofGraph G) A B := by
  obtain ⟨a,ha,b,hb,hab | hab⟩ := hab
  · intro x hx y hy
    have hxb := (GraphTwins.adj (h A hA a ha x hx) (P.subset hB hb)).mp hab
    exact ((GraphTwins.adj (h B hB b hb y hy) (P.subset hA hx)).mp hxb.symm).symm
  · exact False.elim hab

lemma MonoTwinBags.bounded {G : SimpleGraph V} {P : Partition S} {d : ℕ}
    (h : MonoTwinBags G P) (hdeg : MaxDegree G S d) : Bounded (.ofGraph G) 0 d P := by
  classical
  intro A hA
  have hr : redDegree (.ofGraph G) P A = 0 := by
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_notMem.mpr
    intro B hB
    obtain ⟨hBP,_,he,hn⟩ := mem_filter.mp hB
    exact hn (h.black hA hBP he)
  have ht := totalDegree_eq_red_add_black (.ofGraph G) P hA
  have hb := blackDegree_le_blackVertices (.ofGraph G) P A
  have hq := blackVertices_card_le_degree G hdeg P hA
  exact ⟨by omega, by omega⟩

lemma monoTwinBags_merge {G : SimpleGraph V} {P Q : Partition S} {A B : Finset V}
    (h : MonoTwinBags G P) (hA : A ∈ P.parts) (hB : B ∈ P.parts)
    (hab : ∀ a ∈ A, ∀ b ∈ B, GraphTwins G S a b)
    (hQ : Q.parts = insert (A ∪ B) (P.parts \ {A,B})) : MonoTwinBags G Q := by
  intro C hC x hx y hy
  rw [hQ] at hC
  rcases mem_insert.mp hC with rfl | hC
  · rcases mem_union.mp hx with hx | hx <;> rcases mem_union.mp hy with hy | hy
    · exact h A hA x hx y hy
    · exact hab x hx y hy
    · exact (hab y hy x hx).symm
    · exact h B hB x hx y hy
  · exact h C (mem_sdiff.mp hC).1 x hx y hy

lemma monoTwinBags_quotient_twins {G : SimpleGraph V} {P : Partition S} {A B : Finset V}
    (h : MonoTwinBags G P) (hA : A ∈ P.parts) (hB : B ∈ P.parts)
    (hab : ∀ a ∈ A, ∀ b ∈ B, GraphTwins G S a b) :
    Twins ((partitionExpansion P).quotient (.ofGraph G)) P.parts A B := by
  intro C hC hCA hCB
  change ((A ≠ C ∧ Black (.ofGraph G) A C) ↔ (B ≠ C ∧ Black (.ofGraph G) B C)) ∧
    ((A ≠ C ∧ Red (.ofGraph G) A C) ↔ (B ≠ C ∧ Red (.ofGraph G) B C))
  have hb : Black (.ofGraph G) A C ↔ Black (.ofGraph G) B C := by
    obtain ⟨a,ha⟩ := P.nonempty_of_mem_parts hA
    obtain ⟨b,hb⟩ := P.nonempty_of_mem_parts hB
    constructor
    · intro hac y hy z hz
      exact (GraphTwins.adj (hab a ha y hy) (P.subset hC hz)).mp (hac a ha z hz)
    · intro hbc x hx z hz
      exact (GraphTwins.adj (hab x hx b hb) (P.subset hC hz)).mpr (hbc b hb z hz)
  have hnA : ¬ Red (.ofGraph G) A C := fun hh => hh.2 (h.black hA hC hh.1)
  have hnB : ¬ Red (.ofGraph G) B C := fun hh => hh.2 (h.black hB hC hh.1)
  exact ⟨⟨fun hh => ⟨Ne.symm hCB, hb.mp hh.2⟩,
    fun hh => ⟨Ne.symm hCA, hb.mpr hh.2⟩⟩,
    ⟨fun hh => False.elim (hnA hh.2), fun hh => False.elim (hnB hh.2)⟩⟩

/-- Merge every original twin class first, using Lemma 13 exactly as in the paper. -/
lemma prepare_twins (G : SimpleGraph V) {d w s : ℕ} (hdeg : MaxDegree G S d)
    (P : Partition S) (hmono : MonoTwinBags G P) (hc : Continuation (.ofGraph G) w s P) :
    ∃ Q : Partition S, Prefix (.ofGraph G) 0 d P Q ∧ MonoTwinBags G Q ∧
      TwinSaturated G Q ∧ Continuation (.ofGraph G) w s Q := by
  classical
  generalize hn : P.parts.card = n
  induction n using Nat.strong_induction_on generalizing P with | h n ih =>
    by_cases hsat : TwinSaturated G P
    · exact ⟨P,.refl P,hmono,hsat,hc⟩
    unfold TwinSaturated at hsat
    push Not at hsat
    obtain ⟨a,ha,b,hb,hab,hne⟩ := hsat
    let A := P.part a
    let B := P.part b
    have hA : A ∈ P.parts := P.part_mem.mpr ha
    have hB : B ∈ P.parts := P.part_mem.mpr hb
    have hab' : ∀ x ∈ A, ∀ y ∈ B, GraphTwins G S x y := by
      intro x hx y hy
      exact (hmono A hA x hx a (P.mem_part ha)).trans
        (hab.trans (hmono B hB b (P.mem_part hb) y hy))
    obtain ⟨R,hR,_,hcR⟩ := exchange (.ofGraph G) hc hA hB hne
      (Or.inl (monoTwinBags_quotient_twins hmono hA hB hab'))
    have hm : Merge P R := ⟨A,hA,B,hB,hne,hR⟩
    obtain ⟨Q,hprefix,hmonoQ,hsatQ,hcQ⟩ := ih R.parts.card (by simpa [←hn] using hm.card_lt)
      R (monoTwinBags_merge hmono hA hB hab' hR) hcR rfl
    exact ⟨Q,.step (hmono.bounded hdeg) hm hprefix,hmonoQ,hsatQ,hcQ⟩

end Paper
