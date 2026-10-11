import PaperDefinitions

namespace Paper

open Finset
variable {V : Type*} [DecidableEq V] {S : Finset V}

/-- The union operation on partitions from Section 2. -/
def mergePartition (P : Partition S) (A B : Finset V)
    (hA : A ∈ P.parts) (hB : B ∈ P.parts) : Partition S := by
  apply Finpartition.ofExistsUnique (insert (A ∪ B) (P.parts \ {A, B}))
  · intro C hC
    rcases mem_insert.mp hC with rfl | hC
    · exact union_subset (P.subset hA) (P.subset hB)
    · exact P.subset (mem_sdiff.mp hC).1
  · intro v hv
    obtain ⟨C, hC, hvC⟩ := P.exists_mem hv
    have unique : ∀ D ∈ P.parts, v ∈ D → D = C :=
      fun _ hD hvD => P.eq_of_mem_parts hD hC hvD hvC
    by_cases hin : C = A ∨ C = B
    · refine ⟨A ∪ B, ?_, ?_⟩
      · simp only [mem_insert, true_or, true_and, mem_union]
        rcases hin with rfl | rfl
        · exact Or.inl hvC
        · exact Or.inr hvC
      · intro D hD
        obtain ⟨hDP, hvD⟩ := hD
        rcases mem_insert.mp hDP with rfl | hDP
        · rfl
        · obtain ⟨hDP, hDAB⟩ := mem_sdiff.mp hDP
          have hDC := unique D hDP hvD
          exact False.elim (hDAB (by simp [hDC, hin]))
    · have hCA : C ≠ A := fun h => hin (Or.inl h)
      have hCB : C ≠ B := fun h => hin (Or.inr h)
      refine ⟨C, ⟨by simp [hC, hCA, hCB], hvC⟩, ?_⟩
      rintro D ⟨hD, hvD⟩
      rcases mem_insert.mp hD with rfl | hD
      · rcases mem_union.mp hvD with hvA | hvB
        · exact False.elim (hCA (P.eq_of_mem_parts hC hA hvC hvA))
        · exact False.elim (hCB (P.eq_of_mem_parts hC hB hvC hvB))
      · exact unique D (mem_sdiff.mp hD).1 hvD
  · simp [eq_comm (a := (∅ : Finset V)), P.ne_empty hA, P.empty_notMem_parts]

lemma mergePartition_parts (P : Partition S) {A B : Finset V}
    (hA : A ∈ P.parts) (hB : B ∈ P.parts) :
    (mergePartition P A B hA hB).parts = insert (A ∪ B) (P.parts \ {A, B}) := rfl

lemma Merge.card_lt {P Q : Partition S} (h : Merge P Q) : Q.parts.card < P.parts.card := by
  obtain ⟨A, hA, B, hB, hAB, hQ⟩ := h
  have hsub : {A, B} ⊆ P.parts := by
    intro C hC
    rcases mem_insert.mp hC with rfl | hC
    · exact hA
    · exact (mem_singleton.mp hC) ▸ hB
  have hcard := card_le_card hsub
  rw [card_pair hAB] at hcard
  rw [hQ]
  apply lt_of_le_of_lt (card_insert_le _ _) ?_
  rw [card_sdiff_of_subset hsub, card_pair hAB]
  omega

lemma partition_card_le (P : Partition S) : P.parts.card ≤ S.card := by
  calc
    P.parts.card = ∑ _A ∈ P.parts, 1 := by simp
    _ ≤ ∑ A ∈ P.parts, A.card := sum_le_sum fun A hA =>
      one_le_card.mpr (P.nonempty_of_mem_parts hA)
    _ = S.card := P.sum_card_parts

lemma bounded_card (T : Trigraph V) (P : Partition S) : Bounded T S.card S.card P := by
  classical
  intro A _
  exact ⟨(card_filter_le ..).trans (partition_card_le P),
    (card_filter_le ..).trans (partition_card_le P)⟩

lemma continuation_exists (T : Trigraph V) (P : Partition S) :
    Continuation T S.card S.card P := by
  induction hn : P.parts.card using Nat.strong_induction_on generalizing P with
  | h n ih =>
    by_cases hsmall : P.parts.card ≤ 1
    · exact .done (bounded_card T P) hsmall
    · have hpairs := mt card_le_one.mpr hsmall
      push Not at hpairs
      obtain ⟨A, hA, B, hB, hAB⟩ := hpairs
      let Q := mergePartition P A B hA hB
      have hmerge : Merge P Q := ⟨A, hA, B, hB, hAB, rfl⟩
      exact .step (bounded_card T P) hmerge (ih Q.parts.card (hn ▸ hmerge.card_lt) Q rfl)

lemma widths_exist (T : Trigraph V) (S : Finset V) : HasWidths T S S.card S.card :=
  continuation_exists T ⊥

lemma twinWidth_witness (T : Trigraph V) (S : Finset V) :
    ∃ s, HasWidths T S (twinWidth T S) s := by
  apply Nat.sInf_mem (s := {w | ∃ s, HasWidths T S w s})
  exact ⟨S.card, S.card, widths_exist T S⟩

lemma sparseTwinWidth_witness (T : Trigraph V) (S : Finset V) :
    ∃ w, HasWidths T S w (sparseTwinWidth T S) := by
  apply Nat.sInf_mem (s := {s | ∃ w, HasWidths T S w s})
  exact ⟨S.card, S.card, widths_exist T S⟩

lemma twinWidth_le {T : Trigraph V} {w s : ℕ} (h : HasWidths T S w s) :
    twinWidth T S ≤ w := Nat.sInf_le ⟨s, h⟩

lemma sparseTwinWidth_le {T : Trigraph V} {w s : ℕ} (h : HasWidths T S w s) :
    sparseTwinWidth T S ≤ s := Nat.sInf_le ⟨w, h⟩

end Paper
