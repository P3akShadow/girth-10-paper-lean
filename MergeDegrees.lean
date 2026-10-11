import GraphDegrees
import Expansion

/-! Total-degree calculations used in Lemma 9 and Proposition 14. -/

namespace Paper
open Finset
variable {V : Type*} [DecidableEq V] {S : Finset V}

lemma adjacent_union_left (T : Trigraph V) (A B X : Finset V) :
    Adjacent T (A ∪ B) X ↔ Adjacent T A X ∨ Adjacent T B X := by
  simp [Adjacent, or_and_right, exists_or]

lemma adjacent_union_right (T : Trigraph V) (X A B : Finset V) :
    Adjacent T X (A ∪ B) ↔ Adjacent T X A ∨ Adjacent T X B := by
  constructor
  · intro h
    rcases (adjacent_union_left T A B X).mp (adjacent_symm T h) with ha | hb
    · exact Or.inl (adjacent_symm T ha)
    · exact Or.inr (adjacent_symm T hb)
  · rintro (ha | hb)
    · exact adjacent_symm T ((adjacent_union_left T A B X).mpr (Or.inl (adjacent_symm T ha)))
    · exact adjacent_symm T ((adjacent_union_left T A B X).mpr (Or.inr (adjacent_symm T hb)))

lemma union_not_part (P : Partition S) {A B : Finset V}
    (hA : A ∈ P.parts) (hB : B ∈ P.parts) (hAB : A ≠ B) : A ∪ B ∉ P.parts := by
  intro hU
  obtain ⟨a, ha⟩ := P.nonempty_of_mem_parts hA
  obtain ⟨b, hb⟩ := P.nonempty_of_mem_parts hB
  have hAU := P.eq_of_mem_parts hA hU ha (mem_union_left B ha)
  have hBU := P.eq_of_mem_parts hB hU hb (mem_union_right A hb)
  exact hAB (hAU.trans hBU.symm)

lemma outside_totalDegree_le (T : Trigraph V) {P Q : Partition S} {A B X : Finset V}
    (hA : A ∈ P.parts) (hB : B ∈ P.parts) (_hAB : A ≠ B)
    (hQ : Q.parts = insert (A ∪ B) (P.parts \ {A, B}))
    (_hX : X ∈ P.parts) (hXA : X ≠ A) (hXB : X ≠ B) :
    totalDegree T Q X ≤ totalDegree T P X := by
  classical
  let f : Finset V → Finset V := fun C => if C = A ∨ C = B then A ∪ B else C
  have hsub : neighbors (Adjacent T) Q X ⊆ (neighbors (Adjacent T) P X).image f := by
    intro C hC
    obtain ⟨hCQ, hCX, hXC⟩ := mem_filter.mp hC
    rw [hQ] at hCQ
    rcases mem_insert.mp hCQ with rfl | hCP
    · rcases (adjacent_union_right T X A B).mp hXC with hXA' | hXB'
      · exact mem_image.mpr ⟨A, mem_filter.mpr ⟨hA, Ne.symm hXA, hXA'⟩, by simp [f]⟩
      · exact mem_image.mpr ⟨B, mem_filter.mpr ⟨hB, Ne.symm hXB, hXB'⟩, by simp [f]⟩
    · obtain ⟨hCP, hCAB⟩ := mem_sdiff.mp hCP
      have hCA : C ≠ A := fun h => hCAB (by simp [h])
      have hCB : C ≠ B := fun h => hCAB (by simp [h])
      exact mem_image.mpr ⟨C, mem_filter.mpr ⟨hCP, hCX, hXC⟩, by simp [f, hCA, hCB]⟩
  exact (card_le_card hsub).trans card_image_le

lemma merged_neighbors_subset (T : Trigraph V) {P Q : Partition S} {A B : Finset V}
    (hQ : Q.parts = insert (A ∪ B) (P.parts \ {A, B})) :
    neighbors (Adjacent T) Q (A ∪ B) ⊆
      (neighbors (Adjacent T) P A).erase B ∪ (neighbors (Adjacent T) P B).erase A := by
  classical
  intro X hX
  obtain ⟨hXQ, hXU, hUX⟩ := mem_filter.mp hX
  rw [hQ] at hXQ
  obtain ⟨hXP, hXAB⟩ := mem_sdiff.mp ((mem_insert.mp hXQ).resolve_left hXU)
  have hXA : X ≠ A := fun h => hXAB (by simp [h])
  have hXB : X ≠ B := fun h => hXAB (by simp [h])
  rcases (adjacent_union_left T A B X).mp hUX with hAX | hBX
  · exact mem_union_left _ (mem_erase.mpr ⟨hXB, mem_filter.mpr ⟨hXP, hXA, hAX⟩⟩)
  · exact mem_union_right _ (mem_erase.mpr ⟨hXA, mem_filter.mpr ⟨hXP, hXB, hBX⟩⟩)

lemma merged_totalDegree_le_sum (T : Trigraph V) {P Q : Partition S} {A B : Finset V}
    (hQ : Q.parts = insert (A ∪ B) (P.parts \ {A, B})) :
    totalDegree T Q (A ∪ B) ≤ totalDegree T P A + totalDegree T P B := by
  exact (card_le_card (merged_neighbors_subset T hQ)).trans
    ((card_union_le ..).trans (Nat.add_le_add card_erase_le card_erase_le))

lemma adjacent_merge_totalDegree (T : Trigraph V) {P Q : Partition S} {A B : Finset V}
    (hA : A ∈ P.parts) (hB : B ∈ P.parts) (hAB : A ≠ B)
    (hQ : Q.parts = insert (A ∪ B) (P.parts \ {A, B})) (hadj : Adjacent T A B) :
    totalDegree T Q (A ∪ B) + 2 ≤ totalDegree T P A + totalDegree T P B := by
  classical
  have hBA : B ∈ neighbors (Adjacent T) P A := mem_filter.mpr ⟨hB, hAB.symm, hadj⟩
  have hAB' : A ∈ neighbors (Adjacent T) P B :=
    mem_filter.mpr ⟨hA, hAB, adjacent_symm T hadj⟩
  have hbound := (card_le_card (merged_neighbors_subset T hQ)).trans (card_union_le ..)
  have ha := card_erase_add_one hBA
  have hb := card_erase_add_one hAB'
  unfold totalDegree
  omega

lemma common_neighbor_merge_totalDegree (T : Trigraph V) {P Q : Partition S}
    {A B C : Finset V} (hQ : Q.parts = insert (A ∪ B) (P.parts \ {A, B}))
    (hC : C ∈ P.parts) (hCA : C ≠ A) (hCB : C ≠ B)
    (hAC : Adjacent T A C) (hBC : Adjacent T B C) :
    totalDegree T Q (A ∪ B) + 1 ≤ totalDegree T P A + totalDegree T P B := by
  classical
  have hsub : neighbors (Adjacent T) Q (A ∪ B) ⊆
      neighbors (Adjacent T) P A ∪ neighbors (Adjacent T) P B :=
    (merged_neighbors_subset T hQ).trans (union_subset_union (erase_subset _ _) (erase_subset _ _))
  have hinter : 1 ≤ (neighbors (Adjacent T) P A ∩ neighbors (Adjacent T) P B).card :=
    one_le_card.mpr ⟨C, mem_inter.mpr ⟨mem_filter.mpr ⟨hC, hCA, hAC⟩,
      mem_filter.mpr ⟨hC, hCB, hBC⟩⟩⟩
  have hcard := card_union_add_card_inter (neighbors (Adjacent T) P A) (neighbors (Adjacent T) P B)
  have hbound := card_le_card hsub
  unfold totalDegree
  omega

lemma swap_merge_totalDegree (T : Trigraph V) {P Q : Partition S} {A B C : Finset V}
    (hC : C ∈ P.parts) (hCA : C ≠ A) (hAC : Adjacent T A C)
    (hQ : Q.parts = insert (A ∪ C) (P.parts \ {A, C}))
    (hleaf : ∀ X ∈ P.parts, Adjacent T C X → X = A ∨ X = B) :
    totalDegree T Q (A ∪ C) ≤ totalDegree T P A := by
  classical
  have hsub : neighbors (Adjacent T) Q (A ∪ C) ⊆
      insert B ((neighbors (Adjacent T) P A).erase C) := by
    intro X hX
    rcases mem_union.mp (merged_neighbors_subset T hQ hX) with hXA | hXC
    · exact mem_insert_of_mem hXA
    · obtain ⟨hXA, hXC⟩ := mem_erase.mp hXC
      obtain ⟨hXP, _, hCX⟩ := mem_filter.mp hXC
      exact mem_insert.mpr (Or.inl ((hleaf X hXP hCX).resolve_left hXA))
  have hCmem : C ∈ neighbors (Adjacent T) P A := mem_filter.mpr ⟨hC, hCA, hAC⟩
  have hbound := (card_le_card hsub).trans (card_insert_le ..)
  have hcard := card_erase_add_one hCmem
  unfold totalDegree
  omega

end Paper
