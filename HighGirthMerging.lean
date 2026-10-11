import HighGirth
import MergeDegrees

/-! Exact neighborhood changes in the singleton merges of Lemma 3. -/

namespace Paper
open Finset
variable {V : Type*} [DecidableEq V] {S : Finset V}

omit [DecidableEq V] in
lemma singleton_adjacent_graph (G : SimpleGraph V) (u v : V) :
    Adjacent (.ofGraph G) {u} {v} ↔ G.Adj u v := by
  simp [Adjacent, Trigraph.ofGraph]

omit [DecidableEq V] in
lemma singleton_black_graph (G : SimpleGraph V) (u v : V) :
    Black (.ofGraph G) {u} {v} ↔ G.Adj u v := by
  simp [Black, Trigraph.ofGraph]

omit [DecidableEq V] in
lemma singleton_ne_pair {u : V} {A : Finset V} (h : A.card = 2) : {u} ≠ A := by
  intro he
  rw [← he, card_singleton] at h
  omega

lemma black_union_right (T : Trigraph V) (X A B : Finset V) :
    Black T X (A ∪ B) ↔ Black T X A ∧ Black T X B := by
  constructor
  · intro h
    exact ⟨fun x hx a ha => h x hx a (mem_union_left B ha),
      fun x hx b hb => h x hx b (mem_union_right A hb)⟩
  · rintro ⟨hA, hB⟩ x hx y hy
    exact (mem_union.mp hy).elim (hA x hx y) (hB x hx y)

lemma black_union_left (T : Trigraph V) (A B X : Finset V) :
    Black T (A ∪ B) X ↔ Black T A X ∧ Black T B X := by
  constructor
  · intro h
    exact ⟨fun a ha x hx => h a (mem_union_left B ha) x hx,
      fun b hb x hx => h b (mem_union_right A hb) x hx⟩
  · rintro ⟨hA, hB⟩ y hy x hx
    exact (mem_union.mp hy).elim (fun ha => hA y ha x hx) (fun hb => hB y hb x hx)

lemma merged_blackDegree_zero (T : Trigraph V) {P Q : Partition S} {A B : Finset V}
    (hQ : Q.parts = insert (A ∪ B) (P.parts \ {A, B}))
    (hnot : ∀ X ∈ P.parts, X ≠ A → X ≠ B → ¬ (Black T A X ∧ Black T B X)) :
    blackDegree T Q (A ∪ B) = 0 := by
  classical
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro X hX
  obtain ⟨hXQ, hXU, hblack⟩ := mem_filter.mp hX
  rw [hQ] at hXQ
  obtain ⟨hXP, hXAB⟩ := mem_sdiff.mp ((mem_insert.mp hXQ).resolve_left hXU)
  have hXA : X ≠ A := fun he => hXAB (by simp [he])
  have hXB : X ≠ B := fun he => hXAB (by simp [he])
  exact hnot X hXP hXA hXB ((black_union_left T A B X).mp hblack)

lemma red_union_right_of_red (T : Trigraph V) {X A B : Finset V}
    (h : Red T X A) : Red T X (A ∪ B) := by
  refine ⟨(adjacent_union_right T X A B).mpr (Or.inl h.1), ?_⟩
  intro hb
  exact h.2 ((black_union_right T X A B).mp hb).1

lemma red_union_right_of_red_right (T : Trigraph V) {X A B : Finset V}
    (h : Red T X B) : Red T X (A ∪ B) := by
  rw [union_comm]
  exact red_union_right_of_red T h

lemma merged_neighbors_eq (T : Trigraph V) {P Q : Partition S} {A B : Finset V}
    (hA : A ∈ P.parts) (hB : B ∈ P.parts) (hAB : A ≠ B)
    (hQ : Q.parts = insert (A ∪ B) (P.parts \ {A, B})) :
    neighbors (Adjacent T) Q (A ∪ B) =
      (neighbors (Adjacent T) P A).erase B ∪ (neighbors (Adjacent T) P B).erase A := by
  classical
  apply Subset.antisymm (merged_neighbors_subset T hQ)
  intro C hC
  rcases mem_union.mp hC with hC | hC
  · obtain ⟨hCB, hC⟩ := mem_erase.mp hC
    obtain ⟨hCP, hCA, hAC⟩ := mem_filter.mp hC
    refine mem_filter.mpr ⟨?_, ?_, (adjacent_union_left T A B C).mpr (Or.inl hAC)⟩
    · simp [hQ, hCP, hCA, hCB]
    · intro he
      exact union_not_part P hA hB hAB (he ▸ hCP)
  · obtain ⟨hCA, hC⟩ := mem_erase.mp hC
    obtain ⟨hCP, hCB, hBC⟩ := mem_filter.mp hC
    refine mem_filter.mpr ⟨?_, ?_, (adjacent_union_left T A B C).mpr (Or.inr hBC)⟩
    · simp [hQ, hCP, hCA, hCB]
    · intro he
      exact union_not_part P hA hB hAB (he ▸ hCP)

/-- An old red neighborhood can shrink only when two of its red neighbors
are merged, as observed before the six cases in Lemma 3. -/
lemma outside_redDegree_not_decreased (T : Trigraph V)
    {P Q : Partition S} {A B C : Finset V}
    (hA : A ∈ P.parts) (hB : B ∈ P.parts) (hAB : A ≠ B)
    (hQ : Q.parts = insert (A ∪ B) (P.parts \ {A, B}))
    (hC : C ∈ P.parts) (hCA : C ≠ A) (hCB : C ≠ B)
    (hnot : ¬ (Red T C A ∧ Red T C B)) : redDegree T P C ≤ redDegree T Q C := by
  classical
  let f : Finset V → Finset V := fun X => if X = A ∨ X = B then A ∪ B else X
  have hCU : C ≠ A ∪ B := fun he => union_not_part P hA hB hAB (he ▸ hC)
  have hmap : ∀ X ∈ neighbors (Red T) P C, f X ∈ neighbors (Red T) Q C := by
    intro X hX
    obtain ⟨hXP, hXC, hred⟩ := mem_filter.mp hX
    by_cases hXA : X = A
    · subst X
      simp only [f, true_or, ite_true]
      exact mem_filter.mpr ⟨by simp [hQ], hCU.symm, red_union_right_of_red T hred⟩
    by_cases hXB : X = B
    · subst X
      simp only [f, or_true, ite_true]
      exact mem_filter.mpr ⟨by simp [hQ], hCU.symm, red_union_right_of_red_right T hred⟩
    · simp only [f, hXA, hXB, or_self, ite_false]
      exact mem_filter.mpr ⟨by simp [hQ, hXP, hXA, hXB], hXC, hred⟩
  have hinj : Set.InjOn f (neighbors (Red T) P C) := by
    intro X hX Y hY he
    obtain ⟨hXP, _, hredX⟩ := mem_filter.mp hX
    obtain ⟨hYP, _, hredY⟩ := mem_filter.mp hY
    by_cases hx : X = A ∨ X = B <;> by_cases hy : Y = A ∨ Y = B
    · rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · rfl
      · exact False.elim (hnot ⟨hredX, hredY⟩)
      · exact False.elim (hnot ⟨hredY, hredX⟩)
      · rfl
    · have hUY : A ∪ B = Y := by simpa [f, hx, hy] using he
      exact False.elim (union_not_part P hA hB hAB (hUY.symm ▸ hYP))
    · have hXU : X = A ∪ B := by simpa [f, hx, hy] using he
      exact False.elim (union_not_part P hA hB hAB (hXU ▸ hXP))
    · simpa [f, hx, hy] using he
  exact card_le_card_of_injOn f hmap hinj

/-- Merging a black neighbor with a nonneighbor adds a red neighbor, the
saturation obstruction used in cases 4, 5 and 6 of Lemma 3. -/
lemma outside_redDegree_gain (T : Trigraph V)
    {P Q : Partition S} {A B C : Finset V}
    (hA : A ∈ P.parts) (hB : B ∈ P.parts) (hAB : A ≠ B)
    (hQ : Q.parts = insert (A ∪ B) (P.parts \ {A, B}))
    (hC : C ∈ P.parts) (_hCA : C ≠ A) (_hCB : C ≠ B)
    (hblack : Black T C A) (hnon : ¬ Adjacent T C B) :
    redDegree T Q C = redDegree T P C + 1 := by
  classical
  have hCU : C ≠ A ∪ B := fun he => union_not_part P hA hB hAB (he ▸ hC)
  have hred : Red T C (A ∪ B) := by
    refine ⟨(adjacent_union_right T C A B).mpr (Or.inl
      (black_adjacent T (P.nonempty_of_mem_parts hC) (P.nonempty_of_mem_parts hA) hblack)), ?_⟩
    intro hb
    exact hnon (black_adjacent T (P.nonempty_of_mem_parts hC)
      (P.nonempty_of_mem_parts hB) ((black_union_right T C A B).mp hb).2)
  have heq : neighbors (Red T) Q C = insert (A ∪ B) (neighbors (Red T) P C) := by
    ext X
    constructor
    · intro hX
      obtain ⟨hXQ, hXC, hCX⟩ := mem_filter.mp hX
      rw [hQ] at hXQ
      rcases mem_insert.mp hXQ with rfl | hXQ
      · exact mem_insert_self ..
      · exact mem_insert_of_mem (mem_filter.mpr ⟨(mem_sdiff.mp hXQ).1, hXC, hCX⟩)
    · intro hX
      rcases mem_insert.mp hX with rfl | hX
      · exact mem_filter.mpr ⟨by simp [hQ], hCU.symm, hred⟩
      · obtain ⟨hXP, hXC, hCX⟩ := mem_filter.mp hX
        have hXA : X ≠ A := fun he => hCX.2 (he.symm ▸ hblack)
        have hXB : X ≠ B := fun he => hnon (he ▸ hCX.1)
        exact mem_filter.mpr ⟨by simp [hQ, hXP, hXA, hXB], hXC, hCX⟩
  have hU : A ∪ B ∉ neighbors (Red T) P C := by
    intro h
    exact union_not_part P hA hB hAB (mem_filter.mp h).1
  simpa only [redDegree, heq] using card_insert_of_notMem hU

lemma saturated_black_neighbor_forces_adjacency (T : Trigraph V)
    {P Q : Partition S} {A B C : Finset V} {w s : ℕ}
    (hA : A ∈ P.parts) (hB : B ∈ P.parts) (hAB : A ≠ B)
    (hQ : Q.parts = insert (A ∪ B) (P.parts \ {A, B}))
    (hC : C ∈ P.parts) (hCA : C ≠ A) (hCB : C ≠ B)
    (hsat : redDegree T P C = w) (hbounded : Bounded T w s Q)
    (hblack : Black T C A) : Adjacent T C B := by
  by_contra hnon
  have he := outside_redDegree_gain T hA hB hAB hQ hC hCA hCB hblack hnon
  have hcQ : C ∈ Q.parts := by simp [hQ, hC, hCA, hCB]
  have hb := (hbounded C hcQ).1
  omega

lemma outside_redDegree_stays_saturated (T : Trigraph V)
    {P Q : Partition S} {A B C : Finset V} {w s : ℕ}
    (hA : A ∈ P.parts) (hB : B ∈ P.parts) (hAB : A ≠ B)
    (hQ : Q.parts = insert (A ∪ B) (P.parts \ {A, B}))
    (hC : C ∈ P.parts) (hCA : C ≠ A) (hCB : C ≠ B)
    (hsat : redDegree T P C = w) (hbounded : Bounded T w s Q)
    (hnot : ¬ (Red T C A ∧ Red T C B)) : redDegree T Q C = w := by
  have hl := outside_redDegree_not_decreased T hA hB hAB hQ hC hCA hCB hnot
  have hcQ : C ∈ Q.parts := by simp [hQ, hC, hCA, hCB]
  have hb := (hbounded C hcQ).1
  omega

lemma merge_totalDegree_add_common (T : Trigraph V)
    {P Q : Partition S} {A B : Finset V}
    (hA : A ∈ P.parts) (hB : B ∈ P.parts) (hAB : A ≠ B)
    (hQ : Q.parts = insert (A ∪ B) (P.parts \ {A, B})) :
    totalDegree T Q (A ∪ B) +
      ((neighbors (Adjacent T) P A).erase B ∩ (neighbors (Adjacent T) P B).erase A).card =
      ((neighbors (Adjacent T) P A).erase B).card +
      ((neighbors (Adjacent T) P B).erase A).card := by
  unfold totalDegree
  rw [merged_neighbors_eq T hA hB hAB hQ]
  exact card_union_add_card_inter ..

lemma nonadjacent_merge_totalDegree_add_common (T : Trigraph V)
    {P Q : Partition S} {A B : Finset V}
    (hA : A ∈ P.parts) (hB : B ∈ P.parts) (hAB : A ≠ B)
    (hQ : Q.parts = insert (A ∪ B) (P.parts \ {A, B}))
    (hnon : ¬ Adjacent T A B) :
    totalDegree T Q (A ∪ B) +
      (neighbors (Adjacent T) P A ∩ neighbors (Adjacent T) P B).card =
      totalDegree T P A + totalDegree T P B := by
  classical
  have hBnot : B ∉ neighbors (Adjacent T) P A := by
    intro h
    exact hnon (mem_filter.mp h).2.2
  have hAnot : A ∉ neighbors (Adjacent T) P B := by
    intro h
    exact hnon (adjacent_symm T (mem_filter.mp h).2.2)
  simpa only [erase_eq_of_notMem hBnot, erase_eq_of_notMem hAnot, totalDegree] using
    merge_totalDegree_add_common T hA hB hAB hQ

lemma adjacent_merge_totalDegree_add_common (T : Trigraph V)
    {P Q : Partition S} {A B : Finset V}
    (hA : A ∈ P.parts) (hB : B ∈ P.parts) (hAB : A ≠ B)
    (hQ : Q.parts = insert (A ∪ B) (P.parts \ {A, B}))
    (hadj : Adjacent T A B) :
    totalDegree T Q (A ∪ B) +
      ((neighbors (Adjacent T) P A).erase B ∩ (neighbors (Adjacent T) P B).erase A).card + 2 =
      totalDegree T P A + totalDegree T P B := by
  classical
  have hBmem : B ∈ neighbors (Adjacent T) P A := mem_filter.mpr ⟨hB, hAB.symm, hadj⟩
  have hAmem : A ∈ neighbors (Adjacent T) P B :=
    mem_filter.mpr ⟨hA, hAB, adjacent_symm T hadj⟩
  have he := merge_totalDegree_add_common T hA hB hAB hQ
  have ha := card_erase_add_one hAmem
  have hb := card_erase_add_one hBmem
  unfold totalDegree at he ⊢
  omega

lemma merged_blackDegree_zero_of_no_common (T : Trigraph V)
    {P Q : Partition S} {A B : Finset V}
    (hA : A ∈ P.parts) (hB : B ∈ P.parts)
    (hQ : Q.parts = insert (A ∪ B) (P.parts \ {A, B}))
    (hcommon : Disjoint (neighbors (Adjacent T) P A) (neighbors (Adjacent T) P B)) :
    blackDegree T Q (A ∪ B) = 0 := by
  classical
  apply merged_blackDegree_zero T hQ
  rintro X hX hXA hXB ⟨ha, hb⟩
  exact disjoint_left.mp hcommon
    (mem_filter.mpr ⟨hX, hXA,
      black_adjacent T (P.nonempty_of_mem_parts hA) (P.nonempty_of_mem_parts hX) ha⟩)
    (mem_filter.mpr ⟨hX, hXB,
      black_adjacent T (P.nonempty_of_mem_parts hB) (P.nonempty_of_mem_parts hX) hb⟩)

lemma nonadjacent_no_common_merge_redDegree (T : Trigraph V)
    {P Q : Partition S} {A B : Finset V}
    (hA : A ∈ P.parts) (hB : B ∈ P.parts) (hAB : A ≠ B)
    (hQ : Q.parts = insert (A ∪ B) (P.parts \ {A, B}))
    (hnon : ¬ Adjacent T A B)
    (hcommon : Disjoint (neighbors (Adjacent T) P A) (neighbors (Adjacent T) P B)) :
    redDegree T Q (A ∪ B) = totalDegree T P A + totalDegree T P B := by
  have hu : A ∪ B ∈ Q.parts := by simp [hQ]
  have ht := nonadjacent_merge_totalDegree_add_common T hA hB hAB hQ hnon
  rw [disjoint_iff_inter_eq_empty.mp hcommon, card_empty, Nat.add_zero] at ht
  have hr := totalDegree_eq_red_add_black T Q hu
  rw [merged_blackDegree_zero_of_no_common T hA hB hQ hcommon, Nat.add_zero] at hr
  omega

lemma adjacent_no_common_merge_redDegree (T : Trigraph V)
    {P Q : Partition S} {A B : Finset V}
    (hA : A ∈ P.parts) (hB : B ∈ P.parts) (hAB : A ≠ B)
    (hQ : Q.parts = insert (A ∪ B) (P.parts \ {A, B}))
    (hadj : Adjacent T A B)
    (hcommon : Disjoint (neighbors (Adjacent T) P A) (neighbors (Adjacent T) P B)) :
    redDegree T Q (A ∪ B) + 2 = totalDegree T P A + totalDegree T P B := by
  have hu : A ∪ B ∈ Q.parts := by simp [hQ]
  have ht := adjacent_merge_totalDegree_add_common T hA hB hAB hQ hadj
  have hd := hcommon.mono (erase_subset B _) (erase_subset A _)
  rw [disjoint_iff_inter_eq_empty.mp hd, card_empty, Nat.add_zero] at ht
  have hr := totalDegree_eq_red_add_black T Q hu
  rw [merged_blackDegree_zero_of_no_common T hA hB hQ hcommon, Nat.add_zero] at hr
  omega

end Paper
