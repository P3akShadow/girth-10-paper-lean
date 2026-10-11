import PaperDefinitions

namespace Paper

open Finset
variable {V : Type*} [DecidableEq V] {S U : Finset V}

lemma mem_restrict {P : Partition S} (hUS : U ⊆ S) {C : Finset V} :
    C ∈ (P.restrict hUS).parts ↔ C ≠ ∅ ∧ ∃ A ∈ P.parts, A ∩ U = C := by
  simp [Finpartition.parts_restrict]

lemma restrict_card_le (P : Partition S) (hUS : U ⊆ S) :
    (P.restrict hUS).parts.card ≤ P.parts.card := by
  exact card_erase_le.trans card_image_le

lemma restrict_bot (hUS : U ⊆ S) :
    (⊥ : Partition S).restrict hUS = (⊥ : Partition U) := by
  ext C
  rw [mem_restrict, Finpartition.mem_bot_iff]
  constructor
  · rintro ⟨hC, A, hA, hAC⟩
    obtain ⟨a, ha, rfl⟩ := Finpartition.mem_bot_iff.mp hA
    by_cases haU : a ∈ U
    · exact ⟨a, haU, by simpa [haU] using hAC⟩
    · simp [haU] at hAC
      exact False.elim (hC hAC.symm)
  · rintro ⟨a, ha, rfl⟩
    exact ⟨by simp, {a}, Finpartition.mem_bot_iff.mpr ⟨a, hUS ha, rfl⟩,
      by simp [ha]⟩

lemma adjacent_of_restrict (T : Trigraph V) {A B : Finset V}
    (h : Adjacent T (A ∩ U) (B ∩ U)) : Adjacent T A B := by
  obtain ⟨a, ha, b, hb, hab⟩ := h
  exact ⟨a, (mem_inter.mp ha).1, b, (mem_inter.mp hb).1, hab⟩

lemma red_of_restrict (T : Trigraph V) {A B : Finset V}
    (h : Red T (A ∩ U) (B ∩ U)) : Red T A B := by
  refine ⟨adjacent_of_restrict T h.1, ?_⟩
  intro hblack
  exact h.2 fun a ha b hb => hblack a (mem_inter.mp ha).1 b (mem_inter.mp hb).1

lemma restricted_neighbors_card_le
    (R : Finset V → Finset V → Prop)
    (hR : ∀ A B, R (A ∩ U) (B ∩ U) → R A B)
    (P : Partition S) (hUS : U ⊆ S) (A : Finset V) :
    (neighbors R (P.restrict hUS) (A ∩ U)).card ≤ (neighbors R P A).card := by
  classical
  apply le_trans (card_le_card (t := (neighbors R P A).image (· ∩ U)) ?_) card_image_le
  intro C hC
  obtain ⟨hCP, hCA, hRC⟩ := mem_filter.mp hC
  obtain ⟨_, B, hBP, rfl⟩ := (mem_restrict hUS).mp hCP
  apply mem_image.mpr
  refine ⟨B, mem_filter.mpr ⟨hBP, ?_, hR A B hRC⟩, rfl⟩
  intro hBA
  exact hCA (congrArg (· ∩ U) hBA)

lemma bounded_restrict {T : Trigraph V} {w s : ℕ} {P : Partition S}
    (h : Bounded T w s P) (hUS : U ⊆ S) : Bounded T w s (P.restrict hUS) := by
  intro C hC
  obtain ⟨_, A, hAP, rfl⟩ := (mem_restrict hUS).mp hC
  obtain ⟨hred, htotal⟩ := h A hAP
  exact ⟨(restricted_neighbors_card_le (Red T) (fun _ _ => red_of_restrict T)
      P hUS A).trans hred,
    (restricted_neighbors_card_le (Adjacent T) (fun _ _ => adjacent_of_restrict T)
      P hUS A).trans htotal⟩

lemma same_parent_of_nonempty_inter {P : Partition S} {A B : Finset V}
    (hA : A ∈ P.parts) (hB : B ∈ P.parts)
    (hU : (A ∩ U).Nonempty) (heq : A ∩ U = B ∩ U) : A = B := by
  obtain ⟨u, hu⟩ := hU
  have hv : u ∈ B ∩ U := heq ▸ hu
  exact P.eq_of_mem_parts hA hB (mem_inter.mp hu).1 (mem_inter.mp hv).1

lemma restrict_merge_of_empty {P Q : Partition S} (hUS : U ⊆ S)
    {A B : Finset V} (hB : B ∈ P.parts)
    (hQ : Q.parts = insert (A ∪ B) (P.parts \ {A, B}))
    (hA : A ∩ U = ∅) : Q.restrict hUS = P.restrict hUS := by
  have hAB : (A ∪ B) ∩ U = B ∩ U := by simp [union_inter_distrib_right, hA]
  ext C
  simp only [mem_restrict]
  constructor
  · rintro ⟨hC, D, hD, hDC⟩
    rw [hQ] at hD
    rcases mem_insert.mp hD with rfl | hD
    · exact ⟨hC, B, hB, hAB.symm.trans hDC⟩
    · exact ⟨hC, D, (mem_sdiff.mp hD).1, hDC⟩
  · rintro ⟨hC, D, hD, hDC⟩
    refine ⟨hC, ?_⟩
    by_cases hDB : D = B
    · subst D
      exact ⟨A ∪ B, by simp [hQ], hAB.trans hDC⟩
    · have hDA : D ≠ A := by
        intro heq
        subst D
        exact hC (hDC.symm.trans hA)
      exact ⟨D, by simp [hQ, hD, hDA, hDB], hDC⟩

lemma restrict_merge_of_nonempty {P Q : Partition S} (hUS : U ⊆ S)
    {A B : Finset V} (hA : A ∈ P.parts) (hB : B ∈ P.parts) (hAB : A ≠ B)
    (hQ : Q.parts = insert (A ∪ B) (P.parts \ {A, B}))
    (hAU : A ∩ U ≠ ∅) (hBU : B ∩ U ≠ ∅) :
    Merge (P.restrict hUS) (Q.restrict hUS) := by
  have hneq : A ∩ U ≠ B ∩ U := fun h =>
    hAB (same_parent_of_nonempty_inter hA hB (nonempty_iff_ne_empty.mpr hAU) h)
  refine ⟨A ∩ U, (mem_restrict hUS).mpr ⟨hAU, A, hA, rfl⟩,
    B ∩ U, (mem_restrict hUS).mpr ⟨hBU, B, hB, rfl⟩, hneq, ?_⟩
  have hunion : (A ∪ B) ∩ U = (A ∩ U) ∪ (B ∩ U) := union_inter_distrib_right ..
  ext C
  constructor
  · intro hC
    obtain ⟨hC0, D, hD, hDC⟩ := (mem_restrict hUS).mp hC
    rw [hQ] at hD
    rcases mem_insert.mp hD with rfl | hD
    · exact mem_insert.mpr (Or.inl (hDC.symm.trans hunion))
    · obtain ⟨hDP, hDAB⟩ := mem_sdiff.mp hD
      apply mem_insert.mpr ∘ Or.inr ∘ mem_sdiff.mpr
      refine ⟨(mem_restrict hUS).mpr ⟨hC0, D, hDP, hDC⟩, ?_⟩
      simp only [mem_insert, mem_singleton, not_or]
      constructor
      · intro hCA
        have heq := same_parent_of_nonempty_inter hDP hA
          (nonempty_iff_ne_empty.mpr (hDC ▸ hC0)) (hDC.trans hCA)
        exact hDAB (by simp [heq])
      · intro hCB
        have heq := same_parent_of_nonempty_inter hDP hB
          (nonempty_iff_ne_empty.mpr (hDC ▸ hC0)) (hDC.trans hCB)
        exact hDAB (by simp [heq])
  · intro hC
    rcases mem_insert.mp hC with rfl | hC
    · apply (mem_restrict hUS).mpr
      exact ⟨by simp [hAU], A ∪ B, by simp [hQ], hunion⟩
    · obtain ⟨hCP, hCAB⟩ := mem_sdiff.mp hC
      obtain ⟨hC0, D, hD, hDC⟩ := (mem_restrict hUS).mp hCP
      have hDA : D ≠ A := by
        intro h
        exact hCAB (by simp [← hDC, h])
      have hDB : D ≠ B := by
        intro h
        exact hCAB (by simp [← hDC, h])
      exact (mem_restrict hUS).mpr ⟨hC0, D, by simp [hQ, hD, hDA, hDB], hDC⟩

lemma merge_restrict {P Q : Partition S} (h : Merge P Q) (hUS : U ⊆ S) :
    P.restrict hUS = Q.restrict hUS ∨ Merge (P.restrict hUS) (Q.restrict hUS) := by
  obtain ⟨A, hA, B, hB, hAB, hQ⟩ := h
  by_cases hAU : A ∩ U = ∅
  · exact Or.inl (restrict_merge_of_empty hUS hB hQ hAU).symm
  by_cases hBU : B ∩ U = ∅
  · have hQ' : Q.parts = insert (B ∪ A) (P.parts \ {B, A}) := by
      simpa [union_comm, pair_comm] using hQ
    exact Or.inl (restrict_merge_of_empty hUS hA hQ' hBU).symm
  exact Or.inr (restrict_merge_of_nonempty hUS hA hB hAB hQ hAU hBU)

end Paper
