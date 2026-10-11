import GraphDegrees

/-! Proposition 14, the paragraph headed "Counting bound". -/

namespace Paper
open Finset
variable {V : Type*} [DecidableEq V] {S : Finset V}

lemma redDegree_le_remaining_edges (G : SimpleGraph V) (P : Partition S) (A : Finset V) :
    redDegree (.ofGraph G) P A ≤
      ∑ a ∈ A, (graphNeighbors G S a \ blackVertices (.ofGraph G) P A).card := by
  classical
  let Q := blackVertices (.ofGraph G) P A
  have hsub : neighbors (Red (.ofGraph G)) P A ⊆
      A.biUnion (fun a => (graphNeighbors G S a \ Q).image P.part) := by
    intro B hB
    obtain ⟨hBP, _, hred⟩ := mem_filter.mp hB
    obtain ⟨a, ha, b, hb, hab⟩ := hred.1
    have hadj : G.Adj a b := by simpa [Trigraph.ofGraph] using hab
    have hnot : b ∉ Q := by
      intro hQ
      obtain ⟨C, hC, hbC⟩ := mem_biUnion.mp hQ
      obtain ⟨hCP, _, hblack⟩ := mem_filter.mp hC
      have hCB : C = B := P.eq_of_mem_parts hCP hBP hbC hb
      exact hred.2 (hCB ▸ hblack)
    apply mem_biUnion.mpr
    refine ⟨a, ha, mem_image.mpr ⟨b, ?_, P.part_eq_of_mem hBP hb⟩⟩
    exact mem_sdiff.mpr ⟨mem_filter.mpr ⟨P.subset hBP hb, hadj⟩, hnot⟩
  exact (card_le_card hsub).trans (card_biUnion_le.trans
    (sum_le_sum fun _ _ => card_image_le))

lemma redDegree_counting_bound (G : SimpleGraph V) {d : ℕ} (hdeg : MaxDegree G S d)
    (P : Partition S) {A : Finset V} (hA : A ∈ P.parts) :
    redDegree (.ofGraph G) P A ≤
      A.card * (d - (blackVertices (.ofGraph G) P A).card) := by
  classical
  apply le_trans (redDegree_le_remaining_edges G P A)
  calc
    (∑ a ∈ A, (graphNeighbors G S a \ blackVertices (.ofGraph G) P A).card) ≤
        ∑ _a ∈ A, (d - (blackVertices (.ofGraph G) P A).card) := by
      apply sum_le_sum
      intro a ha
      rw [card_sdiff_of_subset (blackVertices_subset_neighbors G P ha)]
      exact Nat.sub_le_sub_right (hdeg a (P.subset hA ha)) _
    _ = _ := by simp

/-- Equation (counting), with p=|A|, q=|blackVertices|, b=blackDegree. -/
theorem degree_counting_bound (G : SimpleGraph V) {d : ℕ} (hdeg : MaxDegree G S d)
    (P : Partition S) {A : Finset V} (hA : A ∈ P.parts) :
    totalDegree (.ofGraph G) P A ≤
      A.card * (d - (blackVertices (.ofGraph G) P A).card) +
        blackDegree (.ofGraph G) P A := by
  rw [totalDegree_eq_red_add_black _ _ hA]
  exact Nat.add_le_add_right (redDegree_counting_bound G hdeg P hA) _

lemma blackVertices_card_le_degree (G : SimpleGraph V) {d : ℕ} (hdeg : MaxDegree G S d)
    (P : Partition S) {A : Finset V} (hA : A ∈ P.parts) :
    (blackVertices (.ofGraph G) P A).card ≤ d := by
  obtain ⟨a, ha⟩ := P.nonempty_of_mem_parts hA
  exact (card_le_card (blackVertices_subset_neighbors G P ha)).trans
    (hdeg a (P.subset hA ha))

lemma Continuation.toSparse {T : Trigraph V} {P : Partition S} {w s : ℕ}
    (h : Continuation T w s P) : Continuation T s s P := by
  have hb : ∀ P : Partition S, Bounded T w s P → Bounded T s s P := by
    intro P hP A hA
    exact ⟨(redDegree_le_totalDegree T P A).trans (hP A hA).2, (hP A hA).2⟩
  induction h with
  | done hP hf => exact .done (hb _ hP) hf
  | step hP hm _ ih => exact .step (hb _ hP) hm ih

theorem twinWidth_le_sparseTwinWidth (T : Trigraph V) (S : Finset V) :
    twinWidth T S ≤ sparseTwinWidth T S := by
  obtain ⟨w, hw⟩ := sparseTwinWidth_witness T S
  exact twinWidth_le hw.toSparse

end Paper
