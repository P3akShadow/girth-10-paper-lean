import Merging

/-! Degree notation and the counting argument of Proposition 14.
All degrees count only vertices in the finite vertex set `S`. -/

namespace Paper
open Finset
variable {V : Type*} [DecidableEq V] {S : Finset V}

noncomputable def graphNeighbors (G : SimpleGraph V) (S : Finset V) (a : V) : Finset V := by
  classical
  exact S.filter (G.Adj a)

def MaxDegree (G : SimpleGraph V) (S : Finset V) (d : ℕ) : Prop :=
  ∀ a ∈ S, (graphNeighbors G S a).card ≤ d

def Regular (G : SimpleGraph V) (S : Finset V) (d : ℕ) : Prop :=
  ∀ a ∈ S, (graphNeighbors G S a).card = d

noncomputable def blackDegree (T : Trigraph V) (P : Partition S) (A : Finset V) : ℕ :=
  (neighbors (Black T) P A).card

noncomputable def blackVertices (T : Trigraph V) (P : Partition S) (A : Finset V) : Finset V :=
  (neighbors (Black T) P A).biUnion id

lemma redDegree_le_totalDegree (T : Trigraph V) (P : Partition S) (A : Finset V) :
    redDegree T P A ≤ totalDegree T P A := by
  classical
  apply card_le_card
  intro B hB
  obtain ⟨hBP, hBA, hred⟩ := mem_filter.mp hB
  exact mem_filter.mpr ⟨hBP, hBA, hred.1⟩

omit [DecidableEq V] in
lemma black_adjacent (T : Trigraph V) {A B : Finset V}
    (hA : A.Nonempty) (hB : B.Nonempty) (h : Black T A B) : Adjacent T A B := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  exact ⟨a, ha, b, hb, Or.inl (h a ha b hb)⟩

lemma totalDegree_eq_red_add_black (T : Trigraph V) (P : Partition S)
    {A : Finset V} (hA : A ∈ P.parts) :
    totalDegree T P A = redDegree T P A + blackDegree T P A := by
  classical
  have heq : neighbors (Adjacent T) P A =
      neighbors (Red T) P A ∪ neighbors (Black T) P A := by
    ext B
    simp only [neighbors, mem_filter, mem_union]
    constructor
    · rintro ⟨hB, hBA, hab⟩
      by_cases hb : Black T A B
      · exact Or.inr ⟨hB, hBA, hb⟩
      · exact Or.inl ⟨hB, hBA, hab, hb⟩
    · rintro (⟨hB, hBA, hred⟩ | ⟨hB, hBA, hblack⟩)
      · exact ⟨hB, hBA, hred.1⟩
      · exact ⟨hB, hBA, black_adjacent T (P.nonempty_of_mem_parts hA)
          (P.nonempty_of_mem_parts hB) hblack⟩
  have hdisj : Disjoint (neighbors (Red T) P A) (neighbors (Black T) P A) := by
    apply disjoint_left.mpr
    intro B hred hblack
    exact (mem_filter.mp hred).2.2.2 (mem_filter.mp hblack).2.2
  unfold totalDegree redDegree blackDegree
  rw [heq, card_union_of_disjoint hdisj]

lemma blackVertices_card (T : Trigraph V) (P : Partition S) (A : Finset V) :
    (blackVertices T P A).card = ∑ B ∈ neighbors (Black T) P A, B.card := by
  classical
  apply card_biUnion
  intro B hB C hC hBC
  exact P.disjoint (mem_filter.mp hB).1 (mem_filter.mp hC).1 hBC

lemma blackDegree_le_blackVertices (T : Trigraph V) (P : Partition S) (A : Finset V) :
    blackDegree T P A ≤ (blackVertices T P A).card := by
  classical
  rw [blackVertices_card]
  calc
    blackDegree T P A = ∑ _B ∈ neighbors (Black T) P A, 1 := by simp [blackDegree]
    _ ≤ _ := sum_le_sum fun B hB =>
      one_le_card.mpr (P.nonempty_of_mem_parts (mem_filter.mp hB).1)

lemma blackVertices_subset_neighbors (G : SimpleGraph V) (P : Partition S)
    {A : Finset V} {a : V} (ha : a ∈ A) :
    blackVertices (.ofGraph G) P A ⊆ graphNeighbors G S a := by
  classical
  intro b hb
  obtain ⟨B, hB, hbB⟩ := mem_biUnion.mp hb
  obtain ⟨hBP, _, hblack⟩ := mem_filter.mp hB
  exact mem_filter.mpr ⟨P.subset hBP hbB, hblack a ha b hbB⟩

lemma black_bag_size_le (G : SimpleGraph V) {d : ℕ} (hdeg : MaxDegree G S d)
    (P : Partition S) {A B : Finset V} (hA : A ∈ P.parts) (hB : B ∈ P.parts)
    (hblack : Black (.ofGraph G) A B) : A.card ≤ d := by
  classical
  obtain ⟨b, hb⟩ := P.nonempty_of_mem_parts hB
  have hsub : A ⊆ graphNeighbors G S b := by
    intro a ha
    exact mem_filter.mpr ⟨P.subset hA ha, (hblack a ha b hb).symm⟩
  exact (card_le_card hsub).trans (hdeg b (P.subset hB hb))

lemma oversized_blackDegree_zero (G : SimpleGraph V) {d : ℕ} (hdeg : MaxDegree G S d)
    (P : Partition S) {A : Finset V} (hA : A ∈ P.parts) (hlarge : d < A.card) :
    blackDegree (.ofGraph G) P A = 0 := by
  classical
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro B hB
  obtain ⟨hBP, _, hblack⟩ := mem_filter.mp hB
  exact (Nat.not_le_of_lt hlarge) (black_bag_size_le G hdeg P hA hBP hblack)

lemma full_bag_neighbor (G : SimpleGraph V) {d : ℕ} (hdeg : MaxDegree G S d)
    (P : Partition S) {A B : Finset V} (hA : A ∈ P.parts) (hB : B ∈ P.parts)
    (hsize : A.card = d) (hblack : Black (.ofGraph G) A B) {b : V} (hb : b ∈ B) :
    graphNeighbors G S b = A := by
  classical
  symm
  apply eq_of_subset_of_card_le
  · intro a ha
    exact mem_filter.mpr ⟨P.subset hA ha, (hblack a ha b hb).symm⟩
  · simpa only [hsize] using hdeg b (P.subset hB hb)

end Paper
