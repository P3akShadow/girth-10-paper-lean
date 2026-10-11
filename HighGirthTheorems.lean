import HighGirthCases
import HighGirthPairPair
import HighGirthCubicPairs

/-! Section 3 lower-bound theorems: a complete sequence must create a first
large bag, and the paper's case analysis excludes that merge. -/
namespace Paper
open Finset
variable {V : Type*} [DecidableEq V] {S : Finset V}

lemma Continuation.raise_red_bound {T : Trigraph V} {w w' s : ℕ} {P : Partition S}
    (h : Continuation T w s P) (hww' : w ≤ w') : Continuation T w' s P := by
  induction h with
  | done hb hn =>
    exact .done (fun A hA => ⟨(hb A hA).1.trans hww', (hb A hA).2⟩) hn
  | step hb hm _ ih =>
    exact .step (fun A hA => ⟨(hb A hA).1.trans hww', (hb A hA).2⟩) hm ih

/-- Theorem 5's first-large-bag exclusion, after applying Lemma 3. -/
theorem no_first_big_bag_general (G : SimpleGraph V) {d s : ℕ}
    (hd : 3 < d) (hg : 8 < G.egirth) (hreg : Regular G S d)
    (hclosed : ∀ u ∈ S, ∀ v, G.Adj u v → v ∈ S)
    {P Q : Partition S}
    (hseq : PartialSequence (.ofGraph G) (2 * d - 2) s P)
    (hsmall : BagsAtMostTwo P) (hm : Merge P Q)
    (hbound : Bounded (.ofGraph G) (2 * d - 2) s Q) : BagsAtMostTwo Q := by
  obtain ⟨sat, near⟩ := two_bag_facts_invariants G (by omega) hg hreg hseq hsmall
  by_contra hlarge
  obtain ⟨A, hA, B, hB, hAB, hA2, hBsize, hQ⟩ := first_large_bag_cases hm hsmall hlarge
  rcases hBsize with hB1 | hB2
  · obtain ⟨u, rfl⟩ := card_eq_one.mp hB1
    exact pair_singleton_merge_impossible G (by omega) hg hreg hsmall near sat
      hA hB hA2 hQ hbound
  · exact two_pairs_general_impossible G hd hg hreg hclosed near hA hB hAB hA2 hB2
      (sat A hA hA2) (sat B hB hB2) hQ hbound

/-- Theorem 5 on an arbitrary finite nonempty component-closed vertex set. -/
theorem girth_general_on (G : SimpleGraph V) {d : ℕ}
    (hd : 3 < d) (hg : 8 < G.egirth) (hreg : Regular G S d)
    (hS : S.Nonempty) (hclosed : ∀ u ∈ S, ∀ v, G.Adj u v → v ∈ S) :
    2 * d - 2 < twinWidth (.ofGraph G) S := by
  by_contra hnot
  have hle : twinWidth (.ofGraph G) S ≤ 2 * d - 2 := by omega
  obtain ⟨s, hseq⟩ := twinWidth_witness (.ofGraph G) S
  have hcont : Continuation (.ofGraph G) (2 * d - 2) s (⊥ : Partition S) :=
    hseq.raise_red_bound hle
  have hbounded : Bounded (.ofGraph G) (2 * d - 2) s (⊥ : Partition S) := by
    cases hcont <;> assumption
  have hcard := regular_card_gt G hreg hS
  obtain ⟨P, Q, hp, hsmall, hm, hb, hlarge⟩ := first_large_bag_merge
    (by omega : 2 < S.card) (PartialSequence.initial hbounded) (bagsAtMostTwo_bot S) hcont
  exact hlarge (no_first_big_bag_general G hd hg hreg hclosed hp hsmall hm hb)

/-- Theorem 5. Every finite nonempty d-regular graph of girth greater than
eight has twin-width greater than 2d-2, when d>3. -/
theorem girth_general [Fintype V] [Nonempty V] (G : SimpleGraph V) {d : ℕ}
    (hd : 3 < d) (hg : 8 < G.egirth) (hreg : Regular G univ d) :
    2 * d - 2 < twinWidth (.ofGraph G) univ :=
  girth_general_on G hd hg hreg univ_nonempty (fun _ _ _ _ => mem_univ _)

/-- Lemma 4. In a cubic graph of girth greater than nine, no width-four
partial sequence can have a first merge producing a bag larger than two. -/
theorem no_big_bags_on (G : SimpleGraph V) {s : ℕ}
    (hg : 9 < G.egirth) (hreg : Regular G S 3)
    (hclosed : ∀ u ∈ S, ∀ v, G.Adj u v → v ∈ S)
    {P Q : Partition S} (hseq : PartialSequence (.ofGraph G) 4 s P)
    (hsmall : BagsAtMostTwo P) (hm : Merge P Q)
    (hbound : Bounded (.ofGraph G) 4 s Q) : BagsAtMostTwo Q := by
  have hg8 : 8 < G.egirth := lt_trans (by norm_num) hg
  obtain ⟨sat, near⟩ := two_bag_facts_invariants G (d := 3) (by omega) hg8 hreg hseq hsmall
  by_contra hlarge
  obtain ⟨A, hA, B, hB, hAB, hA2, hBsize, hQ⟩ := first_large_bag_cases hm hsmall hlarge
  rcases hBsize with hB1 | hB2
  · obtain ⟨u, rfl⟩ := card_eq_one.mp hB1
    exact pair_singleton_merge_impossible G (d := 3) (by omega) hg8 hreg hsmall near sat
      hA hB hA2 hQ hbound
  · exact pair_pair_cubic_merge_impossible G hg hreg hclosed near hA hB hAB hA2 hB2
      (sat A hA hA2) (sat B hB hB2) hQ hbound

/-- Theorem 1 on a finite nonempty component-closed vertex set. -/
theorem girth_cubic_on (G : SimpleGraph V)
    (hg : 9 < G.egirth) (hreg : Regular G S 3)
    (hS : S.Nonempty) (hclosed : ∀ u ∈ S, ∀ v, G.Adj u v → v ∈ S) :
    4 < twinWidth (.ofGraph G) S := by
  by_contra hnot
  have hle : twinWidth (.ofGraph G) S ≤ 4 := by omega
  obtain ⟨s, hseq⟩ := twinWidth_witness (.ofGraph G) S
  have hcont : Continuation (.ofGraph G) 4 s (⊥ : Partition S) := hseq.raise_red_bound hle
  have hbounded : Bounded (.ofGraph G) 4 s (⊥ : Partition S) := by
    cases hcont <;> assumption
  have hcard := regular_card_gt G hreg hS
  obtain ⟨P, Q, hp, hsmall, hm, hb, hlarge⟩ := first_large_bag_merge
    (by omega : 2 < S.card) (PartialSequence.initial hbounded) (bagsAtMostTwo_bot S) hcont
  exact hlarge (no_big_bags_on G hg hreg hclosed hp hsmall hm hb)

/-- Theorem 1: every finite nonempty cubic graph of girth greater than nine
has twin-width greater than four. -/
theorem girth_cubic [Fintype V] [Nonempty V] (G : SimpleGraph V)
    (hg : 9 < G.egirth) (hreg : Regular G univ 3) :
    4 < twinWidth (.ofGraph G) univ :=
  girth_cubic_on G hg hreg univ_nonempty (fun _ _ _ _ => mem_univ _)

/-- Lemma 4 for the whole finite graph, with no auxiliary closure hypothesis. -/
theorem no_big_bags [Fintype V] (G : SimpleGraph V) {s : ℕ}
    (hg : 9 < G.egirth) (hreg : Regular G univ 3)
    {P Q : Partition (univ : Finset V)} (hseq : PartialSequence (.ofGraph G) 4 s P)
    (hsmall : BagsAtMostTwo P) (hm : Merge P Q)
    (hbound : Bounded (.ofGraph G) 4 s Q) : BagsAtMostTwo Q :=
  no_big_bags_on G hg hreg (fun _ _ _ _ => mem_univ _) hseq hsmall hm hbound

end Paper
