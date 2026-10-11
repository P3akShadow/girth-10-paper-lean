import GraphDegrees

/-!
Section 3. Counting facts used in the induction for the two-bag lemma.
The singleton degree identity below is the counting identity in the opening
paragraph of that proof: a black two-bag accounts for exactly one lost neighbor.
-/

namespace Paper

open Finset
variable {V : Type*} [DecidableEq V] {S : Finset V}
attribute [local instance] Classical.propDecidable

def BagsAtMostTwo (P : Partition S) : Prop :=
  ∀ A ∈ P.parts, A.card ≤ 2

/-- A bounded initial segment of a contraction sequence, including its
last partition. This is the partial contraction sequence in Lemma 3. -/
inductive PartialSequence (T : Trigraph V) (w s : ℕ) : Partition S → Prop
  | initial : Bounded T w s (⊥ : Partition S) → PartialSequence T w s ⊥
  | step {P Q} : PartialSequence T w s P → Merge P Q → Bounded T w s Q →
      PartialSequence T w s Q

lemma PartialSequence.bounded {T : Trigraph V} {w s : ℕ} {P : Partition S}
    (h : PartialSequence T w s P) : Bounded T w s P := by
  cases h with
  | initial hb => exact hb
  | step _ _ hb => exact hb

lemma bagsAtMostTwo_bot (S : Finset V) : BagsAtMostTwo (⊥ : Partition S) := by
  intro A hA
  rw [Finpartition.parts_bot] at hA
  obtain ⟨a, _, rfl⟩ := mem_map.mp hA
  simp

lemma Merge.bagsAtMostTwo_before {P Q : Partition S} (hmerge : Merge P Q)
    (hQ : BagsAtMostTwo Q) : BagsAtMostTwo P := by
  obtain ⟨A, hA, B, hB, _, heq⟩ := hmerge
  have hunion : A ∪ B ∈ Q.parts := by simp [heq]
  intro C hC
  by_cases hCA : C = A
  · subst C
    exact (card_le_card subset_union_left).trans (hQ _ hunion)
  by_cases hCB : C = B
  · subst C
    exact (card_le_card subset_union_right).trans (hQ _ hunion)
  apply hQ
  simp [heq, hC, hCA, hCB]

lemma Merge.singleton_sources_of_small {P Q : Partition S} (hmerge : Merge P Q)
    (hQ : BagsAtMostTwo Q) :
    ∃ u v : V, {u} ∈ P.parts ∧ {v} ∈ P.parts ∧ u ≠ v ∧
      Q.parts = insert ({u} ∪ {v}) (P.parts \ {{u}, {v}}) := by
  obtain ⟨A, hA, B, hB, hAB, heq⟩ := hmerge
  have hU : A ∪ B ∈ Q.parts := by simp [heq]
  have hsum := card_union_of_disjoint (P.disjoint hA hB hAB)
  change (A ∪ B).card = A.card + B.card at hsum
  have hAu := hQ _ hU
  have hAl := one_le_card.mpr (P.nonempty_of_mem_parts hA)
  have hBl := one_le_card.mpr (P.nonempty_of_mem_parts hB)
  have hA1 : A.card = 1 := by omega
  have hB1 : B.card = 1 := by omega
  obtain ⟨u, rfl⟩ := card_eq_one.mp hA1
  obtain ⟨v, rfl⟩ := card_eq_one.mp hB1
  exact ⟨u, v, hA, hB, fun he => hAB (he ▸ rfl), heq⟩

lemma small_partition_card_le_two (P : Partition S)
    (hsmall : BagsAtMostTwo P) (hfinal : P.parts.card ≤ 1) : S.card ≤ 2 := by
  rw [← P.sum_card_parts]
  calc
    ∑ A ∈ P.parts, A.card ≤ ∑ _A ∈ P.parts, 2 := sum_le_sum hsmall
    _ = P.parts.card * 2 := by simp
    _ ≤ 2 := by omega

/-- A complete sequence on more than two vertices contains a first merge
creating a large bag, the common starting point of Lemma 4 and Theorem 5. -/
lemma first_large_bag_merge {T : Trigraph V} {w s : ℕ} {P : Partition S}
    (hlarge : 2 < S.card) (hprefix : PartialSequence T w s P)
    (hsmall : BagsAtMostTwo P) (hcont : Continuation T w s P) :
    ∃ P Q : Partition S, PartialSequence T w s P ∧ BagsAtMostTwo P ∧
      Merge P Q ∧ Bounded T w s Q ∧ ¬ BagsAtMostTwo Q := by
  induction hcont with
  | done hb hn =>
    exact False.elim ((Nat.not_le_of_lt hlarge) (small_partition_card_le_two _ hsmall hn))
  | @step P Q hb hm hc ih =>
    have hbQ : Bounded T w s Q := by cases hc <;> assumption
    by_cases hQ : BagsAtMostTwo Q
    · exact ih (PartialSequence.step hprefix hm hbQ) hQ
    · exact ⟨P, Q, hprefix, hsmall, hm, hbQ, hQ⟩

/-- Only a two-bag with a singleton, or two two-bags, can create the first
large bag. The order of the merged bags is chosen so the first has size two. -/
lemma first_large_bag_cases {P Q : Partition S} (hm : Merge P Q)
    (hP : BagsAtMostTwo P) (hQ : ¬ BagsAtMostTwo Q) :
    ∃ A ∈ P.parts, ∃ B ∈ P.parts, A ≠ B ∧ A.card = 2 ∧
      (B.card = 1 ∨ B.card = 2) ∧
      Q.parts = insert (A ∪ B) (P.parts \ {A, B}) := by
  obtain ⟨A, hA, B, hB, hAB, heq⟩ := hm
  have hAl := one_le_card.mpr (P.nonempty_of_mem_parts hA)
  have hBl := one_le_card.mpr (P.nonempty_of_mem_parts hB)
  have hAu := hP A hA
  have hBu := hP B hB
  have hun : 2 < (A ∪ B).card := by
    by_contra hc
    apply hQ
    intro C hC
    rw [heq] at hC
    rcases mem_insert.mp hC with rfl | hC
    · omega
    · exact hP C (mem_sdiff.mp hC).1
  have hc := card_union_of_disjoint (P.disjoint hA hB hAB)
  change (A ∪ B).card = A.card + B.card at hc
  by_cases hA2 : A.card = 2
  · exact ⟨A, hA, B, hB, hAB, hA2, by omega, heq⟩
  · refine ⟨B, hB, A, hA, hAB.symm, by omega, by omega, ?_⟩
    simpa only [union_comm B A, pair_comm B A] using heq

noncomputable def blackTwoBags (G : SimpleGraph V) (P : Partition S)
    (a : V) : Finset (Finset V) := by
  classical
  exact P.parts.filter fun B => B.card = 2 ∧ Black (.ofGraph G) {a} B

lemma regular_card_gt (G : SimpleGraph V) {d : ℕ} (hreg : Regular G S d)
    (hS : S.Nonempty) : d < S.card := by
  obtain ⟨a, ha⟩ := hS
  have hs : graphNeighbors G S a ⊆ S.erase a := by
    intro b hb
    obtain ⟨hbS, hab⟩ := mem_filter.mp hb
    exact mem_erase.mpr ⟨hab.ne.symm, hbS⟩
  have hc := card_le_card hs
  rw [hreg a ha, card_erase_of_mem ha] at hc
  have := one_le_card.mpr ⟨a, ha⟩
  omega

lemma neighbors_partition_sum (G : SimpleGraph V) (P : Partition S) (a : V) :
    (graphNeighbors G S a).card =
      ∑ B ∈ P.parts, (B ∩ graphNeighbors G S a).card := by
  classical
  have heq : graphNeighbors G S a =
      P.parts.biUnion (fun B => B ∩ graphNeighbors G S a) := by
    ext b
    constructor
    · intro hb
      obtain ⟨B, hB, hbB⟩ := P.exists_mem (mem_filter.mp hb).1
      exact mem_biUnion.mpr ⟨B, hB, mem_inter.mpr ⟨hbB, hb⟩⟩
    · intro hb
      obtain ⟨B, _, hbB⟩ := mem_biUnion.mp hb
      exact (mem_inter.mp hbB).2
  conv_lhs => rw [heq]
  apply card_biUnion
  intro A hA B hB hAB
  exact (P.disjoint hA hB hAB).mono inter_subset_left inter_subset_left

lemma singleton_adjacent_iff_inter_nonempty (G : SimpleGraph V) (P : Partition S)
    {a : V} {B : Finset V} (hB : B ∈ P.parts) :
    Adjacent (.ofGraph G) {a} B ↔ (B ∩ graphNeighbors G S a).Nonempty := by
  constructor
  · rintro ⟨x, hx, b, hb, hab⟩
    have hxa : x = a := mem_singleton.mp hx
    subst x
    rcases hab with hab | hab
    · exact ⟨b, mem_inter.mpr ⟨hb, mem_filter.mpr ⟨P.subset hB hb, hab⟩⟩⟩
    · exact False.elim hab
  · rintro ⟨b, hb⟩
    obtain ⟨hbB, hbN⟩ := mem_inter.mp hb
    exact ⟨a, mem_singleton_self a, b, hbB, Or.inl (mem_filter.mp hbN).2⟩

lemma singleton_black_iff_subset_neighbors (G : SimpleGraph V) (P : Partition S)
    {a : V} {B : Finset V} (hB : B ∈ P.parts) :
    Black (.ofGraph G) {a} B ↔ B ⊆ graphNeighbors G S a := by
  constructor
  · intro h b hb
    exact mem_filter.mpr ⟨P.subset hB hb, h a (mem_singleton_self a) b hb⟩
  · intro h x hx b hb
    have hxa : x = a := mem_singleton.mp hx
    subst x
    exact (mem_filter.mp (h hb)).2

lemma small_bag_neighbor_count (G : SimpleGraph V) (P : Partition S)
    {a : V} {B : Finset V} (hB : B ∈ P.parts) (hsize : B.card ≤ 2) :
    (B ∩ graphNeighbors G S a).card =
      (if B ≠ {a} ∧ Adjacent (.ofGraph G) {a} B then 1 else 0) +
      (if B.card = 2 ∧ Black (.ofGraph G) {a} B then 1 else 0) := by
  classical
  have hle : (B ∩ graphNeighbors G S a).card ≤ B.card :=
    card_le_card inter_subset_left
  have hself : ¬ Adjacent (.ofGraph G) {a} {a} := by
    rintro ⟨x, hx, y, hy, hxy⟩
    have hxEq : x = a := mem_singleton.mp hx
    have hyEq : y = a := mem_singleton.mp hy
    subst x
    subst y
    rcases hxy with hxy | hxy
    · exact G.irrefl hxy
    · exact hxy
  have hadj : (B ≠ {a} ∧ Adjacent (.ofGraph G) {a} B) ↔
      0 < (B ∩ graphNeighbors G S a).card := by
    rw [card_pos, ← singleton_adjacent_iff_inter_nonempty G P hB]
    exact ⟨And.right, fun h => ⟨fun he => hself (he ▸ h), h⟩⟩
  have hblack : (B.card = 2 ∧ Black (.ofGraph G) {a} B) ↔
      (B ∩ graphNeighbors G S a).card = 2 := by
    rw [singleton_black_iff_subset_neighbors G P hB]
    constructor
    · rintro ⟨hc, hs⟩
      rw [inter_eq_left.mpr hs, hc]
    · intro hc
      have hb : B.card = 2 := by omega
      refine ⟨hb, ?_⟩
      have he : B ∩ graphNeighbors G S a = B :=
        eq_of_subset_of_card_le inter_subset_left (by omega)
      exact inter_eq_left.mp he
  simp only [hadj, hblack]
  split_ifs <;> omega

/-- Lemma 3(iii), in additive form before subtracting the deficit. -/
lemma singleton_degree_add_blackTwoBags (G : SimpleGraph V) (P : Partition S)
    (hsmall : BagsAtMostTwo P) (a : V) :
    totalDegree (.ofGraph G) P {a} + (blackTwoBags G P a).card =
      (graphNeighbors G S a).card := by
  classical
  rw [neighbors_partition_sum G P a]
  have hs := sum_congr rfl (fun B hB => small_bag_neighbor_count G P (a := a) hB (hsmall B hB))
  rw [hs, sum_add_distrib, sum_boole, sum_boole]
  rfl

/-- The degree assertion in Lemma 3: every black two-bag reduces the
singleton's degree by exactly one. -/
theorem two_bag_facts_singleton_degree (G : SimpleGraph V) {d : ℕ}
    (hreg : Regular G S d) (P : Partition S) (hsmall : BagsAtMostTwo P)
    {a : V} (ha : {a} ∈ P.parts) :
    totalDegree (.ofGraph G) P {a} = d - (blackTwoBags G P a).card := by
  have h := singleton_degree_add_blackTwoBags G P hsmall a
  rw [hreg a (P.subset ha (mem_singleton_self a))] at h
  omega

lemma singleton_degree_le (G : SimpleGraph V) {d : ℕ}
    (hreg : Regular G S d) (P : Partition S) (hsmall : BagsAtMostTwo P)
    {a : V} (ha : {a} ∈ P.parts) : totalDegree (.ofGraph G) P {a} ≤ d := by
  rw [two_bag_facts_singleton_degree G hreg P hsmall ha]
  exact Nat.sub_le ..

lemma singleton_has_blackTwoBag_of_degree_lt (G : SimpleGraph V) {d : ℕ}
    (hreg : Regular G S d) (P : Partition S) (hsmall : BagsAtMostTwo P)
    {a : V} (ha : {a} ∈ P.parts) (hdeg : totalDegree (.ofGraph G) P {a} < d) :
    ∃ B ∈ P.parts, B.card = 2 ∧ Black (.ofGraph G) {a} B := by
  have he := singleton_degree_add_blackTwoBags G P hsmall a
  rw [hreg a (P.subset ha (mem_singleton_self a))] at he
  have hc : 0 < (blackTwoBags G P a).card := by omega
  obtain ⟨B, hB⟩ := card_pos.mp hc
  exact ⟨B, (mem_filter.mp hB).1, (mem_filter.mp hB).2⟩

lemma singleton_has_two_blackTwoBags_of_degree_lt (G : SimpleGraph V) {d : ℕ}
    (hreg : Regular G S d) (P : Partition S) (hsmall : BagsAtMostTwo P)
    {a : V} (ha : {a} ∈ P.parts) (hdeg : totalDegree (.ofGraph G) P {a} + 1 < d) :
    ∃ A ∈ P.parts, ∃ B ∈ P.parts, A ≠ B ∧
      A.card = 2 ∧ B.card = 2 ∧
      Black (.ofGraph G) {a} A ∧ Black (.ofGraph G) {a} B := by
  have he := singleton_degree_add_blackTwoBags G P hsmall a
  rw [hreg a (P.subset ha (mem_singleton_self a))] at he
  have hc : 1 < (blackTwoBags G P a).card := by omega
  obtain ⟨A, hA, B, hB, hAB⟩ := one_lt_card.mp hc
  obtain ⟨hAP, hAsize, hAblack⟩ := mem_filter.mp hA
  obtain ⟨hBP, hBsize, hBblack⟩ := mem_filter.mp hB
  exact ⟨A, hAP, B, hBP, hAB, hAsize, hBsize, hAblack, hBblack⟩

omit [DecidableEq V] in
/-- The four-cycle obstruction used in the first paragraph of Lemma 3. -/
lemma high_girth_no_square (G : SimpleGraph V) (hg : 4 < G.egirth)
    {a b x y : V} (hab : a ≠ b) (hxy : x ≠ y)
    (hax : G.Adj a x) (hbx : G.Adj b x)
    (hay : G.Adj a y) (hby : G.Adj b y) : False := by
  let w : G.Walk a a := .cons hax (.cons hbx.symm (.cons hby (.cons hay.symm .nil)))
  have hw : w.IsCycle := by
    simp [w, SimpleGraph.Walk.cons_isCycle_iff, SimpleGraph.Walk.isPath_def,
      hab, hxy, hax.ne, hay.ne, hby.ne, Ne.symm hab,
      Ne.symm hax.ne, Ne.symm hbx.ne, Ne.symm hay.ne]
  have hc := hw.egirth_le_length
  have hl : w.length = 4 := rfl
  rw [hl] at hc
  exact (not_lt_of_ge hc) hg

lemma high_girth_black_pair_singleton (G : SimpleGraph V) (hg : 4 < G.egirth)
    (P : Partition S) {A B : Finset V} (hA : A ∈ P.parts) (hB : B ∈ P.parts)
    (hsize : A.card = 2) (hblack : Black (.ofGraph G) A B) : B.card = 1 := by
  obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp hsize
  apply Nat.le_antisymm _ (one_le_card.mpr (P.nonempty_of_mem_parts hB))
  apply card_le_one.mpr
  intro x hx y hy
  by_contra hxy
  exact high_girth_no_square G hg hab hxy
    (hblack a (by simp) x hx) (hblack b (by simp) x hx)
    (hblack a (by simp) y hy) (hblack b (by simp) y hy)

/-- A two-bag has at most one black neighbor (Lemma 3, opening paragraph). -/
lemma high_girth_pair_blackDegree_le_one (G : SimpleGraph V) (hg : 4 < G.egirth)
    (P : Partition S) {A : Finset V} (hsize : A.card = 2) :
    blackDegree (.ofGraph G) P A ≤ 1 := by
  classical
  apply card_le_one.mpr
  intro B hB C hC
  obtain ⟨hBP, _, hAB⟩ := mem_filter.mp hB
  obtain ⟨hCP, _, hAC⟩ := mem_filter.mp hC
  obtain ⟨a, b, hab, hAeq⟩ := card_eq_two.mp hsize
  obtain ⟨x, hx⟩ := P.nonempty_of_mem_parts hBP
  obtain ⟨y, hy⟩ := P.nonempty_of_mem_parts hCP
  by_contra hBC
  have hxy : x ≠ y := by
    intro he
    exact hBC (P.eq_of_mem_parts hBP hCP hx (he ▸ hy))
  have ha : a ∈ A := by simp [hAeq]
  have hb : b ∈ A := by simp [hAeq]
  exact high_girth_no_square G hg hab hxy
    (hAB a ha x hx) (hAB b hb x hx) (hAC a ha y hy) (hAC b hb y hy)

lemma full_degree_singleton_no_black_two_bag (G : SimpleGraph V) {d : ℕ}
    (hreg : Regular G S d) (P : Partition S) (hsmall : BagsAtMostTwo P)
    {a : V} (ha : {a} ∈ P.parts) (hdegree : totalDegree (.ofGraph G) P {a} = d)
    {B : Finset V} (hB : B ∈ P.parts) (hsize : B.card = 2) :
    ¬ Black (.ofGraph G) {a} B := by
  intro hblack
  have he := singleton_degree_add_blackTwoBags G P hsmall a
  rw [hreg a (P.subset ha (mem_singleton_self a)), hdegree] at he
  have hc : (blackTwoBags G P a).card = 0 := by omega
  have hb : B ∈ blackTwoBags G P a := mem_filter.mpr ⟨hB, hsize, hblack⟩
  exact notMem_empty B ((card_eq_zero.mp hc) ▸ hb)

lemma blackTwoBags_subset_neighbors (G : SimpleGraph V) (P : Partition S) (a : V) :
    blackTwoBags G P a ⊆ neighbors (Adjacent (.ofGraph G)) P {a} := by
  intro B hB
  obtain ⟨hBP, hcard, hblack⟩ := mem_filter.mp hB
  apply mem_filter.mpr
  refine ⟨hBP, ?_, black_adjacent _ (singleton_nonempty a)
    (P.nonempty_of_mem_parts hBP) hblack⟩
  intro he
  rw [he, card_singleton] at hcard
  omega

lemma singleton_degree_twice_ge (G : SimpleGraph V) {d : ℕ}
    (hreg : Regular G S d) (P : Partition S) (hsmall : BagsAtMostTwo P)
    {a : V} (ha : {a} ∈ P.parts) :
    d ≤ 2 * totalDegree (.ofGraph G) P {a} := by
  have he := singleton_degree_add_blackTwoBags G P hsmall a
  rw [hreg a (P.subset ha (mem_singleton_self a))] at he
  have hm : (blackTwoBags G P a).card ≤ totalDegree (.ofGraph G) P {a} :=
    card_le_card (blackTwoBags_subset_neighbors G P a)
  omega

/-- The singleton degree split used in both first-large-bag proofs. -/
lemma singleton_degree_at_least_two (G : SimpleGraph V) {d : ℕ} (hd : 3 ≤ d)
    (hreg : Regular G S d) (P : Partition S) (hsmall : BagsAtMostTwo P)
    {a : V} (ha : {a} ∈ P.parts) :
    2 ≤ totalDegree (.ofGraph G) P {a} := by
  have := singleton_degree_twice_ge G hreg P hsmall ha
  omega

/-- In Theorem 5, a degree-two singleton forces original degree four and
two black two-bag neighbors. -/
lemma degree_two_singleton_general (G : SimpleGraph V) {d : ℕ} (hd : 3 < d)
    (hreg : Regular G S d) (P : Partition S) (hsmall : BagsAtMostTwo P)
    {a : V} (ha : {a} ∈ P.parts) (ha2 : totalDegree (.ofGraph G) P {a} = 2) :
    d = 4 ∧ (blackTwoBags G P a).card = 2 ∧
      blackTwoBags G P a = neighbors (Adjacent (.ofGraph G)) P {a} := by
  have he := singleton_degree_add_blackTwoBags G P hsmall a
  rw [hreg a (P.subset ha (mem_singleton_self a)), ha2] at he
  have hdle := singleton_degree_twice_ge G hreg P hsmall ha
  rw [ha2] at hdle
  have hdeq : d = 4 := by omega
  have hm : (blackTwoBags G P a).card = 2 := by omega
  refine ⟨hdeq, hm, eq_of_subset_of_card_le (blackTwoBags_subset_neighbors G P a) ?_⟩
  change totalDegree (.ofGraph G) P {a} ≤ (blackTwoBags G P a).card
  omega

end Paper
