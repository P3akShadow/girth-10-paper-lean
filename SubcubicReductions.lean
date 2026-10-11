import HighGirthMerging
import LiftFiberState
import TwinPreparation

/-! Short cycles and vertices of degree at most two admit a nontrivial
partial sequence of total degree at most five ending at a subcubic quotient.
These are the local reductions in Corollary 16. -/

namespace Paper
open Finset
variable {V : Type*} [DecidableEq V] {S : Finset V}

lemma bounded_of_total (T : Trigraph V) (P : Partition S) {s : ℕ}
    (h : ∀ A ∈ P.parts, totalDegree T P A ≤ s) : Bounded T s s P := by
  intro A hA
  exact ⟨(redDegree_le_totalDegree T P A).trans (h A hA), h A hA⟩

lemma maxDegree_bounded_bot (G : SimpleGraph V) {d : ℕ} (h : MaxDegree G S d) :
    Bounded (.ofGraph G) d d (⊥ : Partition S) := by
  apply bounded_of_total
  intro A hA
  obtain ⟨a, ha, rfl⟩ := Finpartition.mem_bot_iff.mp hA
  exact (singleton_totalDegree_le G ⊥ a).trans (h a ha)

/-- An adjacent merge with a common neighbor saves three incidences. -/
lemma adjacent_common_merge_totalDegree (T : Trigraph V)
    {P Q : Partition S} {A B C : Finset V}
    (hA : A ∈ P.parts) (hB : B ∈ P.parts) (hAB : A ≠ B)
    (hQ : Q.parts = insert (A ∪ B) (P.parts \ {A, B}))
    (hC : C ∈ P.parts) (hCA : C ≠ A) (hCB : C ≠ B)
    (hABadj : Adjacent T A B) (hAC : Adjacent T A C) (hBC : Adjacent T B C) :
    totalDegree T Q (A ∪ B) + 3 ≤ totalDegree T P A + totalDegree T P B := by
  classical
  have hcommon : 1 ≤
      ((neighbors (Adjacent T) P A).erase B ∩
        (neighbors (Adjacent T) P B).erase A).card := by
    apply one_le_card.mpr
    exact ⟨C, mem_inter.mpr
      ⟨mem_erase.mpr ⟨hCB, mem_filter.mpr ⟨hC, hCA, hAC⟩⟩,
       mem_erase.mpr ⟨hCA, mem_filter.mpr ⟨hC, hCB, hBC⟩⟩⟩⟩
  have he := adjacent_merge_totalDegree_add_common T hA hB hAB hQ hABadj
  omega

/-- An untouched bag loses a neighbor when two of its neighbors merge. -/
lemma outside_common_merge_totalDegree (T : Trigraph V)
    {P Q : Partition S} {A B C : Finset V}
    (hAB : A ≠ B) (hQ : Q.parts = insert (A ∪ B) (P.parts \ {A, B}))
    (hA : A ∈ P.parts) (hB : B ∈ P.parts) (hCA : C ≠ A) (hCB : C ≠ B)
    (hCAadj : Adjacent T C A) (hCBadj : Adjacent T C B) :
    totalDegree T Q C + 1 ≤ totalDegree T P C := by
  classical
  have hsub : neighbors (Adjacent T) Q C ⊆
      insert (A ∪ B) (((neighbors (Adjacent T) P C).erase A).erase B) := by
    intro X hX
    obtain ⟨hXP, hXC, hCX⟩ := mem_filter.mp hX
    rw [hQ] at hXP
    rcases mem_insert.mp hXP with rfl | hXP
    · exact mem_insert_self ..
    · obtain ⟨hXP, hXAB⟩ := mem_sdiff.mp hXP
      have hXA : X ≠ A := fun he => hXAB (by simp [he])
      have hXB : X ≠ B := fun he => hXAB (by simp [he])
      exact mem_insert_of_mem (mem_erase.mpr ⟨hXB,
        mem_erase.mpr ⟨hXA, mem_filter.mpr ⟨hXP, hXC, hCX⟩⟩⟩)
  have ha : A ∈ neighbors (Adjacent T) P C :=
    mem_filter.mpr ⟨hA, hCA.symm, hCAadj⟩
  have hb : B ∈ (neighbors (Adjacent T) P C).erase A :=
    mem_erase.mpr ⟨hAB.symm, mem_filter.mpr ⟨hB, hCB.symm, hCBadj⟩⟩
  have hbound := (card_le_card hsub).trans (card_insert_le ..)
  have hcardA := card_erase_add_one ha
  have hcardB := card_erase_add_one hb
  unfold totalDegree
  omega

/-- The smaller endpoint is a partition of the original vertex set; its
parts will become the vertices of the smaller simple graph. -/
def SubcubicReduction (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∃ P : Partition S, Prefix (.ofGraph G) 5 5 ⊥ P ∧
    Bounded (.ofGraph G) 3 3 P ∧ P.parts.card < S.card

lemma subcubicReduction_of_merge (G : SimpleGraph V) (hdeg : MaxDegree G S 3)
    {Q : Partition S} (hm : Merge ⊥ Q) (hb : Bounded (.ofGraph G) 3 3 Q) :
    SubcubicReduction G S := by
  have hbot := maxDegree_bounded_bot G hdeg
  refine ⟨Q, .step (fun A hA => ⟨(hbot A hA).1.trans (by omega),
    (hbot A hA).2.trans (by omega)⟩) hm (.refl Q), hb, ?_⟩
  exact hm.card_lt.trans_le (partition_card_le _)

lemma subcubicReduction_triangle (G : SimpleGraph V) (hdeg : MaxDegree G S 3)
    {a b c : V} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a) :
    SubcubicReduction G S := by
  classical
  have hA : {a} ∈ (⊥ : Partition S).parts := Finpartition.mem_bot_iff.mpr ⟨a, ha, rfl⟩
  have hB : {b} ∈ (⊥ : Partition S).parts := Finpartition.mem_bot_iff.mpr ⟨b, hb, rfl⟩
  have hC : {c} ∈ (⊥ : Partition S).parts := Finpartition.mem_bot_iff.mpr ⟨c, hc, rfl⟩
  have hAB : ({a} : Finset V) ≠ {b} := by simpa using hab.ne
  have hCA : ({c} : Finset V) ≠ {a} := by simpa using hca.ne
  have hCB : ({c} : Finset V) ≠ {b} := by simpa using hbc.ne.symm
  let Q := mergePartition ⊥ {a} {b} hA hB
  have hQ := mergePartition_parts (⊥ : Partition S) hA hB
  have hbot := maxDegree_bounded_bot G hdeg
  have hnew := adjacent_common_merge_totalDegree (.ofGraph G) hA hB hAB hQ
    hC hCA hCB ((singleton_adjacent_graph G a b).mpr hab)
    ((singleton_adjacent_graph G a c).mpr hca.symm)
    ((singleton_adjacent_graph G b c).mpr hbc)
  have hdA := (hbot {a} hA).2
  have hdB := (hbot {b} hB).2
  exact subcubicReduction_of_merge G hdeg ⟨{a}, hA, {b}, hB, hAB, hQ⟩
    (bounded_merge_total (.ofGraph G) hA hB hAB hQ hbot (by omega))

lemma subcubicReduction_low_degree (G : SimpleGraph V) (hdeg : MaxDegree G S 3)
    (hcard : 1 < S.card) {v : V} (hv : v ∈ S)
    (hvdeg : (graphNeighbors G S v).card ≤ 2) : SubcubicReduction G S := by
  classical
  have hV : {v} ∈ (⊥ : Partition S).parts := Finpartition.mem_bot_iff.mpr ⟨v, hv, rfl⟩
  have hbot := maxDegree_bounded_bot G hdeg
  by_cases hn : (graphNeighbors G S v).Nonempty
  · obtain ⟨u, hu⟩ := hn
    obtain ⟨huS, hvu⟩ := mem_filter.mp hu
    have hU : {u} ∈ (⊥ : Partition S).parts := Finpartition.mem_bot_iff.mpr ⟨u, huS, rfl⟩
    have hVU : ({v} : Finset V) ≠ {u} := by simpa using hvu.ne
    have hQ := mergePartition_parts (⊥ : Partition S) hV hU
    have hnew := adjacent_merge_totalDegree (.ofGraph G) hV hU hVU hQ
      ((singleton_adjacent_graph G v u).mpr hvu)
    have hdv := (singleton_totalDegree_le G ⊥ v).trans hvdeg
    have hdu := (hbot {u} hU).2
    exact subcubicReduction_of_merge G hdeg ⟨{v}, hV, {u}, hU, hVU, hQ⟩
      (bounded_merge_total (.ofGraph G) hV hU hVU hQ hbot (by omega))
  · have hz : (graphNeighbors G S v).card = 0 := card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp hn)
    obtain ⟨u, hu, huv⟩ := exists_mem_ne (by omega : 1 < S.card) v
    have hU : {u} ∈ (⊥ : Partition S).parts := Finpartition.mem_bot_iff.mpr ⟨u, hu, rfl⟩
    have hVU : ({v} : Finset V) ≠ {u} := by simpa using huv.symm
    have hQ := mergePartition_parts (⊥ : Partition S) hV hU
    have hnew := merged_totalDegree_le_sum (.ofGraph G) hQ
    have hdv := singleton_totalDegree_le G (⊥ : Partition S) v
    have hdu := (hbot {u} hU).2
    exact subcubicReduction_of_merge G hdeg ⟨{v}, hV, {u}, hU, hVU, hQ⟩
      (bounded_merge_total (.ofGraph G) hV hU hVU hQ hbot (by omega))

lemma subcubicReduction_four_cycle (G : SimpleGraph V) (hdeg : MaxDegree G S 3)
    {a b c d : V} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hd : d ∈ S)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a)
    (hac : a ≠ c) (hbd : b ≠ d) : SubcubicReduction G S := by
  classical
  have hA : {a} ∈ (⊥ : Partition S).parts := Finpartition.mem_bot_iff.mpr ⟨a, ha, rfl⟩
  have hB : {b} ∈ (⊥ : Partition S).parts := Finpartition.mem_bot_iff.mpr ⟨b, hb, rfl⟩
  have hC : {c} ∈ (⊥ : Partition S).parts := Finpartition.mem_bot_iff.mpr ⟨c, hc, rfl⟩
  have hD : {d} ∈ (⊥ : Partition S).parts := Finpartition.mem_bot_iff.mpr ⟨d, hd, rfl⟩
  have hAB : ({a} : Finset V) ≠ {b} := by simpa using hab.ne
  have hCA : ({c} : Finset V) ≠ {a} := by simpa using hac.symm
  have hCB : ({c} : Finset V) ≠ {b} := by simpa using hbc.ne.symm
  have hDA : ({d} : Finset V) ≠ {a} := by simpa using hda.ne
  have hDB : ({d} : Finset V) ≠ {b} := by simpa using hbd.symm
  have hCD : ({c} : Finset V) ≠ {d} := by simpa using hcd.ne
  let P := mergePartition ⊥ {a} {b} hA hB
  have hP : P.parts = insert ({a} ∪ {b}) ((⊥ : Partition S).parts \ {{a}, {b}}) := rfl
  have hCP : {c} ∈ P.parts := by simp [hP, hc, hCA, hCB]
  have hDP : {d} ∈ P.parts := by simp [hP, hd, hDA, hDB]
  have hUP : {a} ∪ {b} ∈ P.parts := by simp [hP]
  have hUC : {a} ∪ {b} ≠ ({c} : Finset V) := fun he =>
    union_not_part (⊥ : Partition S) hA hB hAB (he.symm ▸ hC)
  have hUD : {a} ∪ {b} ≠ ({d} : Finset V) := fun he =>
    union_not_part (⊥ : Partition S) hA hB hAB (he.symm ▸ hD)
  let Q := mergePartition P {c} {d} hCP hDP
  have hQ : Q.parts = insert ({c} ∪ {d}) (P.parts \ {{c}, {d}}) := rfl
  have hbot := maxDegree_bounded_bot G hdeg
  have hbot5 : Bounded (.ofGraph G) 5 5 (⊥ : Partition S) := fun X hX =>
    ⟨(hbot X hX).1.trans (by omega), (hbot X hX).2.trans (by omega)⟩
  have hfirst := adjacent_merge_totalDegree (.ofGraph G) hA hB hAB hP
    ((singleton_adjacent_graph G a b).mpr hab)
  have hfirstBound : totalDegree (.ofGraph G) P ({a} ∪ {b}) ≤ 4 := by
    have h1 := (hbot {a} hA).2
    have h2 := (hbot {b} hB).2
    omega
  have hP5 : Bounded (.ofGraph G) 5 5 P :=
    bounded_merge_total (.ofGraph G) hA hB hAB hP hbot5 (by omega)
  have hUCadj : Adjacent (.ofGraph G) ({a} ∪ {b}) {c} :=
    (adjacent_union_left _ _ _ _).mpr (Or.inr ((singleton_adjacent_graph G b c).mpr hbc))
  have hUDadj : Adjacent (.ofGraph G) ({a} ∪ {b}) {d} :=
    (adjacent_union_left _ _ _ _).mpr (Or.inl ((singleton_adjacent_graph G a d).mpr hda.symm))
  have hsecond := adjacent_common_merge_totalDegree (.ofGraph G) hCP hDP hCD hQ
    hUP hUC hUD ((singleton_adjacent_graph G c d).mpr hcd)
    (adjacent_symm _ hUCadj) (adjacent_symm _ hUDadj)
  have hsecondBound : totalDegree (.ofGraph G) Q ({c} ∪ {d}) ≤ 3 := by
    have h1 := (singleton_totalDegree_le G P c).trans (hdeg c hc)
    have h2 := (singleton_totalDegree_le G P d).trans (hdeg d hd)
    omega
  have hfirstLoss := outside_common_merge_totalDegree (.ofGraph G) hCD hQ
    hCP hDP hUC hUD hUCadj hUDadj
  have hQ3 : Bounded (.ofGraph G) 3 3 Q := by
    apply bounded_of_total
    intro X hX
    rw [hQ] at hX
    rcases mem_insert.mp hX with rfl | hX
    · exact hsecondBound
    · have hXP := (mem_sdiff.mp hX).1
      by_cases hXU : X = {a} ∪ {b}
      · subst X
        omega
      · rw [hP] at hXP
        have hXbot := (mem_sdiff.mp ((mem_insert.mp hXP).resolve_left hXU)).1
        obtain ⟨x, hx, rfl⟩ := Finpartition.mem_bot_iff.mp hXbot
        exact (singleton_totalDegree_le G Q x).trans (hdeg x hx)
  have hmP : Merge (⊥ : Partition S) P := ⟨{a}, hA, {b}, hB, hAB, hP⟩
  have hmQ : Merge P Q := ⟨{c}, hCP, {d}, hDP, hCD, hQ⟩
  exact ⟨Q, .step hbot5 hmP (.step hP5 hmQ (.refl Q)), hQ3,
    hmQ.card_lt.trans (hmP.card_lt.trans_le (partition_card_le _))⟩

end Paper
