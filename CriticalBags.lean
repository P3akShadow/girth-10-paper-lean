import TwinPreparation

/-! Critical bags and their immediate elimination in Proposition 14. -/
namespace Paper
open Finset
variable {V : Type*} [DecidableEq V] {S : Finset V}

def NoCritical (G : SimpleGraph V) (P : Partition S) (d : ℕ) : Prop :=
  ∀ A, ¬ Critical G P d A

lemma merge_union_card {P : Partition S} {A B : Finset V}
    (hA : A ∈ P.parts) (hB : B ∈ P.parts) (hne : A ≠ B) :
    (A ∪ B).card = A.card + B.card := card_union_of_disjoint (P.disjoint hA hB hne)

lemma merge_union_two {P : Partition S} {A B : Finset V}
    (hA : A ∈ P.parts) (hB : B ∈ P.parts) (hne : A ≠ B) : 2 ≤ (A ∪ B).card := by
  rw [merge_union_card hA hB hne]
  have := one_le_card.mpr (P.nonempty_of_mem_parts hA)
  have := one_le_card.mpr (P.nonempty_of_mem_parts hB)
  omega

lemma critical_in_merge {G : SimpleGraph V} {P Q : Partition S} {d : ℕ} {A B C : Finset V}
    (hA : A ∈ P.parts) (hB : B ∈ P.parts) (hne : A ≠ B)
    (hQ : Q.parts = insert (A ∪ B) (P.parts \ {A,B})) (hc : Critical G Q d C) :
    C = A ∪ B ∨ Critical G P d C := by
  classical
  obtain ⟨hCQ,hsize,c,hcQ,hblack⟩ := hc
  by_cases hC : C = A ∪ B
  · exact Or.inl hC
  right
  have hCP : C ∈ P.parts := (mem_sdiff.mp ((mem_insert.mp (hQ ▸ hCQ)).resolve_left hC)).1
  have hcn : {c} ≠ A ∪ B := by
    intro heq
    have hh := merge_union_two hA hB hne
    rw [←heq,card_singleton] at hh
    omega
  have hcP : {c} ∈ P.parts := (mem_sdiff.mp ((mem_insert.mp (hQ ▸ hcQ)).resolve_left hcn)).1
  exact ⟨hCP,hsize,c,hcP,hblack⟩

omit [DecidableEq V] in
lemma critical_singleton_ne (G : SimpleGraph V) {A : Finset V} {c : V}
    (hb : Black (.ofGraph G) A {c}) : A ≠ {c} := by
  intro heq
  subst A
  have hh : G.Adj c c := hb c (mem_singleton_self c) c (mem_singleton_self c)
  exact hh.ne rfl

lemma critical_leaf (G : SimpleGraph V) {d : ℕ} (hdeg : MaxDegree G S d)
    (P : Partition S) {A : Finset V} {c : V} (hA : A ∈ P.parts)
    (hc : {c} ∈ P.parts) (hsize : A.card = d) (hb : Black (.ofGraph G) A {c})
    {X : Finset V} (hX : X ∈ P.parts) (he : Adjacent (.ofGraph G) {c} X) : X = A := by
  classical
  obtain ⟨z,hz,x,hx,hcx | hcx⟩ := he
  · have hz' := mem_singleton.mp hz
    subst z
    have hn := full_bag_neighbor G hdeg P hA hc hsize hb (mem_singleton_self c)
    have hxA : x ∈ A := by
      rw [←hn]
      exact mem_filter.mpr ⟨P.subset hX hx,hcx⟩
    exact P.eq_of_mem_parts hX hA hx hxA
  · exact False.elim hcx

lemma critical_redLeaf (G : SimpleGraph V) {d : ℕ} (hdeg : MaxDegree G S d)
    (P : Partition S) (hsat : TwinSaturated G P) {A : Finset V} {c : V}
    (hA : A ∈ P.parts) (hc : {c} ∈ P.parts) (hsize : A.card = d)
    (hb : Black (.ofGraph G) A {c}) :
    RedLeaf ((partitionExpansion P).quotient (.ofGraph G)) P.parts A {c} := by
  classical
  have hne := critical_singleton_ne G hb
  constructor
  · exact Or.inl ⟨Ne.symm hne, black_symm _ hb⟩
  intro X hX hXA hXc
  change ¬ ({c} ≠ X ∧ Black (.ofGraph G) {c} X) ∧
    ¬ ({c} ≠ X ∧ Red (.ofGraph G) {c} X) ∧ ¬ (A ≠ X ∧ Black (.ofGraph G) A X)
  refine ⟨?_,?_,?_⟩
  · intro hh
    exact hXA (critical_leaf G hdeg P hA hc hsize hb hX
      (black_adjacent _ (P.nonempty_of_mem_parts hc) (P.nonempty_of_mem_parts hX) hh.2))
  · intro hh
    exact hXA (critical_leaf G hdeg P hA hc hsize hb hX hh.2.1)
  · intro hh
    have heq := full_bag_black_neighbors_equal G hdeg P hsat hA hsize
      (mem_filter.mpr ⟨hX,Ne.symm hh.1,hh.2⟩)
      (mem_filter.mpr ⟨hc,Ne.symm hne,hb⟩)
    exact hXc heq

lemma critical_exchange (G : SimpleGraph V) {d w s : ℕ} (hdeg : MaxDegree G S d)
    {P : Partition S} (hsat : TwinSaturated G P) (hc : Continuation (.ofGraph G) w s P)
    {A : Finset V} (hcrit : Critical G P d A) :
    ∃ c, ∃ Q : Partition S, {c} ∈ P.parts ∧ Black (.ofGraph G) A {c} ∧
      Q.parts = insert (A ∪ {c}) (P.parts \ {A,{c}}) ∧ Continuation (.ofGraph G) w s Q := by
  obtain ⟨hA,hsize,c,hcP,hblack⟩ := hcrit
  obtain ⟨Q,hQ,_,hcont⟩ := exchange (.ofGraph G) hc hA hcP
    (critical_singleton_ne G hblack) (Or.inr (critical_redLeaf G hdeg P hsat hA hcP hsize hblack))
  exact ⟨c,Q,hcP,hblack,hQ,hcont⟩

lemma critical_merge_larger (G : SimpleGraph V) {d : ℕ} {P : Partition S}
    {A : Finset V} {c : V} (hA : A ∈ P.parts) (hc : {c} ∈ P.parts)
    (hsize : A.card = d) (hb : Black (.ofGraph G) A {c}) : (A ∪ {c}).card = d + 1 := by
  rw [merge_union_card hA hc (critical_singleton_ne G hb),hsize,card_singleton]

lemma red_zero_black (G : SimpleGraph V) {P : Partition S} {A B : Finset V}
    (hB : B ∈ P.parts) (hne : B ≠ A) (hzero : redDegree (.ofGraph G) P A = 0)
    (he : Adjacent (.ofGraph G) A B) : Black (.ofGraph G) A B := by
  classical
  by_contra hb
  have hm : B ∈ neighbors (Red (.ofGraph G)) P A := mem_filter.mpr ⟨hB,hne,he,hb⟩
  have := card_pos.mpr ⟨B,hm⟩
  change 0 < redDegree (.ofGraph G) P A at this
  omega

/-- At the end of twin preparation, a critical bag and its singleton form a component. -/
lemma critical_isolated_pair (G : SimpleGraph V) {d : ℕ} (hdeg : MaxDegree G S d)
    {P : Partition S} (hsat : TwinSaturated G P) (hzero : Bounded (.ofGraph G) 0 d P)
    {A : Finset V} {c : V} (hA : A ∈ P.parts) (hc : {c} ∈ P.parts)
    (hsize : A.card = d) (hb : Black (.ofGraph G) A {c})
    {X : Finset V} (hX : X ∈ P.parts) (hXA : X ≠ A)
    (he : Adjacent (.ofGraph G) A X) : X = {c} := by
  classical
  have hblack := red_zero_black G hX hXA (Nat.eq_zero_of_le_zero (hzero A hA).1) he
  exact full_bag_black_neighbors_equal G hdeg P hsat hA hsize
    (mem_filter.mpr ⟨hX,hXA,hblack⟩)
    (mem_filter.mpr ⟨hc,Ne.symm (critical_singleton_ne G hb),hb⟩)

lemma isolated_pair_merge_bounded (G : SimpleGraph V) {d : ℕ} {P Q : Partition S}
    {A C : Finset V} (hA : A ∈ P.parts) (hC : C ∈ P.parts) (hne : A ≠ C)
    (hQ : Q.parts = insert (A ∪ C) (P.parts \ {A,C}))
    (hz : Bounded (.ofGraph G) 0 d P)
    (hleafA : ∀ X ∈ P.parts, X ≠ A → Adjacent (.ofGraph G) A X → X = C)
    (hleafC : ∀ X ∈ P.parts, X ≠ C → Adjacent (.ofGraph G) C X → X = A) :
    Bounded (.ofGraph G) 0 d Q := by
  classical
  have hout : ∀ X ∈ P.parts \ {A,C}, ¬ Adjacent (.ofGraph G) (A ∪ C) X := by
    intro X hX he
    obtain ⟨hXP,hn⟩ := mem_sdiff.mp hX
    have hXA : X ≠ A := by intro hh; exact hn (by simp [hh])
    have hXC : X ≠ C := by intro hh; exact hn (by simp [hh])
    rcases (adjacent_union_left _ _ _ _).mp he with he | he
    · exact hXC (hleafA X hXP hXA he)
    · exact hXA (hleafC X hXP hXC he)
  have hmerged : totalDegree (.ofGraph G) Q (A ∪ C) = 0 := by
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_notMem.mpr
    intro X hX
    obtain ⟨hX,hneX,he⟩ := mem_filter.mp hX
    exact hout X ((mem_insert.mp (hQ ▸ hX)).resolve_left hneX) he
  intro X hX
  rcases mem_insert.mp (hQ ▸ hX) with rfl | hXP
  · have hh := redDegree_le_totalDegree (.ofGraph G) Q (A ∪ C)
    exact ⟨by omega,by omega⟩
  obtain ⟨hXP,hn⟩ := mem_sdiff.mp hXP
  have hXA : X ≠ A := by intro hh; exact hn (by simp [hh])
  have hXC : X ≠ C := by intro hh; exact hn (by simp [hh])
  constructor
  · apply Nat.le_zero.mpr
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_notMem.mpr
    intro Y hY
    obtain ⟨hY,hYX,he,hnb⟩ := mem_filter.mp hY
    rcases mem_insert.mp (hQ ▸ hY) with rfl | hYP
    · exact hout X (mem_sdiff.mpr ⟨hXP,hn⟩) (adjacent_symm _ he)
    · have hb := red_zero_black G (mem_sdiff.mp hYP).1 hYX
        (Nat.eq_zero_of_le_zero (hz X hXP).1) he
      exact hnb hb
  · exact (outside_totalDegree_le (.ofGraph G) hA hC hne hQ hXP hXA hXC).trans (hz X hXP).2

/-- Remove the isolated critical components before starting the normalized sequence. -/
lemma prepare_critical (G : SimpleGraph V) {d w s : ℕ} (hdeg : MaxDegree G S d)
    (P : Partition S) (hsat : TwinSaturated G P) (hz : Bounded (.ofGraph G) 0 d P)
    (hc : Continuation (.ofGraph G) w s P) :
    ∃ Q : Partition S, Prefix (.ofGraph G) 0 d P Q ∧ TwinSaturated G Q ∧
      NoCritical G Q d ∧ Continuation (.ofGraph G) w s Q := by
  classical
  generalize hn : P.parts.card = n
  induction n using Nat.strong_induction_on generalizing P with | h n ih =>
    by_cases hnc : NoCritical G P d
    · exact ⟨P,.refl P,hsat,hnc,hc⟩
    unfold NoCritical at hnc
    push Not at hnc
    obtain ⟨A,hcrit⟩ := hnc
    obtain ⟨c,R,hcP,hblack,hR,hcR⟩ := critical_exchange G hdeg hsat hc hcrit
    have hne := critical_singleton_ne G hblack
    have hm : Merge P R := ⟨A,hcrit.1,{c},hcP,hne,hR⟩
    have hzR := isolated_pair_merge_bounded G hcrit.1 hcP hne hR hz
      (fun X hX hXA he => critical_isolated_pair G hdeg hsat hz hcrit.1 hcP hcrit.2.1 hblack hX hXA he)
      (fun X hX _ he => critical_leaf G hdeg P hcrit.1 hcP hcrit.2.1 hblack hX he)
    obtain ⟨Q,hpre,hsQ,hnQ,hcQ⟩ := ih R.parts.card (by simpa [←hn] using hm.card_lt)
      R (hsat.merge hm) hzR hcR rfl
    exact ⟨Q,.step hz hm hpre,hsQ,hnQ,hcQ⟩

end Paper
