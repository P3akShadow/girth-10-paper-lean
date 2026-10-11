import CriticalBags

/-! The two sequence normalizations in Proposition 14. -/
namespace Paper
open Finset
variable {V : Type*} [DecidableEq V] {S : Finset V}

lemma merged_old_not_mem {P Q : Partition S} {A B : Finset V}
    (hA : A ∈ P.parts) (hB : B ∈ P.parts) (hne : A ≠ B)
    (hQ : Q.parts = insert (A ∪ B) (P.parts \ {A,B})) : A ∉ Q.parts := by
  classical
  intro ha
  rcases mem_insert.mp (hQ ▸ ha) with heq | heq
  · exact union_not_part P hA hB hne (heq ▸ hA)
  · exact (mem_sdiff.mp heq).2 (by simp)

lemma eliminate_only_critical (G : SimpleGraph V) {d : ℕ} {P Q : Partition S}
    {A : Finset V} {c : V} (hA : A ∈ P.parts) (hc : {c} ∈ P.parts)
    (hsize : A.card = d) (hb : Black (.ofGraph G) A {c})
    (honly : ∀ X, Critical G P d X → X = A)
    (hQ : Q.parts = insert (A ∪ {c}) (P.parts \ {A,{c}})) : NoCritical G Q d := by
  intro X hcrit
  rcases critical_in_merge hA hc (critical_singleton_ne G hb) hQ hcrit with rfl | hcritP
  · have := critical_merge_larger G hA hc hsize hb
    have := hcrit.2.1
    omega
  · have heq := honly X hcritP
    subst X
    exact merged_old_not_mem hA hc (critical_singleton_ne G hb) hQ hcrit.1

lemma three_merge_parts {P Q R : Partition S} {A B C : Finset V}
    (hA : A ∈ P.parts) (hB : B ∈ P.parts) (hne : A ≠ B)
    (hQ : Q.parts = insert (A ∪ B) (P.parts \ {A,B}))
    (hR : R.parts = insert ((A ∪ B) ∪ C) (Q.parts \ {A ∪ B,C})) :
    R.parts = insert ((A ∪ B) ∪ C) (P.parts \ {A,B,C}) := by
  classical
  have hn := union_not_part P hA hB hne
  rw [hR,hQ]
  ext X
  simp only [mem_insert,mem_sdiff,mem_singleton]
  constructor
  · rintro (hh | ⟨hh,hnX⟩)
    · exact Or.inl hh
    · rcases hh with rfl | hh
      · exact False.elim (hnX (Or.inl rfl))
      · exact Or.inr ⟨hh.1,by tauto⟩
  · rintro (hh | ⟨hh,hnX⟩)
    · exact Or.inl hh
    · exact Or.inr ⟨Or.inr ⟨hh,by tauto⟩,by
        rintro (rfl | heq)
        · exact hn hh
        · exact hnX (Or.inr (Or.inr heq))⟩

lemma singleton_before_merge {P Q : Partition S} {A B : Finset V} {c : V}
    (hA : A ∈ P.parts) (hB : B ∈ P.parts) (hne : A ≠ B)
    (hQ : Q.parts = insert (A ∪ B) (P.parts \ {A,B})) (hc : {c} ∈ Q.parts) :
    {c} ∈ P.parts ∧ {c} ≠ A ∧ {c} ≠ B := by
  classical
  have hcn : {c} ≠ A ∪ B := by
    intro heq
    have := merge_union_two hA hB hne
    rw [←heq,card_singleton] at this
    omega
  obtain ⟨hh,hn⟩ := mem_sdiff.mp ((mem_insert.mp (hQ ▸ hc)).resolve_left hcn)
  exact ⟨hh,fun heq => hn (by simp [heq]),fun heq => hn (by simp [heq])⟩

/-- Replace (A,B), then (A∪B,c), by (A,c), then (A∪c,B).
The endpoint partition is literally the same. -/
lemma swap_critical_merges (G : SimpleGraph V) {d : ℕ} (hdeg : MaxDegree G S d)
    {P Q R : Partition S} {A B : Finset V} {c : V}
    (hA : A ∈ P.parts) (hB : B ∈ P.parts) (hne : A ≠ B)
    (hQ : Q.parts = insert (A ∪ B) (P.parts \ {A,B}))
    (hcQ : {c} ∈ Q.parts) (hsize : (A ∪ B).card = d)
    (hblack : Black (.ofGraph G) (A ∪ B) {c})
    (hR : R.parts = insert ((A ∪ B) ∪ {c}) (Q.parts \ {A ∪ B,{c}}))
    {k : ℕ} (hbound : ∀ X ∈ P.parts, totalDegree (.ofGraph G) P X ≤ k) :
    ∃ M : Partition S, Merge P M ∧ Merge M R ∧ Bounded (.ofGraph G) k k M := by
  classical
  obtain ⟨hcP,hcA,hcB⟩ := singleton_before_merge hA hB hne hQ hcQ
  let M := mergePartition P A {c} hA hcP
  have hM : M.parts = insert (A ∪ {c}) (P.parts \ {A,{c}}) := mergePartition_parts ..
  have hACM : A ∪ {c} ∈ M.parts := by rw [hM]; simp
  have hBM : B ∈ M.parts := by rw [hM]; simp [hB,Ne.symm hne,Ne.symm hcB]
  have hACB : A ∪ {c} ≠ B := fun heq => union_not_part P hA hcP (Ne.symm hcA) (heq ▸ hB)
  have hRM : R.parts = insert ((A ∪ {c}) ∪ B) (M.parts \ {A ∪ {c},B}) := by
    have hbase := three_merge_parts hA hB hne hQ hR
    let R' := mergePartition M (A ∪ {c}) B hACM hBM
    have hR' : R'.parts = insert ((A ∪ {c}) ∪ B) (M.parts \ {A ∪ {c},B}) := mergePartition_parts ..
    have hbase' := three_merge_parts hA hcP (Ne.symm hcA) hM hR'
    rw [←hR',hbase',hbase]
    congr 1
    · ext x; simp only [mem_union]; tauto
    · ext X; simp only [mem_sdiff,mem_insert,mem_singleton]; tauto
  refine ⟨M,⟨A,hA,{c},hcP,Ne.symm hcA,hM⟩,⟨A ∪ {c},hACM,B,hBM,hACB,hRM⟩,?_⟩
  have hleaf : ∀ X ∈ P.parts, Adjacent (.ofGraph G) {c} X → X = A ∨ X = B := by
    intro X hX he
    obtain ⟨z,hz,x,hx,he | he⟩ := he
    · have hz' := mem_singleton.mp hz
      subst z
      have hABQ : A ∪ B ∈ Q.parts := by rw [hQ]; simp
      have hn := full_bag_neighbor G hdeg Q hABQ hcQ hsize hblack (mem_singleton_self c)
      have hxAB : x ∈ A ∪ B := by rw [←hn]; exact mem_filter.mpr ⟨P.subset hX hx,he⟩
      rcases mem_union.mp hxAB with hxA | hxB
      · exact Or.inl (P.eq_of_mem_parts hX hA hx hxA)
      · exact Or.inr (P.eq_of_mem_parts hX hB hx hxB)
    · exact False.elim he
  have hAC : Adjacent (.ofGraph G) A {c} := by
    obtain ⟨a,ha⟩ := P.nonempty_of_mem_parts hA
    exact ⟨a,ha,c,mem_singleton_self c,Or.inl (hblack a (mem_union_left _ ha) c (mem_singleton_self c))⟩
  have htotal : ∀ X ∈ M.parts, totalDegree (.ofGraph G) M X ≤ k := by
    intro X hX
    rcases mem_insert.mp (hM ▸ hX) with rfl | hXP
    · exact (swap_merge_totalDegree (.ofGraph G) hcP hcA hAC hM hleaf).trans (hbound A hA)
    · obtain ⟨hXP,hn⟩ := mem_sdiff.mp hXP
      have hXA : X ≠ A := fun hh => hn (by simp [hh])
      have hXc : X ≠ {c} := fun hh => hn (by simp [hh])
      exact (outside_totalDegree_le (.ofGraph G) hA hcP (Ne.symm hcA) hM hXP hXA hXc).trans
        (hbound X hXP)
  exact fun X hX => ⟨(redDegree_le_totalDegree (.ofGraph G) M X).trans (htotal X hX),htotal X hX⟩

/-- Normalize the continuation, immediately eliminating each newly created
critical bag. The second continuation makes precisely the paper's two-merge swap. -/
lemma normalize_sparse (G : SimpleGraph V) {d w s : ℕ} (hd : 3 ≤ d)
    (hdeg : MaxDegree G S d) (P : Partition S) (hsat : TwinSaturated G P)
    (hnc : NoCritical G P d) (hc : Continuation (.ofGraph G) w s P) :
    Continuation (.ofGraph G) w (max (w + 1) ((d - 1)^2)) P ∧
    Continuation (.ofGraph G) (max w ((d - 1)^2 + 1)) (max w ((d - 1)^2 + 1)) P := by
  classical
  generalize hn : P.parts.card = n
  induction n using Nat.strong_induction_on generalizing P with | h n ih =>
    have hb1 : Bounded (.ofGraph G) w (max (w + 1) ((d - 1)^2)) P := by
      intro X hX
      exact ⟨(hc.bounded X hX).1,
        (normalized_bag_degrees G hd hdeg P hsat hX (hc.bounded X hX).1).1⟩
    have ht2 : ∀ X ∈ P.parts, totalDegree (.ofGraph G) P X ≤ max w ((d - 1)^2 + 1) := by
      intro X hX
      exact (normalized_bag_degrees G hd hdeg P hsat hX (hc.bounded X hX).1).2 (hnc X)
    have hb2 : Bounded (.ofGraph G) (max w ((d - 1)^2 + 1)) (max w ((d - 1)^2 + 1)) P :=
      fun X hX => ⟨(redDegree_le_totalDegree (.ofGraph G) P X).trans (ht2 X hX),ht2 X hX⟩
    cases hc with
    | done _ hdone => exact ⟨.done hb1 hdone,.done hb2 hdone⟩
    | @step _ Q _ hm hcQ =>
      have hsatQ := hsat.merge hm
      by_cases hncQ : NoCritical G Q d
      · obtain ⟨h1,h2⟩ := ih Q.parts.card (by simpa [←hn] using hm.card_lt) Q hsatQ hncQ hcQ rfl
        exact ⟨.step hb1 hm h1,.step hb2 hm h2⟩
      unfold NoCritical at hncQ
      push Not at hncQ
      obtain ⟨D,hcrit⟩ := hncQ
      obtain ⟨A,hA,B,hB,hAB,hQ⟩ := hm
      have hD : D = A ∪ B := (critical_in_merge hA hB hAB hQ hcrit).resolve_right (hnc D)
      subst D
      have hU : A ∪ B ∈ Q.parts := hcrit.1
      have hsize : (A ∪ B).card = d := hcrit.2.1
      obtain ⟨c,R,hcQmem,hblack,hR,hcR⟩ := critical_exchange G hdeg hsatQ hcQ hcrit
      have hUR : A ∪ B ≠ {c} := critical_singleton_ne G hblack
      have hmR : Merge Q R := ⟨A ∪ B,hU,{c},hcQmem,hUR,hR⟩
      have honly : ∀ X, Critical G Q d X → X = A ∪ B := by
        intro X hX
        exact (critical_in_merge hA hB hAB hQ hX).resolve_right (hnc X)
      have hncR := eliminate_only_critical G hU hcQmem hsize hblack honly hR
      have hlt : R.parts.card < n := by
        have hPQ := (show Merge P Q from ⟨A,hA,B,hB,hAB,hQ⟩).card_lt
        have hQR := hmR.card_lt
        omega
      obtain ⟨h1,h2⟩ := ih R.parts.card hlt R (hsatQ.merge hmR) hncR hcR rfl
      have hbQ : Bounded (.ofGraph G) w (max (w + 1) ((d - 1)^2)) Q := by
        intro X hX
        exact ⟨(hcQ.bounded X hX).1,
          (normalized_bag_degrees G hd hdeg Q hsatQ hX (hcQ.bounded X hX).1).1⟩
      obtain ⟨M,hmPM,hmMR,hbM⟩ := swap_critical_merges G hdeg hA hB hAB hQ hcQmem hsize hblack hR ht2
      exact ⟨.step hb1 ⟨A,hA,B,hB,hAB,hQ⟩ (.step hbQ hmR h1),
        .step hb2 hmPM (.step hbM hmMR h2)⟩

end Paper
