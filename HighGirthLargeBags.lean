import HighGirthGeometry

/-! First-large-bag arguments of Lemma 4 and Theorem 5. -/
namespace Paper
open Finset SimpleGraph CycleLift
variable {V : Type*} [DecidableEq V] {S : Finset V}
attribute [local instance] Classical.propDecidable

/-- With one merged bag already saturated, merging a nonneighbor can add
no new neighbor: every neighbor of the second bag already meets the first. -/
lemma nonadjacent_saturated_merge_neighbor_subset (T : Trigraph V)
    {P Q : Partition S} {A B : Finset V} {w s : ℕ}
    (hA : A ∈ P.parts) (hB : B ∈ P.parts) (hAB : A ≠ B)
    (hQ : Q.parts = insert (A ∪ B) (P.parts \ {A, B}))
    (hnon : ¬ Adjacent T A B) (hsat : redDegree T P A = w)
    (hbound : Bounded T w s Q) :
    neighbors (Adjacent T) P B ⊆ neighbors (Adjacent T) P A := by
  classical
  have hU : A ∪ B ∈ Q.parts := by simp [hQ]
  have hsub : neighbors (Red T) P A ⊆ neighbors (Red T) Q (A ∪ B) := by
    intro C hC
    obtain ⟨hCP, hCA, hred⟩ := mem_filter.mp hC
    have hCB : C ≠ B := fun he => hnon (he ▸ hred.1)
    refine mem_filter.mpr ⟨by simp [hQ, hCP, hCA, hCB], ?_, ?_⟩
    · intro he
      exact union_not_part P hA hB hAB (he ▸ hCP)
    · exact ⟨(adjacent_union_left T A B C).mpr (Or.inl hred.1),
        fun hb => hred.2 ((black_union_left T A B C).mp hb).1⟩
  have heq : neighbors (Red T) P A = neighbors (Red T) Q (A ∪ B) :=
    eq_of_subset_of_card_le hsub (by simpa [← hsat, redDegree] using (hbound _ hU).1)
  intro C hC
  obtain ⟨hCP, hCB, hBC⟩ := mem_filter.mp hC
  have hCA : C ≠ A := fun he => hnon (adjacent_symm _ (he ▸ hBC))
  apply mem_filter.mpr
  refine ⟨hCP, hCA, ?_⟩
  by_contra hnAC
  have hred : Red T (A ∪ B) C := by
    refine ⟨(adjacent_union_left T A B C).mpr (Or.inr hBC), ?_⟩
    intro hb
    exact hnAC (black_adjacent T (P.nonempty_of_mem_parts hA)
      (P.nonempty_of_mem_parts hCP) ((black_union_left T A B C).mp hb).1)
  have hCQ : C ∈ neighbors (Red T) Q (A ∪ B) := mem_filter.mpr
    ⟨by simp [hQ, hCP, hCA, hCB],
      fun he => union_not_part P hA hB hAB (he ▸ hCP), hred⟩
  rw [← heq] at hCQ
  exact hnAC (mem_filter.mp hCQ).2.2.1

lemma adjacent_singleton_no_common (G : SimpleGraph V) (hg : 8 < G.egirth)
    (P : Partition S) (near : BagsNear G P) {A : Finset V} {u : V}
    (hA : A ∈ P.parts) (hu : {u} ∈ P.parts) (hAu : A ≠ {u})
    (hadj : Adjacent (.ofGraph G) A {u}) :
    Disjoint (neighbors (Adjacent (.ofGraph G)) P A)
      (neighbors (Adjacent (.ofGraph G)) P {u}) := by
  apply Finset.disjoint_left.mpr
  intro B hBA hBu
  obtain ⟨hB, hBA, eAB⟩ := mem_filter.mp hBA
  obtain ⟨_, hBu, euB⟩ := mem_filter.mp hBu
  exact high_girth_no_singleton_triangle G hg P near hu hA hB hAu.symm hBu.symm hBA.symm
    (adjacent_symm _ hadj) eAB (adjacent_symm _ euB)

/-- Adjacent pair/singleton case, common to Lemma 4 and Theorem 5. -/
lemma adjacent_pair_singleton_merge_impossible (G : SimpleGraph V) {d s : ℕ}
    (hd : 3 ≤ d) (hg : 8 < G.egirth) (hreg : Regular G S d)
    {P Q : Partition S} (hsmall : BagsAtMostTwo P) (near : BagsNear G P)
    (hsat : ∀ C ∈ P.parts, C.card = 2 → redDegree (.ofGraph G) P C = 2 * d - 2)
    {A : Finset V} {u : V} (hA : A ∈ P.parts) (hu : {u} ∈ P.parts)
    (hsize : A.card = 2)
    (hQ : Q.parts = insert (A ∪ {u}) (P.parts \ {A, {u}}))
    (hbound : Bounded (.ofGraph G) (2 * d - 2) s Q)
    (hadj : Adjacent (.ofGraph G) A {u}) : False := by
  classical
  have hAu : A ≠ {u} := by intro he; simp [he] at hsize
  have hU : A ∪ {u} ∈ Q.parts := by simp [hQ]
  have hcommon := adjacent_singleton_no_common G hg P near hA hu hAu hadj
  have hformula := adjacent_no_common_merge_redDegree (.ofGraph G) hA hu hAu hQ hadj hcommon
  have hsatA := hsat A hA hsize
  have htotalA := redDegree_le_totalDegree (.ofGraph G) P A
  have htotalu := singleton_degree_at_least_two G hd hreg P hsmall hu
  have hbounded := (hbound _ hU).1
  have hdeg2 : totalDegree (.ofGraph G) P {u} = 2 := by omega
  have hcount := singleton_degree_add_blackTwoBags G P hsmall u
  rw [hreg u (P.subset hu (mem_singleton_self _)), hdeg2] at hcount
  have hblackpos : 0 < (blackTwoBags G P u).card := by omega
  obtain ⟨C, hC⟩ := card_pos.mp hblackpos
  obtain ⟨hCP, hCsize, hblack⟩ := mem_filter.mp hC
  by_cases hCA : C = A
  · subst C
    have hw : {u} ∈ neighbors (Black (.ofGraph G)) P A :=
      mem_filter.mpr ⟨hu, hAu.symm, black_symm _ hblack⟩
    have hpos : 1 ≤ blackDegree (.ofGraph G) P A := one_le_card.mpr ⟨{u}, hw⟩
    have hdecomp := totalDegree_eq_red_add_black (.ofGraph G) P hA
    omega
  · have hCu : C ≠ {u} := by intro he; simp [he] at hCsize
    have hQswap : Q.parts = insert ({u} ∪ A) (P.parts \ {{u}, A}) := by
      simpa only [union_comm, pair_comm] using hQ
    have hCAadj := saturated_black_neighbor_forces_adjacency (.ofGraph G)
      hu hA hAu.symm hQswap hCP hCu hCA (hsat C hCP hCsize) hbound (black_symm _ hblack)
    exact Finset.disjoint_left.mp hcommon
      (mem_filter.mpr ⟨hCP, hCA, adjacent_symm _ hCAadj⟩)
      (mem_filter.mpr ⟨hCP, hCu, black_adjacent _ (singleton_nonempty _) (P.nonempty_of_mem_parts hCP) hblack⟩)

/-- Nonadjacent pair/singleton case. Three singleton neighbors force the
paper's pigeonhole four-cycle; with two neighbors, a black two-bag shortens
one side of the remaining quotient four-cycle. -/
lemma nonadjacent_pair_singleton_merge_impossible (G : SimpleGraph V) {d s : ℕ}
    (hd : 3 ≤ d) (hg : 8 < G.egirth) (hreg : Regular G S d)
    {P Q : Partition S} (hsmall : BagsAtMostTwo P) (near : BagsNear G P)
    {A : Finset V} {u : V} (hA : A ∈ P.parts) (hu : {u} ∈ P.parts)
    (hsize : A.card = 2) (hsat : redDegree (.ofGraph G) P A = 2 * d - 2)
    (hQ : Q.parts = insert (A ∪ {u}) (P.parts \ {A, {u}}))
    (hbound : Bounded (.ofGraph G) (2 * d - 2) s Q)
    (hnon : ¬ Adjacent (.ofGraph G) A {u}) : False := by
  classical
  have hAu : A ≠ {u} := by intro he; simp [he] at hsize
  have hsub := nonadjacent_saturated_merge_neighbor_subset (.ofGraph G) hA hu hAu hQ hnon hsat hbound
  have hcommon := pair_singleton_common_neighbors_le_two G hg P near hA hu hsize
  rw [inter_eq_right.mpr hsub] at hcommon
  have hmin := singleton_degree_at_least_two G hd hreg P hsmall hu
  have hdeg : totalDegree (.ofGraph G) P {u} = 2 := by
    change totalDegree (.ofGraph G) P {u} ≤ 2 at hcommon
    omega
  have hcount := singleton_degree_add_blackTwoBags G P hsmall u
  rw [hreg u (P.subset hu (mem_singleton_self _)), hdeg] at hcount
  obtain ⟨C, hCblack⟩ := card_pos.mp (show 0 < (blackTwoBags G P u).card by omega)
  have hCuN := blackTwoBags_subset_neighbors G P u hCblack
  obtain ⟨hC, hC2, hblack⟩ := mem_filter.mp hCblack
  obtain ⟨_, hCu, euC⟩ := mem_filter.mp hCuN
  obtain ⟨_, hCA, eAC⟩ := mem_filter.mp (hsub hCuN)
  obtain ⟨B, hBuN, hBC⟩ := exists_mem_ne (show 1 < (neighbors (Adjacent (.ofGraph G)) P {u}).card by
    change 1 < totalDegree (.ofGraph G) P {u}; omega) C
  obtain ⟨hB, hBu, euB⟩ := mem_filter.mp hBuN
  obtain ⟨_, hBA, eAB⟩ := mem_filter.mp (hsub hBuN)
  -- Blackness lets us select the same vertex of C for its two cycle edges.
  obtain ⟨a, ha, c, hc, hac | hac⟩ := eAC
  · have euc : Adjacent (.ofGraph G) {u} {c} :=
      ⟨u, mem_singleton_self _, c, mem_singleton_self _, Or.inl (hblack u (mem_singleton_self _) c hc)⟩
    have ecA : Adjacent (.ofGraph G) {c} A :=
      ⟨c, mem_singleton_self _, a, ha, Or.inl hac.symm⟩
    have h := subbag_cycle_egirth_le G P near 1 ![{u}, C, A, B]
      (by intro i; fin_cases i <;> assumption)
      (by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all)
      ![{u}, {c}, A, B]
      (by intro i; fin_cases i
          · exact Subset.rfl
          · simpa using hc
          · exact Subset.rfl
          · exact Subset.rfl)
      (by intro i; fin_cases i
          · simpa using euc
          · simpa using ecA
          · simpa using eAB
          · simpa using adjacent_symm _ euB)
    have hh : G.egirth ≤ 8 := by
      apply h.trans
      norm_num [Fin.sum_univ_succ]
      by_cases hA1 : A.card = 1 <;> by_cases hB1 : B.card = 1 <;> norm_num [hA1, hB1]
    exact not_lt_of_ge hh hg
  · exact hac

/-- The pair/singleton branch of both first-large-bag arguments. -/
lemma pair_singleton_merge_impossible (G : SimpleGraph V) {d s : ℕ}
    (hd : 3 ≤ d) (hg : 8 < G.egirth) (hreg : Regular G S d)
    {P Q : Partition S} (hsmall : BagsAtMostTwo P) (near : BagsNear G P)
    (hsat : ∀ C ∈ P.parts, C.card = 2 → redDegree (.ofGraph G) P C = 2 * d - 2)
    {A : Finset V} {u : V} (hA : A ∈ P.parts) (hu : {u} ∈ P.parts)
    (hsize : A.card = 2)
    (hQ : Q.parts = insert (A ∪ {u}) (P.parts \ {A, {u}}))
    (hbound : Bounded (.ofGraph G) (2 * d - 2) s Q) : False := by
  by_cases hadj : Adjacent (.ofGraph G) A {u}
  · exact adjacent_pair_singleton_merge_impossible G hd hg hreg hsmall near hsat hA hu hsize hQ hbound hadj
  · exact nonadjacent_pair_singleton_merge_impossible G hd hg hreg hsmall near hA hu hsize
      (hsat A hA hsize) hQ hbound hadj

end Paper
