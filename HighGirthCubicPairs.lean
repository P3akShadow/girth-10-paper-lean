import HighGirthVertexBags

/-! The two-pair branch of Lemma 4, including its two distance cases. -/
namespace Paper
open Finset SimpleGraph CycleLift
variable {V : Type*} [DecidableEq V] {S : Finset V}
attribute [local instance] Classical.propDecidable

lemma adjacent_pair_pair_cubic_impossible (G : SimpleGraph V) (hg : 9 < G.egirth)
    {P Q : Partition S} (near : BagsNear G P) {A B : Finset V} {s : ℕ}
    (hA : A ∈ P.parts) (hB : B ∈ P.parts) (hAB : A ≠ B)
    (hsatA : redDegree (.ofGraph G) P A = 4) (hsatB : redDegree (.ofGraph G) P B = 4)
    (hQ : Q.parts = insert (A ∪ B) (P.parts \ {A, B}))
    (hbound : Bounded (.ofGraph G) 4 s Q) (hadj : Adjacent (.ofGraph G) A B) : False := by
  have hcommon : Disjoint (neighbors (Adjacent (.ofGraph G)) P A)
      (neighbors (Adjacent (.ofGraph G)) P B) := by
    apply Finset.disjoint_left.mpr
    intro C hCA hCB
    obtain ⟨hC, hCA, eAC⟩ := mem_filter.mp hCA
    obtain ⟨_, hCB, eBC⟩ := mem_filter.mp hCB
    exact high_girth_no_quotient_triangle G hg P near hA hB hC hAB hCA.symm hCB.symm
      hadj eBC (adjacent_symm _ eAC)
  have hformula := adjacent_no_common_merge_redDegree (.ofGraph G) hA hB hAB hQ hadj hcommon
  have hrA := redDegree_le_totalDegree (.ofGraph G) P A
  have hrB := redDegree_le_totalDegree (.ofGraph G) P B
  have hred := (hbound (A ∪ B) (by simp [hQ])).1
  omega

lemma nonadjacent_pair_pair_cubic_impossible (G : SimpleGraph V) (hg : 9 < G.egirth)
    (hreg : Regular G S 3) (hclosed : ∀ u ∈ S, ∀ v, G.Adj u v → v ∈ S)
    {P Q : Partition S} (near : BagsNear G P) {A B : Finset V} {s : ℕ}
    (hA : A ∈ P.parts) (hB : B ∈ P.parts) (hAB : A ≠ B)
    (hsizeA : A.card = 2) (hsizeB : B.card = 2)
    (hsatA : redDegree (.ofGraph G) P A = 4) (hsatB : redDegree (.ofGraph G) P B = 4)
    (hQ : Q.parts = insert (A ∪ B) (P.parts \ {A, B}))
    (hbound : Bounded (.ofGraph G) 4 s Q) (hnon : ¬ Adjacent (.ofGraph G) A B) : False := by
  classical
  have hQswap : Q.parts = insert (B ∪ A) (P.parts \ {B, A}) := by
    simpa only [union_comm, pair_comm] using hQ
  have hN : neighbors (Adjacent (.ofGraph G)) P A = neighbors (Adjacent (.ofGraph G)) P B :=
    Subset.antisymm
      (nonadjacent_saturated_merge_neighbor_subset (.ofGraph G) hB hA hAB.symm hQswap
        (fun hh => hnon (adjacent_symm _ hh)) hsatB hbound)
      (nonadjacent_saturated_merge_neighbor_subset (.ofGraph G) hA hB hAB hQ hnon hsatA hbound)
  have hExt : ∀ u ∈ A, 2 ≤ (externalBags G P A u).card := by
    intro u hu
    exact externalBags_card_lower_of_mem G (by omega) hreg hclosed P near hA hsizeA hsatA hu
  obtain ⟨x, y, hxy, hBxy⟩ := card_eq_two.mp hsizeB
  have hx : x ∈ B := by simp [hBxy]
  have hy : y ∈ B := by simp [hBxy]
  by_cases hxyadj : G.Adj x y
  · -- Distance one inside B saves one unit in the lifted four-cycle.
    obtain ⟨u, hu⟩ := P.nonempty_of_mem_parts hA
    obtain ⟨C, hCu, D, hDu, hCD⟩ := one_lt_card.mp (show 1 < (externalBags G P A u).card by
      have := hExt u hu; omega)
    have hCBn : C ∈ neighbors (Adjacent (.ofGraph G)) P B := hN ▸ externalBags_subset_neighbors G P hu hCu
    have hDBn : D ∈ neighbors (Adjacent (.ofGraph G)) P B := hN ▸ externalBags_subset_neighbors G P hu hDu
    obtain ⟨hC, hCA, euC⟩ := mem_filter.mp hCu
    obtain ⟨hD, hDA, euD⟩ := mem_filter.mp hDu
    obtain ⟨_, hCB, eBC⟩ := mem_filter.mp hCBn
    obtain ⟨_, hDB, eBD⟩ := mem_filter.mp hDBn
    have h := subbag_cycle_egirth_cost G P 1 ![A, C, B, D]
      (by intro i; fin_cases i <;> assumption)
      (by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all)
      ![{u}, C, B, D]
      (by intro i; fin_cases i
          · simpa using hu
          · exact Subset.rfl
          · exact Subset.rfl
          · exact Subset.rfl)
      (by intro i; fin_cases i
          · simpa using euC
          · simpa using adjacent_symm _ eBC
          · simpa using eBD
          · simpa using adjacent_symm _ euD)
      ![0, 2, 1, 2] (by intro i; fin_cases i <;> norm_num)
      (by
        intro i a ha b hb
        fin_cases i
        · change a ∈ ({u} : Finset V) at ha
          change b ∈ ({u} : Finset V) at hb
          simp only [mem_singleton] at ha hb
          subst a; subst b; simp
        · exact Paper.Near.edist_le_two (near C hC a ha b hb)
        · change a ∈ B at ha
          change b ∈ B at hb
          rw [hBxy] at ha hb
          simp only [mem_insert, mem_singleton] at ha hb
          rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
          · simp
          · exact edist_le_one_iff_adj_or_eq.mpr (Or.inl hxyadj)
          · exact edist_le_one_iff_adj_or_eq.mpr (Or.inl hxyadj.symm)
          · simp
        · exact Paper.Near.edist_le_two (near D hD a ha b hb))
    have hh : G.egirth ≤ 9 := by simpa [Fin.sum_univ_succ] using h
    exact not_lt_of_ge hh hg
  · -- At distance two, the common neighbor z supplies the same endpoint
    -- of B on both sides, so splitting B gives a cycle of length at most 8.
    obtain ⟨z, hxz, hzy⟩ := ((near B hB x hx y hy).resolve_left hxy).resolve_left hxyadj
    have hzS := hclosed x (P.subset hB hx) z hxz
    obtain ⟨Z, hZ, hzZ⟩ := P.exists_mem hzS
    have hzB : z ∉ B := by
      rw [hBxy]
      simp only [mem_insert, mem_singleton, not_or]
      exact ⟨hxz.ne.symm, hzy.ne⟩
    have hZB : Z ≠ B := fun he => hzB (he ▸ hzZ)
    have eBZ : Adjacent (.ofGraph G) B Z := ⟨x, hx, z, hzZ, Or.inl hxz⟩
    have hZNA : Z ∈ neighbors (Adjacent (.ofGraph G)) P A := hN.symm ▸ mem_filter.mpr ⟨hZ, hZB, eBZ⟩
    obtain ⟨_, hZA, u, hu, z', hz', huz' | huz'⟩ := mem_filter.mp hZNA
    · have euZ : Adjacent (.ofGraph G) {u} Z := ⟨u, mem_singleton_self _, z', hz', Or.inl huz'⟩
      have hZu : Z ∈ externalBags G P A u := mem_filter.mpr ⟨hZ, hZA, euZ⟩
      obtain ⟨D, hDu, hDZ⟩ := exists_mem_ne (show 1 < (externalBags G P A u).card by
        have := hExt u hu; omega) Z
      have hDNB : D ∈ neighbors (Adjacent (.ofGraph G)) P B := hN ▸ externalBags_subset_neighbors G P hu hDu
      obtain ⟨hD, hDA, euD⟩ := mem_filter.mp hDu
      obtain ⟨_, hDB, b, hb, d, hd, hbd | hbd⟩ := mem_filter.mp hDNB
      · have hzb : G.Adj z b := by
          rw [hBxy] at hb
          simp only [mem_insert, mem_singleton] at hb
          rcases hb with rfl | rfl
          · exact hxz.symm
          · exact hzy
        have eZb : Adjacent (.ofGraph G) Z {b} := ⟨z, hzZ, b, mem_singleton_self _, Or.inl hzb⟩
        have ebD : Adjacent (.ofGraph G) {b} D := ⟨b, mem_singleton_self _, d, hd, Or.inl hbd⟩
        have h := subbag_cycle_egirth_le G P near 1 ![A, Z, B, D]
          (by intro i; fin_cases i <;> assumption)
          (by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all)
          ![{u}, Z, {b}, D]
          (by intro i; fin_cases i
              · simpa using hu
              · exact Subset.rfl
              · simpa using hb
              · exact Subset.rfl)
          (by intro i; fin_cases i
              · simpa using euZ
              · simpa using eZb
              · simpa using ebD
              · simpa using adjacent_symm _ euD)
        have hh : G.egirth ≤ 8 := by
          apply h.trans
          norm_num [Fin.sum_univ_succ]
          by_cases hZ1 : Z.card = 1 <;> by_cases hD1 : D.card = 1 <;> norm_num [hZ1, hD1]
        exact not_lt_of_ge (hh.trans (by norm_num)) hg
      · exact hbd
    · exact huz'

lemma pair_pair_cubic_merge_impossible (G : SimpleGraph V) (hg : 9 < G.egirth)
    (hreg : Regular G S 3) (hclosed : ∀ u ∈ S, ∀ v, G.Adj u v → v ∈ S)
    {P Q : Partition S} (near : BagsNear G P) {A B : Finset V} {s : ℕ}
    (hA : A ∈ P.parts) (hB : B ∈ P.parts) (hAB : A ≠ B)
    (hsizeA : A.card = 2) (hsizeB : B.card = 2)
    (hsatA : redDegree (.ofGraph G) P A = 4) (hsatB : redDegree (.ofGraph G) P B = 4)
    (hQ : Q.parts = insert (A ∪ B) (P.parts \ {A, B}))
    (hbound : Bounded (.ofGraph G) 4 s Q) : False := by
  by_cases hadj : Adjacent (.ofGraph G) A B
  · exact adjacent_pair_pair_cubic_impossible G hg near hA hB hAB hsatA hsatB hQ hbound hadj
  · exact nonadjacent_pair_pair_cubic_impossible G hg hreg hclosed near hA hB hAB
      hsizeA hsizeB hsatA hsatB hQ hbound hadj

end Paper
