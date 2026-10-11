import HighGirthLargeBags
import HighGirthVertexBags

/-! The two-pair cases of Theorem 5. -/
namespace Paper
open Finset SimpleGraph CycleLift
variable {V : Type*} [DecidableEq V] {S : Finset V}

/-- Theorem 5's four endpoint-pairs: five common bags would give two bags
meeting the same original-vertex pair, hence a lifted cycle of length <= 8. -/
lemma two_pairs_common_neighbors_le_four (G : SimpleGraph V) (hg : 8 < G.egirth)
    (P : Partition S) (near : BagsNear G P) {A B : Finset V}
    (hA : A ∈ P.parts) (hB : B ∈ P.parts) (hAB : A ≠ B)
    (hA2 : A.card = 2) (hB2 : B.card = 2) :
    (neighbors (Adjacent (.ofGraph G)) P A ∩
      neighbors (Adjacent (.ofGraph G)) P B).card ≤ 4 := by
  classical
  obtain ⟨u, v, huv, rfl⟩ := card_eq_two.mp hA2
  obtain ⟨x, y, hxy, rfl⟩ := card_eq_two.mp hB2
  let C := fun a b => P.parts.filter fun X => X ≠ {u, v} ∧ X ≠ {x, y} ∧
    Adjacent (.ofGraph G) {a} X ∧ Adjacent (.ofGraph G) {b} X
  have hsub : neighbors (Adjacent (.ofGraph G)) P {u, v} ∩
      neighbors (Adjacent (.ofGraph G)) P {x, y} ⊆
      (C u x ∪ C u y) ∪ (C v x ∪ C v y) := by
    intro X hX
    obtain ⟨hXA, hXB⟩ := mem_inter.mp hX
    obtain ⟨hXP, hXA, a, ha, a', ha', haa'⟩ := mem_filter.mp hXA
    obtain ⟨_, hXB, b, hb, b', hb', hbb'⟩ := mem_filter.mp hXB
    simp only [mem_insert, mem_singleton] at ha hb
    have haX : Adjacent (.ofGraph G) {a} X := ⟨a, mem_singleton_self _, a', ha', haa'⟩
    have hbX : Adjacent (.ofGraph G) {b} X := ⟨b, mem_singleton_self _, b', hb', hbb'⟩
    have habX : X ∈ C a b := mem_filter.mpr ⟨hXP, hXA, hXB, haX, hbX⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact mem_union_left _ (mem_union_left _ habX)
    · exact mem_union_left _ (mem_union_right _ habX)
    · exact mem_union_right _ (mem_union_left _ habX)
    · exact mem_union_right _ (mem_union_right _ habX)
  have hux : (C u x).card ≤ 1 := vertex_common_neighbors_card_le_one G hg P near
    (u := u) (v := x) hA hB hAB (by simp) (by simp)
  have huy : (C u y).card ≤ 1 := vertex_common_neighbors_card_le_one G hg P near
    (u := u) (v := y) hA hB hAB (by simp) (by simp)
  have hvx : (C v x).card ≤ 1 := vertex_common_neighbors_card_le_one G hg P near
    (u := v) (v := x) hA hB hAB (by simp) (by simp)
  have hvy : (C v y).card ≤ 1 := vertex_common_neighbors_card_le_one G hg P near
    (u := v) (v := y) hA hB hAB (by simp) (by simp)
  have houter := (card_le_card hsub).trans (card_union_le ..)
  have hleft := card_union_le (C u x) (C u y)
  have hright := card_union_le (C v x) (C v y)
  omega

/-- Theorem 5, nonadjacent two-bags: their common neighborhood has at least
2d-2 >= 6 bags, contradicting the four endpoint-pair bound. -/
lemma nonadjacent_two_pairs_general_impossible (G : SimpleGraph V) {d s : ℕ}
    (hd : 3 < d) (hg : 8 < G.egirth) {P Q : Partition S}
    (near : BagsNear G P)
    {A B : Finset V} (hA : A ∈ P.parts) (hB : B ∈ P.parts) (hAB : A ≠ B)
    (hA2 : A.card = 2) (hB2 : B.card = 2)
    (hsatA : redDegree (.ofGraph G) P A = 2 * d - 2)
    (hsatB : redDegree (.ofGraph G) P B = 2 * d - 2)
    (hQ : Q.parts = insert (A ∪ B) (P.parts \ {A, B}))
    (hbound : Bounded (.ofGraph G) (2 * d - 2) s Q)
    (hnon : ¬ Adjacent (.ofGraph G) A B) : False := by
  have hsub := nonadjacent_saturated_merge_neighbor_subset (.ofGraph G)
    hA hB hAB hQ hnon hsatA hbound
  have heq : neighbors (Adjacent (.ofGraph G)) P A ∩
      neighbors (Adjacent (.ofGraph G)) P B = neighbors (Adjacent (.ofGraph G)) P B :=
    inter_eq_right.mpr hsub
  have hc := two_pairs_common_neighbors_le_four G hg P near hA hB hAB hA2 hB2
  rw [heq] at hc
  have ht := redDegree_le_totalDegree (.ofGraph G) P B
  rw [hsatB] at ht
  change totalDegree (.ofGraph G) P B ≤ 4 at hc
  omega

/-- If an endpoint u meets the other merged bag B, it cannot also meet a
common neighbor of A and B: splitting A produces the paper's short triangle. -/
lemma crossing_vertex_no_common (G : SimpleGraph V) (hg : 8 < G.egirth)
    (P : Partition S) (near : BagsNear G P) {A B C : Finset V} {u : V}
    (hA : A ∈ P.parts) (hB : B ∈ P.parts) (hC : C ∈ P.parts)
    (hAB : A ≠ B) (hCA : C ≠ A) (hCB : C ≠ B) (hu : u ∈ A)
    (euB : Adjacent (.ofGraph G) {u} B) (euC : Adjacent (.ofGraph G) {u} C)
    (eBC : Adjacent (.ofGraph G) B C) : False := by
  have h := subbag_cycle_egirth_le G P near 0 ![A, B, C]
    (by intro i; fin_cases i <;> assumption)
    (by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all)
    ![{u}, B, C]
    (by intro i; fin_cases i
        · simpa using hu
        · exact Subset.rfl
        · exact Subset.rfl)
    (by intro i; fin_cases i
        · simpa using euB
        · simpa using eBC
        · simpa using adjacent_symm _ euC)
  have hle : G.egirth ≤ 8 := by
    apply h.trans
    norm_num [Fin.sum_univ_succ]
    by_cases hB1 : B.card = 1 <;> by_cases hC1 : C.card = 1 <;> norm_num [hB1, hC1]
  exact not_lt_of_ge hle hg

/-- The adjacent case's explicit degree count: u can meet B and only one
further external bag. All the other red neighbors of B survive the merge. -/
lemma crossing_vertex_externalBags_le_two (G : SimpleGraph V) {w s : ℕ}
    (hg : 8 < G.egirth) {P Q : Partition S} (near : BagsNear G P)
    {A B : Finset V} {u : V} (hA : A ∈ P.parts) (hB : B ∈ P.parts) (hAB : A ≠ B)
    (hu : u ∈ A) (euB : Adjacent (.ofGraph G) {u} B)
    (hredBA : Red (.ofGraph G) B A) (hsatB : redDegree (.ofGraph G) P B = w)
    (hQ : Q.parts = insert (A ∪ B) (P.parts \ {A, B}))
    (hbound : Bounded (.ofGraph G) w s Q) :
    (externalBags G P A u).card ≤ 2 := by
  classical
  let D := (externalBags G P A u).erase B
  let R := (neighbors (Red (.ofGraph G)) P B).erase A
  have huQ : A ∪ B ∈ Q.parts := by simp [hQ]
  have hBn : B ∈ externalBags G P A u := mem_filter.mpr ⟨hB, hAB.symm, euB⟩
  have hAr : A ∈ neighbors (Red (.ofGraph G)) P B := mem_filter.mpr ⟨hA, hAB, hredBA⟩
  have hDc : D.card + 1 = (externalBags G P A u).card := card_erase_add_one hBn
  have hRc : R.card + 1 = w := by simpa [R, redDegree, ← hsatB] using card_erase_add_one hAr
  have hDnot : ∀ C ∈ D, ¬ Adjacent (.ofGraph G) B C := by
    intro C hCD
    obtain ⟨hCB, hCE⟩ := mem_erase.mp hCD
    obtain ⟨hCP, hCA, euC⟩ := mem_filter.mp hCE
    exact crossing_vertex_no_common G hg P near hA hB hCP hAB hCA hCB hu euB euC
  have hsub : D ∪ R ⊆ neighbors (Red (.ofGraph G)) Q (A ∪ B) := by
    intro C hC
    rcases mem_union.mp hC with hCD | hCR
    · obtain ⟨hCB, hCE⟩ := mem_erase.mp hCD
      obtain ⟨hCP, hCA, x, hx, y, hy, hxy⟩ := mem_filter.mp hCE
      have hxu : x = u := mem_singleton.mp hx
      subst x
      have eAC : Adjacent (.ofGraph G) A C := ⟨u, hu, y, hy, hxy⟩
      refine mem_filter.mpr ⟨by simp [hQ, hCP, hCA, hCB], ?_, ?_⟩
      · intro he
        exact union_not_part P hA hB hAB (he ▸ hCP)
      · refine ⟨(adjacent_union_left _ A B C).mpr (Or.inl eAC), ?_⟩
        intro hb
        exact hDnot C hCD (black_adjacent _ (P.nonempty_of_mem_parts hB)
          (P.nonempty_of_mem_parts hCP) ((black_union_left _ A B C).mp hb).2)
    · obtain ⟨hCA, hCr⟩ := mem_erase.mp hCR
      obtain ⟨hCP, hCB, hred⟩ := mem_filter.mp hCr
      refine mem_filter.mpr ⟨by simp [hQ, hCP, hCA, hCB], ?_, ?_⟩
      · intro he
        exact union_not_part P hA hB hAB (he ▸ hCP)
      · exact ⟨(adjacent_union_left _ A B C).mpr (Or.inr hred.1),
          fun hb => hred.2 ((black_union_left _ A B C).mp hb).2⟩
  have hdis : Disjoint D R := by
    apply Finset.disjoint_left.mpr
    intro C hCD hCR
    exact hDnot C hCD (mem_filter.mp (mem_erase.mp hCR).2).2.2.1
  have hc := card_le_card hsub
  rw [card_union_of_disjoint hdis] at hc
  have hb := (hbound _ huQ).1
  change D.card + R.card ≤ redDegree (.ofGraph G) Q (A ∪ B) at hc
  omega

/-- Theorem 5, adjacent two-bags. This expands the paper's count of the
three possible neighbors: the partner inside A, a neighbor in B, and at
most one further external bag. The endpoint must meet at least d-1 bags. -/
lemma adjacent_two_pairs_general_impossible (G : SimpleGraph V) {d s : ℕ}
    (hd : 3 < d) (hg : 8 < G.egirth) (hreg : Regular G S d)
    (hclosed : ∀ u ∈ S, ∀ v, G.Adj u v → v ∈ S)
    {P Q : Partition S} (near : BagsNear G P)
    {A B : Finset V} (hA : A ∈ P.parts) (hB : B ∈ P.parts) (hAB : A ≠ B)
    (hA2 : A.card = 2) (hB2 : B.card = 2)
    (hsatA : redDegree (.ofGraph G) P A = 2 * d - 2)
    (hsatB : redDegree (.ofGraph G) P B = 2 * d - 2)
    (hQ : Q.parts = insert (A ∪ B) (P.parts \ {A, B}))
    (hbound : Bounded (.ofGraph G) (2 * d - 2) s Q)
    (hadj : Adjacent (.ofGraph G) A B) : False := by
  classical
  have hblack : ¬ Black (.ofGraph G) A B := by
    intro hb
    have hB1 := high_girth_black_pair_singleton G
      (lt_trans (by norm_num : (4 : ℕ∞) < 8) hg) P hA hB hA2 hb
    omega
  have hredBA : Red (.ofGraph G) B A :=
    ⟨adjacent_symm _ hadj, fun hb => hblack (black_symm _ hb)⟩
  obtain ⟨u, hu, x, hx, hux⟩ := hadj
  have euB : Adjacent (.ofGraph G) {u} B := ⟨u, mem_singleton_self _, x, hx, hux⟩
  have hupper := crossing_vertex_externalBags_le_two G hg near hA hB hAB hu euB hredBA hsatB hQ hbound
  obtain ⟨a, b, hab, hAeq⟩ := card_eq_two.mp hA2
  have huAB : u = a ∨ u = b := by simpa [hAeq] using hu
  have hlower : d - 1 ≤ (externalBags G P A u).card := by
    rcases huAB with hua | hub
    · subst u
      have hpair : {a, b} ∈ P.parts := hAeq ▸ hA
      have hnear : Near G a b := near A hA a (by simp [hAeq]) b (by simp [hAeq])
      simpa only [hAeq] using externalBags_pair_card_lower G (by omega) hreg hclosed P hpair hab hnear (hAeq ▸ hsatA)
    · subst u
      have hpair : {b, a} ∈ P.parts := by simpa only [pair_comm b a, ← hAeq] using hA
      have hnear : Near G b a := near A hA b (by simp [hAeq]) a (by simp [hAeq])
      have heq : A = {b, a} := by simpa only [pair_comm b a] using hAeq
      simpa only [heq] using externalBags_pair_card_lower G (by omega) hreg hclosed P hpair hab.symm hnear (heq ▸ hsatA)
  omega

lemma two_pairs_general_impossible (G : SimpleGraph V) {d s : ℕ}
    (hd : 3 < d) (hg : 8 < G.egirth) (hreg : Regular G S d)
    (hclosed : ∀ u ∈ S, ∀ v, G.Adj u v → v ∈ S)
    {P Q : Partition S} (near : BagsNear G P)
    {A B : Finset V} (hA : A ∈ P.parts) (hB : B ∈ P.parts) (hAB : A ≠ B)
    (hA2 : A.card = 2) (hB2 : B.card = 2)
    (hsatA : redDegree (.ofGraph G) P A = 2 * d - 2)
    (hsatB : redDegree (.ofGraph G) P B = 2 * d - 2)
    (hQ : Q.parts = insert (A ∪ B) (P.parts \ {A, B}))
    (hbound : Bounded (.ofGraph G) (2 * d - 2) s Q) : False := by
  by_cases hadj : Adjacent (.ofGraph G) A B
  · exact adjacent_two_pairs_general_impossible G hd hg hreg hclosed near hA hB hAB hA2 hB2 hsatA hsatB hQ hbound hadj
  · exact nonadjacent_two_pairs_general_impossible G hd hg near hA hB hAB hA2 hB2 hsatA hsatB hQ hbound hadj

end Paper
