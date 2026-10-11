import HighGirthGeometry

/-! The six singleton-merge cases of Lemma 3, in the paper's order. -/
namespace Paper
open Finset CycleLift
variable {V : Type*} [DecidableEq V] {S : Finset V}

def TwoBagSaturated (G : SimpleGraph V) (d : ℕ) (P : Partition S) : Prop :=
  ∀ A ∈ P.parts, A.card = 2 → redDegree (.ofGraph G) P A = 2 * d - 2

lemma adjacent_singletons_no_common (G : SimpleGraph V) (hg : 8 < G.egirth)
    (P : Partition S) (near : BagsNear G P) {u v : V}
    (hu : {u} ∈ P.parts) (hv : {v} ∈ P.parts) (huv : u ≠ v)
    (euv : Adjacent (.ofGraph G) {u} {v}) :
    Disjoint (neighbors (Adjacent (.ofGraph G)) P {u})
      (neighbors (Adjacent (.ofGraph G)) P {v}) := by
  classical
  apply disjoint_left.mpr
  intro A hAu hAv
  obtain ⟨hA, hAu, euA⟩ := mem_filter.mp hAu
  obtain ⟨_, hAv, evA⟩ := mem_filter.mp hAv
  exact high_girth_no_singleton_triangle G hg P near hu hv hA
    (by simpa using huv) hAu.symm hAv.symm euv evA (adjacent_symm _ euA)

lemma singleton_common_card_one (G : SimpleGraph V) (hg : 8 < G.egirth)
    (P : Partition S) (near : BagsNear G P) {u v : V}
    (hu : {u} ∈ P.parts) (hv : {v} ∈ P.parts) (huv : u ≠ v)
    {A : Finset V} (hAu : A ∈ neighbors (Adjacent (.ofGraph G)) P {u})
    (hAv : A ∈ neighbors (Adjacent (.ofGraph G)) P {v}) :
    (neighbors (Adjacent (.ofGraph G)) P {u} ∩
      neighbors (Adjacent (.ofGraph G)) P {v}).card = 1 := by
  apply Nat.le_antisymm (singleton_common_neighbors_card_le_one G hg P near hu hv huv)
  exact one_le_card.mpr ⟨A, mem_inter.mpr ⟨hAu, hAv⟩⟩

lemma common_bag_black_new_zero (G : SimpleGraph V) (hg : 8 < G.egirth)
    {P Q : Partition S} (near : BagsNear G P) {u v : V}
    (hu : {u} ∈ P.parts) (hv : {v} ∈ P.parts) (huv : u ≠ v)
    (hQ : Q.parts = insert ({u} ∪ {v}) (P.parts \ {{u}, {v}}))
    {A : Finset V} (hAu : A ∈ neighbors (Adjacent (.ofGraph G)) P {u})
    (hAv : A ∈ neighbors (Adjacent (.ofGraph G)) P {v})
    (hnblack : ¬ Black (.ofGraph G) {v} A) :
    blackDegree (.ofGraph G) Q ({u} ∪ {v}) = 0 := by
  classical
  apply merged_blackDegree_zero _ hQ
  rintro B hB hBu hBv ⟨hub, hvb⟩
  have he : B = A := singleton_common_bag_unique G hg P near hu hv huv
    (mem_filter.mpr ⟨hB, hBu, black_adjacent _ (singleton_nonempty _) (P.nonempty_of_mem_parts hB) hub⟩)
    (mem_filter.mpr ⟨hB, hBv, black_adjacent _ (singleton_nonempty _) (P.nonempty_of_mem_parts hB) hvb⟩)
    hAu hAv
  exact hnblack (he ▸ hvb)

/-- Cases 1, 2 and 3: both singletons have their original degree. -/
lemma full_singletons_step (G : SimpleGraph V) {d s : ℕ} (hd : 3 ≤ d)
    (hg : 8 < G.egirth) (hreg : Regular G S d) {P Q : Partition S}
    (small : BagsAtMostTwo P) (near : BagsNear G P)
    {u v : V} (hu : {u} ∈ P.parts) (hv : {v} ∈ P.parts) (huv : u ≠ v)
    (hQ : Q.parts = insert ({u} ∪ {v}) (P.parts \ {{u}, {v}}))
    (bounded : Bounded (.ofGraph G) (2 * d - 2) s Q)
    (hdu : totalDegree (.ofGraph G) P {u} = d)
    (hdv : totalDegree (.ofGraph G) P {v} = d) :
    Near G u v ∧ redDegree (.ofGraph G) Q ({u} ∪ {v}) = 2 * d - 2 ∧
      ∀ C ∈ P.parts, C.card = 2 → ¬ (Red (.ofGraph G) C {u} ∧ Red (.ofGraph G) C {v}) := by
  classical
  have huvB : ({u} : Finset V) ≠ {v} := by simpa using huv
  have hU : {u} ∪ {v} ∈ Q.parts := by simp [hQ]
  by_cases hadj : Adjacent (.ofGraph G) {u} {v}
  · -- Case 1: adjacent full-degree singletons; no common neighbor.
    have hdis := adjacent_singletons_no_common G hg P near hu hv huv hadj
    have he := adjacent_no_common_merge_redDegree _ hu hv huvB hQ hadj hdis
    rw [hdu, hdv] at he
    refine ⟨Or.inr (Or.inl ((singleton_adjacent_graph G u v).mp hadj)), by omega, ?_⟩
    intro C hC hC2 hred
    exact disjoint_left.mp hdis
      (mem_filter.mpr ⟨hC, (singleton_ne_pair hC2).symm, adjacent_symm _ hred.1.1⟩)
      (mem_filter.mpr ⟨hC, (singleton_ne_pair hC2).symm, adjacent_symm _ hred.2.1⟩)
  by_cases hcommon : (neighbors (Adjacent (.ofGraph G)) P {u} ∩
      neighbors (Adjacent (.ofGraph G)) P {v}).Nonempty
  · -- Case 2: the unique common neighbor must be a singleton.
    obtain ⟨A, hAcommon⟩ := hcommon
    obtain ⟨hAu, hAv⟩ := mem_inter.mp hAcommon
    obtain ⟨hA, hAneU, euA⟩ := mem_filter.mp hAu
    obtain ⟨_, hAneV, evA⟩ := mem_filter.mp hAv
    have hcard := singleton_common_card_one G hg P near hu hv huv hAu hAv
    have ht := nonadjacent_merge_totalDegree_add_common _ hu hv huvB hQ hadj
    rw [hcard, hdu, hdv] at ht
    have hAsmall := small A hA
    have hApos := one_le_card.mpr (P.nonempty_of_mem_parts hA)
    have hA1 : A.card = 1 := by
      by_contra hn1
      have hA2 : A.card = 2 := by omega
      have hb := common_bag_black_new_zero G hg near hu hv huv hQ hAu hAv
        (full_degree_singleton_no_black_two_bag G hreg P small hv hdv hA hA2)
      have hr := totalDegree_eq_red_add_black (.ofGraph G) Q hU
      have hbound := (bounded _ hU).1
      rw [hb] at hr
      omega
    obtain ⟨a, hAeq⟩ := card_eq_one.mp hA1
    have hua : G.Adj u a := (singleton_adjacent_graph G u a).mp (hAeq ▸ euA)
    have hva : G.Adj v a := (singleton_adjacent_graph G v a).mp (hAeq ▸ evA)
    have hblack_le := high_girth_pair_blackDegree_le_one G
      (lt_trans (by norm_num : (4 : ℕ∞) < 8) hg) Q
      (show (({u} : Finset V) ∪ {v}).card = 2 by simp [huv])
    have hr := totalDegree_eq_red_add_black (.ofGraph G) Q hU
    have hbound := (bounded _ hU).1
    refine ⟨Or.inr (Or.inr ⟨a, hua, hva.symm⟩), by omega, ?_⟩
    intro C hC hC2 hred
    have he : C = A := singleton_common_bag_unique G hg P near hu hv huv
      (mem_filter.mpr ⟨hC, (singleton_ne_pair hC2).symm, adjacent_symm _ hred.1.1⟩)
      (mem_filter.mpr ⟨hC, (singleton_ne_pair hC2).symm, adjacent_symm _ hred.2.1⟩) hAu hAv
    rw [he, hA1] at hC2
    omega
  · -- Case 3: no common neighbor would produce red degree 2d.
    have hdis : Disjoint (neighbors (Adjacent (.ofGraph G)) P {u})
        (neighbors (Adjacent (.ofGraph G)) P {v}) :=
      disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hcommon)
    have he := nonadjacent_no_common_merge_redDegree _ hu hv huvB hQ hadj hdis
    have hb := (bounded _ hU).1
    rw [hdu, hdv] at he
    omega

lemma black_pair_forces_common (G : SimpleGraph V) {d s : ℕ}
    {P Q : Partition S} (sat : TwoBagSaturated G d P)
    {u v : V} (hu : {u} ∈ P.parts) (hv : {v} ∈ P.parts) (huv : u ≠ v)
    (hQ : Q.parts = insert ({u} ∪ {v}) (P.parts \ {{u}, {v}}))
    (bounded : Bounded (.ofGraph G) (2 * d - 2) s Q)
    {A : Finset V} (hA : A ∈ P.parts) (hA2 : A.card = 2)
    (huA : Black (.ofGraph G) {u} A) :
    A ∈ neighbors (Adjacent (.ofGraph G)) P {u} ∩
      neighbors (Adjacent (.ofGraph G)) P {v} := by
  classical
  have hAu : A ≠ {u} := (singleton_ne_pair hA2).symm
  have hAv : A ≠ {v} := (singleton_ne_pair hA2).symm
  have hev := saturated_black_neighbor_forces_adjacency (.ofGraph G) hu hv
    (by simpa using huv) hQ hA hAu hAv (sat A hA hA2) bounded (black_symm _ huA)
  exact mem_inter.mpr ⟨mem_filter.mpr ⟨hA, hAu,
    black_adjacent _ (singleton_nonempty _) (P.nonempty_of_mem_parts hA) huA⟩,
    mem_filter.mpr ⟨hA, hAv, adjacent_symm _ hev⟩⟩

/-- Case 4: a degree-(d-1) singleton and a degree-d singleton. -/
lemma one_deficit_singletons_step (G : SimpleGraph V) {d s : ℕ} (hd : 3 ≤ d)
    (hg : 8 < G.egirth) (hreg : Regular G S d) {P Q : Partition S}
    (small : BagsAtMostTwo P) (near : BagsNear G P) (sat : TwoBagSaturated G d P)
    {u v : V} (hu : {u} ∈ P.parts) (hv : {v} ∈ P.parts) (huv : u ≠ v)
    (hQ : Q.parts = insert ({u} ∪ {v}) (P.parts \ {{u}, {v}}))
    (bounded : Bounded (.ofGraph G) (2 * d - 2) s Q)
    (hdu : totalDegree (.ofGraph G) P {u} + 1 = d)
    (hdv : totalDegree (.ofGraph G) P {v} = d) :
    Near G u v ∧ redDegree (.ofGraph G) Q ({u} ∪ {v}) = 2 * d - 2 ∧
      ∀ C ∈ P.parts, C.card = 2 → ¬ (Red (.ofGraph G) C {u} ∧ Red (.ofGraph G) C {v}) := by
  classical
  obtain ⟨A, hA, hA2, hblack⟩ := singleton_has_blackTwoBag_of_degree_lt G hreg P small hu (by omega)
  have hcommon := black_pair_forces_common G sat hu hv huv hQ bounded hA hA2 hblack
  obtain ⟨hAu, hAv⟩ := mem_inter.mp hcommon
  have hadj : ¬ Adjacent (.ofGraph G) {u} {v} := by
    intro he
    exact disjoint_left.mp (adjacent_singletons_no_common G hg P near hu hv huv he) hAu hAv
  have hcard := singleton_common_card_one G hg P near hu hv huv hAu hAv
  have hb := common_bag_black_new_zero G hg near hu hv huv hQ hAu hAv
    (full_degree_singleton_no_black_two_bag G hreg P small hv hdv hA hA2)
  have ht := nonadjacent_merge_totalDegree_add_common (.ofGraph G) hu hv
    (by simpa using huv) hQ hadj
  rw [hcard, hdv] at ht
  have hU : {u} ∪ {v} ∈ Q.parts := by simp [hQ]
  have hr := totalDegree_eq_red_add_black (.ofGraph G) Q hU
  rw [hb] at hr
  have hvA := (mem_filter.mp hAv).2.2
  obtain ⟨x, hx, a, ha, hxa⟩ := hvA
  have hxv : x = v := mem_singleton.mp hx
  subst x
  have hva : G.Adj v a := hxa.elim id (fun h => False.elim h)
  refine ⟨Or.inr (Or.inr ⟨a, hblack u (mem_singleton_self _) a ha, hva.symm⟩), by omega, ?_⟩
  intro C hC hC2 hred
  have he : C = A := singleton_common_bag_unique G hg P near hu hv huv
    (mem_filter.mpr ⟨hC, (singleton_ne_pair hC2).symm, adjacent_symm _ hred.1.1⟩)
    (mem_filter.mpr ⟨hC, (singleton_ne_pair hC2).symm, adjacent_symm _ hred.2.1⟩) hAu hAv
  exact hred.1.2 (he.symm ▸ black_symm _ hblack)

/-- Case 5: two black two-bag neighbors force two common neighbors. -/
lemma two_deficit_singleton_impossible (G : SimpleGraph V) {d s : ℕ}
    (hg : 8 < G.egirth) (hreg : Regular G S d) {P Q : Partition S}
    (small : BagsAtMostTwo P) (near : BagsNear G P) (sat : TwoBagSaturated G d P)
    {u v : V} (hu : {u} ∈ P.parts) (hv : {v} ∈ P.parts) (huv : u ≠ v)
    (hQ : Q.parts = insert ({u} ∪ {v}) (P.parts \ {{u}, {v}}))
    (bounded : Bounded (.ofGraph G) (2 * d - 2) s Q)
    (hdu : totalDegree (.ofGraph G) P {u} + 1 < d) : False := by
  obtain ⟨A, hA, B, hB, hAB, hA2, hB2, huA, huB⟩ :=
    singleton_has_two_blackTwoBags_of_degree_lt G hreg P small hu hdu
  have hAc := mem_inter.mp (black_pair_forces_common G sat hu hv huv hQ bounded hA hA2 huA)
  have hBc := mem_inter.mp (black_pair_forces_common G sat hu hv huv hQ bounded hB hB2 huB)
  exact hAB (singleton_common_bag_unique G hg P near hu hv huv hAc.1 hAc.2 hBc.1 hBc.2)

/-- Case 6: both singletons have degree below d. Their black two-bags are
distinct by the four-cycle obstruction, but saturation makes both common. -/
lemma both_deficit_singletons_impossible (G : SimpleGraph V) {d s : ℕ}
    (hg : 8 < G.egirth) (hreg : Regular G S d) {P Q : Partition S}
    (small : BagsAtMostTwo P) (near : BagsNear G P) (sat : TwoBagSaturated G d P)
    {u v : V} (hu : {u} ∈ P.parts) (hv : {v} ∈ P.parts) (huv : u ≠ v)
    (hQ : Q.parts = insert ({u} ∪ {v}) (P.parts \ {{u}, {v}}))
    (bounded : Bounded (.ofGraph G) (2 * d - 2) s Q)
    (hdu : totalDegree (.ofGraph G) P {u} < d)
    (hdv : totalDegree (.ofGraph G) P {v} < d) : False := by
  obtain ⟨A, hA, hA2, huA⟩ := singleton_has_blackTwoBag_of_degree_lt G hreg P small hu hdu
  obtain ⟨B, hB, hB2, hvB⟩ := singleton_has_blackTwoBag_of_degree_lt G hreg P small hv hdv
  have hAc := mem_inter.mp (black_pair_forces_common G sat hu hv huv hQ bounded hA hA2 huA)
  have hQ' : Q.parts = insert ({v} ∪ {u}) (P.parts \ {{v}, {u}}) := by
    simpa only [union_comm {v} {u}, pair_comm {v} {u}] using hQ
  have hBc := mem_inter.mp (black_pair_forces_common G sat hv hu huv.symm hQ' bounded hB hB2 hvB)
  have he : A = B := singleton_common_bag_unique G hg P near hu hv huv hAc.1 hAc.2 hBc.2 hBc.1
  have hvA : Black (.ofGraph G) {v} A := he.symm ▸ hvB
  obtain ⟨a, b, hab, hAeq⟩ := card_eq_two.mp hA2
  have ha : a ∈ A := by simp [hAeq]
  have hb : b ∈ A := by simp [hAeq]
  exact high_girth_no_square G (lt_trans (by norm_num : (4 : ℕ∞) < 8) hg) huv hab
    (huA u (mem_singleton_self _) a ha) (hvA v (mem_singleton_self _) a ha)
    (huA u (mem_singleton_self _) b hb) (hvA v (mem_singleton_self _) b hb)

/-- The cases above exhaust every permissible singleton merge. -/
lemma singleton_merge_two_bag_facts (G : SimpleGraph V) {d s : ℕ} (hd : 3 ≤ d)
    (hg : 8 < G.egirth) (hreg : Regular G S d) {P Q : Partition S}
    (small : BagsAtMostTwo P) (near : BagsNear G P) (sat : TwoBagSaturated G d P)
    {u v : V} (hu : {u} ∈ P.parts) (hv : {v} ∈ P.parts) (huv : u ≠ v)
    (hQ : Q.parts = insert ({u} ∪ {v}) (P.parts \ {{u}, {v}}))
    (bounded : Bounded (.ofGraph G) (2 * d - 2) s Q) :
    Near G u v ∧ redDegree (.ofGraph G) Q ({u} ∪ {v}) = 2 * d - 2 ∧
      ∀ C ∈ P.parts, C.card = 2 → ¬ (Red (.ofGraph G) C {u} ∧ Red (.ofGraph G) C {v}) := by
  have hdu := singleton_degree_le G hreg P small hu
  have hdv := singleton_degree_le G hreg P small hv
  by_cases hufull : totalDegree (.ofGraph G) P {u} = d
  · by_cases hvfull : totalDegree (.ofGraph G) P {v} = d
    · exact full_singletons_step G hd hg hreg small near hu hv huv hQ bounded hufull hvfull
    · have hQ' : Q.parts = insert ({v} ∪ {u}) (P.parts \ {{v}, {u}}) := by
        simpa only [union_comm {v} {u}, pair_comm {v} {u}] using hQ
      by_cases hdef : totalDegree (.ofGraph G) P {v} + 1 = d
      · obtain ⟨hn, hr, hkeep⟩ := one_deficit_singletons_step G hd hg hreg small near sat
          hv hu huv.symm hQ' bounded hdef hufull
        refine ⟨hn.symm, by simpa only [union_comm {v} {u}] using hr, ?_⟩
        intro C hC hC2 hred
        exact hkeep C hC hC2 ⟨hred.2, hred.1⟩
      · exact False.elim (two_deficit_singleton_impossible G hg hreg small near sat
          hv hu huv.symm hQ' bounded (by omega))
  · by_cases hvfull : totalDegree (.ofGraph G) P {v} = d
    · by_cases hdef : totalDegree (.ofGraph G) P {u} + 1 = d
      · exact one_deficit_singletons_step G hd hg hreg small near sat hu hv huv hQ bounded hdef hvfull
      · exact False.elim (two_deficit_singleton_impossible G hg hreg small near sat
          hu hv huv hQ bounded (by omega))
    · exact False.elim (both_deficit_singletons_impossible G hg hreg small near sat
        hu hv huv hQ bounded (by omega) (by omega))

/-- Lemma 3(i,ii): induction along the actual partial contraction sequence.
The six cases establish the new bag's facts; an old two-bag cannot lose a
red neighbor in any of the surviving cases. -/
theorem two_bag_facts_invariants (G : SimpleGraph V) {d s : ℕ} (hd : 3 ≤ d)
    (hg : 8 < G.egirth) (hreg : Regular G S d) {P : Partition S}
    (hseq : PartialSequence (.ofGraph G) (2 * d - 2) s P)
    (small : BagsAtMostTwo P) : TwoBagSaturated G d P ∧ BagsNear G P := by
  induction hseq with
  | initial hb =>
    constructor
    · intro A hA hA2
      rw [Finpartition.parts_bot] at hA
      obtain ⟨a, _, rfl⟩ := mem_map.mp hA
      simp at hA2
    · intro A hA x hx y hy
      rw [Finpartition.parts_bot] at hA
      obtain ⟨a, _, rfl⟩ := mem_map.mp hA
      have hxa : x = a := mem_singleton.mp hx
      have hya : y = a := mem_singleton.mp hy
      exact Or.inl (hxa.trans hya.symm)
  | @step P Q hprefix hm hb ih =>
    have hPsmall := hm.bagsAtMostTwo_before small
    obtain ⟨hPsat, hPnear⟩ := ih hPsmall
    obtain ⟨u, v, hu, hv, huv, hQ⟩ := hm.singleton_sources_of_small small
    obtain ⟨hn, hr, hkeep⟩ := singleton_merge_two_bag_facts G hd hg hreg hPsmall hPnear hPsat
      hu hv huv hQ hb
    constructor
    · intro A hA hA2
      rw [hQ] at hA
      rcases mem_insert.mp hA with rfl | hA
      · exact hr
      · obtain ⟨hAP, hAuv⟩ := mem_sdiff.mp hA
        have hAu : A ≠ {u} := fun he => hAuv (by simp [he])
        have hAv : A ≠ {v} := fun he => hAuv (by simp [he])
        exact outside_redDegree_stays_saturated _ hu hv (by simpa using huv) hQ hAP hAu hAv
          (hPsat A hAP hA2) hb (hkeep A hAP hA2)
    · intro A hA x hx y hy
      rw [hQ] at hA
      rcases mem_insert.mp hA with rfl | hA
      · simp only [mem_union, mem_singleton] at hx hy
        rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
        · exact Or.inl rfl
        · exact hn
        · exact hn.symm
        · exact Or.inl rfl
      · exact hPnear A (mem_sdiff.mp hA).1 x hx y hy

/-- Lemma 3 (two-bag facts), with the paper's explicit hypothesis d >= 3.
The three conclusions are respectively the red degree, original distance,
and singleton degree. Extended distance gives the usual infinite distance
between disconnected vertices. -/
theorem two_bag_facts (G : SimpleGraph V) {d s : ℕ} (hd : 3 ≤ d)
    (hg : 8 < G.egirth) (hreg : Regular G S d) {P : Partition S}
    (hseq : PartialSequence (.ofGraph G) (2 * d - 2) s P)
    (small : BagsAtMostTwo P) :
    (∀ A ∈ P.parts, A.card = 2 → redDegree (.ofGraph G) P A = 2 * d - 2) ∧
    (∀ A ∈ P.parts, A.card = 2 → ∀ u ∈ A, ∀ v ∈ A, G.edist u v ≤ 2) ∧
    (∀ u, {u} ∈ P.parts →
      totalDegree (.ofGraph G) P {u} = d - (blackTwoBags G P u).card) := by
  obtain ⟨sat, near⟩ := two_bag_facts_invariants G hd hg hreg hseq small
  refine ⟨sat, ?_, fun u hu => two_bag_facts_singleton_degree G hreg P small hu⟩
  intro A hA _ u hu v hv
  obtain ⟨p, _, hp⟩ := (near A hA u hu v hv).exists_path
  exact p.edist_le.trans (by exact_mod_cast hp)

end Paper
