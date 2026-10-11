import BagCounting
import MergeDegrees
import Lemma13Exchange

/-! Twin classes and critical bags in Proposition 14. -/

namespace Paper
open Finset
variable {V : Type*} [DecidableEq V] {S : Finset V}

def GraphTwins (G : SimpleGraph V) (S : Finset V) (a b : V) : Prop :=
  graphNeighbors G S a = graphNeighbors G S b

def TwinSaturated (G : SimpleGraph V) (P : Partition S) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, GraphTwins G S a b → P.part a = P.part b

def Critical (G : SimpleGraph V) (P : Partition S) (d : ℕ) (A : Finset V) : Prop :=
  A ∈ P.parts ∧ A.card = d ∧ ∃ c, {c} ∈ P.parts ∧ Black (.ofGraph G) A {c}

lemma full_bag_black_neighbors_equal (G : SimpleGraph V) {d : ℕ} (hdeg : MaxDegree G S d)
    (P : Partition S) (hsat : TwinSaturated G P) {A B C : Finset V}
    (hA : A ∈ P.parts) (hsize : A.card = d)
    (hB : B ∈ neighbors (Black (.ofGraph G)) P A)
    (hC : C ∈ neighbors (Black (.ofGraph G)) P A) : B = C := by
  classical
  obtain ⟨hBP, _, hAB⟩ := mem_filter.mp hB
  obtain ⟨hCP, _, hAC⟩ := mem_filter.mp hC
  obtain ⟨b, hb⟩ := P.nonempty_of_mem_parts hBP
  obtain ⟨c, hc⟩ := P.nonempty_of_mem_parts hCP
  have hbt := full_bag_neighbor G hdeg P hA hBP hsize hAB hb
  have hct := full_bag_neighbor G hdeg P hA hCP hsize hAC hc
  have heq := hsat b (P.subset hBP hb) c (P.subset hCP hc) (hbt.trans hct.symm)
  simpa only [P.part_eq_of_mem hBP hb, P.part_eq_of_mem hCP hc] using heq

lemma full_bag_blackDegree_le_one (G : SimpleGraph V) {d : ℕ} (hdeg : MaxDegree G S d)
    (P : Partition S) (hsat : TwinSaturated G P) {A : Finset V}
    (hA : A ∈ P.parts) (hsize : A.card = d) : blackDegree (.ofGraph G) P A ≤ 1 := by
  apply card_le_one.mpr
  intro B hB C hC
  exact full_bag_black_neighbors_equal G hdeg P hsat hA hsize hB hC

lemma large_black_neighbor_count (T : Trigraph V) (P : Partition S) {A B : Finset V}
    (hB : B ∈ neighbors (Black T) P A) (hlarge : 2 ≤ B.card) :
    blackDegree T P A + 1 ≤ (blackVertices T P A).card := by
  classical
  have hrest : ((neighbors (Black T) P A).erase B).card ≤
      ∑ C ∈ (neighbors (Black T) P A).erase B, C.card := by
    calc
      _ = ∑ _C ∈ (neighbors (Black T) P A).erase B, 1 := by simp
      _ ≤ _ := sum_le_sum fun C hC => one_le_card.mpr
        (P.nonempty_of_mem_parts (mem_filter.mp (mem_of_mem_erase hC)).1)
  have hsum := sum_erase_add (neighbors (Black T) P A) (fun C : Finset V => C.card) hB
  have hcard := card_erase_add_one hB
  rw [blackVertices_card]
  unfold blackDegree
  omega

lemma all_singleton_black_critical (G : SimpleGraph V) (P : Partition S) {d : ℕ}
    {A : Finset V} (hA : A ∈ P.parts) (hsize : A.card = d)
    (hb : 0 < blackDegree (.ofGraph G) P A)
    (hsmall : ∀ B ∈ neighbors (Black (.ofGraph G)) P A, B.card ≤ 1) : Critical G P d A := by
  classical
  obtain ⟨B, hB⟩ := card_pos.mp hb
  obtain ⟨hBP, _, hblack⟩ := mem_filter.mp hB
  have hcard : B.card = 1 := Nat.le_antisymm (hsmall B hB)
    (one_le_card.mpr (P.nonempty_of_mem_parts hBP))
  obtain ⟨c, rfl⟩ := card_eq_one.mp hcard
  exact ⟨hA, hsize, c, hBP, hblack⟩

lemma counting_small_many {d p b q t : ℕ} (hd : 3 ≤ d) (hp : p ≤ d - 1)
    (hb : 2 ≤ b) (hbq : b ≤ q) (hqd : q ≤ d)
    (ht : t ≤ p * (d - q) + b) : t ≤ (d - 1)^2 := by
  have hmul : p * (d - q) ≤ (d - 1) * (d - q) := Nat.mul_le_mul_right _ hp
  have hmul' : (d - 1) * (d - q) ≤ (d - 1) * (d - b) :=
    Nat.mul_le_mul_left _ (Nat.sub_le_sub_left hbq d)
  have hd1 : d - 1 + 1 = d := by omega
  have hd2 : d - 2 + 2 = d := by omega
  have hb2 : b - 2 + 2 = b := by omega
  have hdb : d - b + b = d := by omega
  nlinarith [Nat.zero_le ((d - 2) * (b - 2))]

lemma counting_full_large {d b q t : ℕ} (hd : 3 ≤ d) (hb : 1 ≤ b)
    (hbq : b + 1 ≤ q) (hqd : q ≤ d) (ht : t ≤ d * (d - q) + b) : t ≤ (d - 1)^2 := by
  have hd1 : d - 1 + 1 = d := by omega
  have hdq : d - q + q = d := by omega
  have hb1 : b - 1 + 1 = b := by omega
  have hq : d * (b + 1) ≤ d * q := Nat.mul_le_mul_left _ hbq
  nlinarith [Nat.zero_le ((d - 1) * (b - 1))]

/-- All five degree cases in the normalized-sequence paragraph of Proposition 14. -/
lemma normalized_bag_degrees (G : SimpleGraph V) {d w : ℕ} (hd : 3 ≤ d)
    (hdeg : MaxDegree G S d) (P : Partition S) (hsat : TwinSaturated G P)
    {A : Finset V} (hA : A ∈ P.parts) (hr : redDegree (.ofGraph G) P A ≤ w) :
    totalDegree (.ofGraph G) P A ≤ max (w + 1) ((d - 1)^2) ∧
    (¬ Critical G P d A → totalDegree (.ofGraph G) P A ≤ max w ((d - 1)^2 + 1)) := by
  classical
  let b := blackDegree (.ofGraph G) P A
  let q := (blackVertices (.ofGraph G) P A).card
  let t := totalDegree (.ofGraph G) P A
  have hsplit : t = redDegree (.ofGraph G) P A + b := totalDegree_eq_red_add_black _ _ hA
  have hcount : t ≤ A.card * (d - q) + b := degree_counting_bound G hdeg P hA
  have hbq : b ≤ q := blackDegree_le_blackVertices _ _ _
  have hqd : q ≤ d := blackVertices_card_le_degree G hdeg P hA
  by_cases hb0 : b = 0
  · exact ⟨by omega, fun _ => by omega⟩
  have hb1 : 1 ≤ b := by omega
  have hp : A.card ≤ d := by
    by_contra h
    exact hb0 (oversized_blackDegree_zero G hdeg P hA (by omega))
  by_cases hpsmall : A.card ≤ d - 1
  · by_cases hb : b = 1
    · have hq1 : 1 ≤ q := by omega
      have hmul : A.card * (d - q) ≤ (d - 1) * (d - 1) :=
        Nat.mul_le_mul hpsmall (Nat.sub_le_sub_left hq1 d)
      constructor
      · omega
      · intro _
        have : t ≤ (d - 1)^2 + 1 := by nlinarith
        exact this.trans (le_max_right _ _)
    · have ht := counting_small_many hd hpsmall (by omega : 2 ≤ b) hbq hqd hcount
      exact ⟨ht.trans (le_max_right _ _), fun _ =>
        (ht.trans (Nat.le_succ _)).trans (le_max_right _ _)⟩
  · have hpd : A.card = d := by omega
    by_cases hlarge : ∃ B ∈ neighbors (Black (.ofGraph G)) P A, 2 ≤ B.card
    · obtain ⟨B, hB, hBcard⟩ := hlarge
      have hqbig : b + 1 ≤ q := large_black_neighbor_count _ _ hB hBcard
      have ht := counting_full_large hd hb1 hqbig hqd (by simpa only [hpd] using hcount)
      exact ⟨ht.trans (le_max_right _ _), fun _ =>
        (ht.trans (Nat.le_succ _)).trans (le_max_right _ _)⟩
    · have hb_le : b ≤ 1 := full_bag_blackDegree_le_one G hdeg P hsat hA hpd
      have hcrit : Critical G P d A := all_singleton_black_critical G P hA hpd
        (by omega) (by intro B hB; by_contra h; exact hlarge ⟨B, hB, by omega⟩)
      exact ⟨by omega, fun h => False.elim (h hcrit)⟩

end Paper
