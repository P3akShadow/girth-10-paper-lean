import HighGirthMerging
import Lemma02CycleLift

/-! The short quotient-cycle exclusions used in the six cases of Lemma 3
and in the first-large-bag arguments of Lemma 4 and Theorem 5. Every exclusion
is an application of Lemma 2, with one unit for every crossing edge and at
most two units inside each nonsingleton bag. -/
namespace Paper
open Finset SimpleGraph CycleLift
variable {V : Type*} [DecidableEq V] {S : Finset V}
attribute [local instance] Classical.propDecidable

/-- Every pair in each bag has original-graph distance at most two. -/
def BagsNear (G : SimpleGraph V) (P : Partition S) : Prop :=
  ∀ A ∈ P.parts, ∀ a ∈ A, ∀ b ∈ A, Near G a b

lemma Near.edist_le_two {G : SimpleGraph V} {u v : V} (h : Near G u v) : G.edist u v ≤ 2 := by
  obtain ⟨p, _, hp⟩ := h.exists_path
  exact p.edist_le.trans (by exact_mod_cast hp)

lemma subbag_cycle_egirth_cost (G : SimpleGraph V) (P : Partition S)
    (n : ℕ) (A : Fin (n + 3) → Finset V)
    (hA : ∀ i, A i ∈ P.parts) (hAi : Function.Injective A)
    (B : Fin (n + 3) → Finset V) (hBA : ∀ i, B i ⊆ A i)
    (cross : ∀ i, Adjacent (.ofGraph G) (B i) (B (i + 1)))
    (d : Fin (n + 3) → ℕ) (short : ∀ i, d i ≤ 2)
    (diam : ∀ i, ∀ u ∈ B i, ∀ v ∈ B i, G.edist u v ≤ d i) :
    G.egirth ≤ ((n + 3) + ∑ i, d i : ℕ) := by
  classical
  have edges : ∀ i, ∃ b ∈ B i, ∃ c ∈ B (i + 1), G.Adj b c := by
    intro i
    obtain ⟨b, hb, c, hc, he | he⟩ := cross i
    · exact ⟨b, hb, c, hc, he⟩
    · exact False.elim he
  choose b hb c hc he using edges
  let a : Fin (n + 3) → V := fun i => c (i - 1)
  have ha : ∀ i, a i ∈ B i := by intro i; simpa [a] using hc (i - 1)
  have hcross : ∀ i, G.Adj (b i) (a (i + 1)) := by simpa [a] using he
  exact cycle_lift_egirth G n a b
    (separated_of_partition P A hA hAi a b (fun i => hBA i (ha i)) (fun i => hBA i (hb i)))
    hcross d (fun i => diam i _ (ha i) _ (hb i)) short

lemma subbag_cycle_egirth_le (G : SimpleGraph V) (P : Partition S)
    (near : BagsNear G P) (n : ℕ) (A : Fin (n + 3) → Finset V)
    (hA : ∀ i, A i ∈ P.parts) (hAi : Function.Injective A)
    (B : Fin (n + 3) → Finset V) (hBA : ∀ i, B i ⊆ A i)
    (cross : ∀ i, Adjacent (.ofGraph G) (B i) (B (i + 1))) :
    G.egirth ≤ ((n + 3) + ∑ i, if (B i).card = 1 then 0 else 2 : ℕ) := by
  classical
  have edges : ∀ i, ∃ b ∈ B i, ∃ c ∈ B (i + 1), G.Adj b c := by
    intro i
    obtain ⟨b, hb, c, hc, he | he⟩ := cross i
    · exact ⟨b, hb, c, hc, he⟩
    · exact False.elim he
  choose b hb c hc he using edges
  let a : Fin (n + 3) → V := fun i => c (i - 1)
  have ha : ∀ i, a i ∈ B i := by
    intro i
    simpa [a] using hc (i - 1)
  have hcross : ∀ i, G.Adj (b i) (a (i + 1)) := by simpa [a] using he
  apply cycle_lift_egirth G n a b (separated_of_partition P A hA hAi a b (fun i => hBA i (ha i)) (fun i => hBA i (hb i))) hcross
  · intro i
    by_cases hsing : (B i).card = 1
    · have hab : a i = b i := card_le_one.mp (by omega : (B i).card ≤ 1) (a i) (ha i) (b i) (hb i)
      simp [hsing, hab]
    · obtain ⟨p, _, hp⟩ := (near (A i) (hA i) (a i) (hBA i (ha i)) (b i) (hBA i (hb i))).exists_path
      simpa [hsing] using p.edist_le.trans (show (p.length : ℕ∞) ≤ (2 : ℕ) by exact_mod_cast hp)
  · intro i
    split_ifs <;> omega

lemma quotient_cycle_egirth_le (G : SimpleGraph V) (P : Partition S)
    (near : BagsNear G P) (n : ℕ) (A : Fin (n + 3) → Finset V)
    (hA : ∀ i, A i ∈ P.parts) (hAi : Function.Injective A)
    (cross : ∀ i, Adjacent (.ofGraph G) (A i) (A (i + 1))) :
    G.egirth ≤ ((n + 3) + ∑ i, if (A i).card = 1 then 0 else 2 : ℕ) := by
  classical
  have edges : ∀ i, ∃ b ∈ A i, ∃ c ∈ A (i + 1), G.Adj b c := by
    intro i
    obtain ⟨b, hb, c, hc, he | he⟩ := cross i
    · exact ⟨b, hb, c, hc, he⟩
    · exact False.elim he
  choose b hb c hc he using edges
  let a : Fin (n + 3) → V := fun i => c (i - 1)
  have ha : ∀ i, a i ∈ A i := by
    intro i
    simpa [a] using hc (i - 1)
  have hcross : ∀ i, G.Adj (b i) (a (i + 1)) := by simpa [a] using he
  apply cycle_lift_egirth G n a b (separated_of_partition P A hA hAi a b ha hb) hcross
  · intro i
    by_cases hsing : (A i).card = 1
    · have hab : a i = b i := card_le_one.mp (by omega : (A i).card ≤ 1) (a i) (ha i) (b i) (hb i)
      simp [hsing, hab]
    · obtain ⟨p, _, hp⟩ := (near (A i) (hA i) (a i) (ha i) (b i) (hb i)).exists_path
      simpa [hsing] using p.edist_le.trans (show (p.length : ℕ∞) ≤ (2 : ℕ) by exact_mod_cast hp)
  · intro i
    split_ifs <;> omega

lemma quotient_triangle_egirth_le (G : SimpleGraph V) (P : Partition S)
    (near : BagsNear G P) {A B C : Finset V}
    (hA : A ∈ P.parts) (hB : B ∈ P.parts) (hC : C ∈ P.parts)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    (eAB : Adjacent (.ofGraph G) A B) (eBC : Adjacent (.ofGraph G) B C)
    (eCA : Adjacent (.ofGraph G) C A) : G.egirth ≤ 9 := by
  have h := quotient_cycle_egirth_le G P near 0 ![A, B, C]
    (by intro i; fin_cases i <;> assumption)
    (by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all)
    (by intro i; fin_cases i
        · simpa using eAB
        · simpa using eBC
        · simpa using eCA)
  apply h.trans
  norm_num [Fin.sum_univ_succ]
  by_cases hA1 : A.card = 1 <;> by_cases hB1 : B.card = 1 <;>
    by_cases hC1 : C.card = 1 <;> norm_num [hA1, hB1, hC1]

lemma high_girth_no_quotient_triangle (G : SimpleGraph V) (hg : 9 < G.egirth)
    (P : Partition S) (near : BagsNear G P) {A B C : Finset V}
    (hA : A ∈ P.parts) (hB : B ∈ P.parts) (hC : C ∈ P.parts)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
    (eAB : Adjacent (.ofGraph G) A B) (eBC : Adjacent (.ofGraph G) B C)
    (eCA : Adjacent (.ofGraph G) C A) : False :=
  (not_lt_of_ge (quotient_triangle_egirth_le G P near hA hB hC hAB hAC hBC eAB eBC eCA)) hg

lemma quotient_singleton_triangle_egirth_le (G : SimpleGraph V) (P : Partition S)
    (near : BagsNear G P) {u : V} {A B : Finset V}
    (hu : {u} ∈ P.parts) (hA : A ∈ P.parts) (hB : B ∈ P.parts)
    (huA : {u} ≠ A) (huB : {u} ≠ B) (hAB : A ≠ B)
    (euA : Adjacent (.ofGraph G) {u} A) (eAB : Adjacent (.ofGraph G) A B)
    (eBu : Adjacent (.ofGraph G) B {u}) : G.egirth ≤ 7 := by
  have h := quotient_cycle_egirth_le G P near 0 ![{u}, A, B]
    (by intro i; fin_cases i <;> assumption)
    (by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all)
    (by intro i; fin_cases i
        · simpa using euA
        · simpa using eAB
        · simpa using eBu)
  apply h.trans
  norm_num [Fin.sum_univ_succ]
  by_cases hA1 : A.card = 1 <;> by_cases hB1 : B.card = 1 <;> norm_num [hA1, hB1]

lemma high_girth_no_singleton_triangle (G : SimpleGraph V) (hg : 8 < G.egirth)
    (P : Partition S) (near : BagsNear G P) {u : V} {A B : Finset V}
    (hu : {u} ∈ P.parts) (hA : A ∈ P.parts) (hB : B ∈ P.parts)
    (huA : {u} ≠ A) (huB : {u} ≠ B) (hAB : A ≠ B)
    (euA : Adjacent (.ofGraph G) {u} A) (eAB : Adjacent (.ofGraph G) A B)
    (eBu : Adjacent (.ofGraph G) B {u}) : False := by
  have h := quotient_singleton_triangle_egirth_le G P near hu hA hB huA huB hAB euA eAB eBu
  exact (not_lt_of_ge (h.trans (by norm_num))) hg

lemma quotient_two_singletons_triangle_egirth_le (G : SimpleGraph V) (P : Partition S)
    (near : BagsNear G P) {u v : V} {A : Finset V}
    (hu : {u} ∈ P.parts) (hv : {v} ∈ P.parts) (hA : A ∈ P.parts)
    (huv : u ≠ v) (huA : {u} ≠ A) (hvA : {v} ≠ A)
    (euA : Adjacent (.ofGraph G) {u} A) (eAv : Adjacent (.ofGraph G) A {v})
    (evu : Adjacent (.ofGraph G) {v} {u}) : G.egirth ≤ 5 := by
  have h := quotient_cycle_egirth_le G P near 0 ![{u}, A, {v}]
    (by intro i; fin_cases i <;> assumption)
    (by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all)
    (by intro i; fin_cases i
        · simpa using euA
        · simpa using eAv
        · simpa using evu)
  apply h.trans
  norm_num [Fin.sum_univ_succ]
  by_cases hA1 : A.card = 1 <;> norm_num [hA1]

lemma high_girth_no_two_singletons_triangle (G : SimpleGraph V) (hg : 8 < G.egirth)
    (P : Partition S) (near : BagsNear G P) {u v : V} {A : Finset V}
    (hu : {u} ∈ P.parts) (hv : {v} ∈ P.parts) (hA : A ∈ P.parts)
    (huv : u ≠ v) (huA : {u} ≠ A) (hvA : {v} ≠ A)
    (euA : Adjacent (.ofGraph G) {u} A) (eAv : Adjacent (.ofGraph G) A {v})
    (evu : Adjacent (.ofGraph G) {v} {u}) : False := by
  have h := quotient_two_singletons_triangle_egirth_le G P near hu hv hA huv huA hvA euA eAv evu
  exact (not_lt_of_ge (h.trans (by norm_num))) hg

lemma quotient_alternating_square_egirth_le (G : SimpleGraph V) (P : Partition S)
    (near : BagsNear G P) {u v : V} {A B : Finset V}
    (hu : {u} ∈ P.parts) (hv : {v} ∈ P.parts)
    (hA : A ∈ P.parts) (hB : B ∈ P.parts)
    (huv : u ≠ v) (hAB : A ≠ B)
    (huA : {u} ≠ A) (huB : {u} ≠ B) (hvA : {v} ≠ A) (hvB : {v} ≠ B)
    (euA : Adjacent (.ofGraph G) {u} A) (eAv : Adjacent (.ofGraph G) A {v})
    (evB : Adjacent (.ofGraph G) {v} B) (eBu : Adjacent (.ofGraph G) B {u}) :
    G.egirth ≤ 8 := by
  have h := quotient_cycle_egirth_le G P near 1 ![{u}, A, {v}, B]
    (by intro i; fin_cases i <;> assumption)
    (by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all)
    (by intro i; fin_cases i
        · simpa using euA
        · simpa using eAv
        · simpa using evB
        · simpa using eBu)
  apply h.trans
  norm_num [Fin.sum_univ_succ]
  by_cases hA1 : A.card = 1 <;> by_cases hB1 : B.card = 1 <;> norm_num [hA1, hB1]

lemma high_girth_no_alternating_square (G : SimpleGraph V) (hg : 8 < G.egirth)
    (P : Partition S) (near : BagsNear G P) {u v : V} {A B : Finset V}
    (hu : {u} ∈ P.parts) (hv : {v} ∈ P.parts)
    (hA : A ∈ P.parts) (hB : B ∈ P.parts)
    (huv : u ≠ v) (hAB : A ≠ B)
    (huA : {u} ≠ A) (huB : {u} ≠ B) (hvA : {v} ≠ A) (hvB : {v} ≠ B)
    (euA : Adjacent (.ofGraph G) {u} A) (eAv : Adjacent (.ofGraph G) A {v})
    (evB : Adjacent (.ofGraph G) {v} B) (eBu : Adjacent (.ofGraph G) B {u}) : False :=
  (not_lt_of_ge (quotient_alternating_square_egirth_le G P near hu hv hA hB huv hAB
    huA huB hvA hvB euA eAv evB eBu)) hg

/-- Two singleton bags have at most one common neighbor. Two different
common bags would lift the alternating quotient four-cycle to length ≤8. -/
lemma singleton_common_neighbors_card_le_one (G : SimpleGraph V) (hg : 8 < G.egirth)
    (P : Partition S) (near : BagsNear G P) {u v : V}
    (hu : {u} ∈ P.parts) (hv : {v} ∈ P.parts) (huv : u ≠ v) :
    (neighbors (Adjacent (.ofGraph G)) P {u} ∩
      neighbors (Adjacent (.ofGraph G)) P {v}).card ≤ 1 := by
  classical
  apply card_le_one.mpr
  intro A hA B hB
  obtain ⟨hAu, hAv⟩ := mem_inter.mp hA
  obtain ⟨hBu, hBv⟩ := mem_inter.mp hB
  obtain ⟨hAP, hAu, euA⟩ := mem_filter.mp hAu
  obtain ⟨_, hAv, evA⟩ := mem_filter.mp hAv
  obtain ⟨hBP, hBu, euB⟩ := mem_filter.mp hBu
  obtain ⟨_, hBv, evB⟩ := mem_filter.mp hBv
  by_contra hAB
  exact high_girth_no_alternating_square G hg P near hu hv hAP hBP huv hAB
    hAu.symm hBu.symm hAv.symm hBv.symm euA (adjacent_symm _ evA) evB (adjacent_symm _ euB)

lemma singleton_common_bag_unique (G : SimpleGraph V) (hg : 8 < G.egirth)
    (P : Partition S) (near : BagsNear G P) {u v : V}
    (hu : {u} ∈ P.parts) (hv : {v} ∈ P.parts) (huv : u ≠ v) {A B : Finset V}
    (hAu : A ∈ neighbors (Adjacent (.ofGraph G)) P {u})
    (hAv : A ∈ neighbors (Adjacent (.ofGraph G)) P {v})
    (hBu : B ∈ neighbors (Adjacent (.ofGraph G)) P {u})
    (hBv : B ∈ neighbors (Adjacent (.ofGraph G)) P {v}) : A = B :=
  card_le_one.mp (singleton_common_neighbors_card_le_one G hg P near hu hv huv)
    A (mem_inter.mpr ⟨hAu, hAv⟩) B (mem_inter.mpr ⟨hBu, hBv⟩)

lemma high_girth_singleton_common_unique (G : SimpleGraph V) (hg : 8 < G.egirth)
    (P : Partition S) (near : BagsNear G P) {u v : V} {A B : Finset V}
    (hu : {u} ∈ P.parts) (hv : {v} ∈ P.parts) (huv : u ≠ v)
    (hA : A ∈ P.parts) (hB : B ∈ P.parts)
    (huA : {u} ≠ A) (huB : {u} ≠ B) (hvA : {v} ≠ A) (hvB : {v} ≠ B)
    (euA : Adjacent (.ofGraph G) {u} A) (evA : Adjacent (.ofGraph G) {v} A)
    (euB : Adjacent (.ofGraph G) {u} B) (evB : Adjacent (.ofGraph G) {v} B) : A = B := by
  classical
  exact singleton_common_bag_unique G hg P near hu hv huv
    (mem_filter.mpr ⟨hA, huA.symm, euA⟩) (mem_filter.mpr ⟨hA, hvA.symm, evA⟩)
    (mem_filter.mpr ⟨hB, huB.symm, euB⟩) (mem_filter.mpr ⟨hB, hvB.symm, evB⟩)

/-- Splitting the endpoint bags at selected vertices, as in the pigeonhole
arguments of Lemma 4 and Theorem 5. -/
lemma vertex_common_bag_unique (G : SimpleGraph V) (hg : 8 < G.egirth)
    (P : Partition S) (near : BagsNear G P) {X Y A B : Finset V} {u v : V}
    (hX : X ∈ P.parts) (hY : Y ∈ P.parts) (hA : A ∈ P.parts) (hB : B ∈ P.parts)
    (hXY : X ≠ Y) (hXA : X ≠ A) (hXB : X ≠ B) (hYA : Y ≠ A) (hYB : Y ≠ B)
    (hu : u ∈ X) (hv : v ∈ Y)
    (euA : Adjacent (.ofGraph G) {u} A) (evA : Adjacent (.ofGraph G) {v} A)
    (euB : Adjacent (.ofGraph G) {u} B) (evB : Adjacent (.ofGraph G) {v} B) : A = B := by
  by_contra hAB
  have h := subbag_cycle_egirth_le G P near 1 ![X, A, Y, B]
    (by intro i; fin_cases i <;> assumption)
    (by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all)
    ![{u}, A, {v}, B]
    (by intro i; fin_cases i
        · simpa using hu
        · exact Subset.rfl
        · simpa using hv
        · exact Subset.rfl)
    (by intro i; fin_cases i
        · simpa using euA
        · simpa using adjacent_symm _ evA
        · simpa using evB
        · simpa using adjacent_symm _ euB)
  have hh : G.egirth ≤ 8 := by
    apply h.trans
    norm_num [Fin.sum_univ_succ]
    by_cases hA1 : A.card = 1 <;> by_cases hB1 : B.card = 1 <;> norm_num [hA1, hB1]
  exact not_lt_of_ge hh hg

lemma vertex_common_neighbors_card_le_one (G : SimpleGraph V) (hg : 8 < G.egirth)
    (P : Partition S) (near : BagsNear G P) {X Y : Finset V} {u v : V}
    (hX : X ∈ P.parts) (hY : Y ∈ P.parts) (hXY : X ≠ Y) (hu : u ∈ X) (hv : v ∈ Y) :
    (P.parts.filter fun A => A ≠ X ∧ A ≠ Y ∧
      Adjacent (.ofGraph G) {u} A ∧ Adjacent (.ofGraph G) {v} A).card ≤ 1 := by
  classical
  apply card_le_one.mpr
  intro A hA B hB
  obtain ⟨hAP, hAX, hAY, euA, evA⟩ := mem_filter.mp hA
  obtain ⟨hBP, hBX, hBY, euB, evB⟩ := mem_filter.mp hB
  exact vertex_common_bag_unique G hg P near hX hY hAP hBP hXY
    hAX.symm hBX.symm hAY.symm hBY.symm hu hv euA evA euB evB

/-- The pigeonhole step: a singleton and a two-bag cannot have three common
neighbor bags, since two would meet the same vertex of the two-bag. -/
lemma pair_singleton_common_neighbors_le_two (G : SimpleGraph V) (hg : 8 < G.egirth)
    (P : Partition S) (near : BagsNear G P) {X : Finset V} {w : V}
    (hX : X ∈ P.parts) (hw : {w} ∈ P.parts) (hsize : X.card = 2) :
    (neighbors (Adjacent (.ofGraph G)) P X ∩
      neighbors (Adjacent (.ofGraph G)) P {w}).card ≤ 2 := by
  classical
  obtain ⟨u, v, huv, rfl⟩ := card_eq_two.mp hsize
  have hXw : ({u, v} : Finset V) ≠ {w} := by
    intro he
    have hh := congrArg Finset.card he
    simp [huv] at hh
  let C := fun t => P.parts.filter fun A => A ≠ {u, v} ∧ A ≠ {w} ∧
    Adjacent (.ofGraph G) {t} A ∧ Adjacent (.ofGraph G) {w} A
  have hsub : neighbors (Adjacent (.ofGraph G)) P {u, v} ∩
      neighbors (Adjacent (.ofGraph G)) P {w} ⊆ C u ∪ C v := by
    intro A hA
    obtain ⟨hAX, hAw⟩ := mem_inter.mp hA
    obtain ⟨hAP, hAX, x, hx, y, hy, hxy⟩ := mem_filter.mp hAX
    obtain ⟨_, hAw, ewA⟩ := mem_filter.mp hAw
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact mem_union_left _ (mem_filter.mpr ⟨hAP, hAX, hAw,
        ⟨_, mem_singleton_self _, y, hy, hxy⟩, ewA⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hAP, hAX, hAw,
        ⟨_, mem_singleton_self _, y, hy, hxy⟩, ewA⟩)
  have hCu : (C u).card ≤ 1 := vertex_common_neighbors_card_le_one G hg P near (u := u) (v := w) hX hw hXw
    (by simp) (by simp)
  have hCv : (C v).card ≤ 1 := vertex_common_neighbors_card_le_one G hg P near (u := v) (v := w) hX hw hXw
    (by simp) (by simp)
  have hh := (card_le_card hsub).trans (card_union_le _ _)
  omega

end Paper
