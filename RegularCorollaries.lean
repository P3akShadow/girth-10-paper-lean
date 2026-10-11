import HighGirthTheorems
import GirthExpander
import BagCounting
import RegularExistence

/-! Corollaries 10 and 11. The lower bounds of Section 3 and the sparse
upper bound of Lemma 9 coincide once the stated girth threshold is reached. -/
namespace Paper
open Finset

lemma egirth_gt_of_girth_ge {V : Type*} (G : SimpleGraph V) {k g : ℕ}
    (hkg : k < g) (hg : g ≤ G.girth) : (k : ℕ∞) < G.egirth := by
  have hc : (k : ℕ∞) < (G.girth : ℕ∞) := by exact_mod_cast hkg.trans_le hg
  exact hc.trans_le (ENat.natCast_toNat_le_self G.egirth)

section Graphs
variable {V : Type*} [DecidableEq V] [Fintype V] [Nonempty V]

lemma cubic_widths_eq_five (G : SimpleGraph V) (hreg : Regular G univ 3)
    (hg : 10 ≤ G.girth) (hw : sparseTwinWidth (.ofGraph G) univ ≤ 5) :
    twinWidth (.ofGraph G) univ = 5 ∧ sparseTwinWidth (.ofGraph G) univ = 5 := by
  have hl := girth_cubic G (egirth_gt_of_girth_ge G (k := 9) (g := 10) (by omega) hg) hreg
  have hle := twinWidth_le_sparseTwinWidth (.ofGraph G) univ
  omega

lemma regular_widths_eq (G : SimpleGraph V) {d : ℕ} (hd : 4 ≤ d)
    (hreg : Regular G univ d) (hg : 9 ≤ G.girth)
    (hw : sparseTwinWidth (.ofGraph G) univ ≤ 2 * d - 1) :
    twinWidth (.ofGraph G) univ = 2 * d - 1 ∧
      sparseTwinWidth (.ofGraph G) univ = 2 * d - 1 := by
  have hl := girth_general G (by omega) (egirth_gt_of_girth_ge G (k := 8) (g := 9) (by omega) hg) hreg
  have hle := twinWidth_le_sparseTwinWidth (.ofGraph G) univ
  omega

end Graphs

section Towers
variable {V : Type*} [DecidableEq V] [Fintype V]

/-- Corollary 10, the assertion about every high-girth graph in a cubic TWNGE. -/
theorem TWNGE.cubic_width_eq (F : TWNGE V)
    (hreg : Regular (F.graph 0) univ 3) (hconn : (F.graph 0).Connected)
    (hwidth : sparseTwinWidth (.ofGraph (F.graph 0)) univ ≤ 5)
    (n : ℕ) (hg : 10 ≤ (F.graph n).girth) :
    twinWidth (.ofGraph (F.graph n)) univ = 5 ∧
      sparseTwinWidth (.ofGraph (F.graph n)) univ = 5 := by
  let _ : Nonempty (TowerVertex V n) := ⟨F.x n⟩
  exact cubic_widths_eq_five (F.graph n) (F.regular hreg n) hg
    (F.sparseTwinWidth_le (by omega) hreg hconn hwidth n)

/-- Corollary 11, the assertion about every high-girth graph in a d-regular TWNGE. -/
theorem TWNGE.regular_width_eq (F : TWNGE V) {d : ℕ} (hd : 4 ≤ d)
    (hreg : Regular (F.graph 0) univ d) (hconn : (F.graph 0).Connected)
    (hwidth : sparseTwinWidth (.ofGraph (F.graph 0)) univ ≤ 2 * d - 1)
    (n : ℕ) (hg : 9 ≤ (F.graph n).girth) :
    twinWidth (.ofGraph (F.graph n)) univ = 2 * d - 1 ∧
      sparseTwinWidth (.ofGraph (F.graph n)) univ = 2 * d - 1 := by
  let _ : Nonempty (TowerVertex V n) := ⟨F.x n⟩
  exact regular_widths_eq (F.graph n) hd (F.regular hreg n) hg
    (F.sparseTwinWidth_le (by omega) hreg hconn hwidth n)

end Towers

/-- The universal lower-bound half of Corollary 10's minimum statement. -/
theorem cubic_minimum_lower (g : ℕ) (hg : 10 ≤ g) :
    ∀ (V : Type) [DecidableEq V] [Fintype V] (G : SimpleGraph V),
      G.Connected → Regular G univ 3 → g ≤ G.girth →
        5 ≤ twinWidth (.ofGraph G) univ := by
  intro V _ _ G hconn hreg hgg
  let _ : Nonempty V := hconn.nonempty
  have hlarge : 9 < G.egirth := egirth_gt_of_girth_ge G (k := 9) (g := g) (by omega) hgg
  have h := girth_cubic G hlarge hreg
  omega

/-- The universal lower-bound half of Corollary 11's minimum statement. -/
theorem regular_minimum_lower (d g : ℕ) (hd : 4 ≤ d) (hg : 9 ≤ g) :
    ∀ (V : Type) [DecidableEq V] [Fintype V] (G : SimpleGraph V),
      G.Connected → Regular G univ d → g ≤ G.girth →
        2 * d - 1 ≤ twinWidth (.ofGraph G) univ := by
  intro V _ _ G hconn hreg hgg
  let _ : Nonempty V := hconn.nonempty
  have hlarge : 8 < G.egirth := egirth_gt_of_girth_ge G (k := 8) (g := g) (by omega) hgg
  have h := girth_general G (by omega) hlarge hreg
  omega

/-- Corollary 10, minimum assertion. The universal bound and an attaining
connected cubic graph explicitly characterize the minimum as five. -/
theorem min_cubic (g : ℕ) (hg : 10 ≤ g) :
    (∀ (V : Type) [DecidableEq V] [Fintype V] (G : SimpleGraph V),
      G.Connected → Regular G univ 3 → g ≤ G.girth →
        5 ≤ twinWidth (.ofGraph G) univ) ∧
    (∃ n, ∃ G : SimpleGraph (TowerVertex (Fin 4) n),
      G.Connected ∧ Regular G univ 3 ∧ g ≤ G.girth ∧
        twinWidth (.ofGraph G) univ = 5 ∧ sparseTwinWidth (.ofGraph G) univ = 5) := by
  refine ⟨cubic_minimum_lower g hg, ?_⟩
  obtain ⟨n, G, hconn, hreg, hgg, hwidth⟩ := regular_girth_exists (d := 3) (by omega) g
  let _ : Nonempty (TowerVertex (Fin 4) n) := hconn.nonempty
  have h := cubic_widths_eq_five G hreg (hg.trans hgg) hwidth
  exact ⟨n, G, hconn, hreg, hgg, h⟩

/-- Corollary 11, minimum assertion. Theorem 6 supplies the attaining
connected regular graph; Theorem 5 supplies the universal lower bound. -/
theorem min_general (d g : ℕ) (hd : 4 ≤ d) (hg : 9 ≤ g) :
    (∀ (V : Type) [DecidableEq V] [Fintype V] (G : SimpleGraph V),
      G.Connected → Regular G univ d → g ≤ G.girth →
        2 * d - 1 ≤ twinWidth (.ofGraph G) univ) ∧
    (∃ n, ∃ G : SimpleGraph (TowerVertex (Fin (d + 1)) n),
      G.Connected ∧ Regular G univ d ∧ g ≤ G.girth ∧
        twinWidth (.ofGraph G) univ = 2 * d - 1 ∧
          sparseTwinWidth (.ofGraph G) univ = 2 * d - 1) := by
  refine ⟨regular_minimum_lower d g hd hg, ?_⟩
  obtain ⟨n, G, hconn, hreg, hgg, hwidth⟩ := regular_girth_exists (d := d) (by omega) g
  let _ : Nonempty (TowerVertex (Fin (d + 1)) n) := hconn.nonempty
  have h := regular_widths_eq G hd hreg (hg.trans hgg) hwidth
  exact ⟨n, G, hconn, hreg, hgg, h⟩

end Paper
