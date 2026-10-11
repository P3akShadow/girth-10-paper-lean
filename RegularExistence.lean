import LiftImprovement

/-! Theorem 6's final step: start with K_(d+1) and take a stage whose girth
reaches the prescribed value. Lemma 9 supplies the sparse-width bound. -/
namespace Paper
open Finset

lemma regular_graph_from_unbounded_tower {d : ℕ} (hd : 3 ≤ d)
    (F : TWNGE (Fin (d+1))) (hstart : F.graph 0 = ⊤)
    (hunbounded : ∀ g : ℕ, ∃ n, g ≤ (F.graph n).girth) (g : ℕ) :
    ∃ n, (F.graph n).Connected ∧ Regular (F.graph n) univ d ∧
      g ≤ (F.graph n).girth ∧ sparseTwinWidth (.ofGraph (F.graph n)) univ ≤ 2*d-1 := by
  obtain ⟨hconn,hreg,hwidth⟩ := regular_seed d
  obtain ⟨n,hn⟩ := hunbounded g
  have hc0 : (F.graph 0).Connected := hstart ▸ hconn
  have hr0 : Regular (F.graph 0) univ d := hstart ▸ hreg
  have hw0 : sparseTwinWidth (.ofGraph (F.graph 0)) univ ≤ 2*d-1 := by
    rw [hstart]
    exact hwidth.trans (by omega)
  exact ⟨n,F.connected hc0 n,F.regular hr0 n,hn,
    F.sparseTwinWidth_le (by omega) hr0 hc0 hw0 n⟩

/-- Theorem 6: the complete-graph seed and Lemmas 8 and 9 provide connected
regular graphs of arbitrarily large girth with sparse width at most 2d-1. -/
theorem regular_girth_exists {d : ℕ} (hd : 3 ≤ d) (g : ℕ) :
    ∃ n, ∃ G : SimpleGraph (TowerVertex (Fin (d+1)) n),
      G.Connected ∧ Regular G univ d ∧ g ≤ G.girth ∧
        sparseTwinWidth (.ofGraph G) univ ≤ 2*d-1 := by
  obtain ⟨hc,hr,_⟩ := regular_seed d
  obtain ⟨F,hstart,hunbounded⟩ := lift_girth (⊤ : SimpleGraph (Fin (d+1))) (by omega) hr hc
  obtain ⟨n,hn⟩ := regular_graph_from_unbounded_tower hd F hstart hunbounded g
  exact ⟨n,F.graph n,hn⟩

/-- The integer-threshold wording of Theorem 6 in the paper. -/
theorem regular_girth_exists_int {d : ℕ} (hd : 3 ≤ d) (g : ℤ) :
    ∃ n, ∃ G : SimpleGraph (TowerVertex (Fin (d+1)) n),
      G.Connected ∧ Regular G univ d ∧ g ≤ (G.girth : ℤ) ∧
        sparseTwinWidth (.ofGraph G) univ ≤ 2*d-1 := by
  obtain ⟨n,G,hc,hr,hg,hw⟩ := regular_girth_exists hd g.toNat
  exact ⟨n,G,hc,hr,by omega,hw⟩

end Paper
