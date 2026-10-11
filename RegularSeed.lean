import GirthExpander

/-! The complete-graph seed K_(d+1) used in Theorem 6. -/
namespace Paper
open Finset
variable {V : Type*} [DecidableEq V] {S : Finset V}

lemma totalDegree_le_card_sub_one (T : Trigraph V) (P : Partition S)
    {A : Finset V} (hA : A ∈ P.parts) : totalDegree T P A ≤ S.card - 1 := by
  classical
  have hs : neighbors (Adjacent T) P A ⊆ P.parts.erase A := by
    intro B hB
    obtain ⟨hB,hne,_⟩ := mem_filter.mp hB
    exact mem_erase.mpr ⟨hne,hB⟩
  have hh := card_le_card hs
  rw [card_erase_of_mem hA] at hh
  exact hh.trans (Nat.sub_le_sub_right (partition_card_le P) 1)

lemma complete_black {P : Partition S} {A B : Finset V}
    (hA : A ∈ P.parts) (hB : B ∈ P.parts) (hne : A ≠ B) :
    Black (.ofGraph (⊤ : SimpleGraph V)) A B := by
  intro a ha b hb
  change a ≠ b
  intro heq
  subst b
  exact hne (P.eq_of_mem_parts hA hB ha hb)

lemma complete_bounded (P : Partition S) : Bounded (.ofGraph (⊤ : SimpleGraph V)) 0 (S.card-1) P := by
  classical
  intro A hA
  constructor
  · apply Nat.le_zero.mpr
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_notMem.mpr
    intro B hB
    obtain ⟨hB,hne,_,hn⟩ := mem_filter.mp hB
    exact hn (complete_black hA hB (Ne.symm hne))
  · exact totalDegree_le_card_sub_one _ P hA

lemma complete_continuation (P : Partition S) :
    Continuation (.ofGraph (⊤ : SimpleGraph V)) 0 (S.card-1) P := by
  induction hn : P.parts.card using Nat.strong_induction_on generalizing P with | h n ih =>
    by_cases hd : P.parts.card ≤ 1
    · exact .done (complete_bounded P) hd
    have hh := mt card_le_one.mpr hd
    push Not at hh
    obtain ⟨A,hA,B,hB,hAB⟩ := hh
    let Q := mergePartition P A B hA hB
    have hm : Merge P Q := ⟨A,hA,B,hB,hAB,rfl⟩
    exact .step (complete_bounded P) hm (ih Q.parts.card (hn ▸ hm.card_lt) Q rfl)

lemma complete_regular (d : ℕ) : Regular (⊤ : SimpleGraph (Fin (d+1))) univ d := by
  classical
  intro a _
  have hn : graphNeighbors (⊤ : SimpleGraph (Fin (d+1))) univ a = univ.erase a := by
    ext b
    simp only [graphNeighbors,mem_filter,mem_univ,true_and,SimpleGraph.top_adj,mem_erase]
    tauto
  rw [hn,card_erase_of_mem (mem_univ a),card_univ,Fintype.card_fin]
  omega

lemma complete_widths (d : ℕ) : HasWidths (.ofGraph (⊤ : SimpleGraph (Fin (d+1)))) univ 0 d := by
  have hh := complete_continuation (⊥ : Partition (univ : Finset (Fin (d+1))))
  simpa [HasWidths] using hh

/-- The paper starts the TWNGE with K_(d+1), whose sparse width is at most d. -/
theorem regular_seed (d : ℕ) :
    (⊤ : SimpleGraph (Fin (d+1))).Connected ∧
    Regular (⊤ : SimpleGraph (Fin (d+1))) univ d ∧
    sparseTwinWidth (.ofGraph (⊤ : SimpleGraph (Fin (d+1)))) univ ≤ d := by
  exact ⟨SimpleGraph.connected_top,complete_regular d,sparseTwinWidth_le (complete_widths d)⟩

omit [DecidableEq V] in
lemma graphNeighbors_univ [Fintype V] (G : SimpleGraph V) (a : V)
    [Fintype (G.neighborSet a)] : graphNeighbors G univ a = G.neighborFinset a := by
  classical
  ext b
  simp [graphNeighbors]

omit [DecidableEq V] in
/-- A finite connected regular graph of degree at least two contains a cycle. -/
lemma regular_not_acyclic [Fintype V] (G : SimpleGraph V) {d : ℕ} (hd : 2 ≤ d)
    (hreg : Regular G univ d) (hconn : G.Connected) : ¬ G.IsAcyclic := by
  classical
  have : Nonempty V := hconn.nonempty
  obtain ⟨a⟩ := ‹Nonempty V›
  have hn : d ≤ Fintype.card V := by
    have hh := card_filter_le (s := (univ : Finset V)) (p := G.Adj a)
    have hr := hreg a (mem_univ a)
    rw [←hr]
    simpa only [graphNeighbors,card_univ] using hh
  have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  intro hac
  have htree : G.IsTree := ⟨hconn,hac⟩
  obtain ⟨v,hv⟩ := htree.exists_vert_degree_one_of_nontrivial
  have hregv := hreg v (mem_univ v)
  rw [graphNeighbors_univ,G.card_neighborFinset_eq_degree,hv] at hregv
  omega

omit [DecidableEq V] in
lemma regular_shortest_cycle [Fintype V] (G : SimpleGraph V) {d : ℕ} (hd : 2 ≤ d)
    (hreg : Regular G univ d) (hconn : G.Connected) :
    ∃ a, ∃ p : G.Walk a a, p.IsCycle ∧ p.length = G.girth := by
  obtain ⟨a,p,hp,hlen⟩ := SimpleGraph.exists_girth_eq_length.mpr (regular_not_acyclic G hd hreg hconn)
  exact ⟨a,p,hp,hlen.symm⟩

end Paper
