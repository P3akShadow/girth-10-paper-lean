import CycleLiftForest

/-!
Lemma 2 (`lemm:cycle-lift`). The proof follows the paper:
construct the union H of the chosen shortest paths and crossing edges; assume
H is a forest; identify each pair of selected endpoints; the crossing edges
then form a cycle, a contradiction; finally count H's edges.

We allow an ambient vertex type containing vertices outside H, hence express
"H is not a tree" as "the edge-supported graph H is not a forest". This avoids
an irrelevant connectedness assertion about unused ambient vertices.
-/
namespace Paper
open SimpleGraph Finset
open CycleLift
variable {V : Type*} [DecidableEq V]

/-- Lemma 2, with the chosen paths explicit. Index `n` represents a cycle of
length `n + 3`; this records that a simple quotient cycle has at least three
vertices. `Separated` is precisely disjointness of its chosen endpoint pairs. -/
theorem cycle_lift (G : SimpleGraph V) (n : ℕ)
    (a b : Fin (n + 3) → V) (hsep : Separated a b)
    (cross : ∀ i, G.Adj (b i) (a (i + 1)))
    (paths : ∀ i, G.Walk (a i) (b i))
    (short : ∀ i, (paths i).length ≤ 2) :
    ∃ v, ∃ c : G.Walk v v, c.IsCycle ∧ c.length ≤ (n + 3) + ∑ i, (paths i).length := by
  classical
  -- H consists of the internal paths and the crossing edges of the traversal.
  let E₁ := univ.biUnion fun i => (paths i).edges.toFinset
  let E₂ := univ.image fun i => s(b i, a (i + 1))
  let E := E₁ ∪ E₂
  let H : SimpleGraph V := fromEdgeSet (E : Set (Sym2 V))
  have hE : ∀ e ∈ E, e ∈ G.edgeSet := by
    intro e he
    rcases mem_union.mp he with he | he
    · obtain ⟨i, _, hei⟩ := mem_biUnion.mp he
      exact (paths i).edges_subset_edgeSet (List.mem_toFinset.mp hei)
    · obtain ⟨i, _, rfl⟩ := mem_image.mp he
      exact (G.mem_edgeSet).mpr (cross i)
  have hHE : H.edgeSet = (E : Set (Sym2 V)) := by
    dsimp only [H]
    rw [edgeSet_fromEdgeSet]
    ext e
    exact ⟨And.left, fun he => ⟨he, G.not_isDiag_of_mem_edgeSet (hE e he)⟩⟩
  have hHG : H ≤ G := edgeSet_subset_edgeSet.mp (by
    intro e he
    exact hE e (by simpa only [hHE, mem_coe] using he))
  have hpaths : ∀ i, ∀ e ∈ (paths i).edges, e ∈ H.edgeSet := by
    intro i e he
    rw [hHE]
    exact mem_union_left _ (mem_biUnion.mpr ⟨i, mem_univ i, List.mem_toFinset.mpr he⟩)
  have hshort : ∀ i, Near H (a i) (b i) := by
    intro i
    exact near_of_walk ((paths i).transfer H (hpaths i)) (by simpa using short i)
  have hcross : ∀ i, H.Adj (b i) (a (i + 1)) := by
    intro i
    apply (H.mem_edgeSet).mp
    rw [hHE]
    exact mem_union_right _ (mem_image.mpr ⟨i, mem_univ i, rfl⟩)
  -- Identifying distance-at-most-two pairs preserves a forest. The resulting
  -- graph contains the quotient cycle, so H was not a forest.
  have hcycle : ¬ H.IsAcyclic := cycle_crossing_not_isAcyclic n a b hsep hshort hcross
  obtain ⟨v, c, hc⟩ : ∃ v, ∃ c : H.Walk v v, c.IsCycle := by
    simpa only [SimpleGraph.IsAcyclic, not_forall, Classical.not_not] using hcycle
  -- The union contains at most the sum of the path lengths plus n+3 edges.
  have hE₁ : E₁.card ≤ ∑ i, (paths i).length := by
    calc
      E₁.card ≤ ∑ i, (paths i).edges.toFinset.card := card_biUnion_le
      _ ≤ ∑ i, (paths i).length := sum_le_sum fun i _ => by
        simpa using (paths i).edges.toFinset_card_le
  have hE₂ : E₂.card ≤ n + 3 := by
    simpa [E₂] using (card_image_le (s := (univ : Finset (Fin (n + 3))))
      (f := fun i => s(b i, a (i + 1))))
  have hcard : E.card ≤ (n + 3) + ∑ i, (paths i).length := by
    have h := card_union_le E₁ E₂
    dsimp [E] at *
    omega
  let : Fintype H.edgeSet := (show H.edgeSet.Finite by rw [hHE]; exact E.finite_toSet).fintype
  have hEF : H.edgeFinset = E := by ext e; simp [mem_edgeFinset, hHE]
  refine ⟨v, c.mapLe hHG, hc.mapLe hHG, ?_⟩
  rw [Walk.length_mapLe]
  exact (hc.isCircuit.isTrail.length_le_card_edgeFinset.trans (hEF ▸ hcard))

/-- The distance formulation of Lemma 2. Reachability records the finite
meaning of distance in the paper: Mathlib's natural-valued `dist` also returns
zero for disconnected vertices, while mathematical distance is infinite. -/
theorem cycle_lift_distance (G : SimpleGraph V) (n : ℕ)
    (a b : Fin (n + 3) → V) (hsep : Separated a b)
    (cross : ∀ i, G.Adj (b i) (a (i + 1)))
    (reachable : ∀ i, G.Reachable (a i) (b i))
    (short : ∀ i, G.dist (a i) (b i) ≤ 2) :
    ∃ v, ∃ c : G.Walk v v, c.IsCycle ∧
      c.length ≤ (n + 3) + ∑ i, G.dist (a i) (b i) := by
  choose paths hpaths using fun i => (reachable i).exists_walk_length_eq_dist
  simpa [hpaths] using cycle_lift G n a b hsep cross paths (by simpa [hpaths] using short)

/-- Disjoint bags provide exactly the endpoint separation used above. -/
lemma separated_of_partition {S : Finset V} (P : Partition S) {I : Type*}
    (A : I → Finset V) (hA : ∀ i, A i ∈ P.parts) (hAi : Function.Injective A)
    (a b : I → V) (ha : ∀ i, a i ∈ A i) (hb : ∀ i, b i ∈ A i) : Separated a b := by
  intro i j hij
  have hd := Finset.disjoint_left.mp (P.disjoint (hA i) (hA j) (hAi.ne hij))
  exact ⟨fun h => hd (ha i) (h ▸ ha j), fun h => hd (ha i) (h ▸ hb j),
    fun h => hd (hb i) (h ▸ ha j), fun h => hd (hb i) (h ▸ hb j)⟩

/-- Lemma 2 with the paper's partition and cyclically ordered distinct bags
explicit. Distances are measured in G, so the shortest internal paths may
pass through other bags, exactly as in the paper's proof. -/
theorem cycle_lift_partition (G : SimpleGraph V) {S : Finset V} (P : Partition S)
    (n : ℕ) (A : Fin (n + 3) → Finset V)
    (hA : ∀ i, A i ∈ P.parts) (hAi : Function.Injective A)
    (a b : Fin (n + 3) → V) (ha : ∀ i, a i ∈ A i) (hb : ∀ i, b i ∈ A i)
    (cross : ∀ i, G.Adj (b i) (a (i + 1)))
    (reachable : ∀ i, G.Reachable (a i) (b i))
    (short : ∀ i, G.dist (a i) (b i) ≤ 2) :
    ∃ v, ∃ c : G.Walk v v, c.IsCycle ∧
      c.length ≤ (n + 3) + ∑ i, G.dist (a i) (b i) :=
  cycle_lift_distance G n a b (separated_of_partition P A hA hAi a b ha hb)
    cross reachable short

/-- A useful equivalent application of Lemma 2, using the extended distance
so that disconnected vertices are handled without an extra hypothesis. -/
theorem cycle_lift_egirth (G : SimpleGraph V) (n : ℕ)
    (a b : Fin (n + 3) → V) (hsep : Separated a b)
    (cross : ∀ i, G.Adj (b i) (a (i + 1))) (d : Fin (n + 3) → ℕ)
    (distance : ∀ i, G.edist (a i) (b i) ≤ d i) (short : ∀ i, d i ≤ 2) :
    G.egirth ≤ ((n + 3) + ∑ i, d i : ℕ) := by
  have hfinite : ∀ i, G.edist (a i) (b i) ≠ ⊤ := fun i =>
    ne_top_of_le_ne_top (by simp) (distance i)
  choose paths hpaths using fun i => G.exists_walk_of_edist_ne_top (hfinite i)
  have hlen : ∀ i, (paths i).length ≤ d i := by
    intro i
    exact ENat.natCast_le_natCast.mp (by simpa [hpaths i] using distance i)
  obtain ⟨v, c, hc, hcl⟩ := cycle_lift G n a b hsep cross paths (fun i => (hlen i).trans (short i))
  apply hc.egirth_le_length.trans
  exact_mod_cast hcl.trans (Nat.add_le_add_left (sum_le_sum fun i _ => hlen i) _)

/-- A distance-two quotient cycle has an original cycle of length at most
three times its length, saving two for every selected equal endpoint pair. -/
theorem cycle_lift_near (G : SimpleGraph V) (n : ℕ)
    (a b : Fin (n + 3) → V) (hsep : Separated a b)
    (cross : ∀ i, G.Adj (b i) (a (i + 1)))
    (near : ∀ i, Near G (a i) (b i)) :
    G.egirth ≤ ((n + 3) + ∑ i, if a i = b i then 0 else 2 : ℕ) := by
  classical
  apply cycle_lift_egirth G n a b hsep cross
  · intro i
    by_cases heq : a i = b i
    · simp [heq]
    · obtain ⟨p, _, hp⟩ := (near i).exists_path
      simpa [heq] using p.edist_le.trans (show (p.length : ℕ∞) ≤ (2 : ℕ) by exact_mod_cast hp)
  · intro i
    split_ifs <;> omega

end Paper
