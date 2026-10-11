import Lemma02CycleLift
import HighGirthTheorems
import RegularCorollaries
import Lemma12InducedMonotone
import Lemma13Exchange
import Corollary15CubicSparse
import Corollary16MinimalSubcubic

/-!
Every numbered mathematical statement of paper-girth10-twinwidth/paper.tex,
written out in this file in paper order: items 1--16 and Equation (1).
The three numbered conclusions of Lemma 3 and both assertions of each
corollary are included. Each declaration has an explicit statement and a
checked proof, using the supporting modules imported above.

The graph/trigraph and partition notation comes from PaperDefinitions.
`univ` is the whole finite vertex set; `S` is an explicitly specified finite
vertex set. `egirth` and `edist` allow infinity for acyclic graphs and
disconnected vertices. In Lemma 2, `n + 3` is the quotient cycle length.

Definition 7 below includes the initial graph assumptions as well as the
entire sequence construction. Its conversion to `Paper.TWNGE` connects it
to the existing proofs, whose initial graph assumptions are separate.
-/

namespace Paper.Numbered
open Finset

variable {V : Type*} [DecidableEq V] {S : Finset V}

/-- Theorem 1 (`thm:girth`). Every cubic graph of girth greater than 9
has twin-width greater than 4. -/
theorem theorem_01 [Fintype V] [Nonempty V] (G : SimpleGraph V)
    (hg : 9 < G.egirth) (hreg : Regular G univ 3) :
    4 < twinWidth (.ofGraph G) univ :=
  Paper.girth_cubic G hg hreg

/-- Lemma 2 (`lemm:cycle-lift`). A quotient cycle with within-bag distances
at most 2 lifts to an original cycle of length at most the quotient cycle
length plus the sum of those distances. Reachability excludes the special
value 0 that natural-valued `dist` assigns to disconnected vertices. -/
theorem lemma_02 (G : SimpleGraph V) (P : Partition S)
    (n : ℕ) (A : Fin (n + 3) → Finset V)
    (hA : ∀ i, A i ∈ P.parts) (hAi : Function.Injective A)
    (a b : Fin (n + 3) → V) (ha : ∀ i, a i ∈ A i) (hb : ∀ i, b i ∈ A i)
    (cross : ∀ i, G.Adj (b i) (a (i + 1)))
    (reachable : ∀ i, G.Reachable (a i) (b i))
    (short : ∀ i, G.dist (a i) (b i) ≤ 2) :
    ∃ v, ∃ c : G.Walk v v, c.IsCycle ∧
      c.length ≤ (n + 3) + ∑ i, G.dist (a i) (b i) :=
  Paper.cycle_lift_partition G P n A hA hAi a b ha hb cross reachable short

/-- Lemma 3 (`lemm:2-bag-facts`), including all three numbered subclaims:
1. Every two-vertex bag has red degree 2d-2 (`lemm:deg4`).
2. Its two vertices have distance at most 2 (`lemm:dist`).
3. Every singleton has degree d minus its number of black two-vertex
   neighboring bags (`lemm:deg2`). -/
theorem lemma_03 (G : SimpleGraph V) {d s : ℕ} (hd : 3 ≤ d)
    (hg : 8 < G.egirth) (hreg : Regular G S d) {P : Partition S}
    (hseq : PartialSequence (.ofGraph G) (2 * d - 2) s P)
    (small : BagsAtMostTwo P) :
    (∀ A ∈ P.parts, A.card = 2 → redDegree (.ofGraph G) P A = 2 * d - 2) ∧
    (∀ A ∈ P.parts, A.card = 2 → ∀ u ∈ A, ∀ v ∈ A, G.edist u v ≤ 2) ∧
    (∀ u, {u} ∈ P.parts →
      totalDegree (.ofGraph G) P {u} = d - (blackTwoBags G P u).card) :=
  Paper.two_bag_facts G hd hg hreg hseq small

/-- Lemma 4 (`lemm:no-big-bags`). A width-4 sequence in a cubic graph
of girth greater than 9 cannot create the first bag larger than 2. -/
theorem lemma_04 [Fintype V] (G : SimpleGraph V) {s : ℕ}
    (hg : 9 < G.egirth) (hreg : Regular G univ 3)
    {P Q : Partition (univ : Finset V)}
    (hseq : PartialSequence (.ofGraph G) 4 s P)
    (hsmall : BagsAtMostTwo P) (hm : Merge P Q)
    (hbound : Bounded (.ofGraph G) 4 s Q) :
    BagsAtMostTwo Q :=
  Paper.no_big_bags G hg hreg hseq hsmall hm hbound

/-- Theorem 5 (`thm:girth-general`). For d > 3, every d-regular graph
of girth greater than 8 has twin-width greater than 2d-2. -/
theorem theorem_05 [Fintype V] [Nonempty V] (G : SimpleGraph V) {d : ℕ}
    (hd : 3 < d) (hg : 8 < G.egirth) (hreg : Regular G univ d) :
    2 * d - 2 < twinWidth (.ofGraph G) univ :=
  Paper.girth_general G hd hg hreg

/-- Theorem 6 (`thm:lift`). For every d >= 3 and integer g, there is a
connected d-regular graph of girth at least g and sparse twin-width at most
2d-1. The finite vertex type explicitly records the iterated lifts. -/
theorem theorem_06 {d : ℕ} (hd : 3 ≤ d) (g : ℤ) :
    ∃ n, ∃ G : SimpleGraph (TowerVertex (Fin (d + 1)) n),
      G.Connected ∧ Regular G univ d ∧ g ≤ (G.girth : ℤ) ∧
        sparseTwinWidth (.ofGraph G) univ ≤ 2 * d - 1 :=
  Paper.regular_girth_exists_int hd g

/-- Definition 7. A twin-width neutral girth expander (TWNGE).
`TowerVertex V 0 = V` and `TowerVertex V (n+1) = TowerVertex V n × Bool`.
At each step choose an edge xy on a shortest cycle and a symmetric signing.
`girthLift` deletes xy, adds each signed horizontal edge
(u,i)--(v,i xor signing(u,v)), and adds the two vertical edges
(x,false)--(x,true) and (y,false)--(y,true). -/
structure Definition07 (V : Type*) [DecidableEq V] [Fintype V] (d : ℕ) where
  degree_ge_two : 2 ≤ d
  graph : (n : ℕ) → SimpleGraph (TowerVertex V n)
  initial_regular : Regular (graph 0) univ d
  initial_connected : (graph 0).Connected
  initial_sparse_width : sparseTwinWidth (.ofGraph (graph 0)) univ ≤ 2 * d - 1
  x : (n : ℕ) → TowerVertex V n
  y : (n : ℕ) → TowerVertex V n
  signing : (n : ℕ) → Signing (TowerVertex V n)
  shortest : ∀ n, ∃ (a : TowerVertex V n) (p : (graph n).Walk a a),
    p.IsCycle ∧ s(x n, y n) ∈ p.edges ∧ p.length = (graph n).girth
  step : ∀ n, graph (n + 1) = girthLift (graph n) (x n) (y n) (signing n)

/-- Forget only the initial assumptions, which the supporting proofs take
as separate hypotheses. The graphs, chosen edges, and signings are unchanged. -/
def Definition07.toTWNGE [Fintype V] {d : ℕ} (F : Definition07 V d) : Paper.TWNGE V where
  graph := F.graph
  x := F.x
  y := F.y
  signing := F.signing
  shortest := F.shortest
  step := F.step

/-- The final assertion within Definition 7: every graph remains regular
and connected. -/
theorem definition_07_regular_connected [Fintype V] {d : ℕ}
    (F : Definition07 V d) (n : ℕ) :
    Regular (F.graph n) univ d ∧ (F.graph n).Connected :=
  ⟨F.toTWNGE.regular F.initial_regular n,
    F.toTWNGE.connected F.initial_connected n⟩

/-- Lemma 8 (`lemm:lift-girth`). The choices in a TWNGE can be made so
that the resulting sequence has unbounded girth, starting from any graph
satisfying Definition 7's initial assumptions. -/
theorem lemma_08 [Fintype V] (G₀ : SimpleGraph V) {d : ℕ} (hd : 2 ≤ d)
    (hr : Regular G₀ univ d) (hc : G₀.Connected)
    (hw : sparseTwinWidth (.ofGraph G₀) univ ≤ 2 * d - 1) :
    ∃ F : Definition07 V d,
      F.graph 0 = G₀ ∧ ∀ g : ℕ, ∃ n, g ≤ (F.graph n).girth := by
  obtain ⟨F, hstart, hgirth⟩ := Paper.lift_girth G₀ hd hr hc
  refine ⟨{
    degree_ge_two := hd
    graph := F.graph
    initial_regular := hstart.symm ▸ hr
    initial_connected := hstart.symm ▸ hc
    initial_sparse_width := hstart.symm ▸ hw
    x := F.x
    y := F.y
    signing := F.signing
    shortest := F.shortest
    step := F.step }, hstart, hgirth⟩

/-- Lemma 9 (`lemm:lift-stww`). Every graph in a TWNGE has sparse
twin-width at most 2d-1. -/
theorem lemma_09 [Fintype V] {d : ℕ} (F : Definition07 V d) (n : ℕ) :
    sparseTwinWidth (.ofGraph (F.graph n)) univ ≤ 2 * d - 1 :=
  F.toTWNGE.sparseTwinWidth_le F.degree_ge_two F.initial_regular
    F.initial_connected F.initial_sparse_width n

/-- Corollary 10 (`cor:min-cubic`), first assertion. For g >= 10, the
minimum twin-width among connected cubic graphs of girth at least g is 5:
all such graphs have width at least 5, and some such graph attains 5. -/
theorem corollary_10_minimum (g : ℕ) (hg : 10 ≤ g) :
    (∀ (V : Type) [DecidableEq V] [Fintype V] (G : SimpleGraph V),
      G.Connected → Regular G univ 3 → g ≤ G.girth →
        5 ≤ twinWidth (.ofGraph G) univ) ∧
    (∃ n, ∃ G : SimpleGraph (TowerVertex (Fin 4) n),
      G.Connected ∧ Regular G univ 3 ∧ g ≤ G.girth ∧
        twinWidth (.ofGraph G) univ = 5 ∧ sparseTwinWidth (.ofGraph G) univ = 5) :=
  Paper.min_cubic g hg

/-- Corollary 10, second assertion. Every graph of girth at least 10
in a cubic TWNGE has twin-width and sparse twin-width both equal to 5. -/
theorem corollary_10_tower [Fintype V] (F : Definition07 V 3)
    (n : ℕ) (hg : 10 ≤ (F.graph n).girth) :
    twinWidth (.ofGraph (F.graph n)) univ = 5 ∧
      sparseTwinWidth (.ofGraph (F.graph n)) univ = 5 :=
  F.toTWNGE.cubic_width_eq F.initial_regular F.initial_connected F.initial_sparse_width n hg

/-- Corollary 11 (`cor:min-general`), first assertion. For d >= 4 and
g >= 9, the minimum twin-width among connected d-regular graphs of girth
at least g is 2d-1, expressed by a universal bound and an attaining graph. -/
theorem corollary_11_minimum (d g : ℕ) (hd : 4 ≤ d) (hg : 9 ≤ g) :
    (∀ (V : Type) [DecidableEq V] [Fintype V] (G : SimpleGraph V),
      G.Connected → Regular G univ d → g ≤ G.girth →
        2 * d - 1 ≤ twinWidth (.ofGraph G) univ) ∧
    (∃ n, ∃ G : SimpleGraph (TowerVertex (Fin (d + 1)) n),
      G.Connected ∧ Regular G univ d ∧ g ≤ G.girth ∧
        twinWidth (.ofGraph G) univ = 2 * d - 1 ∧
          sparseTwinWidth (.ofGraph G) univ = 2 * d - 1) :=
  Paper.min_general d g hd hg

/-- Corollary 11, second assertion. Every graph of girth at least 9
in a d-regular TWNGE, d >= 4, has both widths equal to 2d-1. -/
theorem corollary_11_tower [Fintype V] {d : ℕ} (hd : 4 ≤ d)
    (F : Definition07 V d) (n : ℕ) (hg : 9 ≤ (F.graph n).girth) :
    twinWidth (.ofGraph (F.graph n)) univ = 2 * d - 1 ∧
      sparseTwinWidth (.ofGraph (F.graph n)) univ = 2 * d - 1 :=
  F.toTWNGE.regular_width_eq hd F.initial_regular F.initial_connected
    F.initial_sparse_width n hg

/-- Lemma 12 (`lemm:induced-monotone`). Both widths are monotone under
induced subtrigraphs; the subtrigraph is represented by U ⊆ S. -/
theorem lemma_12 (T : Trigraph V) {U : Finset V} (hUS : U ⊆ S) :
    twinWidth T U ≤ twinWidth T S ∧ sparseTwinWidth T U ≤ sparseTwinWidth T S :=
  Paper.induced_monotone T hUS

/-- Lemma 13 (`lemm:exchange`). At any quotient in a contraction sequence,
two distinct bags can be merged next, preserving both width bounds, if:
1. they have identical black and red neighborhoods outside each other; or
2. A is B's only neighbor and all other neighbors of A are red.
The continuation is replaced only after P, so the prefix stays unchanged. -/
theorem lemma_13 (T : Trigraph V) {P : Partition S} {A B : Finset V} {w s : ℕ}
    (h : Continuation T w s P) (hA : A ∈ P.parts) (hB : B ∈ P.parts) (hAB : A ≠ B)
    (hcases : Twins ((partitionExpansion P).quotient T) P.parts A B ∨
      RedLeaf ((partitionExpansion P).quotient T) P.parts A B) :
    ∃ Q : Partition S,
      Q.parts = insert (A ∪ B) (P.parts \ {A, B}) ∧
      Bounded T w s P ∧ Continuation T w s Q :=
  Paper.exchange T h hA hB hAB hcases

/-- Proposition 14 (`prop:sparse-bounds`). Both sparse twin-width bounds
for graphs of maximum degree at most d, where d >= 3. -/
theorem proposition_14 (G : SimpleGraph V) {d : ℕ}
    (hd : 3 ≤ d) (hdeg : MaxDegree G S d) :
    sparseTwinWidth (.ofGraph G) S ≤ max (twinWidth (.ofGraph G) S + 1) ((d - 1)^2) ∧
    sparseTwinWidth (.ofGraph G) S ≤ max (twinWidth (.ofGraph G) S) ((d - 1)^2 + 1) :=
  Paper.sparse_bounds G hd hdeg

/-- Equation (1) (`eq:counting`), in the proof of Proposition 14:
degree(A) <= p(d-q)+b, where p is the bag size, q counts vertices in its
black neighboring bags, and b is its black degree. -/
theorem equation_01 (G : SimpleGraph V) {d : ℕ} (hdeg : MaxDegree G S d)
    (P : Partition S) {A : Finset V} (hA : A ∈ P.parts) :
    totalDegree (.ofGraph G) P A ≤
      A.card * (d - (blackVertices (.ofGraph G) P A).card) +
        blackDegree (.ofGraph G) P A :=
  Paper.degree_counting_bound G hdeg P hA

/-- Corollary 15 (`cor:cubic-sparse`), including both implications.
For maximum degree at most 3, twin-width at least 5 implies equality of
the two widths, as does sparse twin-width at least 6. -/
theorem corollary_15 (G : SimpleGraph V) (hdeg : MaxDegree G S 3) :
    (5 ≤ twinWidth (.ofGraph G) S →
      sparseTwinWidth (.ofGraph G) S = twinWidth (.ofGraph G) S) ∧
    (6 ≤ sparseTwinWidth (.ofGraph G) S →
      twinWidth (.ofGraph G) S = sparseTwinWidth (.ofGraph G) S) :=
  ⟨Paper.cubic_sparse_of_twinWidth G hdeg,
    fun hw => (Paper.cubic_sparse_of_sparseTwinWidth G hdeg hw).symm⟩

/-- Corollary 16. Every minimum-order subcubic graph with twin-width at
least six is cubic and has girth at least five. `SubcubicOrderMinimal`
quantifies over all smaller finite simple subcubic graphs, rather than
only the induced subgraphs of G. -/
theorem corollary_16 [Fintype V] (G : SimpleGraph V)
    (hdeg : MaxDegree G univ 3) (hw : 6 ≤ twinWidth (.ofGraph G) univ)
    (hmin : SubcubicOrderMinimal (univ : Finset V) 6) :
    5 ≤ G.egirth ∧ Regular G univ 3 :=
  Paper.minimum_subcubic_cubic_girth G hdeg (by omega) hw hmin

end Paper.Numbered
