import Mathlib.Order.Partition.Finpartition
import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Tactic

/-!
Definitions transcribed from Section 2 of the paper.

Vertices live in an ambient type; `S` is the finite vertex set. This lets an
induced subtrigraph use the same edge relations and a smaller vertex set.
Partitions consist of nonempty, pairwise disjoint bags covering `S`.
-/

namespace Paper

structure Trigraph (V : Type*) where
  black : SimpleGraph V
  red : SimpleGraph V
  exclusive : ∀ ⦃u v⦄, black.Adj u v → ¬ red.Adj u v

def Trigraph.ofGraph {V : Type*} (G : SimpleGraph V) : Trigraph V :=
  ⟨G, ⊥, by simp⟩

variable {V : Type*} [DecidableEq V]

abbrev Partition (S : Finset V) := Finpartition S

def Black (T : Trigraph V) (A B : Finset V) : Prop :=
  ∀ a ∈ A, ∀ b ∈ B, T.black.Adj a b

def Adjacent (T : Trigraph V) (A B : Finset V) : Prop :=
  ∃ a ∈ A, ∃ b ∈ B, T.black.Adj a b ∨ T.red.Adj a b

def Red (T : Trigraph V) (A B : Finset V) : Prop :=
  Adjacent T A B ∧ ¬ Black T A B

noncomputable def neighbors (R : Finset V → Finset V → Prop)
    {S : Finset V} (P : Partition S) (A : Finset V) : Finset (Finset V) := by
  classical
  exact P.parts.filter fun B => B ≠ A ∧ R A B

noncomputable def redDegree (T : Trigraph V) {S : Finset V}
    (P : Partition S) (A : Finset V) : ℕ :=
  (neighbors (Red T) P A).card

noncomputable def totalDegree (T : Trigraph V) {S : Finset V}
    (P : Partition S) (A : Finset V) : ℕ :=
  (neighbors (Adjacent T) P A).card

def Bounded (T : Trigraph V) (w s : ℕ) {S : Finset V} (P : Partition S) : Prop :=
  ∀ A ∈ P.parts, redDegree T P A ≤ w ∧ totalDegree T P A ≤ s

/-- Exactly one of the binary bag merges in Section 2. -/
def Merge {S : Finset V} (P Q : Partition S) : Prop :=
  ∃ A ∈ P.parts, ∃ B ∈ P.parts, A ≠ B ∧
    Q.parts = insert (A ∪ B) (P.parts \ {A, B})

/-- A complete sequence beginning at `P`, with simultaneous width bounds.
The singleton (or empty) final partition is included in the bounds. -/
inductive Continuation (T : Trigraph V) (w s : ℕ) {S : Finset V} :
    Partition S → Prop
  | done {P} : Bounded T w s P → P.parts.card ≤ 1 → Continuation T w s P
  | step {P Q} : Bounded T w s P → Merge P Q → Continuation T w s Q →
      Continuation T w s P

def HasWidths (T : Trigraph V) (S : Finset V) (w s : ℕ) : Prop :=
  Continuation T w s (⊥ : Partition S)

noncomputable def twinWidth (T : Trigraph V) (S : Finset V) : ℕ :=
  sInf {w | ∃ s, HasWidths T S w s}

noncomputable def sparseTwinWidth (T : Trigraph V) (S : Finset V) : ℕ :=
  sInf {s | ∃ w, HasWidths T S w s}

end Paper
