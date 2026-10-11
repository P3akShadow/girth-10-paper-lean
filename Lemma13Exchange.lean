import Lemma12InducedMonotone
import ExchangeConstruction

/-!
Lemma 13 (`lemm:exchange`).
Source: sections/05-Twinwidth-vs-Sparse-Twinwidth.tex:29–48.

`exchange` replaces the continuation at the specified partition. Therefore
the prefix of the given sequence can be retained verbatim. The result gives
the prescribed next partition and a continuation with both original bounds.
-/

namespace Paper
open Finset
variable {V : Type*} [DecidableEq V] {S : Finset V}

private theorem exchange_vertices (T : Trigraph V) {p q : V} {w s : ℕ}
    (h : HasWidths T S w s) (hp : p ∈ S) (hq : q ∈ S) (hpq : p ≠ q)
    (hcases : Twins T S p q ∨ RedLeaf T S p q) :
    ∃ R : Partition S,
      R.parts = insert ({p} ∪ {q}) ((⊥ : Partition S).parts \ {{p}, {q}}) ∧
      Continuation T w s R := by
  -- Line 40: form T* by merging p and q, retaining p as the name of the bag.
  let E := pairExpansion hp hq hpq
  -- Lines 41–44: in either case T* has exactly the colors of T - q.
  -- `pairExpansion_agree` explicitly checks the twin and red-leaf cases.
  have hstatus := pairExpansion_agree T hp hq hpq hcases
  -- Lines 45–46: restrict the given continuation to all vertices except q.
  have hrestricted := hasWidths_induced h (erase_subset q S)
  have hrenamed : HasWidths (E.quotient T) (S.erase q) w s :=
    hstatus.symm.continuation hrestricted
  -- Line 47: restore the name p ∪ q and prepend the prescribed merge.
  exact ⟨E.partition ⊥, pairExpansion_merge hp hq hpq, E.continuation T hrenamed⟩

/-- Lemma 13 at the current quotient partition. The untouched prefix can be
followed by the indicated binary merge and the resulting continuation. -/
theorem exchange (T : Trigraph V) {P : Partition S} {A B : Finset V} {w s : ℕ}
    (h : Continuation T w s P) (hA : A ∈ P.parts) (hB : B ∈ P.parts) (hAB : A ≠ B)
    (hcases : Twins ((partitionExpansion P).quotient T) P.parts A B ∨
      RedLeaf ((partitionExpansion P).quotient T) P.parts A B) :
    ∃ Q : Partition S,
      Q.parts = insert (A ∪ B) (P.parts \ {A, B}) ∧
      Bounded T w s P ∧ Continuation T w s Q := by
  -- The quotient-composition observation preceding Lemma 12 identifies the
  -- remainder of the original sequence with a sequence of the current T.
  let E := partitionExpansion P
  have hquot : HasWidths (E.quotient T) P.parts w s := by
    apply (E.continuation_iff T ⊥ w s).mp
    simpa only [E, partitionExpansion_bot] using h
  -- Follow lines 40–47 of the paper on the vertices of the current quotient.
  obtain ⟨R, hRparts, hRcont⟩ := exchange_vertices (E.quotient T) hquot hA hB hAB hcases
  have hAs : {A} ∈ (⊥ : Partition P.parts).parts :=
    Finpartition.mem_bot_iff.mpr ⟨A, hA, rfl⟩
  have hBs : {B} ∈ (⊥ : Partition P.parts).parts :=
    Finpartition.mem_bot_iff.mpr ⟨B, hB, rfl⟩
  have hparts := E.merge_parts hAs hBs hRparts
  refine ⟨E.partition R, ?_, h.bounded, E.continuation T hRcont⟩
  have hEA : E.bag {A} = A := by simp [E, Expansion.bag, partitionExpansion]
  have hEB : E.bag {B} = B := by simp [E, Expansion.bag, partitionExpansion]
  have hEP : E.partition ⊥ = P := partitionExpansion_bot P
  simpa only [hEA, hEB, hEP] using hparts

end Paper
