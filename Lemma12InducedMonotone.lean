import Merging
import Restriction

/-!
Lemma 12 (`lemm:induced-monotone`).
Source: sections/05-Twinwidth-vs-Sparse-Twinwidth.tex:17–27.

The four steps below follow the four sentences of the paper's proof.
The restriction and degree calculations are expanded in `Restriction`;
the existence of a witnessing sequence follows from the definitions in
Section 2 and is checked in `Merging`.
-/

namespace Paper

variable {V : Type*} [DecidableEq V] {S U : Finset V}

theorem continuation_induced {T : Trigraph V} {w s : ℕ} {P : Partition S}
    (h : Continuation T w s P) (hUS : U ⊆ S) :
    Continuation T w s (P.restrict hUS) := by
  -- Line 23: intersect every block with V(T'), discarding empty blocks.
  induction h with
  | done hwidth hfinal =>
    exact .done (bounded_restrict hwidth hUS)
      ((restrict_card_le _ hUS).trans hfinal)
  | step hwidth hmerge _ ih =>
    -- Lines 23–24: discard repeated partitions; otherwise this is one merge.
    rcases merge_restrict hmerge hUS with hsame | hstep
    · exact hsame ▸ ih
    -- Lines 25–26: each remaining neighbor has a distinct original parent;
    -- red edges and edges of either color lift to the original quotient.
    · exact .step (bounded_restrict hwidth hUS) hstep ih

theorem hasWidths_induced {T : Trigraph V} {w s : ℕ}
    (h : HasWidths T S w s) (hUS : U ⊆ S) : HasWidths T U w s := by
  have hrestricted := continuation_induced h hUS
  simpa only [restrict_bot, HasWidths] using hrestricted

/-- Lemma 12, with an induced subtrigraph represented by its vertex subset. -/
theorem induced_monotone (T : Trigraph V) (hUS : U ⊆ S) :
    twinWidth T U ≤ twinWidth T S ∧ sparseTwinWidth T U ≤ sparseTwinWidth T S := by
  -- Line 23: take a witnessing sequence of T for each of the two widths.
  obtain ⟨s, htww⟩ := twinWidth_witness T S
  obtain ⟨w, hstww⟩ := sparseTwinWidth_witness T S
  -- Lines 23–26: restrict those sequences; both degree bounds survive.
  exact ⟨twinWidth_le (hasWidths_induced htww hUS),
    sparseTwinWidth_le (hasWidths_induced hstww hUS)⟩

end Paper
