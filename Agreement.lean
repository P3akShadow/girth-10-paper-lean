import Expansion

namespace Paper
open Finset
variable {V : Type*} [DecidableEq V] {S : Finset V}

def Agree (T T' : Trigraph V) (S : Finset V) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S,
    (T.black.Adj a b ↔ T'.black.Adj a b) ∧ (T.red.Adj a b ↔ T'.red.Adj a b)

omit [DecidableEq V] in
lemma Agree.black {T T' : Trigraph V} (h : Agree T T' S)
    {A B : Finset V} (hA : A ⊆ S) (hB : B ⊆ S) : Black T A B ↔ Black T' A B := by
  constructor
  · intro hb a ha b hb'
    exact (h a (hA ha) b (hB hb')).1.mp (hb a ha b hb')
  · intro hb a ha b hb'
    exact (h a (hA ha) b (hB hb')).1.mpr (hb a ha b hb')

omit [DecidableEq V] in
lemma Agree.adjacent {T T' : Trigraph V} (h : Agree T T' S)
    {A B : Finset V} (hA : A ⊆ S) (hB : B ⊆ S) : Adjacent T A B ↔ Adjacent T' A B := by
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    exact ⟨a, ha, b, hb, hab.imp (h a (hA ha) b (hB hb)).1.mp
      (h a (hA ha) b (hB hb)).2.mp⟩
  · rintro ⟨a, ha, b, hb, hab⟩
    exact ⟨a, ha, b, hb, hab.imp (h a (hA ha) b (hB hb)).1.mpr
      (h a (hA ha) b (hB hb)).2.mpr⟩

omit [DecidableEq V] in
lemma Agree.red {T T' : Trigraph V} (h : Agree T T' S)
    {A B : Finset V} (hA : A ⊆ S) (hB : B ⊆ S) : Red T A B ↔ Red T' A B := by
  simp only [Red, h.adjacent hA hB, h.black hA hB]

lemma neighbor_card_congr (P : Partition S) {R R' : Finset V → Finset V → Prop}
    (h : ∀ A ∈ P.parts, ∀ B ∈ P.parts, R A B ↔ R' A B)
    {A : Finset V} (hA : A ∈ P.parts) :
    (neighbors R P A).card = (neighbors R' P A).card := by
  classical
  congr 1
  exact filter_congr fun B hB => and_congr_right fun _ => h A hA B hB

lemma Agree.bounded {T T' : Trigraph V} (h : Agree T T' S) (P : Partition S) (w s : ℕ) :
    Bounded T w s P ↔ Bounded T' w s P := by
  have hr : ∀ A ∈ P.parts, redDegree T P A = redDegree T' P A := fun _ hA =>
    neighbor_card_congr P (fun A hA B hB => h.red (P.subset hA) (P.subset hB)) hA
  have ht : ∀ A ∈ P.parts, totalDegree T P A = totalDegree T' P A := fun _ hA =>
    neighbor_card_congr P (fun A hA B hB => h.adjacent (P.subset hA) (P.subset hB)) hA
  constructor
  · intro hb A hA
    obtain ⟨hred, htotal⟩ := hb A hA
    exact ⟨hr A hA ▸ hred, ht A hA ▸ htotal⟩
  · intro hb A hA
    obtain ⟨hred, htotal⟩ := hb A hA
    exact ⟨(hr A hA).symm ▸ hred, (ht A hA).symm ▸ htotal⟩

lemma Agree.continuation {T T' : Trigraph V} (h : Agree T T' S)
    {P : Partition S} {w s : ℕ} (hc : Continuation T w s P) : Continuation T' w s P := by
  induction hc with
  | done hb hf => exact .done ((h.bounded ..).mp hb) hf
  | step hb hm _ ih => exact .step ((h.bounded ..).mp hb) hm ih

omit [DecidableEq V] in
lemma Agree.symm {T T' : Trigraph V} (h : Agree T T' S) : Agree T' T S := by
  intro a ha b hb
  exact ⟨(h a ha b hb).1.symm, (h a ha b hb).2.symm⟩

lemma Continuation.bounded {T : Trigraph V} {P : Partition S} {w s : ℕ}
    (h : Continuation T w s P) : Bounded T w s P := by
  cases h with
  | done hb _ => exact hb
  | step hb _ _ => exact hb

end Paper
