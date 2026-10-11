import LiftConstruction

/-! Lemma 8's averaging argument. Toggling a single edge of a nonempty cycle
reverses its parity, so exactly half of the signings give two surviving lifts.
Summing over the cycles gives a signing with at most the original cycle count. -/

namespace Paper
open Finset
variable {E : Type*} [DecidableEq E]

local instance : Std.Commutative Bool.xor := ⟨Bool.xor_comm⟩

def signingParity (σ : E → Bool) (C : Finset E) : Bool := C.fold Bool.xor false σ

def toggleSigning (σ : E → Bool) (e : E) : E → Bool :=
  fun a => if a = e then !(σ a) else σ a

lemma toggleSigning_involutive (e : E) : Function.Involutive (toggleSigning (E := E) · e) := by
  intro σ
  funext a
  by_cases h : a = e <;> simp [toggleSigning,h]

lemma signingParity_erase (σ : E → Bool) {C : Finset E} {e : E} (he : e ∈ C) :
    signingParity σ C = (σ e ^^ signingParity σ (C.erase e)) := by
  conv_lhs => rw [← insert_erase he]
  exact fold_insert (notMem_erase _ _)

lemma signingParity_toggle (σ : E → Bool) {C : Finset E} {e : E} (he : e ∈ C) :
    signingParity (toggleSigning σ e) C = !(signingParity σ C) := by
  have herase : signingParity (toggleSigning σ e) (C.erase e) = signingParity σ (C.erase e) := by
    apply fold_congr
    intro a ha
    simp [toggleSigning,(mem_erase.mp ha).1]
  rw [signingParity_erase _ he,signingParity_erase σ he,herase]
  simp only [toggleSigning,ite_true]
  cases σ e <;> cases signingParity σ (C.erase e) <;> rfl

lemma signingParity_balanced [Fintype E] {C : Finset E} (hne : C.Nonempty) :
    2 * ((univ : Finset (E → Bool)).filter (fun σ => signingParity σ C = false)).card =
      Fintype.card (E → Bool) := by
  classical
  obtain ⟨e,he⟩ := hne
  let even := (univ : Finset (E → Bool)).filter (fun σ => signingParity σ C = false)
  let odd := (univ : Finset (E → Bool)).filter (fun σ => signingParity σ C = true)
  have hcard : even.card = odd.card := by
    apply card_bij (fun σ _ => toggleSigning σ e)
    · intro σ hσ
      have hpar := (mem_filter.mp hσ).2
      simp only [odd,mem_filter,mem_univ,true_and,signingParity_toggle σ he,hpar]
      rfl
    · intro σ _ τ _ heq
      exact (toggleSigning_involutive e).injective heq
    · intro τ hτ
      have hpar := (mem_filter.mp hτ).2
      refine ⟨toggleSigning τ e,?_,toggleSigning_involutive e τ⟩
      simp only [even,mem_filter,mem_univ,true_and,signingParity_toggle τ he,hpar]
      rfl
  have hdisj : Disjoint even odd := by
    apply disjoint_left.mpr
    intro σ hσ hσ'
    have h0 := (mem_filter.mp hσ).2
    have h1 := (mem_filter.mp hσ').2
    exact Bool.false_ne_true (h0.symm.trans h1)
  have hcover : even ∪ odd = univ := by
    ext σ
    cases hp : signingParity σ C <;> simp [even,odd,hp]
  have hsum := card_union_of_disjoint hdisj
  rw [hcover,card_univ,hcard] at hsum
  change 2 * even.card = _
  omega

noncomputable def survivingCycleCount (cycles : Finset (Finset E)) (σ : E → Bool) : ℕ := by
  classical
  exact 2 * (cycles.filter (fun C => signingParity σ C = false)).card

lemma sum_survivingCycleCount [Fintype E] (cycles : Finset (Finset E))
    (hne : ∀ C ∈ cycles, C.Nonempty) :
    (∑ σ : E → Bool, survivingCycleCount cycles σ) = Fintype.card (E → Bool) * cycles.card := by
  classical
  have hpoint : ∀ σ, survivingCycleCount cycles σ =
      ∑ C ∈ cycles, if signingParity σ C = false then 2 else 0 := by
    intro σ
    simp [survivingCycleCount,← sum_filter,Nat.mul_comm]
  simp_rw [hpoint]
  rw [sum_comm]
  calc
    (∑ C ∈ cycles, ∑ σ : E → Bool, if signingParity σ C = false then 2 else 0) =
        ∑ _C ∈ cycles, Fintype.card (E → Bool) := by
      apply sum_congr rfl
      intro C hC
      have hh := signingParity_balanced (hne C hC)
      simpa [← sum_filter,Nat.mul_comm] using hh
    _ = _ := by simp [Nat.mul_comm]

/-- The probabilistic method in Lemma 8, expressed as a finite sum over all
independent uniform edge signings. -/
theorem exists_signing_few_surviving [Fintype E] (cycles : Finset (Finset E))
    (hne : ∀ C ∈ cycles, C.Nonempty) :
    ∃ σ : E → Bool, survivingCycleCount cycles σ ≤ cycles.card := by
  classical
  by_contra h
  push Not at h
  have hlt : (∑ _σ : E → Bool, cycles.card) < ∑ σ : E → Bool, survivingCycleCount cycles σ := by
    apply sum_lt_sum_of_nonempty
    · exact univ_nonempty
    · intro σ _
      exact h σ
  rw [sum_survivingCycleCount cycles hne] at hlt
  simp only [sum_const,card_univ,smul_eq_mul] at hlt
  omega

/-- The same expectation calculation with cycles indexed by a chosen root
and orientation. Different indices may describe the same edge set. -/
theorem exists_signing_few_surviving_indexed [Fintype E] {I : Type*}
    (cycles : Finset I) (edges : I → Finset E) (hne : ∀ C ∈ cycles, (edges C).Nonempty) :
    ∃ σ : E → Bool, 2 * (cycles.filter (fun C => signingParity σ (edges C) = false)).card ≤ cycles.card := by
  classical
  let count := fun σ : E → Bool => 2 * (cycles.filter (fun C => signingParity σ (edges C) = false)).card
  have hpoint : ∀ σ, count σ = ∑ C ∈ cycles, if signingParity σ (edges C) = false then 2 else 0 := by
    intro σ
    simp [count,← sum_filter,Nat.mul_comm]
  have hsum : (∑ σ : E → Bool, count σ) = Fintype.card (E → Bool) * cycles.card := by
    simp_rw [hpoint]
    rw [sum_comm]
    calc
      (∑ C ∈ cycles, ∑ σ : E → Bool, if signingParity σ (edges C) = false then 2 else 0) =
          ∑ _C ∈ cycles, Fintype.card (E → Bool) := by
        apply sum_congr rfl
        intro C hC
        simpa [← sum_filter,Nat.mul_comm] using signingParity_balanced (hne C hC)
      _ = _ := by simp [Nat.mul_comm]
  by_contra h
  push Not at h
  have hlt : (∑ _σ : E → Bool, cycles.card) < ∑ σ : E → Bool, count σ := by
    apply sum_lt_sum_of_nonempty
    · exact univ_nonempty
    · intro σ _
      exact h σ
  rw [hsum] at hlt
  simp only [sum_const,card_univ,smul_eq_mul] at hlt
  omega

end Paper
