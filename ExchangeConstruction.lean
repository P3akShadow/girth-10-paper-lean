import Agreement

namespace Paper
open Finset
variable {V : Type*} [DecidableEq V] {S : Finset V} {p q : V}

def pairExpansion (hp : p ∈ S) (hq : q ∈ S) (hpq : p ≠ q) : Expansion S (S.erase q) where
  atom := fun x => if x = p then {p, q} else {x}
  nonempty := by intro x _; split_ifs <;> simp
  disjoint := by
    intro u hu v hv huv
    obtain ⟨huq, _⟩ := mem_erase.mp hu
    obtain ⟨hvq, _⟩ := mem_erase.mp hv
    split_ifs with hup hvp hvp
    · exact False.elim (huv (hup.trans hvp.symm))
    · subst u
      simp [disjoint_left, Ne.symm hvp, Ne.symm hvq]
    · subst v
      simp [hup, huq]
    · simp [huv]
  cover := by
    ext x
    simp only [mem_biUnion, mem_erase]
    constructor
    · rintro ⟨u, ⟨huq, hu⟩, hx⟩
      split_ifs at hx with hup
      · rcases mem_insert.mp hx with rfl | hx
        · exact hp
        · exact (mem_singleton.mp hx) ▸ hq
      · exact (mem_singleton.mp hx) ▸ hu
    · intro hx
      by_cases hxq : x = q
      · subst x
        exact ⟨p, ⟨hpq, hp⟩, by simp⟩
      · exact ⟨x, ⟨hxq, hx⟩, by split_ifs <;> simp_all⟩

lemma pairExpansion_merge (hp : p ∈ S) (hq : q ∈ S) (hpq : p ≠ q) :
    ((pairExpansion hp hq hpq).partition ⊥).parts =
      insert ({p} ∪ {q}) ((⊥ : Partition S).parts \ {{p}, {q}}) := by
  ext C
  simp only [Expansion.partition_parts, mem_image, Finpartition.mem_bot_iff,
    mem_insert, mem_sdiff, mem_singleton, not_or]
  constructor
  · rintro ⟨A, ⟨u, hu, rfl⟩, hAC⟩
    have huq := (mem_erase.mp hu).1
    have huS := (mem_erase.mp hu).2
    by_cases hup : u = p
    · subst u
      left
      simpa [Expansion.bag, pairExpansion] using hAC.symm
    · right
      have hUC : {u} = C := by simpa [Expansion.bag, pairExpansion, hup] using hAC
      exact ⟨⟨u, huS, hUC⟩, by simpa [← hUC] using hup, by simpa [← hUC] using huq⟩
  · rintro (rfl | ⟨⟨u, hu, rfl⟩, hup, huq⟩)
    · exact ⟨{p}, ⟨p, mem_erase.mpr ⟨hpq, hp⟩, rfl⟩,
        by simp [Expansion.bag, pairExpansion]⟩
    · have hup' : u ≠ p := by simpa using hup
      have huq' : u ≠ q := by simpa using huq
      exact ⟨{u}, ⟨u, mem_erase.mpr ⟨huq', hu⟩, rfl⟩,
        by simp [Expansion.bag, pairExpansion, hup']⟩

def Twins (T : Trigraph V) (S : Finset V) (p q : V) : Prop :=
  ∀ x ∈ S, x ≠ p → x ≠ q →
    (T.black.Adj p x ↔ T.black.Adj q x) ∧ (T.red.Adj p x ↔ T.red.Adj q x)

def RedLeaf (T : Trigraph V) (S : Finset V) (p q : V) : Prop :=
  (T.black.Adj q p ∨ T.red.Adj q p) ∧
  ∀ x ∈ S, x ≠ p → x ≠ q →
    ¬ T.black.Adj q x ∧ ¬ T.red.Adj q x ∧ ¬ T.black.Adj p x

lemma pairExpansion_agree (T : Trigraph V) (hp : p ∈ S) (hq : q ∈ S) (hpq : p ≠ q)
    (hcases : Twins T S p q ∨ RedLeaf T S p q) :
    Agree ((pairExpansion hp hq hpq).quotient T) T (S.erase q) := by
  classical
  let E := pairExpansion hp hq hpq
  have hpstatus : ∀ x ∈ S.erase q, x ≠ p →
      ((E.quotient T).black.Adj p x ↔ T.black.Adj p x) ∧
      ((E.quotient T).red.Adj p x ↔ T.red.Adj p x) := by
    intro x hx hxp
    obtain ⟨hxq, hxS⟩ := mem_erase.mp hx
    have hdisj : ¬ (T.black.Adj p x ∧ T.red.Adj p x) := fun h => T.exclusive h.1 h.2
    change ((p ≠ x ∧ Black T (E.atom p) (E.atom x)) ↔ T.black.Adj p x) ∧
      ((p ≠ x ∧ Red T (E.atom p) (E.atom x)) ↔ T.red.Adj p x)
    dsimp [E, pairExpansion]
    simp only [ite_eq_right hxp, Ne.symm hxp, Black, Red, Adjacent, mem_singleton]
    rcases hcases with htwins | hleaf
    · obtain ⟨hb, hr⟩ := htwins x hxS hxp hxq
      aesop
    · obtain ⟨hbq, hrq, hbp⟩ := hleaf.2 x hxS hxp hxq
      aesop
  intro a ha b hb
  by_cases hab : a = b
  · subst b
    simp
  by_cases hap : a = p
  · subst a
    exact hpstatus b hb (Ne.symm hab)
  by_cases hbp : b = p
  · subst b
    obtain ⟨hblack, hred⟩ := hpstatus a ha hap
    exact ⟨⟨fun h => ((hblack.mp h.symm).symm), fun h => (hblack.mpr h.symm).symm⟩,
      ⟨fun h => (hred.mp h.symm).symm, fun h => (hred.mpr h.symm).symm⟩⟩
  change ((a ≠ b ∧ Black T (E.atom a) (E.atom b)) ↔ T.black.Adj a b) ∧
    ((a ≠ b ∧ Red T (E.atom a) (E.atom b)) ↔ T.red.Adj a b)
  have hdisj : ¬ (T.black.Adj a b ∧ T.red.Adj a b) := fun h => T.exclusive h.1 h.2
  simp [E, pairExpansion, hap, hbp, hab, Black, Red, Adjacent]
  tauto

end Paper
