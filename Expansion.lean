import Merging

/-! The quotient-of-a-quotient observation preceding Lemma 12, Section 5.
An expansion replaces each quotient vertex by its original nonempty bag. -/

namespace Paper
open Finset
variable {V W : Type*} [DecidableEq V] [DecidableEq W]
variable {S : Finset V} {U : Finset W}

structure Expansion (S : Finset V) (U : Finset W) where
  atom : W → Finset V
  nonempty : ∀ u ∈ U, (atom u).Nonempty
  disjoint : ∀ u ∈ U, ∀ v ∈ U, u ≠ v → Disjoint (atom u) (atom v)
  cover : U.biUnion atom = S

def Expansion.bag (E : Expansion S U) (A : Finset W) : Finset V := A.biUnion E.atom

lemma Expansion.bag_union (E : Expansion S U) (A B : Finset W) :
    E.bag (A ∪ B) = E.bag A ∪ E.bag B := by
  ext x
  simp [Expansion.bag, or_and_right, exists_or]

lemma Expansion.atom_unique (E : Expansion S U) {u v : W}
    (hu : u ∈ U) (hv : v ∈ U) {x : V} (hxu : x ∈ E.atom u) (hxv : x ∈ E.atom v) :
    u = v := by
  by_contra hne
  exact disjoint_left.mp (E.disjoint u hu v hv hne) hxu hxv

lemma Expansion.bag_injective (E : Expansion S U) {A B : Finset W}
    (hA : A ⊆ U) (hB : B ⊆ U) (heq : E.bag A = E.bag B) : A = B := by
  suffices h : ∀ C D : Finset W, C ⊆ U → D ⊆ U → E.bag C = E.bag D → C ⊆ D by
    exact Subset.antisymm (h A B hA hB heq) (h B A hB hA heq.symm)
  intro C D hC hD hCD u hu
  obtain ⟨x, hx⟩ := E.nonempty u (hC hu)
  have hxC : x ∈ E.bag C := mem_biUnion.mpr ⟨u, hu, hx⟩
  obtain ⟨v, hv, hxv⟩ := mem_biUnion.mp (hCD ▸ hxC)
  exact (E.atom_unique (hC hu) (hD hv) hx hxv) ▸ hv

omit [DecidableEq W] in
lemma Expansion.bag_nonempty (E : Expansion S U) {A : Finset W}
    (hA : A ⊆ U) (hne : A.Nonempty) : (E.bag A).Nonempty := by
  obtain ⟨u, hu⟩ := hne
  obtain ⟨v, hv⟩ := E.nonempty u (hA hu)
  exact ⟨v, mem_biUnion.mpr ⟨u, hu, hv⟩⟩

def Expansion.partition (E : Expansion S U) (P : Partition U) : Partition S := by
  apply Finpartition.ofExistsUnique (P.parts.image E.bag)
  · intro C hC x hx
    obtain ⟨A, hA, rfl⟩ := mem_image.mp hC
    obtain ⟨u, hu, hxu⟩ := mem_biUnion.mp hx
    rw [← E.cover]
    exact mem_biUnion.mpr ⟨u, P.subset hA hu, hxu⟩
  · intro x hx
    rw [← E.cover] at hx
    obtain ⟨u, hu, hxu⟩ := mem_biUnion.mp hx
    obtain ⟨A, hA, huA⟩ := P.exists_mem hu
    refine ⟨E.bag A, ⟨mem_image.mpr ⟨A, hA, rfl⟩,
      mem_biUnion.mpr ⟨u, huA, hxu⟩⟩, ?_⟩
    rintro C ⟨hC, hxC⟩
    obtain ⟨B, hB, rfl⟩ := mem_image.mp hC
    obtain ⟨v, hv, hxv⟩ := mem_biUnion.mp hxC
    have hvu : v = u := E.atom_unique (P.subset hB hv) hu hxv hxu
    have hBA : B = A := P.eq_of_mem_parts hB hA (hvu ▸ hv) huA
    exact congrArg E.bag hBA
  · intro h
    obtain ⟨A, hA, hAE⟩ := mem_image.mp h
    exact (E.bag_nonempty (P.subset hA) (P.nonempty_of_mem_parts hA)).ne_empty hAE

lemma Expansion.partition_parts (E : Expansion S U) (P : Partition U) :
    (E.partition P).parts = P.parts.image E.bag := rfl

lemma Expansion.partition_card (E : Expansion S U) (P : Partition U) :
    (E.partition P).parts.card = P.parts.card := by
  apply card_image_of_injOn
  intro A hA B hB heq
  exact E.bag_injective (P.subset hA) (P.subset hB) heq

lemma Expansion.merge_parts (E : Expansion S U) {P Q : Partition U}
    {A B : Finset W} (hA : A ∈ P.parts) (hB : B ∈ P.parts)
    (hQ : Q.parts = insert (A ∪ B) (P.parts \ {A, B})) :
    (E.partition Q).parts = insert (E.bag A ∪ E.bag B)
      ((E.partition P).parts \ {E.bag A, E.bag B}) := by
  ext C
  simp only [partition_parts, hQ, mem_image, mem_insert, mem_sdiff, mem_singleton, not_or]
  constructor
  · rintro ⟨D, hD, hDC⟩
    rcases hD with rfl | ⟨hD, hDA, hDB⟩
    · exact Or.inl (hDC.symm.trans (E.bag_union A B))
    · refine Or.inr ⟨⟨D, hD, hDC⟩, ?_, ?_⟩
      · intro hCA
        exact hDA (E.bag_injective (P.subset hD) (P.subset hA) (hDC.trans hCA))
      · intro hCB
        exact hDB (E.bag_injective (P.subset hD) (P.subset hB) (hDC.trans hCB))
  · rintro (hC | ⟨⟨D, hD, hDC⟩, hCA, hCB⟩)
    · exact ⟨A ∪ B, Or.inl rfl, (E.bag_union A B).trans hC.symm⟩
    · refine ⟨D, Or.inr ⟨hD, ?_, ?_⟩, hDC⟩
      · intro h
        exact hCA (hDC.symm.trans (congrArg E.bag h))
      · intro h
        exact hCB (hDC.symm.trans (congrArg E.bag h))

lemma Expansion.merge (E : Expansion S U) {P Q : Partition U} (h : Merge P Q) :
    Merge (E.partition P) (E.partition Q) := by
  obtain ⟨A, hA, B, hB, hAB, hQ⟩ := h
  exact ⟨E.bag A, mem_image.mpr ⟨A, hA, rfl⟩,
    E.bag B, mem_image.mpr ⟨B, hB, rfl⟩,
    fun heq => hAB (E.bag_injective (P.subset hA) (P.subset hB) heq),
    E.merge_parts hA hB hQ⟩

omit [DecidableEq V] in
lemma black_symm (T : Trigraph V) {A B : Finset V} (h : Black T A B) : Black T B A := by
  intro b hb a ha
  exact T.black.adj_symm (h a ha b hb)

omit [DecidableEq V] in
lemma adjacent_symm (T : Trigraph V) {A B : Finset V} (h : Adjacent T A B) :
    Adjacent T B A := by
  obtain ⟨a, ha, b, hb, hab⟩ := h
  exact ⟨b, hb, a, ha, hab.elim (fun h => Or.inl (T.black.adj_symm h))
    (fun h => Or.inr (T.red.adj_symm h))⟩

def Expansion.quotient (E : Expansion S U) (T : Trigraph V) : Trigraph W where
  black := {
    Adj := fun a b => a ≠ b ∧ Black T (E.atom a) (E.atom b)
    symm := ⟨fun _ _ h => ⟨h.1.symm, black_symm T h.2⟩⟩
    loopless := ⟨fun _ h => h.1 rfl⟩ }
  red := {
    Adj := fun a b => a ≠ b ∧ Red T (E.atom a) (E.atom b)
    symm := ⟨fun _ _ h => ⟨h.1.symm, adjacent_symm T h.2.1,
      fun hb => h.2.2 (black_symm T hb)⟩⟩
    loopless := ⟨fun _ h => h.1 rfl⟩ }
  exclusive := by intro a b hb hr; exact hr.2.2 hb.2

omit [DecidableEq W] in
lemma Expansion.quotient_adjacent (E : Expansion S U) (T : Trigraph V)
    {a b : W} (ha : a ∈ U) (hb : b ∈ U) (hne : a ≠ b) :
    ((E.quotient T).black.Adj a b ∨ (E.quotient T).red.Adj a b) ↔
      Adjacent T (E.atom a) (E.atom b) := by
  classical
  constructor
  · rintro (hblack | hred)
    · obtain ⟨x, hx⟩ := E.nonempty a ha
      obtain ⟨y, hy⟩ := E.nonempty b hb
      exact ⟨x, hx, y, hy, Or.inl (hblack.2 x hx y hy)⟩
    · exact hred.2.1
  · intro hadj
    by_cases hblack : Black T (E.atom a) (E.atom b)
    · exact Or.inl ⟨hne, hblack⟩
    · exact Or.inr ⟨hne, hadj, hblack⟩

omit [DecidableEq W] in
lemma Expansion.black_bag (E : Expansion S U) (T : Trigraph V)
    {A B : Finset W} (hdisj : Disjoint A B) :
    Black (E.quotient T) A B ↔ Black T (E.bag A) (E.bag B) := by
  constructor
  · intro h x hx y hy
    obtain ⟨a, ha, hxa⟩ := mem_biUnion.mp hx
    obtain ⟨b, hb, hyb⟩ := mem_biUnion.mp hy
    exact (h a ha b hb).2 x hxa y hyb
  · intro h a ha b hb
    refine ⟨fun heq => disjoint_left.mp hdisj ha (heq ▸ hb), ?_⟩
    intro x hx y hy
    exact h x (mem_biUnion.mpr ⟨a, ha, hx⟩) y (mem_biUnion.mpr ⟨b, hb, hy⟩)

omit [DecidableEq W] in
lemma Expansion.adjacent_bag (E : Expansion S U) (T : Trigraph V)
    {A B : Finset W} (hA : A ⊆ U) (hB : B ⊆ U) (hdisj : Disjoint A B) :
    Adjacent (E.quotient T) A B ↔ Adjacent T (E.bag A) (E.bag B) := by
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    have hne : a ≠ b := fun heq => disjoint_left.mp hdisj ha (heq ▸ hb)
    obtain ⟨x, hx, y, hy, hxy⟩ := (E.quotient_adjacent T (hA ha) (hB hb) hne).mp hab
    exact ⟨x, mem_biUnion.mpr ⟨a, ha, hx⟩, y, mem_biUnion.mpr ⟨b, hb, hy⟩, hxy⟩
  · rintro ⟨x, hx, y, hy, hxy⟩
    obtain ⟨a, ha, hxa⟩ := mem_biUnion.mp hx
    obtain ⟨b, hb, hyb⟩ := mem_biUnion.mp hy
    have hne : a ≠ b := fun heq => disjoint_left.mp hdisj ha (heq ▸ hb)
    exact ⟨a, ha, b, hb, (E.quotient_adjacent T (hA ha) (hB hb) hne).mpr
      ⟨x, hxa, y, hyb, hxy⟩⟩

omit [DecidableEq W] in
lemma Expansion.red_bag (E : Expansion S U) (T : Trigraph V)
    {A B : Finset W} (hA : A ⊆ U) (hB : B ⊆ U) (hdisj : Disjoint A B) :
    Red (E.quotient T) A B ↔ Red T (E.bag A) (E.bag B) := by
  simp only [Red, E.adjacent_bag T hA hB hdisj, E.black_bag T hdisj]

lemma Expansion.neighbor_card (E : Expansion S U) (P : Partition U)
    (R : Finset W → Finset W → Prop) (R' : Finset V → Finset V → Prop)
    (hR : ∀ A ∈ P.parts, ∀ B ∈ P.parts, A ≠ B →
      (R A B ↔ R' (E.bag A) (E.bag B))) {A : Finset W} (hA : A ∈ P.parts) :
    (neighbors R' (E.partition P) (E.bag A)).card = (neighbors R P A).card := by
  classical
  have heq : neighbors R' (E.partition P) (E.bag A) = (neighbors R P A).image E.bag := by
    ext C
    constructor
    · intro hC
      obtain ⟨hCP, hCA, hRC⟩ := mem_filter.mp hC
      obtain ⟨B, hBP, rfl⟩ := mem_image.mp hCP
      have hBA : B ≠ A := fun h => hCA (congrArg E.bag h)
      exact mem_image.mpr ⟨B, mem_filter.mpr ⟨hBP, hBA,
        (hR A hA B hBP hBA.symm).mpr hRC⟩, rfl⟩
    · intro hC
      obtain ⟨B, hB, rfl⟩ := mem_image.mp hC
      obtain ⟨hBP, hBA, hRB⟩ := mem_filter.mp hB
      exact mem_filter.mpr ⟨mem_image.mpr ⟨B, hBP, rfl⟩,
        fun h => hBA (E.bag_injective (P.subset hBP) (P.subset hA) h),
        (hR A hA B hBP hBA.symm).mp hRB⟩
  rw [heq]
  apply card_image_of_injOn
  intro B hB C hC hBC
  exact E.bag_injective (P.subset (mem_filter.mp hB).1)
    (P.subset (mem_filter.mp hC).1) hBC

lemma Expansion.bounded_iff (E : Expansion S U) (T : Trigraph V)
    (P : Partition U) (w s : ℕ) :
    Bounded T w s (E.partition P) ↔ Bounded (E.quotient T) w s P := by
  have hred : ∀ A ∈ P.parts,
      redDegree T (E.partition P) (E.bag A) = redDegree (E.quotient T) P A := by
    intro A hA
    exact E.neighbor_card P (Red (E.quotient T)) (Red T)
      (fun A hA B hB hne => E.red_bag T (P.subset hA) (P.subset hB) (P.disjoint hA hB hne)) hA
  have htotal : ∀ A ∈ P.parts,
      totalDegree T (E.partition P) (E.bag A) = totalDegree (E.quotient T) P A := by
    intro A hA
    exact E.neighbor_card P (Adjacent (E.quotient T)) (Adjacent T)
      (fun A hA B hB hne => E.adjacent_bag T (P.subset hA) (P.subset hB) (P.disjoint hA hB hne)) hA
  constructor
  · intro h A hA
    obtain ⟨hr, ht⟩ := h (E.bag A) (mem_image.mpr ⟨A, hA, rfl⟩)
    exact ⟨(hred A hA) ▸ hr, (htotal A hA) ▸ ht⟩
  · intro h C hC
    obtain ⟨A, hA, rfl⟩ := mem_image.mp hC
    obtain ⟨hr, ht⟩ := h A hA
    exact ⟨(hred A hA).symm ▸ hr, (htotal A hA).symm ▸ ht⟩

lemma Expansion.continuation (E : Expansion S U) (T : Trigraph V)
    {P : Partition U} {w s : ℕ} (h : Continuation (E.quotient T) w s P) :
    Continuation T w s (E.partition P) := by
  induction h with
  | done hb hc => exact .done ((E.bounded_iff ..).mpr hb) ((E.partition_card _) ▸ hc)
  | step hb hm _ ih => exact .step ((E.bounded_iff ..).mpr hb) (E.merge hm) ih

lemma Expansion.unmerge (E : Expansion S U) {P : Partition U} {R : Partition S}
    (h : Merge (E.partition P) R) : ∃ Q, Merge P Q ∧ E.partition Q = R := by
  obtain ⟨C, hC, D, hD, hCD, hR⟩ := h
  obtain ⟨A, hA, rfl⟩ := mem_image.mp hC
  obtain ⟨B, hB, rfl⟩ := mem_image.mp hD
  let Q := mergePartition P A B hA hB
  refine ⟨Q, ⟨A, hA, B, hB, fun heq => hCD (congrArg E.bag heq), rfl⟩, ?_⟩
  apply Finpartition.ext
  exact (E.merge_parts hA hB (mergePartition_parts P hA hB)).trans hR.symm

lemma Expansion.continuation_iff (E : Expansion S U) (T : Trigraph V)
    (P : Partition U) (w s : ℕ) :
    Continuation T w s (E.partition P) ↔ Continuation (E.quotient T) w s P := by
  refine ⟨?_, E.continuation T⟩
  suffices h : ∀ R, Continuation T w s R → ∀ P, E.partition P = R →
      Continuation (E.quotient T) w s P from fun hc => h _ hc P rfl
  intro R hc
  induction hc with
  | @done R hb hcard =>
    intro P hP
    subst R
    exact .done ((E.bounded_iff ..).mp hb) ((E.partition_card _) ▸ hcard)
  | @step R R' hb hm hc ih =>
    intro P hP
    subst R
    obtain ⟨Q, hPQ, hQ⟩ := E.unmerge hm
    exact .step ((E.bounded_iff ..).mp hb) hPQ (ih Q hQ)

def partitionExpansion (P : Partition S) : Expansion S P.parts where
  atom := id
  nonempty := fun _ h => P.nonempty_of_mem_parts h
  disjoint := fun _ hA _ hB hne => P.disjoint hA hB hne
  cover := P.biUnion_parts

lemma partitionExpansion_bot (P : Partition S) :
    (partitionExpansion P).partition ⊥ = P := by
  ext C
  simp only [Expansion.partition_parts, mem_image, Finpartition.mem_bot_iff]
  constructor
  · rintro ⟨A, ⟨B, hB, rfl⟩, hBC⟩
    have hBC' : B = C := by simpa [Expansion.bag, partitionExpansion] using hBC
    exact hBC' ▸ hB
  · intro hC
    exact ⟨{C}, ⟨C, hC, rfl⟩, by simp [Expansion.bag, partitionExpansion]⟩

end Paper
