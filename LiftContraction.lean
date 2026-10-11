import LiftConstruction
import BagCounting

/-! The last stage of Lemma 9: contract the two copies of each base vertex,
then use the base graph's contraction sequence. Edge colors are irrelevant to
the sparse width, and deleting the chosen edge can only reduce total degrees. -/

namespace Paper
open Finset
variable {V : Type*} [DecidableEq V] {S : Finset V}

def SupportedBy (T U : Trigraph V) (S : Finset V) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, T.black.Adj a b ∨ T.red.Adj a b →
    U.black.Adj a b ∨ U.red.Adj a b

omit [DecidableEq V] in
lemma SupportedBy.adjacent {T U : Trigraph V} (h : SupportedBy T U S)
    {A B : Finset V} (hA : A ⊆ S) (hB : B ⊆ S) (hab : Adjacent T A B) :
    Adjacent U A B := by
  obtain ⟨a,ha,b,hb,hab⟩ := hab
  exact ⟨a,ha,b,hb,h a (hA ha) b (hB hb) hab⟩

lemma SupportedBy.totalDegree {T U : Trigraph V} (h : SupportedBy T U S)
    (P : Partition S) {A : Finset V} (hA : A ∈ P.parts) :
    totalDegree T P A ≤ totalDegree U P A := by
  classical
  apply card_le_card
  intro B hB
  obtain ⟨hBP,hBA,hab⟩ := mem_filter.mp hB
  exact mem_filter.mpr ⟨hBP,hBA,h.adjacent (P.subset hA) (P.subset hBP) hab⟩

lemma SupportedBy.bounded {T U : Trigraph V} (h : SupportedBy T U S)
    {P : Partition S} {w s : ℕ} (hb : Bounded U w s P) : Bounded T s s P := by
  intro A hA
  have ht := (h.totalDegree P hA).trans (hb A hA).2
  exact ⟨(redDegree_le_totalDegree T P A).trans ht, ht⟩

lemma SupportedBy.continuation {T U : Trigraph V} (h : SupportedBy T U S)
    {P : Partition S} {w s : ℕ} (hc : Continuation U w s P) :
    Continuation T s s P := by
  induction hc with
  | done hb hf => exact .done (h.bounded hb) hf
  | step hb hm _ ih => exact .step (h.bounded hb) hm ih

/-- Subgraph monotonicity, used in the proof of Lemma 9. -/
theorem sparseTwinWidth_supported {T U : Trigraph V} (h : SupportedBy T U S) :
    sparseTwinWidth T S ≤ sparseTwinWidth U S := by
  obtain ⟨w,hw⟩ := sparseTwinWidth_witness U S
  exact sparseTwinWidth_le (h.continuation hw)

def fiber (u : V) : Finset (V × Bool) := {(u,false),(u,true)}

lemma mem_fiber {u : V} {a : V × Bool} : a ∈ fiber u ↔ a.1 = u := by
  rcases a with ⟨a,i⟩
  cases i <;> simp [fiber]

lemma fiber_nonempty (u : V) : (fiber u).Nonempty := ⟨(u,false),by simp [fiber]⟩

def fiberExpansion (S : Finset V) : Expansion (liftVertices S) S where
  atom := fiber
  nonempty := fun u _ => fiber_nonempty u
  disjoint := by
    intro u _ v _ huv
    apply disjoint_left.mpr
    intro a hau hav
    exact huv ((mem_fiber.mp hau).symm.trans (mem_fiber.mp hav))
  cover := by
    ext a
    simp only [mem_biUnion,mem_fiber,mem_liftVertices]
    constructor
    · rintro ⟨u,hu,hau⟩
      exact hau ▸ hu
    · intro ha
      exact ⟨a.1,ha,rfl⟩

lemma fiberExpansion_supported (G : SimpleGraph V) (x y : V) (σ : Signing V) :
    SupportedBy ((fiberExpansion S).quotient (.ofGraph (girthLift G x y σ)))
      (.ofGraph (edgeDeleted G x y)) S := by
  intro a ha b hb hab
  have hne : a ≠ b := hab.elim (fun h => h.1) (fun h => h.1)
  have h := ((fiberExpansion S).quotient_adjacent (.ofGraph (girthLift G x y σ)) ha hb hne).mp hab
  obtain ⟨u,hu,v,hv,huv⟩ := h
  have hu' : u.1 = a := mem_fiber.mp hu
  have hv' : v.1 = b := mem_fiber.mp hv
  have huv' : (girthLift G x y σ).Adj u v := by simpa [Trigraph.ofGraph] using huv
  rcases huv' with huv' | huv'
  · exact Or.inl (by simpa only [Trigraph.ofGraph,hu',hv'] using huv'.1)
  · exact False.elim (hne (hu'.symm.trans (huv'.1.trans hv')))

lemma edgeDeleted_supported (G : SimpleGraph V) (x y : V) :
    SupportedBy (.ofGraph (edgeDeleted G x y)) (.ofGraph G) S := by
  intro a _ b _ h
  have h' : (edgeDeleted G x y).Adj a b := by simpa [Trigraph.ofGraph] using h
  exact Or.inl h'.1

/-- After all fibers have been merged, the base sequence can be followed at
the same sparse width. This is the final paragraph of Lemma 9's argument. -/
lemma girthLift_fiber_continuation (G : SimpleGraph V) (x y : V) (σ : Signing V)
    {w s : ℕ} (h : HasWidths (.ofGraph G) S w s) :
    Continuation (.ofGraph (girthLift G x y σ)) s s ((fiberExpansion S).partition ⊥) := by
  apply Expansion.continuation
  exact (fiberExpansion_supported G x y σ).continuation
    ((edgeDeleted_supported G x y).continuation h)

end Paper
