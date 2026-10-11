import PaperDefinitions

/-! The breadth-first choice used in Lemma 9. At every stage the next
uncontracted fiber has minimum distance from the root in H. -/
namespace Paper
open Finset

/-- A vertex of minimum root-distance among the unprocessed vertices.
Every smaller-distance vertex is processed already, and unless this is the
root, a shortest path supplies a processed parent one level earlier. -/
lemma breadth_first_next {V : Type*} [Fintype V] (H : SimpleGraph V)
    (hconn : H.Connected) (root : V) (processed : V → Prop)
    (hmissing : ∃ v, ¬ processed v) :
    ∃ u, ¬ processed u ∧
      (∀ v, ¬ processed v → H.dist root u ≤ H.dist root v) ∧
      (∀ v, H.dist root v < H.dist root u → processed v) ∧
      (u = root ∨ ∃ p, processed p ∧ H.Adj u p ∧
        H.dist root p + 1 = H.dist root u) := by
  classical
  let U := univ.filter fun u => ¬ processed u
  have hU : U.Nonempty := by
    obtain ⟨v, hv⟩ := hmissing
    exact ⟨v, mem_filter.mpr ⟨mem_univ _, hv⟩⟩
  obtain ⟨u, hu, hmin⟩ := U.exists_min_image (H.dist root) hU
  have hun : ¬ processed u := (mem_filter.mp hu).2
  have hminimum : ∀ v, ¬ processed v → H.dist root u ≤ H.dist root v := by
    intro v hv
    exact hmin v (mem_filter.mpr ⟨mem_univ _, hv⟩)
  have hearlier : ∀ v, H.dist root v < H.dist root u → processed v := by
    intro v hv
    by_contra hnot
    exact not_lt_of_ge (hminimum v hnot) hv
  refine ⟨u, hun, hminimum, hearlier, ?_⟩
  by_cases hroot : u = root
  · exact Or.inl hroot
  · obtain ⟨walk, hlen⟩ := (hconn.preconnected root u).exists_walk_length_eq_dist
    have hpositive : 0 < walk.length := by
      rw [hlen]
      exact hconn.pos_dist_of_ne (Ne.symm hroot)
    let p := walk.getVert (walk.length - 1)
    have hlast : walk.length - 1 + 1 = walk.length := by omega
    have hpu : H.Adj p u := by
      have h := walk.adj_getVert_succ (show walk.length - 1 < walk.length by omega)
      simpa only [hlast, walk.getVert_length] using h
    have hdist : H.dist root p ≤ walk.length - 1 := by
      have h := SimpleGraph.dist_le (walk.take (walk.length - 1))
      rw [SimpleGraph.Walk.take_length] at h
      exact h.trans (min_le_left _ _)
    have hparent : processed p := hearlier p (by omega)
    have hstep : H.dist root p + 1 = H.dist root u := by
      have htri : H.dist root u ≤ H.dist root p + H.dist p u := hconn.dist_triangle
      rw [SimpleGraph.dist_eq_one_iff_adj.mpr hpu] at htri
      omega
    exact Or.inr ⟨p, hparent, hpu.symm, hstep⟩

end Paper
