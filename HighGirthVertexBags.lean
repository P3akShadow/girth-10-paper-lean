import HighGirthLargeBags

/-! The endpoint degree observation used in the two-pair merge cases. -/
namespace Paper
open Finset SimpleGraph CycleLift
variable {V : Type*} [DecidableEq V] {S : Finset V}
attribute [local instance] Classical.propDecidable

noncomputable def externalBags (G : SimpleGraph V) (P : Partition S)
    (A : Finset V) (u : V) : Finset (Finset V) :=
  P.parts.filter fun B => B ≠ A ∧ Adjacent (.ofGraph G) {u} B

lemma externalBags_subset_neighbors (G : SimpleGraph V) (P : Partition S)
    {A : Finset V} {u : V} (hu : u ∈ A) :
    externalBags G P A u ⊆ neighbors (Adjacent (.ofGraph G)) P A := by
  intro B hB
  obtain ⟨hBP, hBA, x, hx, y, hy, hxy⟩ := mem_filter.mp hB
  have hxu := mem_singleton.mp hx
  subst x
  exact mem_filter.mpr ⟨hBP, hBA, u, hu, y, hy, hxy⟩

lemma externalBags_eq_image (G : SimpleGraph V) (P : Partition S)
    {A : Finset V} (hA : A ∈ P.parts) {u : V} :
    externalBags G P A u = (graphNeighbors G S u \ A).image P.part := by
  classical
  ext B
  constructor
  · intro hB
    obtain ⟨hBP, hBA, x, hx, y, hy, hxy⟩ := mem_filter.mp hB
    have hxu := mem_singleton.mp hx
    subst x
    have huy : G.Adj u y := hxy.resolve_right (by simp [Trigraph.ofGraph])
    have hyA : y ∉ A := fun hyA => hBA (P.eq_of_mem_parts hBP hA hy hyA)
    exact mem_image.mpr ⟨y, mem_sdiff.mpr ⟨mem_filter.mpr ⟨P.subset hBP hy, huy⟩, hyA⟩,
      P.part_eq_of_mem hBP hy⟩
  · intro hB
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hB
    obtain ⟨hyN, hyA⟩ := mem_sdiff.mp hy
    obtain ⟨hyS, huy⟩ := mem_filter.mp hyN
    obtain ⟨B, hB, hyB⟩ := P.exists_mem hyS
    rw [P.part_eq_of_mem hB hyB]
    exact mem_filter.mpr ⟨hB, fun he => hyA (he ▸ hyB),
      u, mem_singleton_self _, y, hyB, Or.inl huy⟩

lemma externalBags_card_le (G : SimpleGraph V) {d : ℕ} (hreg : Regular G S d)
    (P : Partition S) {A : Finset V} (hA : A ∈ P.parts) {u : V} (hu : u ∈ A) :
    (externalBags G P A u).card ≤ d := by
  rw [externalBags_eq_image G P hA]
  exact card_image_le.trans ((card_le_card sdiff_subset).trans (le_of_eq (hreg u (P.subset hA hu))))

lemma externalBags_card_add_one_le (G : SimpleGraph V) {d : ℕ} (hreg : Regular G S d)
    (P : Partition S) {A : Finset V} (hA : A ∈ P.parts) {u v : V}
    (hu : u ∈ A) (hv : v ∈ A) (huv : G.Adj u v) :
    (externalBags G P A u).card + 1 ≤ d := by
  classical
  rw [externalBags_eq_image G P hA]
  have hsub : graphNeighbors G S u \ A ⊆ (graphNeighbors G S u).erase v := by
    intro w hw
    obtain ⟨hwN, hwA⟩ := mem_sdiff.mp hw
    exact mem_erase.mpr ⟨fun he => hwA (he ▸ hv), hwN⟩
  have hvN : v ∈ graphNeighbors G S u := mem_filter.mpr ⟨P.subset hA hv, huv⟩
  have hh := (card_image_le (f := P.part) (s := graphNeighbors G S u \ A)).trans (card_le_card hsub)
  have he := card_erase_add_one hvN
  rw [hreg u (P.subset hA hu)] at he
  omega

lemma pair_neighbors_eq_external_union (G : SimpleGraph V) (P : Partition S) (u v : V) :
    neighbors (Adjacent (.ofGraph G)) P {u, v} =
      externalBags G P {u, v} u ∪ externalBags G P {u, v} v := by
  classical
  ext B
  simp only [neighbors, externalBags, mem_filter, mem_union]
  constructor
  · rintro ⟨hB, hBA, x, hx, y, hy, hxy⟩
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Or.inl ⟨hB, hBA, _, mem_singleton_self _, y, hy, hxy⟩
    · exact Or.inr ⟨hB, hBA, _, mem_singleton_self _, y, hy, hxy⟩
  · rintro (⟨hB, hBA, x, hx, y, hy, hxy⟩ | ⟨hB, hBA, x, hx, y, hy, hxy⟩)
    · exact ⟨hB, hBA, x, mem_insert.mpr (Or.inl (mem_singleton.mp hx)), y, hy, hxy⟩
    · exact ⟨hB, hBA, x, mem_insert.mpr (Or.inr hx), y, hy, hxy⟩

/-- Each endpoint of a saturated two-bag meets at least d-1 external bags.
If the two endpoints are adjacent, the internal edge costs a neighbor at
both endpoints. Otherwise their distance-two path gives a common bag. -/
lemma externalBags_pair_card_lower (G : SimpleGraph V) {d : ℕ}
    (hd : 3 ≤ d) (hreg : Regular G S d)
    (hclosed : ∀ u ∈ S, ∀ v, G.Adj u v → v ∈ S)
    (P : Partition S) {u v : V} (hP : {u, v} ∈ P.parts) (huv : u ≠ v)
    (hnear : Near G u v) (hsat : redDegree (.ofGraph G) P {u, v} = 2 * d - 2) :
    d - 1 ≤ (externalBags G P {u, v} u).card := by
  classical
  have hred := redDegree_le_totalDegree (.ofGraph G) P {u, v}
  have hunion := pair_neighbors_eq_external_union G P u v
  have hbound := card_union_le (externalBags G P {u, v} u) (externalBags G P {u, v} v)
  have hvbound := externalBags_card_le G hreg P hP (show v ∈ ({u, v} : Finset V) by simp)
  have hsum := card_union_add_card_inter (externalBags G P {u, v} u) (externalBags G P {u, v} v)
  change redDegree (.ofGraph G) P {u, v} ≤ (neighbors (Adjacent (.ofGraph G)) P {u, v}).card at hred
  rw [hsat, hunion] at hred
  by_cases hadj : G.Adj u v
  · have hh := externalBags_card_add_one_le G hreg P hP (show v ∈ ({u, v} : Finset V) by simp)
      (show u ∈ ({u, v} : Finset V) by simp) hadj.symm
    omega
  · obtain ⟨z, huz, hzv⟩ := (hnear.resolve_left huv).resolve_left hadj
    have hzS := hclosed u (P.subset hP (by simp)) z huz
    obtain ⟨Z, hZ, hzZ⟩ := P.exists_mem hzS
    have hzP : z ∉ ({u, v} : Finset V) := by
      simp only [mem_insert, mem_singleton, not_or]
      exact ⟨huz.ne.symm, hzv.ne⟩
    have hZP : Z ≠ {u, v} := fun he => hzP (he ▸ hzZ)
    have hcommon : 1 ≤ (externalBags G P {u, v} u ∩ externalBags G P {u, v} v).card :=
      one_le_card.mpr ⟨Z, mem_inter.mpr ⟨
        mem_filter.mpr ⟨hZ, hZP, u, mem_singleton_self _, z, hzZ, Or.inl huz⟩,
        mem_filter.mpr ⟨hZ, hZP, v, mem_singleton_self _, z, hzZ, Or.inl hzv.symm⟩⟩⟩
    omega

lemma externalBags_card_lower_of_mem (G : SimpleGraph V) {d : ℕ}
    (hd : 3 ≤ d) (hreg : Regular G S d)
    (hclosed : ∀ u ∈ S, ∀ v, G.Adj u v → v ∈ S)
    (P : Partition S) (near : BagsNear G P) {A : Finset V}
    (hA : A ∈ P.parts) (hsize : A.card = 2)
    (hsat : redDegree (.ofGraph G) P A = 2 * d - 2) {u : V} (hu : u ∈ A) :
    d - 1 ≤ (externalBags G P A u).card := by
  obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp hsize
  simp only [mem_insert, mem_singleton] at hu
  rcases hu with rfl | rfl
  · exact externalBags_pair_card_lower G hd hreg hclosed P hA hab
      (near _ hA _ (by simp) _ (by simp)) hsat
  · have hP : {u, a} ∈ P.parts := by simpa only [pair_comm] using hA
    have hs : redDegree (.ofGraph G) P {u, a} = 2 * d - 2 := by simpa only [pair_comm] using hsat
    simpa only [pair_comm] using externalBags_pair_card_lower G hd hreg hclosed P hP hab.symm
      (near _ hP _ (by simp) _ (by simp)) hs

end Paper
