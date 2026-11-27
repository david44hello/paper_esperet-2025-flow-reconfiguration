module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Flow.Defs.Frames
public import Flow.Proofs.Extraction

@[expose] public section

/-!
# Section 3 (Part 2): Blocks, truncated cubic expansions, and auxiliary graph existence

This module proves Lemma 3.4(a) (`lem_3_4_a`), Lemma 3.4(b) (`lem_3_4_b`), block
uniqueness (`block_unique_of_edge`, `exists_block_containing_edge`), and `aux_graph_exists`.
-/

namespace Flow.Proofs

open Flow Multigraph

section BlockHelpers

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- Helper: `ReflTransGen H.Adj` is symmetric. -/
lemma subgraph_adj_symm {G : Multigraph V E} {H : G.Subgraph} {u v : V}
    (h : Relation.ReflTransGen H.Adj u v) : Relation.ReflTransGen H.Adj v u := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
    rcases hstep with ⟨e, he, h | h⟩
    · exact Relation.ReflTransGen.head ⟨e, he, Or.inr h⟩ ih
    · exact Relation.ReflTransGen.head ⟨e, he, Or.inl h⟩ ih

/-- Helper: `ReflTransGen G.Adj` is symmetric. -/
lemma graph_adj_symm {G : Multigraph V E} {u v : V}
    (h : Relation.ReflTransGen G.Adj u v) : Relation.ReflTransGen G.Adj v u := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
    rcases hstep with ⟨e, h | h⟩
    · exact Relation.ReflTransGen.head ⟨e, Or.inr h⟩ ih
    · exact Relation.ReflTransGen.head ⟨e, Or.inl h⟩ ih

/-- A `j`-edge-connected graph (`j ≥ 1`) is connected. -/
lemma connected_of_edgeConnected {G : Multigraph V E} {j : ℕ} (hj : 1 ≤ j)
    (hconn : G.IsEdgeConnected j) : G.Connected := by
  intro u v
  by_contra hnot
  classical
  let S : Finset V := Finset.univ.filter (fun w => Relation.ReflTransGen G.Adj u w)
  have huS : u ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Relation.ReflTransGen.refl⟩
  have hvS : v ∈ Finset.univ \ S :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h => hnot (Finset.mem_filter.mp h).2⟩
  have hge := hconn S ⟨u, huS⟩ ⟨v, hvS⟩
  have hcut0 : (G.cutEdges S).card = 0 := by
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro e he
    have hcr := (Finset.mem_filter.mp he).2
    rcases hcr with ⟨ht, hh⟩ | ⟨ht, hh⟩
    · exact hh (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        Relation.ReflTransGen.tail (Finset.mem_filter.mp ht).2 ⟨e, Or.inl ⟨rfl, rfl⟩⟩⟩)
    · exact ht (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        Relation.ReflTransGen.tail (Finset.mem_filter.mp hh).2 ⟨e, Or.inr ⟨rfl, rfl⟩⟩⟩)
  omega

/-- In a `j`-edge-connected graph on `≥ 2` vertices, every vertex has degree `≥ j`. -/
lemma deg_ge_of_edgeConnected {G : Multigraph V E} {j : ℕ}
    (hconn : G.IsEdgeConnected j) (hn : 2 ≤ Fintype.card V) (v : V) :
    j ≤ G.deg v := by
  have hne_comp : (Finset.univ \ ({v} : Finset V)).Nonempty := by
    obtain ⟨a, b, hab⟩ := Fintype.one_lt_card_iff.mp (by omega : 1 < Fintype.card V)
    let w := if v = a then b else a
    have hw : w ≠ v := by
      dsimp only [w]; split_ifs with h
      · exact fun h' => hab (h.symm.trans h'.symm)
      · exact fun h' => h h'.symm
    exact ⟨w, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by simp [hw]⟩⟩
  have hcut := hconn {v} (Finset.singleton_nonempty v) hne_comp
  have hsub : G.cutEdges {v} ⊆
      Finset.univ.filter (fun e => G.tail e = v) ∪ Finset.univ.filter (fun e => G.head e = v) := by
    intro e he
    simp only [Multigraph.cutEdges, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton] at he
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases he with ⟨ht, _⟩ | ⟨_, hh⟩
    · left; exact ht
    · right; exact hh
  have hle : (G.cutEdges {v}).card ≤ G.deg v := by
    unfold Multigraph.deg
    exact le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
  omega

/-- Union of two subgraphs. -/
def subgraphUnion {G : Multigraph V E} (H₁ H₂ : G.Subgraph) : G.Subgraph where
  verts := H₁.verts ∪ H₂.verts
  edges := H₁.edges ∪ H₂.edges
  tail_mem {e} he := by
    rw [Finset.mem_union] at he ⊢
    rcases he with h1 | h2
    · left; exact H₁.tail_mem h1
    · right; exact H₂.tail_mem h2
  head_mem {e} he := by
    rw [Finset.mem_union] at he ⊢
    rcases he with h1 | h2
    · left; exact H₁.head_mem h1
    · right; exact H₂.head_mem h2

/-- Union of two connected cut-vertex-free subgraphs sharing at least `2` vertices is
connected and cut-vertex-free. -/
lemma subgraphUnion_noCutVertex {G : Multigraph V E} {K₁ K₂ : G.Subgraph}
    (hc1 : K₁.Connected) (hc2 : K₂.Connected)
    (hnc1 : K₁.HasNoCutVertex) (hnc2 : K₂.HasNoCutVertex)
    (hshare : 2 ≤ (K₁.verts ∩ K₂.verts).card) :
    (subgraphUnion K₁ K₂).Connected ∧ (subgraphUnion K₁ K₂).HasNoCutVertex := by
  have h1le : K₁ ≤ subgraphUnion K₁ K₂ := ⟨Finset.subset_union_left, Finset.subset_union_left⟩
  have h2le : K₂ ≤ subgraphUnion K₁ K₂ := ⟨Finset.subset_union_right, Finset.subset_union_right⟩
  have hlift : ∀ {A B : G.Subgraph}, A ≤ B → ∀ {u v : V},
      Relation.ReflTransGen A.Adj u v → Relation.ReflTransGen B.Adj u v := by
    intro A B hle u v h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hstep ih =>
      rcases hstep with ⟨e, he, hadj⟩
      exact Relation.ReflTransGen.tail ih ⟨e, hle.2 he, hadj⟩
  have hconn : (subgraphUnion K₁ K₂).Connected := by
    obtain ⟨w, hw12⟩ := Finset.card_pos.mp (by omega : 0 < (K₁.verts ∩ K₂.verts).card)
    have hw1 : w ∈ K₁.verts := (Finset.mem_inter.mp hw12).1
    have hw2 : w ∈ K₂.verts := (Finset.mem_inter.mp hw12).2
    refine ⟨⟨w, Finset.mem_union_left _ hw1⟩, fun u hu v hv => ?_⟩
    have hto_w : ∀ z ∈ (subgraphUnion K₁ K₂).verts,
        Relation.ReflTransGen (subgraphUnion K₁ K₂).Adj z w := by
      intro z hz
      rcases Finset.mem_union.mp hz with hz1 | hz2
      · exact hlift h1le (hc1.2 z hz1 w hw1)
      · exact hlift h2le (hc2.2 z hz2 w hw2)
    exact Relation.ReflTransGen.trans (hto_w u hu) (subgraph_adj_symm (hto_w v hv))
  refine ⟨hconn, fun v hv ⟨_, u, w, hu, hw, hnot⟩ => ?_⟩
  -- Pick `x ∈ (K₁.verts ∩ K₂.verts) \ {v}` (exists since `|K₁.verts ∩ K₂.verts| ≥ 2`)
  have hex_x : ∃ x ∈ K₁.verts ∩ K₂.verts, x ≠ v := by
    have hne : ((K₁.verts ∩ K₂.verts).erase v).Nonempty := by
      apply Finset.card_pos.mp
      by_cases hv12 : v ∈ K₁.verts ∩ K₂.verts
      · rw [Finset.card_erase_of_mem hv12]; omega
      · rw [Finset.erase_eq_of_notMem hv12]; omega
    rcases hne with ⟨x, hx⟩
    exact ⟨x, Finset.mem_of_mem_erase hx, Finset.ne_of_mem_erase hx⟩
  rcases hex_x with ⟨x, hx12, hxv⟩
  have hx1 : x ∈ K₁.verts := (Finset.mem_inter.mp hx12).1
  have hx2 : x ∈ K₂.verts := (Finset.mem_inter.mp hx12).2
  have hdel1 : K₁.deleteVertex v ≤ (subgraphUnion K₁ K₂).deleteVertex v :=
    ⟨Finset.erase_subset_erase v Finset.subset_union_left,
     Finset.filter_subset_filter _ Finset.subset_union_left⟩
  have hdel2 : K₂.deleteVertex v ≤ (subgraphUnion K₁ K₂).deleteVertex v :=
    ⟨Finset.erase_subset_erase v Finset.subset_union_right,
     Finset.filter_subset_filter _ Finset.subset_union_right⟩
  have hreach_x : ∀ z ∈ ((subgraphUnion K₁ K₂).deleteVertex v).verts,
      Relation.ReflTransGen ((subgraphUnion K₁ K₂).deleteVertex v).Adj z x := by
    intro z hz
    have hzv : z ≠ v := (Finset.mem_erase.mp hz).1
    have hzU : z ∈ (subgraphUnion K₁ K₂).verts := (Finset.mem_erase.mp hz).2
    rcases Finset.mem_union.mp hzU with hz1 | hz2
    · apply hlift hdel1
      by_cases hv1 : v ∈ K₁.verts
      · by_contra hno
        exact hnc1 v hv1 ⟨hv1, z, x, Finset.mem_erase.mpr ⟨hzv, hz1⟩,
          Finset.mem_erase.mpr ⟨hxv, hx1⟩, hno⟩
      · have heq : K₁.deleteVertex v = K₁ := by
          ext a
          · simp [Subgraph.deleteVertex, Finset.erase_eq_of_notMem hv1]
          · simp only [Subgraph.deleteVertex, Finset.mem_filter, and_iff_left_iff_imp]
            intro ha; exact ⟨fun ht => hv1 (ht ▸ K₁.tail_mem ha), fun hh => hv1 (hh ▸ K₁.head_mem ha)⟩
        rw [heq]; exact hc1.2 z hz1 x hx1
    · apply hlift hdel2
      by_cases hv2 : v ∈ K₂.verts
      · by_contra hno
        exact hnc2 v hv2 ⟨hv2, z, x, Finset.mem_erase.mpr ⟨hzv, hz2⟩,
          Finset.mem_erase.mpr ⟨hxv, hx2⟩, hno⟩
      · have heq : K₂.deleteVertex v = K₂ := by
          ext a
          · simp [Subgraph.deleteVertex, Finset.erase_eq_of_notMem hv2]
          · simp only [Subgraph.deleteVertex, Finset.mem_filter, and_iff_left_iff_imp]
            intro ha; exact ⟨fun ht => hv2 (ht ▸ K₂.tail_mem ha), fun hh => hv2 (hh ▸ K₂.head_mem ha)⟩
        rw [heq]; exact hc2.2 z hz2 x hx2
  exact hnot (Relation.ReflTransGen.trans (hreach_x u hu) (subgraph_adj_symm (hreach_x w hw)))

/-- Every non-loop edge lies in a unique block of `G`. -/
lemma existsUnique_block_of_nonloop {G : Multigraph V E} (e : E) (hne : G.tail e ≠ G.head e) :
    ∃! K : G.Subgraph, G.IsBlock K ∧ e ∈ K.edges := by
  classical
  -- Single-edge subgraph `{tail e, head e}, {e}` is connected and cut-vertex-free
  let K₀ : G.Subgraph :=
    { verts := {G.tail e, G.head e}
      edges := {e}
      tail_mem := fun he' => by simp [Finset.mem_singleton.mp he']
      head_mem := fun he' => by simp [Finset.mem_singleton.mp he'] }
  have hK₀_conn : K₀.Connected := by
    refine ⟨⟨G.tail e, Finset.mem_insert_self _ _⟩, fun u hu v hv => ?_⟩
    simp only [K₀, Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single ⟨e, Finset.mem_singleton_self _, Or.inl ⟨rfl, rfl⟩⟩
    · exact Relation.ReflTransGen.single ⟨e, Finset.mem_singleton_self _, Or.inr ⟨rfl, rfl⟩⟩
    · exact Relation.ReflTransGen.refl
  have hK₀_nc : K₀.HasNoCutVertex := by
    intro v hv ⟨_, u, w, hu, hw, hnot⟩
    simp only [K₀, Subgraph.deleteVertex, Finset.mem_erase, Finset.mem_insert,
      Finset.mem_singleton] at hv hu hw
    rcases hv with rfl | rfl
    · have hu' : u = G.head e := hu.2.resolve_left hu.1
      have hw' : w = G.head e := hw.2.resolve_left hw.1
      subst hu'; subst hw'; exact hnot Relation.ReflTransGen.refl
    · have hu' : u = G.tail e := hu.2.resolve_right hu.1
      have hw' : w = G.tail e := hw.2.resolve_right hw.1
      subst hu'; subst hw'; exact hnot Relation.ReflTransGen.refl
  -- Maximize `K.verts.card + K.edges.card` among connected cut-vertex-free subgraphs `K ≥ K₀`
  let Good (k : ℕ) : Prop :=
    ∃ K : G.Subgraph, K₀ ≤ K ∧ K.Connected ∧ K.HasNoCutVertex ∧ K.verts.card + K.edges.card = k
  let S := (Finset.range (Fintype.card V + Fintype.card E + 1)).filter Good
  have hS_ne : S.Nonempty := by
    refine ⟨K₀.verts.card + K₀.edges.card, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_,
      K₀, ⟨Finset.Subset.refl _, Finset.Subset.refl _⟩, hK₀_conn, hK₀_nc, rfl⟩⟩
    have h1 := Finset.card_le_univ K₀.verts
    have h2 := Finset.card_le_univ K₀.edges
    omega
  let kmax := S.max' hS_ne
  obtain ⟨K, hK₀K, hKconn, hKnc, hKcard⟩ := (Finset.mem_filter.mp (Finset.max'_mem S hS_ne)).2
  have hKblock : G.IsBlock K := by
    refine ⟨hKconn, hKnc, fun K' hKK' hK'conn hK'nc => ?_⟩
    have hle_sum : K'.verts.card + K'.edges.card ≤ kmax := by
      apply Finset.le_max' S
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_,
        K', ⟨hK₀K.1.trans hKK'.1, hK₀K.2.trans hKK'.2⟩, hK'conn, hK'nc, rfl⟩
      have h1 := Finset.card_le_univ K'.verts
      have h2 := Finset.card_le_univ K'.edges
      omega
    have hv_le := Finset.card_le_card hKK'.1
    have he_le := Finset.card_le_card hKK'.2
    have hv_eq : K'.verts = K.verts := (Finset.eq_of_subset_of_card_le hKK'.1 (by omega)).symm
    have he_eq : K'.edges = K.edges := (Finset.eq_of_subset_of_card_le hKK'.2 (by omega)).symm
    exact Subgraph.ext hv_eq he_eq
  have heK : e ∈ K.edges := hK₀K.2 (Finset.mem_singleton_self e)
  refine ⟨K, ⟨hKblock, heK⟩, fun K' ⟨hK'block, heK'⟩ => ?_⟩
  -- Uniqueness: `K` and `K'` share `{tail e, head e}` (size 2), so their union is connected & cut-vertex-free!
  have hshare : 2 ≤ (K.verts ∩ K'.verts).card := by
    have hsub : ({G.tail e, G.head e} : Finset V) ⊆ K.verts ∩ K'.verts := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨K.tail_mem heK, K'.tail_mem heK'⟩
      · exact Finset.mem_inter.mpr ⟨K.head_mem heK, K'.head_mem heK'⟩
    exact le_trans (by rw [Finset.card_pair hne]) (Finset.card_le_card hsub)
  obtain ⟨hu_conn, hu_nc⟩ := subgraphUnion_noCutVertex hKconn hK'block.1 hKnc hK'block.2.1 hshare
  have h1 : subgraphUnion K K' = K := hKblock.2.2 _ ⟨Finset.subset_union_left, Finset.subset_union_left⟩ hu_conn hu_nc
  have h2 : subgraphUnion K K' = K' := hK'block.2.2 _ ⟨Finset.subset_union_right, Finset.subset_union_right⟩ hu_conn hu_nc
  exact h2.symm.trans h1

/-- Every cycle subgraph has no cut vertex (parity argument). -/
lemma isCycle_hasNoCutVertex {G : Multigraph V E} {C : G.Subgraph} (hC : C.IsCycle) :
    C.HasNoCutVertex := by
  intro v hv ⟨_, u, w, hu, hw, hnot⟩
  classical
  let Cv := C.deleteVertex v
  let S₁ : Finset V := Cv.verts.filter (fun z => Relation.ReflTransGen Cv.Adj u z)
  let S₂ : Finset V := Cv.verts \ S₁
  have hu1 : u ∈ S₁ := Finset.mem_filter.mpr ⟨hu, Relation.ReflTransGen.refl⟩
  have hw2 : w ∈ S₂ := Finset.mem_sdiff.mpr ⟨hw, fun h => hnot (Finset.mem_filter.mp h).2⟩
  have hS1_sub : S₁ ⊆ C.verts := fun z hz => Finset.erase_subset v C.verts (Finset.mem_filter.mp hz).1
  have hS2_sub : S₂ ⊆ C.verts := fun z hz => Finset.erase_subset v C.verts (Finset.mem_sdiff.mp hz).1
  -- No edge of `C` connects `S₁` to `S₂` (else it would lie in `Cv.edges`!)
  have hno_cross12 : ∀ e ∈ C.edges, ¬ ((G.tail e ∈ S₁ ∧ G.head e ∈ S₂) ∨ (G.tail e ∈ S₂ ∧ G.head e ∈ S₁)) := by
    intro e he hcr
    have ht_ne : G.tail e ≠ v := by
      rcases hcr with ⟨ht, _⟩ | ⟨ht, _⟩
      · exact (Finset.mem_erase.mp (Finset.mem_filter.mp ht).1).1
      · exact (Finset.mem_erase.mp (Finset.mem_sdiff.mp ht).1).1
    have hh_ne : G.head e ≠ v := by
      rcases hcr with ⟨_, hh⟩ | ⟨_, hh⟩
      · exact (Finset.mem_erase.mp (Finset.mem_sdiff.mp hh).1).1
      · exact (Finset.mem_erase.mp (Finset.mem_filter.mp hh).1).1
    have heCv : e ∈ Cv.edges := Finset.mem_filter.mpr ⟨he, ht_ne, hh_ne⟩
    rcases hcr with ⟨ht, hh⟩ | ⟨ht, hh⟩
    · exact (Finset.mem_sdiff.mp hh).2 (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hh).1,
        Relation.ReflTransGen.tail (Finset.mem_filter.mp ht).2 ⟨e, heCv, Or.inl ⟨rfl, rfl⟩⟩⟩)
    · exact (Finset.mem_sdiff.mp ht).2 (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp ht).1,
        Relation.ReflTransGen.tail (Finset.mem_filter.mp hh).2 ⟨e, heCv, Or.inr ⟨rfl, rfl⟩⟩⟩)
  -- For each `i ∈ {1, 2}`, cut of `S_i` in `C` is EVEN (handshake!) and POSITIVE (`C` connected), hence `≥ 2`!
  -- And every edge crossing `S_i` must meet `v` (since none crosses `S₁ ↔ S₂`), so `C.deg v ≥ 4`, contradicting `C.deg v = 2`!
  have hcut_ge2 : ∀ (S : Finset V), S ⊆ C.verts → S.Nonempty → v ∉ S →
      (C.edges.filter (fun e => (G.tail e ∈ S ∧ G.head e ∉ S) ∨ (G.tail e ∉ S ∧ G.head e ∈ S))).card ≥ 2 := by
    intro S hSsub hSne hvS
    have hhs := subgraph_cut_handshake C S hSsub
    have hsum2 : ∑ z ∈ S, C.deg z = 2 * S.card := by
      rw [Finset.sum_congr rfl (fun z hz => hC.2 z (hSsub hz))]; simp [Nat.mul_comm]
    -- Show cut ≥ 1 via connectedness of C
    have hpos : 0 < (C.edges.filter (fun e =>
        (G.tail e ∈ S ∧ G.head e ∉ S) ∨ (G.tail e ∉ S ∧ G.head e ∈ S))).card := by
      rcases hSne with ⟨s₀, hs₀⟩
      have hwalk := hC.1.2 s₀ (hSsub hs₀) v hv
      have hex : ∀ {x : V}, Relation.ReflTransGen C.Adj s₀ x → x ∉ S → ∃ a ∈ S, ∃ b ∉ S, C.Adj a b := by
        intro x hx
        induction hx with
        | refl => intro hnot; exact absurd hs₀ hnot
        | @tail b c hsb hbc ih =>
          intro hcS
          by_cases hbS : b ∈ S
          · exact ⟨b, hbS, c, hcS, hbc⟩
          · exact ih hbS
      rcases hex hwalk hvS with ⟨a, haS, b, hbS, e, heC, ⟨ht, hh⟩ | ⟨ht, hh⟩⟩
      · exact Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨heC, Or.inl ⟨ht ▸ haS, hh ▸ hbS⟩⟩⟩
      · exact Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨heC, Or.inr ⟨ht ▸ hbS, hh ▸ haS⟩⟩⟩
    omega
  have hc1 := hcut_ge2 S₁ hS1_sub ⟨u, hu1⟩ (fun h => (Finset.mem_erase.mp (Finset.mem_filter.mp h).1).1 rfl)
  have hc2 := hcut_ge2 S₂ hS2_sub ⟨w, hw2⟩ (fun h => (Finset.mem_erase.mp (Finset.mem_sdiff.mp h).1).1 rfl)
  let Cut1 := C.edges.filter (fun e => (G.tail e ∈ S₁ ∧ G.head e ∉ S₁) ∨ (G.tail e ∉ S₁ ∧ G.head e ∈ S₁))
  let Cut2 := C.edges.filter (fun e => (G.tail e ∈ S₂ ∧ G.head e ∉ S₂) ∨ (G.tail e ∉ S₂ ∧ G.head e ∈ S₂))
  have hdisj12 : Disjoint Cut1 Cut2 := by
    rw [Finset.disjoint_left]
    intro e he1 he2
    have heC := (Finset.mem_filter.mp he1).1
    have h1 := (Finset.mem_filter.mp he1).2
    have h2 := (Finset.mem_filter.mp he2).2
    have hS12_disj : Disjoint S₁ S₂ := Finset.disjoint_sdiff
    rcases h1 with ⟨ht1, _⟩ | ⟨_, hh1⟩ <;> rcases h2 with ⟨ht2, _⟩ | ⟨_, hh2⟩
    · exact Finset.disjoint_left.mp hS12_disj ht1 ht2
    · exact hno_cross12 e heC (Or.inl ⟨ht1, hh2⟩)
    · exact hno_cross12 e heC (Or.inr ⟨ht2, hh1⟩)
    · exact Finset.disjoint_left.mp hS12_disj hh1 hh2
  have hsub_v : Cut1 ∪ Cut2 ⊆
      C.edges.filter (fun e => G.tail e = v) ∪ C.edges.filter (fun e => G.head e = v) := by
    intro e he
    have hmem_v : ∀ (S : Finset V) (hS : S = S₁ ∨ S = S₂),
        e ∈ C.edges → ((G.tail e ∈ S ∧ G.head e ∉ S) ∨ (G.tail e ∉ S ∧ G.head e ∈ S)) →
        G.tail e = v ∨ G.head e = v := by
      intro S hS heC hcr
      have hpart : ∀ z ∈ C.verts, z = v ∨ z ∈ S₁ ∨ z ∈ S₂ := fun z hz => by
        by_cases hzv : z = v
        · exact Or.inl hzv
        · have hzCv : z ∈ Cv.verts := Finset.mem_erase.mpr ⟨hzv, hz⟩
          by_cases hz1 : z ∈ S₁
          · exact Or.inr (Or.inl hz1)
          · exact Or.inr (Or.inr (Finset.mem_sdiff.mpr ⟨hzCv, hz1⟩))
      rcases hcr with ⟨htS, hhnot⟩ | ⟨htnot, hhS⟩
      · rcases hpart (G.head e) (C.head_mem heC) with hhv | hh1 | hh2
        · exact Or.inr hhv
        · rcases hS with rfl | rfl
          · exact absurd hh1 hhnot
          · exact absurd (Or.inr ⟨htS, hh1⟩) (hno_cross12 e heC)
        · rcases hS with rfl | rfl
          · exact absurd (Or.inl ⟨htS, hh2⟩) (hno_cross12 e heC)
          · exact absurd hh2 hhnot
      · rcases hpart (G.tail e) (C.tail_mem heC) with htv | ht1 | ht2
        · exact Or.inl htv
        · rcases hS with rfl | rfl
          · exact absurd ht1 htnot
          · exact absurd (Or.inl ⟨ht1, hhS⟩) (hno_cross12 e heC)
        · rcases hS with rfl | rfl
          · exact absurd (Or.inr ⟨ht2, hhS⟩) (hno_cross12 e heC)
          · exact absurd ht2 htnot
    rcases Finset.mem_union.mp he with h1 | h2
    · have heC := (Finset.mem_filter.mp h1).1
      rcases hmem_v S₁ (Or.inl rfl) heC (Finset.mem_filter.mp h1).2 with ht | hh
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨heC, ht⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨heC, hh⟩)
    · have heC := (Finset.mem_filter.mp h2).1
      rcases hmem_v S₂ (Or.inr rfl) heC (Finset.mem_filter.mp h2).2 with ht | hh
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨heC, ht⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨heC, hh⟩)
  have hdeg_ge4 : 4 ≤ C.deg v := by
    unfold Subgraph.deg
    calc 4 ≤ Cut1.card + Cut2.card := by dsimp only [Cut1, Cut2]; omega
      _ = (Cut1 ∪ Cut2).card := (Finset.card_union_of_disjoint hdisj12).symm
      _ ≤ (C.edges.filter (fun e => G.tail e = v) ∪ C.edges.filter (fun e => G.head e = v)).card :=
          Finset.card_le_card hsub_v
      _ ≤ _ := Finset.card_union_le _ _
  have hdeg2 := hC.2 v hv
  omega

/-- Every cycle in a loopless graph is contained in a unique block (the block of any of its edges). -/
lemma cycle_subset_block {G : Multigraph V E} (hll : G.IsLoopless)
    {C K : G.Subgraph} (hC : C.IsCycle) (hK : G.IsBlock K)
    {e : E} (heC : e ∈ C.edges) (heK : e ∈ K.edges) :
    C ≤ K := by
  have hshare : 2 ≤ (K.verts ∩ C.verts).card := by
    have hsub : ({G.tail e, G.head e} : Finset V) ⊆ K.verts ∩ C.verts := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨K.tail_mem heK, C.tail_mem heC⟩
      · exact Finset.mem_inter.mpr ⟨K.head_mem heK, C.head_mem heC⟩
    exact le_trans (by rw [Finset.card_pair (hll e)]) (Finset.card_le_card hsub)
  obtain ⟨hu_conn, hu_nc⟩ := subgraphUnion_noCutVertex hK.1 hC.1 hK.2.1 (isCycle_hasNoCutVertex hC) hshare
  have heq := hK.2.2 (subgraphUnion K C) ⟨Finset.subset_union_left, Finset.subset_union_left⟩ hu_conn hu_nc
  rw [← heq]
  exact ⟨Finset.subset_union_right, Finset.subset_union_right⟩

end BlockHelpers

section Lemma34

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- **Lemma 3.4(a) (Blocks of a loopless 3-edge-connected multigraph).** -/
theorem lem_3_4_a
    (H₀ : Multigraph V E) (hll : H₀.IsLoopless) (h3 : H₀.IsEdgeConnected 3)
    (hn : 2 ≤ Fintype.card V) (K : H₀.Subgraph) (hK : H₀.IsBlock K) :
    K.toMultigraph.IsLoopless ∧
    K.toMultigraph.IsEdgeConnected 3 ∧
    2 ≤ K.verts.card ∧
    K.HasNoCutVertex := by
  have hK_ll : K.toMultigraph.IsLoopless := fun e h => hll e.1 (congrArg Subtype.val h)
  have hK_nc : K.HasNoCutVertex := hK.2.1
  -- Show `2 ≤ K.verts.card`
  have hK_v2 : 2 ≤ K.verts.card := by
    by_contra hlt
    rcases hK.1.1 with ⟨u, huK⟩
    have hcard1 : K.verts.card = 1 := by have := Finset.card_pos.mpr ⟨u, huK⟩; omega
    have hKv_eq : K.verts = {u} := by
      symm; exact Finset.eq_of_subset_of_card_le (Finset.singleton_subset_iff.mpr huK) (by simp [hcard1])
    have hKe_empty : K.edges = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro e he
      have ht : H₀.tail e = u := Finset.mem_singleton.mp (hKv_eq ▸ K.tail_mem he)
      have hh : H₀.head e = u := Finset.mem_singleton.mp (hKv_eq ▸ K.head_mem he)
      exact hll e (ht.trans hh.symm)
    -- `u` has degree `≥ 3` in `H₀`, so there is an edge `e` incident to `u`
    have hdeg3 := deg_ge_of_edgeConnected h3 hn u
    have hex_e : ∃ e : E, H₀.tail e = u ∨ H₀.head e = u := by
      unfold Multigraph.deg at hdeg3
      by_cases ht : 0 < (Finset.univ.filter (fun e => H₀.tail e = u)).card
      · rcases Finset.card_pos.mp ht with ⟨e, he⟩
        exact ⟨e, Or.inl (Finset.mem_filter.mp he).2⟩
      · have hh : 0 < (Finset.univ.filter (fun e => H₀.head e = u)).card := by omega
        rcases Finset.card_pos.mp hh with ⟨e, he⟩
        exact ⟨e, Or.inr (Finset.mem_filter.mp he).2⟩
    rcases hex_e with ⟨e, heu⟩
    let K' : H₀.Subgraph :=
      { verts := {H₀.tail e, H₀.head e}
        edges := {e}
        tail_mem := fun he' => by simp [Finset.mem_singleton.mp he']
        head_mem := fun he' => by simp [Finset.mem_singleton.mp he'] }
    have hKK' : K ≤ K' := by
      refine ⟨?_, by simp [hKe_empty]⟩
      rw [hKv_eq, Finset.singleton_subset_iff]
      rcases heu with rfl | rfl <;> simp [K']
    have hK'_conn : K'.Connected := by
      refine ⟨⟨H₀.tail e, Finset.mem_insert_self _ _⟩, fun a ha b hb => ?_⟩
      simp only [K', Finset.mem_insert, Finset.mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact Relation.ReflTransGen.refl
      · exact Relation.ReflTransGen.single ⟨e, Finset.mem_singleton_self _, Or.inl ⟨rfl, rfl⟩⟩
      · exact Relation.ReflTransGen.single ⟨e, Finset.mem_singleton_self _, Or.inr ⟨rfl, rfl⟩⟩
      · exact Relation.ReflTransGen.refl
    have hK'_nc : K'.HasNoCutVertex := by
      intro v hv ⟨_, a, b, ha, hb, hnot⟩
      simp only [K', Subgraph.deleteVertex, Finset.mem_erase, Finset.mem_insert,
        Finset.mem_singleton] at hv ha hb
      rcases hv with rfl | rfl
      · have ha' := ha.2.resolve_left ha.1; have hb' := hb.2.resolve_left hb.1
        subst ha'; subst hb'; exact hnot Relation.ReflTransGen.refl
      · have ha' := ha.2.resolve_right ha.1; have hb' := hb.2.resolve_right hb.1
        subst ha'; subst hb'; exact hnot Relation.ReflTransGen.refl
    have heq := hK.2.2 K' hKK' hK'_conn hK'_nc
    have : K'.verts.card = 2 := by simp [K', Finset.card_pair (hll e)]
    rw [heq] at this; omega
  -- Show `K.toMultigraph.IsEdgeConnected 3` via reachability outside `K.edges`
  have hK_3ec : K.toMultigraph.IsEdgeConnected 3 := by
    classical
    let Hout : H₀.Subgraph :=
      { verts := Finset.univ
        edges := Finset.univ \ K.edges
        tail_mem := fun _ => Finset.mem_univ _
        head_mem := fun _ => Finset.mem_univ _ }
    -- Key claim: no path in `Hout` connects two distinct vertices of `K.verts`
    have hno_ear : ∀ x ∈ K.verts, ∀ y ∈ K.verts, x ≠ y → ¬ Relation.ReflTransGen Hout.Adj x y := by
      intro x hx y hy hxy hwalk
      obtain ⟨verts, edges, hlen, hv_nodup, hhead, hlast, hedges_out, hstep⟩ :=
        exists_simplePath_of_reflTransGen hwalk
      -- Find a minimal sub-segment `[i..j]` (`i < j`) with `verts[i], verts[j] ∈ K.verts` and no interior vertex in `K.verts`
      have hv_pos : 0 < verts.length := by omega
      have hfirst_K : verts[0]'hv_pos ∈ K.verts := by
        cases verts with
        | nil => simp at hhead
        | cons a _ => simp only [List.head?_cons, Option.some.injEq] at hhead; exact hhead ▸ hx
      have hlast_K : verts[edges.length]'(by omega) ∈ K.verts := by
        rw [List.getLast?_eq_getElem?] at hlast
        have hidx : verts.length - 1 = edges.length := by omega
        rw [hidx, List.getElem?_eq_getElem (by omega)] at hlast
        exact Option.some.inj hlast ▸ hy
      have hlen_ge1 : 1 ≤ edges.length := by
        by_contra h0
        have he0 : edges.length = 0 := by omega
        cases verts with
        | nil => simp at hhead
        | cons a as =>
          cases as with
          | nil =>
            simp only [List.head?_cons, List.getLast?_singleton, Option.some.injEq] at hhead hlast
            exact hxy (hhead.symm.trans hlast)
          | cons _ _ => simp at hlen; omega
      -- Let `j` be the LEAST `j ≥ 1` with `verts[j] ∈ K.verts`! Then `i = 0 < j`, `verts[0] ≠ verts[j]`,
      -- and for all `0 < r < j`, `verts[r] ∉ K.verts`!
      have hex_j : ∃ j, 1 ≤ j ∧ j < verts.length ∧ ∃ (hj : j < verts.length), verts[j]'hj ∈ K.verts :=
        ⟨edges.length, hlen_ge1, by omega, by omega, hlast_K⟩
      let j := Nat.find hex_j
      obtain ⟨hj_ge1, hj_lt, _, hvj_K⟩ := Nat.find_spec hex_j
      have hmin_j : ∀ r (hr : r < verts.length), 1 ≤ r → r < j → verts[r]'hr ∉ K.verts := by
        intro r hr hr1 hrj hmem
        exact Nat.find_min hex_j hrj ⟨hr1, hr, hr, hmem⟩
      -- Build ear subgraph `P` on `verts.take (j + 1)` and `edges.take j`
      let pVerts := verts.take (j + 1)
      let pEdges := edges.take j
      let P : H₀.Subgraph :=
        { verts := pVerts.toFinset
          edges := pEdges.toFinset
          tail_mem := fun {e} he => by
            rw [List.mem_toFinset] at he ⊢
            obtain ⟨r, hr, rfl⟩ := List.getElem_of_mem he
            have hrj : r < j := by simp [pEdges] at hr; omega
            simp only [pEdges, List.getElem_take]
            rcases hstep r (by omega) with ⟨ht, _⟩ | ⟨ht, _⟩
            · rw [ht]
              have : pVerts[r]'(by simp [pVerts]; omega) = verts[r]'(by omega) := List.getElem_take
              rw [← this]; exact List.getElem_mem _
            · rw [ht]
              have : pVerts[r + 1]'(by simp [pVerts]; omega) = verts[r + 1]'(by omega) := List.getElem_take
              rw [← this]; exact List.getElem_mem _
          head_mem := fun {e} he => by
            rw [List.mem_toFinset] at he ⊢
            obtain ⟨r, hr, rfl⟩ := List.getElem_of_mem he
            have hrj : r < j := by simp [pEdges] at hr; omega
            simp only [pEdges, List.getElem_take]
            rcases hstep r (by omega) with ⟨_, hh⟩ | ⟨_, hh⟩
            · rw [hh]
              have : pVerts[r + 1]'(by simp [pVerts]; omega) = verts[r + 1]'(by omega) := List.getElem_take
              rw [← this]; exact List.getElem_mem _
            · rw [hh]
              have : pVerts[r]'(by simp [pVerts]; omega) = verts[r]'(by omega) := List.getElem_take
              rw [← this]; exact List.getElem_mem _ }
      -- `K' = K ∪ P` is connected and cut-vertex-free, yet strictly larger than `K`!
      let K' := subgraphUnion K P
      have hK_le : K ≤ K' := ⟨Finset.subset_union_left, Finset.subset_union_left⟩
      have hP_le : P ≤ K' := ⟨Finset.subset_union_right, Finset.subset_union_right⟩
      have hlift : ∀ {A B : H₀.Subgraph}, A ≤ B → ∀ {a b : V},
          Relation.ReflTransGen A.Adj a b → Relation.ReflTransGen B.Adj a b := by
        intro A B hle a b h
        induction h with
        | refl => exact Relation.ReflTransGen.refl
        | tail _ hs ih => rcases hs with ⟨e, he, ha⟩; exact Relation.ReflTransGen.tail ih ⟨e, hle.2 he, ha⟩
      -- Reachability along prefixes/suffixes of `P`
      have hP_step : ∀ (r : ℕ) (hr : r < j), P.Adj (verts[r]'(by omega)) (verts[r + 1]'(by omega)) := by
        intro r hr
        refine ⟨edges[r]'(by omega), List.mem_toFinset.mpr ?_, hstep r (by omega)⟩
        have : edges[r]'(by omega) = pEdges[r]'(by simp [pEdges]; omega) := (List.getElem_take).symm
        rw [this]; exact List.getElem_mem _
      have hP_walk : ∀ (a b : ℕ) (ha : a ≤ b) (hb : b ≤ j) (v_avoid : V),
          (∀ r (hr : r < verts.length), a ≤ r → r ≤ b → verts[r]'hr ≠ v_avoid) →
          Relation.ReflTransGen (K'.deleteVertex v_avoid).Adj (verts[a]'(by omega)) (verts[b]'(by omega)) := by
        intro a b ha hb v_avoid havoid
        induction b with
        | zero =>
          have ha0 : a = 0 := by omega
          subst ha0; exact Relation.ReflTransGen.refl
        | succ b ih =>
          by_cases hab : a = b + 1
          · subst hab; exact Relation.ReflTransGen.refl
          · refine Relation.ReflTransGen.tail (ih (by omega) (by omega) (fun r hr h1 h2 => havoid r hr h1 (by omega))) ?_
            rcases hP_step b (by omega) with ⟨e, heP, hadj⟩
            have hne1 : verts[b]'(by omega) ≠ v_avoid := havoid b (by omega) (by omega) (by omega)
            have hne2 : verts[b + 1]'(by omega) ≠ v_avoid := havoid (b + 1) (by omega) (by omega) le_rfl
            have het : H₀.tail e ≠ v_avoid := by rcases hadj with ⟨ht, _⟩ | ⟨ht, _⟩ <;> [exact ht ▸ hne1; exact ht ▸ hne2]
            have heh : H₀.head e ≠ v_avoid := by rcases hadj with ⟨_, hh⟩ | ⟨_, hh⟩ <;> [exact hh ▸ hne2; exact hh ▸ hne1]
            exact ⟨e, Finset.mem_filter.mpr ⟨hP_le.2 heP, het, heh⟩, hadj⟩
      have hK'_conn : K'.Connected := by
        refine ⟨⟨verts[0]'hv_pos, Finset.mem_union_left _ hfirst_K⟩, fun u hu v hv => ?_⟩
        have hto0 : ∀ z ∈ K'.verts, Relation.ReflTransGen K'.Adj z (verts[0]'hv_pos) := by
          intro z hz
          rcases Finset.mem_union.mp hz with hzK | hzP
          · exact hlift hK_le (hK.1.2 z hzK _ hfirst_K)
          · rw [List.mem_toFinset] at hzP
            obtain ⟨r, hr, rfl⟩ := List.getElem_of_mem hzP
            have hrj : r ≤ j := by simp [pVerts] at hr; omega
            simp only [pVerts, List.getElem_take]
            -- Walk from `verts[r]` back to `verts[0]` in `P`
            have h0r : ∀ (m : ℕ) (hm : m ≤ j), Relation.ReflTransGen P.Adj (verts[0]'hv_pos) (verts[m]'(by omega)) := by
              intro m
              induction m with
              | zero => intro _; exact Relation.ReflTransGen.refl
              | succ m ihm => intro hm; exact Relation.ReflTransGen.tail (ihm (by omega)) (hP_step m (by omega))
            exact hlift hP_le (subgraph_adj_symm (h0r r hrj))
        exact Relation.ReflTransGen.trans (hto0 u hu) (subgraph_adj_symm (hto0 v hv))
      have hK'_nc : K'.HasNoCutVertex := by
        intro v hv ⟨_, u, w, hu, hw, hnot⟩
        have hKdel_le : K.deleteVertex v ≤ K'.deleteVertex v :=
          ⟨Finset.erase_subset_erase v Finset.subset_union_left,
           Finset.filter_subset_filter _ Finset.subset_union_left⟩
        have hKdel_conn : ∀ a ∈ K.verts, ∀ b ∈ K.verts, a ≠ v → b ≠ v →
            Relation.ReflTransGen (K'.deleteVertex v).Adj a b := by
          intro a ha b hb hav hbv
          apply hlift hKdel_le
          by_cases hvK : v ∈ K.verts
          · by_contra hno
            exact hK.2.1 v hvK ⟨hvK, a, b, Finset.mem_erase.mpr ⟨hav, ha⟩,
              Finset.mem_erase.mpr ⟨hbv, hb⟩, hno⟩
          · have heq : K.deleteVertex v = K := by
              ext z
              · simp [Subgraph.deleteVertex, Finset.erase_eq_of_notMem hvK]
              · simp only [Subgraph.deleteVertex, Finset.mem_filter, and_iff_left_iff_imp]
                intro hz; exact ⟨fun ht => hvK (ht ▸ K.tail_mem hz), fun hh => hvK (hh ▸ K.head_mem hz)⟩
            rw [heq]; exact hK.1.2 a ha b hb
        -- Pick a target vertex `anchor ∈ K.verts` with `anchor ≠ v` (one of `verts[0], verts[j]`!)
        have hv0_ne_vj : verts[0]'hv_pos ≠ verts[j]'hj_lt := fun h => by
          have := (List.Nodup.getElem_inj_iff hv_nodup).mp h; omega
        -- Every `z ∈ (K'.deleteVertex v).verts` reaches `verts[0]` or `verts[j]` (whichever is ≠ v)
        let anchor := if verts[0]'hv_pos = v then verts[j]'hj_lt else verts[0]'hv_pos
        have hanch_K : anchor ∈ K.verts := by dsimp only [anchor]; split_ifs <;> assumption
        have hanch_ne : anchor ≠ v := by dsimp only [anchor]; split_ifs with h <;> [exact fun h' => hv0_ne_vj (h.trans h'.symm); exact h]
        have hreach_anch : ∀ z ∈ (K'.deleteVertex v).verts,
            Relation.ReflTransGen (K'.deleteVertex v).Adj z anchor := by
          intro z hz
          have hzv : z ≠ v := (Finset.mem_erase.mp hz).1
          have hzK' : z ∈ K'.verts := (Finset.mem_erase.mp hz).2
          rcases Finset.mem_union.mp hzK' with hzK | hzP
          · exact hKdel_conn z hzK anchor hanch_K hzv hanch_ne
          · rw [List.mem_toFinset] at hzP
            obtain ⟨r, hr, rfl⟩ := List.getElem_of_mem hzP
            have hrj : r ≤ j := by simp [pVerts] at hr; omega
            simp only [pVerts, List.getElem_take] at hzv ⊢
            by_cases hv_on_left : ∃ s, s ≤ r ∧ ∃ (hs : s < verts.length), verts[s]'hs = v
            · -- `v` is on `[0..r]` (actually `< r` since `verts[r] ≠ v`), so `[r..j]` avoids `v`!
              rcases hv_on_left with ⟨s, hsr, hs, hvs⟩
              have hne_s : s ≠ r := fun h => hzv (h ▸ hvs)
              have havoid : ∀ t (ht : t < verts.length), r ≤ t → t ≤ j → verts[t]'ht ≠ v := by
                intro t ht hrt _ heqt
                have hst : t = s := (List.Nodup.getElem_inj_iff hv_nodup).mp (heqt.trans hvs.symm)
                omega
              have hw1 := hP_walk r j hrj le_rfl v havoid
              have hvj_ne : verts[j]'hj_lt ≠ v := havoid j hj_lt hrj le_rfl
              exact Relation.ReflTransGen.trans hw1 (hKdel_conn _ hvj_K anchor hanch_K hvj_ne hanch_ne)
            · push Not at hv_on_left
              have havoid : ∀ t (ht : t < verts.length), 0 ≤ t → t ≤ r → verts[t]'ht ≠ v :=
                fun t ht _ htr => hv_on_left t htr ht
              have hw1 := subgraph_adj_symm (hP_walk 0 r (Nat.zero_le r) hrj v havoid)
              have hv0_ne : verts[0]'hv_pos ≠ v := havoid 0 hv_pos le_rfl (Nat.zero_le r)
              exact Relation.ReflTransGen.trans hw1 (hKdel_conn _ hfirst_K anchor hanch_K hv0_ne hanch_ne)
        exact hnot (Relation.ReflTransGen.trans (hreach_anch u hu) (subgraph_adj_symm (hreach_anch w hw)))
      have heq := hK.2.2 K' hK_le hK'_conn hK'_nc
      -- Yet `edges[0] ∈ P.edges ⊆ K'.edges = K.edges`, contradicting `edges[0] ∈ Hout.edges`!
      have he0_P : edges[0]'(by omega) ∈ P.edges := by
        rw [List.mem_toFinset]
        have : edges[0]'(by omega) = pEdges[0]'(by simp [pEdges]; omega) := (List.getElem_take).symm
        rw [this]; exact List.getElem_mem _
      have he0_K : edges[0]'(by omega) ∈ K.edges := by
        have heqE : K'.edges = K.edges := congrArg Subgraph.edges heq
        rw [← heqE]; exact Finset.mem_union_right _ he0_P
      have he0_out := hedges_out (edges[0]'(by omega)) (List.getElem_mem _)
      exact (Finset.mem_sdiff.mp he0_out).2 he0_K
    -- Every `v : V` reaches a unique `x ∈ K.verts` in `Hout`
    have hreach_K : ∀ v : V, ∃ x ∈ K.verts, Relation.ReflTransGen Hout.Adj x v := by
      intro v
      rcases hK.1.1 with ⟨x₀, hx₀⟩
      have hwalk := connected_of_edgeConnected (by omega : 1 ≤ 3) h3 v x₀
      induction hwalk using Relation.ReflTransGen.head_induction_on with
      | refl => exact ⟨x₀, hx₀, Relation.ReflTransGen.refl⟩
      | @head a b hab _ ih =>
        by_cases ha : a ∈ K.verts
        · exact ⟨a, ha, Relation.ReflTransGen.refl⟩
        · rcases ih with ⟨x, hxK, hxb⟩
          rcases hab with ⟨e, hab_e⟩
          have he_notK : e ∉ K.edges := fun heK => by
            rcases hab_e with ⟨ht, _⟩ | ⟨_, hh⟩
            · exact ha (ht ▸ K.tail_mem heK)
            · exact ha (hh ▸ K.head_mem heK)
          have heOut : e ∈ Hout.edges := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, he_notK⟩
          have hba : Hout.Adj b a := ⟨e, heOut, by rcases hab_e with h | h <;> [exact Or.inr h; exact Or.inl h]⟩
          exact ⟨x, hxK, Relation.ReflTransGen.tail hxb hba⟩
    -- Now prove `K.toMultigraph.IsEdgeConnected 3`
    intro S hSne hScomp
    let Sbig : Finset V := Finset.univ.filter (fun v => ∃ x ∈ S, Relation.ReflTransGen Hout.Adj x.1 v)
    have hSbig_ne : Sbig.Nonempty := by
      rcases hSne with ⟨x, hxS⟩
      exact ⟨x.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, hxS, Relation.ReflTransGen.refl⟩⟩
    have hSbig_comp : (Finset.univ \ Sbig).Nonempty := by
      rcases hScomp with ⟨y, hyS⟩
      have hy_notS : y ∉ S := (Finset.mem_sdiff.mp hyS).2
      refine ⟨y.1, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hyBig => ?_⟩⟩
      rcases (Finset.mem_filter.mp hyBig).2 with ⟨x, hxS, hxy⟩
      have hxeq : x.1 = y.1 := by
        by_contra hne; exact hno_ear x.1 x.2 y.1 y.2 hne hxy
      exact hy_notS (Subtype.ext hxeq ▸ hxS)
    have hcut3 := h3 Sbig hSbig_ne hSbig_comp
    -- Every edge `e ∈ H₀.cutEdges Sbig` MUST lie in `K.edges` and cross `S`!
    have hcut_in_K : ∀ e ∈ H₀.cutEdges Sbig, e ∈ K.edges := by
      intro e he
      by_contra hnotK
      have heOut : e ∈ Hout.edges := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnotK⟩
      rcases (Finset.mem_filter.mp he).2 with ⟨ht, hh⟩ | ⟨ht, hh⟩
      · rcases (Finset.mem_filter.mp ht).2 with ⟨x, hxS, hxt⟩
        exact hh (Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, hxS,
          Relation.ReflTransGen.tail hxt ⟨e, heOut, Or.inl ⟨rfl, rfl⟩⟩⟩)
      · rcases (Finset.mem_filter.mp hh).2 with ⟨x, hxS, hxh⟩
        exact ht (Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, hxS,
          Relation.ReflTransGen.tail hxh ⟨e, heOut, Or.inr ⟨rfl, rfl⟩⟩⟩)
    -- And for `x : {v // v ∈ K.verts}`, `x.1 ∈ Sbig ↔ x ∈ S`
    have hK_in_Sbig : ∀ x : {v : V // v ∈ K.verts}, x.1 ∈ Sbig ↔ x ∈ S := by
      intro x
      constructor
      · intro hxBig
        rcases (Finset.mem_filter.mp hxBig).2 with ⟨y, hyS, hyx⟩
        have hyeq : y.1 = x.1 := by
          by_contra hne; exact hno_ear y.1 y.2 x.1 x.2 hne hyx
        exact Subtype.ext hyeq ▸ hyS
      · intro hxS
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, hxS, Relation.ReflTransGen.refl⟩
    have hcard_le : (H₀.cutEdges Sbig).card ≤ (K.toMultigraph.cutEdges S).card := by
      have hne_e : (K.toMultigraph.cutEdges S).card ≥ (H₀.cutEdges Sbig).card := by
        let g : {e : E // e ∈ K.edges} → E := Subtype.val
        have hsub : H₀.cutEdges Sbig ⊆ (K.toMultigraph.cutEdges S).image g := by
          intro e he
          have heK := hcut_in_K e he
          refine Finset.mem_image.mpr ⟨⟨e, heK⟩, ?_, rfl⟩
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          have h1 := hK_in_Sbig ⟨H₀.tail e, K.tail_mem heK⟩
          have h2 := hK_in_Sbig ⟨H₀.head e, K.head_mem heK⟩
          dsimp only [Subgraph.toMultigraph]
          rw [← h1, ← h2]
          exact (Finset.mem_filter.mp he).2
        exact le_trans (Finset.card_le_card hsub) Finset.card_image_le
      exact hne_e
    omega
  exact ⟨hK_ll, hK_3ec, hK_v2, hK_nc⟩

/-- Helper: in a cycle `Fin d` (`d ≥ 2`), any nonempty proper subset `A ⊂ Fin d` has at least `2`
indices `i : Fin d` where `(i ∈ A) ≠ ((i + 1) % d ∈ A)`. -/
private lemma cycle_fin_cut_ge2 {d : ℕ} (hd : 2 ≤ d) (A : Finset (Fin d))
    (hAne : A.Nonempty) (hAcomp : (Finset.univ \ A).Nonempty) :
    2 ≤ (Finset.univ.filter (fun i : Fin d =>
      let j : Fin d := ⟨(i.1 + 1) % d, Nat.mod_lt _ (by omega)⟩
      (i ∈ A ∧ j ∉ A) ∨ (i ∉ A ∧ j ∈ A))).card := by
  have hd_pos : 0 < d := by omega
  -- Find an edge leaving `A` (`i₁ ∈ A`, `next i₁ ∉ A`) and an edge entering `A` (`i₂ ∉ A`, `next i₂ ∈ A`)
  have hstep_walk : ∀ (P : Fin d → Prop) [DecidablePred P],
      (∃ a, P a) → (∃ b, ¬ P b) →
      ∃ i : Fin d, P i ∧ ¬ P ⟨(i.1 + 1) % d, Nat.mod_lt _ hd_pos⟩ := by
    intro P _ ⟨a, ha⟩ ⟨b, hb⟩
    by_contra hall
    push Not at hall
    have hind : ∀ k : ℕ, P ⟨(a.1 + k) % d, Nat.mod_lt _ hd_pos⟩ := by
      intro k
      induction k with
      | zero => simpa [Nat.mod_eq_of_lt a.2] using ha
      | succ k ih =>
        have hnext := hall ⟨(a.1 + k) % d, Nat.mod_lt _ hd_pos⟩ ih
        have hmod : ((a.1 + k) % d + 1) % d = (a.1 + (k + 1)) % d := by
          rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.add_assoc]
        simpa only [hmod] using hnext
    have hreach_b : ∃ k, (a.1 + k) % d = b.1 := by
      refine ⟨(b.1 + d - a.1) % d, ?_⟩
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      have : a.1 + (b.1 + d - a.1) = b.1 + d := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt b.2]
    rcases hreach_b with ⟨k, hk⟩
    have hpb := hind k
    have : (⟨(a.1 + k) % d, Nat.mod_lt _ hd_pos⟩ : Fin d) = b := Fin.ext hk
    rw [this] at hpb
    exact hb hpb
  rcases hAne with ⟨a, haA⟩
  rcases hAcomp with ⟨b, hb⟩
  have hbA : b ∉ A := (Finset.mem_sdiff.mp hb).2
  obtain ⟨i₁, hi₁A, hi₁_next⟩ := hstep_walk (fun x => x ∈ A) ⟨a, haA⟩ ⟨b, hbA⟩
  obtain ⟨i₂, hi₂_not, hi₂_next⟩ := hstep_walk (fun x => x ∉ A) ⟨b, hbA⟩ ⟨a, fun h => h haA⟩
  push Not at hi₂_next
  have hne : i₁ ≠ i₂ := fun h => hi₂_not (h ▸ hi₁A)
  have hsub : ({i₁, i₂} : Finset (Fin d)) ⊆ Finset.univ.filter (fun i : Fin d =>
      let j : Fin d := ⟨(i.1 + 1) % d, Nat.mod_lt _ hd_pos⟩
      (i ∈ A ∧ j ∉ A) ∨ (i ∉ A ∧ j ∈ A)) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ⟨hi₁A, hi₁_next⟩⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨hi₂_not, hi₂_next⟩⟩
  exact le_trans (by rw [Finset.card_pair hne]) (Finset.card_le_card hsub)

/-- **Lemma 3.4(b) (Truncated cubic expansion of a block).** -/
theorem lem_3_4_b
    (K : Multigraph V E) (hll : K.IsLoopless) (h3 : K.IsEdgeConnected 3)
    (hn : 2 ≤ Fintype.card V) (hnc : (Multigraph.Subgraph.top K).HasNoCutVertex) :
    Nonempty (TruncatedCubicExpansion K) := by
  classical
  -- Step 1: Pick two distinct vertices `u₁ ≠ u₂ : V` and form `K⁺` on `Option V`, `E ⊕ Fin 3`
  obtain ⟨u₁, u₂, hu12⟩ := Fintype.one_lt_card_iff.mp (by omega : 1 < Fintype.card V)
  let Kplus : Multigraph (Option V) (E ⊕ Fin 3) :=
    { tail := fun e => match e with
        | Sum.inl e' => some (K.tail e')
        | Sum.inr _ => none
      head := fun e => match e with
        | Sum.inl e' => some (K.head e')
        | Sum.inr i => if i.1 = 2 then some u₂ else some u₁ }
  have hKp_ll : Kplus.IsLoopless := by
    intro e
    cases e with
    | inl e' => intro h; exact hll e' (Option.some.inj h)
    | inr i =>
      dsimp only [Kplus]
      split_ifs <;> intro h <;> cases h
  have hKp_deg_none : Kplus.deg none = 3 := by
    unfold Multigraph.deg
    have ht : (Finset.univ.filter (fun e : E ⊕ Fin 3 => Kplus.tail e = none)).card = 3 := by
      have heq : Finset.univ.filter (fun e : E ⊕ Fin 3 => Kplus.tail e = none) =
          Finset.univ.image Sum.inr := by
        ext e; cases e with
        | inl _ => simp [Kplus]
        | inr i => simp [Kplus]
      rw [heq, Finset.card_image_of_injective _ Sum.inr_injective, Finset.card_univ, Fintype.card_fin]
    have hh : (Finset.univ.filter (fun e : E ⊕ Fin 3 => Kplus.head e = none)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro e he
      have h1 := (Finset.mem_filter.mp he).2
      cases e with
      | inl _ => dsimp only [Kplus] at h1; cases h1
      | inr i => dsimp only [Kplus] at h1; split_ifs at h1 <;> cases h1
    omega
  have hKp_deg_ge3 : ∀ x : Option V, 3 ≤ Kplus.deg x := by
    intro x
    cases x with
    | none => omega
    | some u =>
      have hKu := deg_ge_of_edgeConnected h3 hn u
      unfold Multigraph.deg at hKu ⊢
      have ht_le : (Finset.univ.filter (fun e : E => K.tail e = u)).card ≤
          (Finset.univ.filter (fun e : E ⊕ Fin 3 => Kplus.tail e = some u)).card := by
        rw [← Finset.card_image_of_injective (f := (Sum.inl : E → E ⊕ Fin 3)) _ Sum.inl_injective]
        apply Finset.card_le_card
        intro e he
        rcases Finset.mem_image.mp he with ⟨e', he', rfl⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, congrArg some (Finset.mem_filter.mp he').2⟩
      have hh_le : (Finset.univ.filter (fun e : E => K.head e = u)).card ≤
          (Finset.univ.filter (fun e : E ⊕ Fin 3 => Kplus.head e = some u)).card := by
        rw [← Finset.card_image_of_injective (f := (Sum.inl : E → E ⊕ Fin 3)) _ Sum.inl_injective]
        apply Finset.card_le_card
        intro e he
        rcases Finset.mem_image.mp he with ⟨e', he', rfl⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, congrArg some (Finset.mem_filter.mp he').2⟩
      omega
  have hKp_deg_u1 : 4 ≤ Kplus.deg (some u₁) := by
    have hKu := deg_ge_of_edgeConnected h3 hn u₁
    unfold Multigraph.deg at hKu ⊢
    have ht_le : (Finset.univ.filter (fun e : E => K.tail e = u₁)).card ≤
        (Finset.univ.filter (fun e : E ⊕ Fin 3 => Kplus.tail e = some u₁)).card := by
      rw [← Finset.card_image_of_injective (f := (Sum.inl : E → E ⊕ Fin 3)) _ Sum.inl_injective]
      apply Finset.card_le_card
      intro e he; rcases Finset.mem_image.mp he with ⟨e', he', rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, congrArg some (Finset.mem_filter.mp he').2⟩
    have hh_lt : (Finset.univ.filter (fun e : E => K.head e = u₁)).card + 1 ≤
        (Finset.univ.filter (fun e : E ⊕ Fin 3 => Kplus.head e = some u₁)).card := by
      have hsub : insert (Sum.inr (0 : Fin 3))
          ((Finset.univ.filter (fun e : E => K.head e = u₁)).image Sum.inl) ⊆
          Finset.univ.filter (fun e : E ⊕ Fin 3 => Kplus.head e = some u₁) := by
        intro e he
        rcases Finset.mem_insert.mp he with rfl | h1
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [Kplus]⟩
        · rcases Finset.mem_image.mp h1 with ⟨e', he', rfl⟩
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, congrArg some (Finset.mem_filter.mp he').2⟩
      have hnot : Sum.inr (0 : Fin 3) ∉ (Finset.univ.filter (fun e : E => K.head e = u₁)).image Sum.inl := by
        simp
      have hc := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem hnot, Finset.card_image_of_injective _ Sum.inl_injective] at hc
      exact hc
    omega
  -- `K⁺` is 3-edge-connected
  have hKp_3ec : Kplus.IsEdgeConnected 3 := by
    intro S hSne hScomp
    let SV : Finset V := Finset.univ.filter (fun u => some u ∈ S)
    by_cases hSV_empty : SV = ∅
    · -- `S = {none}`, so all 3 edges `Sum.inr i` cross `S`!
      have hS_none : S = {none} := by
        ext x; cases x with
        | none =>
          simp only [Finset.mem_singleton, iff_true]
          rcases hSne with ⟨y, hyS⟩
          cases y with
          | none => exact hyS
          | some u =>
            have : u ∈ SV := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyS⟩
            rw [hSV_empty] at this; exact absurd this (Finset.notMem_empty _)
        | some u =>
          simp only [Finset.mem_singleton, reduceCtorEq, iff_false]
          intro huS
          have : u ∈ SV := Finset.mem_filter.mpr ⟨Finset.mem_univ _, huS⟩
          rw [hSV_empty] at this; exact absurd this (Finset.notMem_empty _)
      have hsub : (Finset.univ.image (Sum.inr : Fin 3 → E ⊕ Fin 3)) ⊆ Kplus.cutEdges S := by
        intro e he
        rcases Finset.mem_image.mp he with ⟨i, _, rfl⟩
        rw [hS_none]
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ⟨Finset.mem_singleton.mpr rfl, ?_⟩⟩
        dsimp only [Kplus]; split_ifs <;> simp
      calc 3 = (Finset.univ.image (Sum.inr : Fin 3 → E ⊕ Fin 3)).card := by
            rw [Finset.card_image_of_injective _ Sum.inr_injective, Finset.card_univ, Fintype.card_fin]
        _ ≤ (Kplus.cutEdges S).card := Finset.card_le_card hsub
    · by_cases hSV_univ : SV = Finset.univ
      · -- `univ \ S = {none}`, so all 3 edges `Sum.inr i` cross `S`!
        have hnone_notS : none ∉ S := by
          intro hnone
          rcases hScomp with ⟨y, hy⟩
          have hynot := (Finset.mem_sdiff.mp hy).2
          cases y with
          | none => exact hynot hnone
          | some u =>
            have : u ∈ SV := by rw [hSV_univ]; exact Finset.mem_univ _
            exact hynot (Finset.mem_filter.mp this).2
        have hsub : (Finset.univ.image (Sum.inr : Fin 3 → E ⊕ Fin 3)) ⊆ Kplus.cutEdges S := by
          intro e he
          rcases Finset.mem_image.mp he with ⟨i, _, rfl⟩
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨hnone_notS, ?_⟩⟩
          have hu_in : ∀ u : V, some u ∈ S := fun u =>
            (Finset.mem_filter.mp (by rw [hSV_univ]; exact Finset.mem_univ u : u ∈ SV)).2
          dsimp only [Kplus]; split_ifs <;> exact hu_in _
        calc 3 = (Finset.univ.image (Sum.inr : Fin 3 → E ⊕ Fin 3)).card := by
              rw [Finset.card_image_of_injective _ Sum.inr_injective, Finset.card_univ, Fintype.card_fin]
          _ ≤ (Kplus.cutEdges S).card := Finset.card_le_card hsub
      · -- `SV` is a proper nonempty subset of `V`, so `≥ 3` edges of `K` cross `SV`, hence cross `S`!
        have hSV_ne : SV.Nonempty := Finset.nonempty_iff_ne_empty.mpr hSV_empty
        have hSV_comp : (Finset.univ \ SV).Nonempty := by
          by_contra h0
          rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at h0
          exact hSV_univ (Finset.Subset.antisymm (Finset.subset_univ _) h0)
        have hKcut := h3 SV hSV_ne hSV_comp
        have hsub : (K.cutEdges SV).image Sum.inl ⊆ Kplus.cutEdges S := by
          intro e he
          rcases Finset.mem_image.mp he with ⟨e', he', rfl⟩
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          have hcr := (Finset.mem_filter.mp he').2
          simp only [SV, Finset.mem_filter, Finset.mem_univ, true_and] at hcr
          exact hcr
        calc 3 ≤ (K.cutEdges SV).card := hKcut
          _ = ((K.cutEdges SV).image Sum.inl).card := (Finset.card_image_of_injective _ Sum.inl_injective).symm
          _ ≤ (Kplus.cutEdges S).card := Finset.card_le_card hsub
  -- `K⁺` has no cut vertex
  have hKp_nc : (Subgraph.top Kplus).HasNoCutVertex := by
    intro x _ ⟨_, a, b, ha, hb, hnot⟩
    have hav : a ≠ x := (Finset.mem_erase.mp ha).1
    have hbv : b ≠ x := (Finset.mem_erase.mp hb).1
    cases x with
    | none =>
      cases a with
      | none => exact hav rfl
      | some ua =>
        cases b with
        | none => exact hbv rfl
        | some ub =>
          have hwalk := connected_of_edgeConnected (by omega : 1 ≤ 3) h3 ua ub
          apply hnot
          clear ha hb hav hbv hnot
          induction hwalk with
          | refl => exact Relation.ReflTransGen.refl
          | tail _ hstep ih =>
            rcases hstep with ⟨e, h⟩
            refine Relation.ReflTransGen.tail ih ⟨Sum.inl e, ?_, ?_⟩
            · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (fun h => by cases h), (fun h => by cases h)⟩
            · rcases h with ⟨ht, hh⟩ | ⟨ht, hh⟩
              · left; exact ⟨congrArg some ht, congrArg some hh⟩
              · right; exact ⟨congrArg some ht, congrArg some hh⟩
    | some u =>
      -- Every `some w` (`w ≠ u`) is connected inside `K - u`, and `none` connects to `some u₁` or `some u₂` (`≠ some u`)!
      have hKu_conn : ∀ w₁ w₂ : V, w₁ ≠ u → w₂ ≠ u →
          Relation.ReflTransGen ((Subgraph.top Kplus).deleteVertex (some u)).Adj (some w₁) (some w₂) := by
        intro w₁ w₂ hw1 hw2
        have hKwalk : Relation.ReflTransGen ((Subgraph.top K).deleteVertex u).Adj w₁ w₂ := by
          by_contra hno
          exact hnc u (Finset.mem_univ u) ⟨Finset.mem_univ u, w₁, w₂,
            Finset.mem_erase.mpr ⟨hw1, Finset.mem_univ _⟩,
            Finset.mem_erase.mpr ⟨hw2, Finset.mem_univ _⟩, hno⟩
        clear hw2
        induction hKwalk with
        | refl => exact Relation.ReflTransGen.refl
        | tail _ hstep ih =>
          rcases hstep with ⟨e, he, hadj⟩
          have hne_t : K.tail e ≠ u := (Finset.mem_filter.mp he).2.1
          have hne_h : K.head e ≠ u := (Finset.mem_filter.mp he).2.2
          refine Relation.ReflTransGen.tail ih ⟨Sum.inl e, ?_, ?_⟩
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
              fun h => hne_t (Option.some.inj h), fun h => hne_h (Option.some.inj h)⟩
          · rcases hadj with ⟨ht, hh⟩ | ⟨ht, hh⟩
            · left; exact ⟨congrArg some ht, congrArg some hh⟩
            · right; exact ⟨congrArg some ht, congrArg some hh⟩
      -- Pick `u0 ∈ {u₁, u₂}` with `u0 ≠ u`, adjacent to `none` in `K⁺ - some u`
      let u0 := if u₁ = u then u₂ else u₁
      have hu0_ne : u0 ≠ u := by dsimp only [u0]; split_ifs with h <;> [exact fun h' => hu12 (h.trans h'.symm); exact h]
      have hnone_u0 : ((Subgraph.top Kplus).deleteVertex (some u)).Adj none (some u0) := by
        by_cases h1 : u₁ = u
        · refine ⟨Sum.inr ⟨2, by omega⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, (fun h => by cases h), ?_⟩,
            Or.inl ⟨rfl, ?_⟩⟩
          · dsimp only [Kplus]; simp [u0, h1] at hu0_ne ⊢; exact hu0_ne
          · dsimp only [Kplus]; simp [u0, h1]
        · refine ⟨Sum.inr ⟨0, by omega⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, (fun h => by cases h), ?_⟩,
            Or.inl ⟨rfl, ?_⟩⟩
          · dsimp only [Kplus]; simp [u0, h1]
          · dsimp only [Kplus]; simp [u0, h1]
      have hreach_u0 : ∀ z : Option V, z ≠ some u →
          Relation.ReflTransGen ((Subgraph.top Kplus).deleteVertex (some u)).Adj z (some u0) := by
        intro z hz
        cases z with
        | none => exact Relation.ReflTransGen.single hnone_u0
        | some w => exact hKu_conn w u0 (fun h => hz (congrArg some h)) hu0_ne
      exact hnot (Relation.ReflTransGen.trans (hreach_u0 a hav) (subgraph_adj_symm (hreach_u0 b hbv)))
  -- Step 2: Expand every `x : Option V` with `4 ≤ Kplus.deg x` into a cycle of length `Kplus.deg x`
  let Inc (x : Option V) := {e : E ⊕ Fin 3 // Kplus.tail e = x ∨ Kplus.head e = x}
  have hcard_Inc : ∀ x : Option V, Fintype.card (Inc x) = Kplus.deg x := by
    intro x
    unfold Multigraph.deg
    rw [Fintype.card_subtype]
    have hdisj : Disjoint (Finset.univ.filter (fun e => Kplus.tail e = x))
        (Finset.univ.filter (fun e => Kplus.head e = x)) := by
      rw [Finset.disjoint_left]; intro e ht hh
      exact hKp_ll e ((Finset.mem_filter.mp ht).2.trans (Finset.mem_filter.mp hh).2.symm)
    rw [← Finset.card_union_of_disjoint hdisj]
    congr 1; ext e; simp
  let attach (x : Option V) : Inc x ≃ Fin (Kplus.deg x) :=
    Fintype.equivFinOfCardEq (hcard_Inc x)
  let expDeg (x : Option V) : ℕ := if 4 ≤ Kplus.deg x then Kplus.deg x else 1
  have hexpDeg_pos : ∀ x, 0 < expDeg x := fun x => by dsimp only [expDeg]; split_ifs <;> omega
  let slot (x : Option V) (e : E ⊕ Fin 3) (hinc : Kplus.tail e = x ∨ Kplus.head e = x) : Fin (expDeg x) :=
    if h4 : 4 ≤ Kplus.deg x then
      ⟨(attach x ⟨e, hinc⟩).1, by dsimp only [expDeg]; simp [h4]⟩
    else ⟨0, hexpDeg_pos x⟩
  let Vc := Σ x : Option V, Fin (expDeg x)
  let ExpIdx := {x : Option V // 4 ≤ Kplus.deg x}
  let Ec := (E ⊕ Fin 3) ⊕ (Σ x : ExpIdx, Fin (Kplus.deg x.1))
  let Kc : Multigraph Vc Ec :=
    { tail := fun e => match e with
        | Sum.inl e' => ⟨Kplus.tail e', slot (Kplus.tail e') e' (Or.inl rfl)⟩
        | Sum.inr ⟨⟨x, hx⟩, i⟩ => ⟨x, ⟨i.1, by dsimp only [expDeg]; simp [hx]⟩⟩
      head := fun e => match e with
        | Sum.inl e' => ⟨Kplus.head e', slot (Kplus.head e') e' (Or.inr rfl)⟩
        | Sum.inr ⟨⟨x, hx⟩, i⟩ =>
            ⟨x, ⟨(i.1 + 1) % Kplus.deg x, by
              dsimp only [expDeg]; simp only [hx, ↓reduceIte]
              exact Nat.mod_lt _ (by omega)⟩⟩ }
  have hVc_eq : ∀ {x y : Option V} {a : Fin (expDeg x)} {b : Fin (expDeg y)},
      x = y → a.1 = b.1 → (⟨x, a⟩ : Vc) = ⟨y, b⟩ := by
    rintro x _ a b rfl h; exact Sigma.ext rfl (heq_of_eq (Fin.ext h))
  have hslot_congr : ∀ {x y : Option V} (e' : E ⊕ Fin 3) (hxy : x = y)
      (hx : Kplus.tail e' = x ∨ Kplus.head e' = x) (hy : Kplus.tail e' = y ∨ Kplus.head e' = y),
      (slot x e' hx).1 = (slot y e' hy).1 := by
    intro x y e' hxy hx hy; subst hxy; rfl
  -- Verify `Kc` is cubic!
  have hKc_cubic : Kc.IsCubic := by
    intro ⟨x, i⟩
    by_cases h4 : 4 ≤ Kplus.deg x
    · -- Vertex on cycle `O_x`: 1 incident `inl` edge + 1 outgoing cycle edge + 1 incoming cycle edge = 3!
      have hi_lt : i.1 < Kplus.deg x := lt_of_lt_of_eq i.2 (if_pos h4)
      let iFin : Fin (Kplus.deg x) := ⟨i.1, hi_lt⟩
      let e₀ := (attach x).symm iFin
      have he₀_slot_val : (slot x e₀.1 e₀.2).1 = i.1 := by
        dsimp only [slot]; rw [dif_pos h4]; simp [e₀, iFin]
      have hinl_unique : ∀ e' : E ⊕ Fin 3,
          ((Kc.tail (Sum.inl e') = ⟨x, i⟩) ↔ (Kplus.tail e' = x ∧ e' = e₀.1)) ∧
          ((Kc.head (Sum.inl e') = ⟨x, i⟩) ↔ (Kplus.head e' = x ∧ e' = e₀.1)) := by
        intro e'
        constructor
        · constructor
          · intro h
            have hx_eq : Kplus.tail e' = x := congrArg Sigma.fst h
            refine ⟨hx_eq, ?_⟩
            have hval : (slot (Kplus.tail e') e' (Or.inl rfl)).1 = i.1 := by
              cases hx_eq; exact congrArg Fin.val (eq_of_heq (Sigma.mk.inj h).2)
            have hat : attach x ⟨e', Or.inl hx_eq⟩ = iFin := by
              apply Fin.ext
              cases hx_eq
              simpa only [slot, h4, ↓reduceDIte] using hval
            have := congrArg (attach x).symm hat
            rw [Equiv.symm_apply_apply] at this
            exact congrArg Subtype.val this
          · rintro ⟨ht, rfl⟩
            exact hVc_eq ht ((hslot_congr e₀.1 ht (Or.inl rfl) e₀.2).trans he₀_slot_val)
        · constructor
          · intro h
            have hx_eq : Kplus.head e' = x := congrArg Sigma.fst h
            refine ⟨hx_eq, ?_⟩
            have hval : (slot (Kplus.head e') e' (Or.inr rfl)).1 = i.1 := by
              cases hx_eq; exact congrArg Fin.val (eq_of_heq (Sigma.mk.inj h).2)
            have hat : attach x ⟨e', Or.inr hx_eq⟩ = iFin := by
              apply Fin.ext
              cases hx_eq
              simpa only [slot, h4, ↓reduceDIte] using hval
            have := congrArg (attach x).symm hat
            rw [Equiv.symm_apply_apply] at this
            exact congrArg Subtype.val this
          · rintro ⟨hh, rfl⟩
            exact hVc_eq hh ((hslot_congr e₀.1 hh (Or.inr rfl) e₀.2).trans he₀_slot_val)
      let eOut : Ec := Sum.inr ⟨⟨x, h4⟩, iFin⟩
      let pIdx : Fin (Kplus.deg x) := ⟨(i.1 + Kplus.deg x - 1) % Kplus.deg x, Nat.mod_lt _ (by omega)⟩
      let eIn : Ec := Sum.inr ⟨⟨x, h4⟩, pIdx⟩
      have hp_succ : (pIdx.1 + 1) % Kplus.deg x = i.1 := by
        dsimp only [pIdx]
        by_cases hi0 : i.1 = 0
        · rw [hi0, zero_add]
          have hlt1 : Kplus.deg x - 1 < Kplus.deg x := by omega
          rw [Nat.mod_eq_of_lt hlt1]
          have h1 : Kplus.deg x - 1 + 1 = Kplus.deg x := by omega
          rw [h1, Nat.mod_self]
        · have h1 : i.1 + Kplus.deg x - 1 = (i.1 - 1) + Kplus.deg x := by omega
          have hlt1 : i.1 - 1 < Kplus.deg x := by omega
          rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt hlt1]
          have h2 : i.1 - 1 + 1 = i.1 := by omega
          rw [h2, Nat.mod_eq_of_lt hi_lt]
      have hinr_tail : ∀ y : (Σ x : ExpIdx, Fin (Kplus.deg x.1)),
          Kc.tail (Sum.inr y) = ⟨x, i⟩ ↔ Sum.inr y = eOut := by
        rintro ⟨⟨x', hx'⟩, j⟩
        constructor
        · intro h
          have hx_eq : x' = x := congrArg Sigma.fst h
          subst hx_eq
          have hj_eq : j.1 = i.1 := congrArg Fin.val (eq_of_heq (Sigma.mk.inj h).2)
          congr 1; exact Sigma.ext rfl (heq_of_eq (Fin.ext hj_eq))
        · intro h
          rw [h]
      have hinr_head : ∀ y : (Σ x : ExpIdx, Fin (Kplus.deg x.1)),
          Kc.head (Sum.inr y) = ⟨x, i⟩ ↔ Sum.inr y = eIn := by
        rintro ⟨⟨x', hx'⟩, j⟩
        constructor
        · intro h
          have hx_eq : x' = x := congrArg Sigma.fst h
          subst hx_eq
          have hj_mod : (j.1 + 1) % Kplus.deg x' = i.1 := congrArg Fin.val (eq_of_heq (Sigma.mk.inj h).2)
          have hj_eq : j = pIdx := by
            apply Fin.ext; dsimp only [pIdx]
            by_cases hlt : j.1 + 1 < Kplus.deg x'
            · rw [Nat.mod_eq_of_lt hlt] at hj_mod
              have : i.1 + Kplus.deg x' - 1 = j.1 + Kplus.deg x' := by omega
              rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt j.2]
            · have hj1 : j.1 + 1 = Kplus.deg x' := by
                have hlt_j : j.1 < Kplus.deg x' := j.2
                omega
              rw [hj1, Nat.mod_self] at hj_mod
              have hlt1 : Kplus.deg x' - 1 < Kplus.deg x' := by omega
              rw [← hj_mod, zero_add, Nat.mod_eq_of_lt hlt1]; omega
          congr 1; exact Sigma.ext rfl (heq_of_eq hj_eq)
        · intro h
          rw [h]; exact hVc_eq rfl hp_succ
      -- Now count tail-filter and head-filter directly!
      unfold Multigraph.deg
      rcases e₀.2 with ht0 | hh0
      · have hnot_hh : Kplus.head e₀.1 ≠ x := fun hh => hKp_ll e₀.1 (ht0.trans hh.symm)
        have htf : Finset.univ.filter (fun e : Ec => Kc.tail e = ⟨x, i⟩) = {Sum.inl e₀.1, eOut} := by
          ext e; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
            Finset.mem_singleton]
          cases e with
          | inl e' =>
            rw [(hinl_unique e').1]
            exact ⟨fun ⟨_, h⟩ => Or.inl (congrArg Sum.inl h),
              fun h => by
                rcases h with h | h
                · exact ⟨(Sum.inl.inj h) ▸ ht0, Sum.inl.inj h⟩
                · simp [eOut] at h⟩
          | inr y =>
            rw [hinr_tail y]
            exact ⟨Or.inr, fun h => h.resolve_left (fun h' => by cases h')⟩
        have hhf : Finset.univ.filter (fun e : Ec => Kc.head e = ⟨x, i⟩) = {eIn} := by
          ext e; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          cases e with
          | inl e' =>
            rw [(hinl_unique e').2]
            exact ⟨fun ⟨hh, heq⟩ => absurd (heq ▸ hh) hnot_hh, fun h => by simp [eIn] at h⟩
          | inr y => rw [hinr_head y]
        change (Finset.univ.filter (fun e : Ec => Kc.tail e = ⟨x, i⟩)).card +
            (Finset.univ.filter (fun e : Ec => Kc.head e = ⟨x, i⟩)).card = 3
        rw [htf, hhf, Finset.card_pair (fun h => by simp [eOut] at h), Finset.card_singleton]
      · have hnot_ht : Kplus.tail e₀.1 ≠ x := fun ht => hKp_ll e₀.1 (ht.trans hh0.symm)
        have htf : Finset.univ.filter (fun e : Ec => Kc.tail e = ⟨x, i⟩) = {eOut} := by
          ext e; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          cases e with
          | inl e' =>
            rw [(hinl_unique e').1]
            exact ⟨fun ⟨ht, heq⟩ => absurd (heq ▸ ht) hnot_ht, fun h => by simp [eOut] at h⟩
          | inr y => rw [hinr_tail y]
        have hhf : Finset.univ.filter (fun e : Ec => Kc.head e = ⟨x, i⟩) = {Sum.inl e₀.1, eIn} := by
          ext e; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
            Finset.mem_singleton]
          cases e with
          | inl e' =>
            rw [(hinl_unique e').2]
            exact ⟨fun ⟨_, h⟩ => Or.inl (congrArg Sum.inl h),
              fun h => by
                rcases h with h | h
                · exact ⟨(Sum.inl.inj h) ▸ hh0, Sum.inl.inj h⟩
                · simp [eIn] at h⟩
          | inr y =>
            rw [hinr_head y]
            exact ⟨Or.inr, fun h => h.resolve_left (fun h' => by cases h')⟩
        change (Finset.univ.filter (fun e : Ec => Kc.tail e = ⟨x, i⟩)).card +
            (Finset.univ.filter (fun e : Ec => Kc.head e = ⟨x, i⟩)).card = 3
        rw [htf, hhf, Finset.card_singleton, Finset.card_pair (fun h => by simp [eIn] at h)]
    · -- Degree-3 vertex `x` (`expDeg x = 1`): no cycle edges, same degree `3` as in `Kplus`!
      have hdeg3 : Kplus.deg x = 3 := by have := hKp_deg_ge3 x; omega
      have hi0 : i = ⟨0, hexpDeg_pos x⟩ := by
        apply Fin.ext
        have hexp1 : expDeg x = 1 := by simp [expDeg, h4]
        have h : i.1 < 1 := lt_of_lt_of_eq i.2 hexp1
        omega
      subst hi0
      have htf : Finset.univ.filter (fun e : Ec => Kc.tail e = ⟨x, ⟨0, hexpDeg_pos x⟩⟩) =
          (Finset.univ.filter (fun e' : E ⊕ Fin 3 => Kplus.tail e' = x)).image Sum.inl := by
        ext e; cases e with
        | inl e' =>
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
          constructor
          · intro h; exact ⟨e', congrArg Sigma.fst h, rfl⟩
          · rintro ⟨a, ha, heq⟩; cases Sum.inl.inj heq
            apply hVc_eq ha; dsimp only [slot]; rw [dif_neg (ha.symm ▸ h4)]
        | inr y =>
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, reduceCtorEq,
            and_false, exists_false, iff_false]
          intro h
          have hx' : y.1.1 = x := congrArg Sigma.fst h
          exact h4 (hx' ▸ y.1.2)
      have hhf : Finset.univ.filter (fun e : Ec => Kc.head e = ⟨x, ⟨0, hexpDeg_pos x⟩⟩) =
          (Finset.univ.filter (fun e' : E ⊕ Fin 3 => Kplus.head e' = x)).image Sum.inl := by
        ext e; cases e with
        | inl e' =>
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
          constructor
          · intro h; exact ⟨e', congrArg Sigma.fst h, rfl⟩
          · rintro ⟨a, ha, heq⟩; cases Sum.inl.inj heq
            apply hVc_eq ha; dsimp only [slot]; rw [dif_neg (ha.symm ▸ h4)]
        | inr y =>
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, reduceCtorEq,
            and_false, exists_false, iff_false]
          intro h
          have hx' : y.1.1 = x := congrArg Sigma.fst h
          exact h4 (hx' ▸ y.1.2)
      unfold Multigraph.deg at hdeg3 ⊢
      change (Finset.univ.filter (fun e : Ec => Kc.tail e = ⟨x, ⟨0, hexpDeg_pos x⟩⟩)).card +
          (Finset.univ.filter (fun e : Ec => Kc.head e = ⟨x, ⟨0, hexpDeg_pos x⟩⟩)).card = 3
      rw [htf, hhf, Finset.card_image_of_injective _ Sum.inl_injective,
          Finset.card_image_of_injective _ Sum.inl_injective, hdeg3]
  -- Verify `4 ≤ Fintype.card Vc`
  have hKc_card4 : 4 ≤ Fintype.card Vc := by
    have h1 : expDeg (some u₁) = Kplus.deg (some u₁) := by simp [expDeg, hKp_deg_u1]
    have hle : expDeg (some u₁) ≤ Fintype.card Vc := by
      rw [Fintype.card_sigma]
      have := Finset.single_le_sum (f := fun x : Option V => Fintype.card (Fin (expDeg x)))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ (some u₁))
      simpa using this
    omega
  -- Verify `Kc` is 3-edge-connected!
  have hKc_3ec : Kc.IsEdgeConnected 3 := by
    intro S hSne hScomp
    by_contra hlt3
    -- Case 1: every fiber lies wholly on one side of `S`
    by_cases hsplit : ∃ x : Option V, (∃ i : Fin (expDeg x), (⟨x, i⟩ : Vc) ∈ S) ∧
        (∃ j : Fin (expDeg x), (⟨x, j⟩ : Vc) ∉ S)
    · -- Case 2: some fiber `O_x` meets both `S` and `Sᶜ`
      rcases hsplit with ⟨x, ⟨i₁, hi₁⟩, ⟨i₂, hi₂⟩⟩
      have h4x : 4 ≤ Kplus.deg x := by
        by_contra hnot4
        have hi_eq : i₁ = i₂ := by
          apply Fin.ext
          have hexp1 : expDeg x = 1 := by simp [expDeg, hnot4]
          have h1 : i₁.1 < 1 := lt_of_lt_of_eq i₁.2 hexp1
          have h2 : i₂.1 < 1 := lt_of_lt_of_eq i₂.2 hexp1
          omega
        exact hi₂ (hi_eq ▸ hi₁)
      have hexp_eq : expDeg x = Kplus.deg x := by simp [expDeg, h4x]
      -- At least 2 cycle edges of `O_x` cross `S`!
      let Ax : Finset (Fin (Kplus.deg x)) :=
        Finset.univ.filter (fun i => (⟨x, ⟨i.1, hexp_eq.symm ▸ i.2⟩⟩ : Vc) ∈ S)
      have hAx_ne : Ax.Nonempty := ⟨⟨i₁.1, hexp_eq ▸ i₁.2⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi₁⟩⟩
      have hAx_comp : (Finset.univ \ Ax).Nonempty :=
        ⟨⟨i₂.1, hexp_eq ▸ i₂.2⟩, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h => hi₂ (Finset.mem_filter.mp h).2⟩⟩
      have hcyc_cut := cycle_fin_cut_ge2 (by omega : 2 ≤ Kplus.deg x) Ax hAx_ne hAx_comp
      let OxCut := Finset.univ.filter (fun i : Fin (Kplus.deg x) =>
        let j : Fin (Kplus.deg x) := ⟨(i.1 + 1) % Kplus.deg x, Nat.mod_lt _ (by omega)⟩
        (i ∈ Ax ∧ j ∉ Ax) ∨ (i ∉ Ax ∧ j ∈ Ax))
      let OxCutE : Finset Ec := OxCut.image (fun i => Sum.inr ⟨⟨x, h4x⟩, i⟩)
      have hOx_sub : OxCutE ⊆ Kc.cutEdges S := by
        intro e he
        rcases Finset.mem_image.mp he with ⟨i, hi, rfl⟩
        have hcr := (Finset.mem_filter.mp hi).2
        simp only [Ax, Finset.mem_filter, Finset.mem_univ, true_and] at hcr
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcr⟩
      have hOx_card : OxCutE.card = OxCut.card :=
        Finset.card_image_of_injective _ (fun a b h => by
          have := Sum.inr.inj h; exact eq_of_heq (Sigma.mk.inj this).2)
      -- Since `|Kc.cutEdges S| ≤ 2` and `|OxCutE| ≥ 2`, EVERY edge in `Kc.cutEdges S` lies in `OxCutE`,
      -- so NO `Sum.inl e'` crosses `S` and NO other fiber `O_y` (`y ≠ x`) crosses `S`!
      have hcut_eq : Kc.cutEdges S = OxCutE :=
        (Finset.eq_of_subset_of_card_le hOx_sub (by
          have h2 : 2 ≤ OxCut.card := hcyc_cut
          omega)).symm
      have hno_inl_cross : ∀ e' : E ⊕ Fin 3,
          Kc.tail (Sum.inl e') ∈ S ↔ Kc.head (Sum.inl e') ∈ S := by
        intro e'
        have hnot : Sum.inl e' ∉ Kc.cutEdges S := by
          rw [hcut_eq]; simp [OxCutE]
        simp only [Multigraph.cutEdges, Finset.mem_filter, Finset.mem_univ, true_and] at hnot
        by_cases h1 : Kc.tail (Sum.inl e') ∈ S <;> by_cases h2 : Kc.head (Sum.inl e') ∈ S <;> simp [h1, h2] at hnot ⊢
      have hno_other_split : ∀ y : Option V, y ≠ x → ∀ j₁ j₂ : Fin (expDeg y),
          (⟨y, j₁⟩ : Vc) ∈ S ↔ (⟨y, j₂⟩ : Vc) ∈ S := by
        intro y hy j₁ j₂
        by_cases h4y : 4 ≤ Kplus.deg y
        · -- Along cycle `O_y`, no cycle edge crosses `S`, so `O_y` is monochromatic!
          have hstep_y : ∀ (k : ℕ) (hk : k < expDeg y),
              (⟨y, ⟨k, hk⟩⟩ : Vc) ∈ S ↔
              (⟨y, ⟨(k + 1) % expDeg y, Nat.mod_lt _ (hexpDeg_pos y)⟩⟩ : Vc) ∈ S := by
            intro k hk
            have hk' : k < Kplus.deg y := by dsimp only [expDeg] at hk; simp only [h4y, ↓reduceIte] at hk; exact hk
            let e_y : Ec := Sum.inr ⟨⟨y, h4y⟩, ⟨k, hk'⟩⟩
            have hnot : e_y ∉ Kc.cutEdges S := by
              rw [hcut_eq]; intro hm
              rcases Finset.mem_image.mp hm with ⟨i, _, hi⟩
              exact hy (congrArg Subtype.val (congrArg Sigma.fst (Sum.inr.inj hi))).symm
            simp only [Multigraph.cutEdges, Finset.mem_filter, Finset.mem_univ, true_and] at hnot
            have hte : Kc.tail e_y = ⟨y, ⟨k, hk⟩⟩ := rfl
            have hhe : Kc.head e_y = ⟨y, ⟨(k + 1) % expDeg y, Nat.mod_lt _ (hexpDeg_pos y)⟩⟩ :=
              hVc_eq rfl (by simp [Kc, e_y, expDeg, h4y])
            rw [hte, hhe] at hnot
            by_cases h1 : (⟨y, ⟨k, hk⟩⟩ : Vc) ∈ S <;>
            by_cases h2 : (⟨y, ⟨(k + 1) % expDeg y, Nat.mod_lt _ (hexpDeg_pos y)⟩⟩ : Vc) ∈ S <;>
              simp [h1, h2] at hnot ⊢
          have hall0 : ∀ j : Fin (expDeg y), (⟨y, ⟨0, hexpDeg_pos y⟩⟩ : Vc) ∈ S ↔ (⟨y, j⟩ : Vc) ∈ S := by
            intro ⟨m, hm⟩
            induction m with
            | zero => rfl
            | succ m ih =>
              have h1 := ih (by omega)
              have h2 := hstep_y m (by omega)
              have hmod : (m + 1) % expDeg y = m + 1 := Nat.mod_eq_of_lt hm
              simpa only [hmod] using h1.trans h2
          exact (hall0 j₁).symm.trans (hall0 j₂)
        · have heq : j₁ = j₂ := by
            apply Fin.ext
            have hexp1 : expDeg y = 1 := by simp [expDeg, h4y]
            have h1 : j₁.1 < 1 := lt_of_lt_of_eq j₁.2 hexp1
            have h2 : j₂.1 < 1 := lt_of_lt_of_eq j₂.2 hexp1
            omega
          rw [heq]
      -- Now derive that `x` is a cut vertex of `K⁺`, contradicting `hKp_nc`!
      let e₁ := (attach x).symm ⟨i₁.1, hexp_eq ▸ i₁.2⟩
      let e₂ := (attach x).symm ⟨i₂.1, hexp_eq ▸ i₂.2⟩
      let y₁ := if Kplus.tail e₁.1 = x then Kplus.head e₁.1 else Kplus.tail e₁.1
      let y₂ := if Kplus.tail e₂.1 = x then Kplus.head e₂.1 else Kplus.tail e₂.1
      have hy1_ne : y₁ ≠ x := by
        dsimp only [y₁]; split_ifs with ht
        · exact fun hh => hKp_ll e₁.1 (ht.trans hh.symm)
        · exact fun ht' => ht ht'
      have hy2_ne : y₂ ≠ x := by
        dsimp only [y₂]; split_ifs with ht
        · exact fun hh => hKp_ll e₂.1 (ht.trans hh.symm)
        · exact fun ht' => ht ht'
      have hy1_in : (⟨y₁, ⟨0, hexpDeg_pos y₁⟩⟩ : Vc) ∈ S := by
        have hcr := hno_inl_cross e₁.1
        have hslot1 : (slot x e₁.1 e₁.2).1 = i₁.1 := by
          dsimp only [slot]; rw [dif_pos h4x]; simp [e₁]
        by_cases ht : Kplus.tail e₁.1 = x
        · have hy1_eq : y₁ = Kplus.head e₁.1 := by simp [y₁, ht]
          have htail : Kc.tail (Sum.inl e₁.1) = ⟨x, i₁⟩ :=
            hVc_eq ht ((hslot_congr e₁.1 ht (Or.inl rfl) e₁.2).trans hslot1)
          have hhead_in : Kc.head (Sum.inl e₁.1) ∈ S := hcr.mp (htail ▸ hi₁)
          rw [hy1_eq]
          exact (hno_other_split (Kplus.head e₁.1) (hy1_eq ▸ hy1_ne) _ _).mp hhead_in
        · have hh : Kplus.head e₁.1 = x := e₁.2.resolve_left ht
          have hy1_eq : y₁ = Kplus.tail e₁.1 := by simp [y₁, ht]
          have hhead : Kc.head (Sum.inl e₁.1) = ⟨x, i₁⟩ :=
            hVc_eq hh ((hslot_congr e₁.1 hh (Or.inr rfl) e₁.2).trans hslot1)
          have htail_in : Kc.tail (Sum.inl e₁.1) ∈ S := hcr.mpr (hhead ▸ hi₁)
          rw [hy1_eq]
          exact (hno_other_split (Kplus.tail e₁.1) (hy1_eq ▸ hy1_ne) _ _).mp htail_in
      have hy2_not : (⟨y₂, ⟨0, hexpDeg_pos y₂⟩⟩ : Vc) ∉ S := by
        have hcr := hno_inl_cross e₂.1
        have hslot2 : (slot x e₂.1 e₂.2).1 = i₂.1 := by
          dsimp only [slot]; rw [dif_pos h4x]; simp [e₂]
        by_cases ht : Kplus.tail e₂.1 = x
        · have hy2_eq : y₂ = Kplus.head e₂.1 := by simp [y₂, ht]
          have htail : Kc.tail (Sum.inl e₂.1) = ⟨x, i₂⟩ :=
            hVc_eq ht ((hslot_congr e₂.1 ht (Or.inl rfl) e₂.2).trans hslot2)
          have hhead_not : Kc.head (Sum.inl e₂.1) ∉ S := fun h => hi₂ (htail ▸ hcr.mpr h)
          rw [hy2_eq]
          exact fun h => hhead_not ((hno_other_split (Kplus.head e₂.1) (hy2_eq ▸ hy2_ne) _ _).mpr h)
        · have hh : Kplus.head e₂.1 = x := e₂.2.resolve_left ht
          have hy2_eq : y₂ = Kplus.tail e₂.1 := by simp [y₂, ht]
          have hhead : Kc.head (Sum.inl e₂.1) = ⟨x, i₂⟩ :=
            hVc_eq hh ((hslot_congr e₂.1 hh (Or.inr rfl) e₂.2).trans hslot2)
          have htail_not : Kc.tail (Sum.inl e₂.1) ∉ S := fun h => hi₂ (hhead ▸ hcr.mp h)
          rw [hy2_eq]
          exact fun h => htail_not ((hno_other_split (Kplus.tail e₂.1) (hy2_eq ▸ hy2_ne) _ _).mpr h)
      -- No walk in `K⁺ - x` can connect `y₁` to `y₂`!
      apply hKp_nc x (Finset.mem_univ x)
      refine ⟨Finset.mem_univ x, y₁, y₂,
        Finset.mem_erase.mpr ⟨hy1_ne, Finset.mem_univ _⟩,
        Finset.mem_erase.mpr ⟨hy2_ne, Finset.mem_univ _⟩, fun hwalk => ?_⟩
      have hpres : ∀ {a b : Option V},
          Relation.ReflTransGen ((Subgraph.top Kplus).deleteVertex x).Adj a b →
          (⟨a, ⟨0, hexpDeg_pos a⟩⟩ : Vc) ∈ S → (⟨b, ⟨0, hexpDeg_pos b⟩⟩ : Vc) ∈ S := by
        intro a b hab
        induction hab with
        | refl => exact id
        | tail _ hstep ih =>
          intro haS
          have hcur := ih haS
          rcases hstep with ⟨e', he', hadj⟩
          have ht_ne : Kplus.tail e' ≠ x := (Finset.mem_filter.mp he').2.1
          have hh_ne : Kplus.head e' ≠ x := (Finset.mem_filter.mp he').2.2
          have hcr := hno_inl_cross e'
          rcases hadj with ⟨ht, hh⟩ | ⟨ht, hh⟩
          · rw [← ht] at hcur
            have h1 : Kc.tail (Sum.inl e') ∈ S :=
              (hno_other_split (Kplus.tail e') ht_ne _ _).mp hcur
            have h2 := hcr.mp h1
            rw [← hh]
            exact (hno_other_split (Kplus.head e') hh_ne _ _).mp h2
          · rw [← hh] at hcur
            have h1 : Kc.head (Sum.inl e') ∈ S :=
              (hno_other_split (Kplus.head e') hh_ne _ _).mp hcur
            have h2 := hcr.mpr h1
            rw [← ht]
            exact (hno_other_split (Kplus.tail e') ht_ne _ _).mp h2
      exact hy2_not (hpres hwalk hy1_in)
    · -- Case 1: every fiber is monochromatic; project `S` to `T ⊆ Option V`
      push Not at hsplit
      let T : Finset (Option V) := Finset.univ.filter (fun x => (⟨x, ⟨0, hexpDeg_pos x⟩⟩ : Vc) ∈ S)
      have hmono : ∀ (x : Option V) (i : Fin (expDeg x)), (⟨x, i⟩ : Vc) ∈ S ↔ x ∈ T := by
        intro x i
        simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro hi; exact hsplit x ⟨i, hi⟩ ⟨0, hexpDeg_pos x⟩
        · intro h0; exact hsplit x ⟨⟨0, hexpDeg_pos x⟩, h0⟩ i
      have hT_ne : T.Nonempty := by
        rcases hSne with ⟨⟨x, i⟩, hxS⟩
        exact ⟨x, (hmono x i).mp hxS⟩
      have hT_comp : (Finset.univ \ T).Nonempty := by
        rcases hScomp with ⟨⟨x, i⟩, hx⟩
        exact ⟨x, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hT => (Finset.mem_sdiff.mp hx).2 ((hmono x i).mpr hT)⟩⟩
      have hKp_cut := hKp_3ec T hT_ne hT_comp
      have hsub : (Kplus.cutEdges T).image Sum.inl ⊆ Kc.cutEdges S := by
        intro e he
        rcases Finset.mem_image.mp he with ⟨e', he', rfl⟩
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        have hcr := (Finset.mem_filter.mp he').2
        dsimp only [Kc]
        rw [hmono, hmono]
        exact hcr
      have hge3 : 3 ≤ (Kc.cutEdges S).card :=
        calc 3 ≤ (Kplus.cutEdges T).card := hKp_cut
          _ = ((Kplus.cutEdges T).image Sum.inl).card := (Finset.card_image_of_injective _ Sum.inl_injective).symm
          _ ≤ (Kc.cutEdges S).card := Finset.card_le_card hsub
      omega
  -- Step 3: Set `Q = Kc.deleteVertex v₀` where `v₀ = ⟨none, ⟨0, _⟩⟩`!
  let v₀ : Vc := ⟨none, ⟨0, hexpDeg_pos none⟩⟩
  let Q := Kc.deleteVertex v₀
  have hQ_tc : Q.IsTruncatedCubic3EC :=
    ⟨Vc, Ec, inferInstance, inferInstance, inferInstance, inferInstance, Kc, v₀,
     hKc_cubic, hKc_3ec, hKc_card4,
     ⟨{ toVert := Equiv.refl _
        toEdge := Equiv.refl _
        dir := fun _ => false
        tail_eq := fun _ => rfl
        head_eq := fun _ => rfl }⟩⟩
  have hnone_unique : ∀ i : Fin (expDeg none), (⟨none, i⟩ : Vc) = v₀ := by
    intro i
    apply hVc_eq rfl
    have hexp1 : expDeg none = 1 := by simp [expDeg, hKp_deg_none]
    have h : i.1 < 1 := lt_of_lt_of_eq i.2 hexp1
    omega
  have hfst_some : ∀ u : {u : Vc // u ≠ v₀}, ∃ x : V, u.1.1 = some x := by
    intro ⟨⟨opt, i⟩, hne⟩
    cases opt with
    | none => exact absurd (hnone_unique i) hne
    | some x => exact ⟨x, rfl⟩
  let contractVFn : {u : Vc // u ≠ v₀} → V := fun u => (hfst_some u).choose
  have hcontract_eq : ∀ u : {u : Vc // u ≠ v₀}, u.1.1 = some (contractVFn u) :=
    fun u => (hfst_some u).choose_spec
  let origEdgeFn : E ↪ {e : Ec // Kc.tail e ≠ v₀ ∧ Kc.head e ≠ v₀} :=
    { toFun := fun e => ⟨Sum.inl (Sum.inl e),
        (fun h => by have h' := congrArg Sigma.fst h; cases h'),
        (fun h => by have h' := congrArg Sigma.fst h; cases h')⟩
      inj' := fun e₁ e₂ h => Sum.inl.inj (Sum.inl.inj (congrArg Subtype.val h)) }
  refine ⟨{
    VQ := {u : Vc // u ≠ v₀}
    EQ := {e : Ec // Kc.tail e ≠ v₀ ∧ Kc.head e ≠ v₀}
    Q := Q
    isTC3EC := hQ_tc
    origEdge := origEdgeFn
    contractV := contractVFn
    contractV_surj := fun x => by
      let u : {u : Vc // u ≠ v₀} := ⟨⟨some x, ⟨0, hexpDeg_pos (some x)⟩⟩,
        fun h => by have := congrArg Sigma.fst h; cases this⟩
      exact ⟨u, Option.some.inj (hcontract_eq u).symm⟩
    orig_tail := fun e => Option.some.inj (hcontract_eq (Q.tail (origEdgeFn e))).symm
    orig_head := fun e => Option.some.inj (hcontract_eq (Q.head (origEdgeFn e))).symm
    exp_fiber := fun e hexp => by
      cases he1 : e.1 with
      | inl e' =>
        cases e' with
        | inl ek => exfalso; exact hexp ek (Subtype.ext he1.symm)
        | inr j => exfalso; exact e.2.1 (by simp [he1, Kc, Kplus, hnone_unique])
      | inr y =>
        have ht : (Q.tail e).1.1 = y.1.1 := by
          change (Kc.tail e.1).1 = y.1.1; rw [he1]
        have hh : (Q.head e).1.1 = y.1.1 := by
          change (Kc.head e.1).1 = y.1.1; rw [he1]
        rw [hcontract_eq] at ht hh
        exact Option.some.inj (ht.trans hh.symm)
    fiber_cycle_or_singleton := fun x => by
      let U := Finset.univ.filter (fun u : {u : Vc // u ≠ v₀} => contractVFn u = x)
      let F := Finset.univ.filter (fun e : {e : Ec // Kc.tail e ≠ v₀ ∧ Kc.head e ≠ v₀} =>
        (∀ k : E, origEdgeFn k ≠ e) ∧ contractVFn (Q.tail e) = x)
      by_cases h4 : 4 ≤ Kplus.deg (some x)
      · right
        -- Fiber `x` is the cycle of length `d = Kplus.deg (some x) ≥ 4`!
        let d := Kplus.deg (some x)
        have hd_eq : expDeg (some x) = d := by simp [expDeg, d, h4]
        let vList : List {u : Vc // u ≠ v₀} :=
          (List.finRange d).map (fun i =>
            ⟨⟨some x, ⟨i.1, hd_eq.symm ▸ i.2⟩⟩, (fun h => by have h' := congrArg Sigma.fst h; cases h')⟩)
        let eList : List {e : Ec // Kc.tail e ≠ v₀ ∧ Kc.head e ≠ v₀} :=
          (List.finRange d).map (fun i =>
            ⟨Sum.inr ⟨⟨some x, h4⟩, i⟩,
             (fun h => by have h' := congrArg Sigma.fst h; cases h'),
             (fun h => by have h' := congrArg Sigma.fst h; cases h')⟩)
        have hv_nodup : vList.Nodup :=
          (List.nodup_finRange d).map (fun a b h =>
            Fin.ext (congrArg (fun u : {u : Vc // u ≠ v₀} => u.1.2.1) h))
        have he_nodup : eList.Nodup :=
          (List.nodup_finRange d).map (fun a b h =>
            Fin.ext (congrArg (fun p : (Σ y : {x : Option V // 4 ≤ Kplus.deg x}, Fin (Kplus.deg y.1)) => p.2.1)
              (Sum.inr.inj (congrArg Subtype.val h))))
        let C := directedCycleOfSimpleClosedWalk Q vList eList
          (by simp [vList, d]; omega)
          (by simp [vList, eList])
          hv_nodup he_nodup
          (fun i hi => by
            left
            simp only [eList, vList, List.length_map, List.length_finRange, List.getElem_map,
              List.getElem_finRange] at hi ⊢
            constructor <;> apply Subtype.ext <;> apply Sigma.ext rfl <;> apply heq_of_eq <;>
              apply Fin.ext <;> simp [Q, Multigraph.deleteVertex, Kc, d])
        refine ⟨C.sub, ?_, ?_, C.isCycle⟩
        · ext u
          simp only [C, directedCycleOfSimpleClosedWalk, List.mem_toFinset, vList, List.mem_map,
            List.mem_finRange, true_and, U, Finset.mem_filter, Finset.mem_univ]
          constructor
          · rintro ⟨i, rfl⟩; exact Option.some.inj (hcontract_eq _).symm
          · intro hcx
            have hu1 : u.1.1 = some x := hcx ▸ hcontract_eq u
            rcases u with ⟨⟨opt, idx⟩, hne⟩
            dsimp only at hu1; subst hu1
            exact ⟨⟨idx.1, hd_eq ▸ idx.2⟩, rfl⟩
        · ext e
          simp only [C, directedCycleOfSimpleClosedWalk, List.mem_toFinset, eList, List.mem_map,
            List.mem_finRange, true_and, F, Finset.mem_filter, Finset.mem_univ]
          constructor
          · rintro ⟨i, rfl⟩
            refine ⟨(fun k hk => by have := congrArg Subtype.val hk; cases this), ?_⟩
            exact Option.some.inj (hcontract_eq _).symm
          · rintro ⟨hexp, hcx⟩
            rcases e with ⟨ec, htne, hhne⟩
            cases ec with
            | inl e' =>
              cases e' with
              | inl ek => exfalso; exact hexp ek (Subtype.ext rfl)
              | inr j => exfalso; exact htne (by simp [Kc, Kplus, hnone_unique])
            | inr y =>
              rcases y with ⟨⟨opt, hopt⟩, idx⟩
              have hu1 : opt = some x := by
                have hce := hcontract_eq (Q.tail ⟨Sum.inr ⟨⟨opt, hopt⟩, idx⟩, htne, hhne⟩)
                rw [hcx] at hce
                exact hce
              subst hu1
              exact ⟨idx, rfl⟩
      · left
        -- Degree 3: singleton fiber and empty expansion edge set
        have hU1 : U = {⟨⟨some x, ⟨0, hexpDeg_pos (some x)⟩⟩,
            fun h => by have := congrArg Sigma.fst h; cases this⟩} := by
          ext u
          simp only [U, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          constructor
          · intro hcx
            have hu1 : u.1.1 = some x := hcx ▸ hcontract_eq u
            rcases u with ⟨⟨opt, idx⟩, hne⟩
            dsimp only at hu1; subst hu1
            apply Subtype.ext
            show (⟨some x, idx⟩ : Vc) = ⟨some x, ⟨0, hexpDeg_pos (some x)⟩⟩
            congr 1
            apply Fin.ext
            have hexp1 : expDeg (some x) = 1 := by simp [expDeg, h4]
            have hlt : idx.1 < 1 := lt_of_lt_of_eq idx.2 hexp1
            omega
          · rintro rfl; exact Option.some.inj (hcontract_eq _).symm
        have hF0 : F = ∅ := by
          rw [Finset.eq_empty_iff_forall_notMem]
          intro e he
          obtain ⟨hexp, hcx⟩ := (Finset.mem_filter.mp he).2
          rcases e with ⟨ec, htne, hhne⟩
          cases ec with
          | inl e' =>
            cases e' with
            | inl ek => exact hexp ek (Subtype.ext rfl)
            | inr j => exact htne (by simp [Kc, Kplus, hnone_unique])
          | inr y =>
            have hu1 : y.1.1 = some x := by
              have hce := hcontract_eq (Q.tail ⟨Sum.inr y, htne, hhne⟩)
              rw [hcx] at hce
              exact hce
            exact h4 (hu1 ▸ y.1.2)
        exact ⟨by change U.card = 1; rw [hU1, Finset.card_singleton], hF0⟩
  }⟩

/-- **Definition 3.5 / Lemma 3.4 existence:**
For every `(SUB)` subdivision `H` of `G`, there is a reorientation `flip` (supported on
`H.edges`) after which `H` admits an auxiliary graph `AuxGraphData`. -/
theorem aux_graph_exists
    {G : Multigraph V E} {H : G.Subgraph} (sub : SubdivisionData G H) :
    ∃ (flip : E → Bool), (∀ e, e ∉ H.edges → flip e = false) ∧
      ∃ (H' : (G.reorient flip).Subgraph) (sub' : SubdivisionData (G.reorient flip) H'),
        H'.verts = H.verts ∧ H'.edges = H.edges ∧
        Nonempty (AuxGraphData (G.reorient flip) H' sub') := by
  classical
  -- Step 1: Build `flip` aligning every edge of `H` with its thread direction
  let flip : E → Bool := fun e =>
    if h : e ∈ H.edges then
      let t := (sub.edges_cover e h).choose
      let het : e ∈ (sub.thread t).edges := (sub.edges_cover e h).choose_spec
      let i := (sub.thread t).edges.idxOf e
      let hi : i < (sub.thread t).edges.length := List.idxOf_lt_length_of_mem het
      decide (G.tail e ≠ (sub.thread t).verts[i]'(by have := (sub.thread t).verts_len; omega))
    else false
  have hflip_out : ∀ e, e ∉ H.edges → flip e = false := fun e he => by simp [flip, he]
  let G' := G.reorient flip
  let H' := reorientSubgraph G flip H
  -- Thread edges in `sub.thread t` are pairwise distinct (simple path in `H`)
  have htp_nodup : ∀ t : sub.E₀, (sub.thread t).edges.Nodup := fun t =>
    simplePath_edges_nodup (sub.thread t).verts_nodup (sub.thread t).verts_len (sub.thread t).step_connect
  -- Show alignment holds in `G'`
  have haligned : ∀ (t : sub.E₀) (i : ℕ) (hi : i < (sub.thread t).edges.length),
      G'.tail ((sub.thread t).edges[i]'hi) = (sub.thread t).verts[i]'(by
        have := (sub.thread t).verts_len; omega) ∧
      G'.head ((sub.thread t).edges[i]'hi) = (sub.thread t).verts[i + 1]'(by
        have := (sub.thread t).verts_len; omega) := by
    intro t i hi
    let e := (sub.thread t).edges[i]'hi
    have het : e ∈ (sub.thread t).edges := List.getElem_mem hi
    have heH : e ∈ H.edges := (sub.thread t).edges_sub e het
    have ht_eq : (sub.edges_cover e heH).choose = t := by
      by_contra hne
      exact sub.edges_disjoint _ t hne e (sub.edges_cover e heH).choose_spec het
    have hidx : (sub.thread t).edges.idxOf e = i := List.Nodup.idxOf_getElem (htp_nodup t) i hi
    have hstep := (sub.thread t).step_connect i hi
    have huv_ne : (sub.thread t).verts[i]'(by have := (sub.thread t).verts_len; omega) ≠
        (sub.thread t).verts[i + 1]'(by have := (sub.thread t).verts_len; omega) := by
      intro h; have := (List.Nodup.getElem_inj_iff (sub.thread t).verts_nodup).mp h; omega
    have hfl_eq : flip e = decide (G.tail e ≠ (sub.thread t).verts[i]'(by
        have := (sub.thread t).verts_len; omega)) := by
      have haux : ∀ (t' : sub.E₀) (het' : e ∈ (sub.thread t').edges), t' = t →
          decide (G.tail e ≠ (sub.thread t').verts[(sub.thread t').edges.idxOf e]'(by
            have := (sub.thread t').verts_len
            have := List.idxOf_lt_length_of_mem het'; omega)) =
          decide (G.tail e ≠ (sub.thread t).verts[i]'(by have := (sub.thread t).verts_len; omega)) := by
        intro t' het' htt; subst htt; simp only [hidx]
      simp only [flip, heH, ↓reduceDIte]
      exact haux (sub.edges_cover e heH).choose (sub.edges_cover e heH).choose_spec ht_eq
    dsimp only [G', Multigraph.reorient]
    dsimp only [e] at hfl_eq
    rw [hfl_eq]
    rcases hstep with ⟨ht, hh⟩ | ⟨ht, hh⟩
    · simp [ht, hh]
    · simp [ht, hh, huv_ne.symm]
  let sub' : SubdivisionData G' H' :=
    { V₀ := sub.V₀
      E₀ := sub.E₀
      H₀ := sub.H₀
      loopless := sub.loopless
      edgeConn3 := sub.edgeConn3
      card_ge_two := sub.card_ge_two
      embedV := sub.embedV
      embedV_mem := sub.embedV_mem
      thread := fun t =>
        { verts := (sub.thread t).verts
          edges := (sub.thread t).edges
          len_pos := (sub.thread t).len_pos
          len_le := (sub.thread t).len_le
          verts_len := (sub.thread t).verts_len
          verts_nodup := (sub.thread t).verts_nodup
          verts_sub := (sub.thread t).verts_sub
          edges_sub := (sub.thread t).edges_sub
          head_eq := (sub.thread t).head_eq
          last_eq := (sub.thread t).last_eq
          step_connect := fun i hi => Or.inl (haligned t i hi) }
      edges_disjoint := sub.edges_disjoint
      edges_cover := sub.edges_cover
      interior_disjoint_branch := sub.interior_disjoint_branch
      interior_disjoint := sub.interior_disjoint
      verts_cover := sub.verts_cover }
  -- Step 2: Decompose `sub.H₀` into its finite set of blocks `{K_b}` and expand each via `lem_3_4_a` + `lem_3_4_b`
  let blockOf (t : sub.E₀) : sub.H₀.Subgraph :=
    (existsUnique_block_of_nonloop t (sub.loopless t)).choose
  have hblockOf_spec : ∀ t : sub.E₀, sub.H₀.IsBlock (blockOf t) ∧ t ∈ (blockOf t).edges :=
    fun t => (existsUnique_block_of_nonloop t (sub.loopless t)).choose_spec.1
  have hblockOf_uniq : ∀ t : sub.E₀, ∀ K : sub.H₀.Subgraph,
      sub.H₀.IsBlock K → t ∈ K.edges → K = blockOf t :=
    fun t K hK ht => (existsUnique_block_of_nonloop t (sub.loopless t)).choose_spec.2 K ⟨hK, ht⟩
  let blocksFin : Finset sub.H₀.Subgraph := Finset.univ.image blockOf
  let numBlocks := blocksFin.card
  let blockEquiv : Fin numBlocks ≃ {K : sub.H₀.Subgraph // K ∈ blocksFin} :=
    (Fintype.equivFinOfCardEq (Fintype.card_coe blocksFin)).symm
  let Kblock (b : Fin numBlocks) : sub.H₀.Subgraph := (blockEquiv b).1
  have hKblock_is : ∀ b : Fin numBlocks, sub.H₀.IsBlock (Kblock b) := fun b => by
    rcases Finset.mem_image.mp (blockEquiv b).2 with ⟨t, _, ht⟩
    dsimp only [Kblock]; rw [← ht]; exact (hblockOf_spec t).1
  have hKblock_inj : Function.Injective Kblock := fun b₁ b₂ h =>
    blockEquiv.injective (Subtype.ext h)
  -- For each `b`, expand `Kblock b` via `lem_3_4_a` and `lem_3_4_b`
  have hexp_exists : ∀ b : Fin numBlocks, Nonempty (TruncatedCubicExpansion (Kblock b).toMultigraph) := by
    intro b
    obtain ⟨hll_b, h3_b, hv2_b, hnc_b⟩ := lem_3_4_a sub.H₀ sub.loopless sub.edgeConn3 sub.card_ge_two
      (Kblock b) (hKblock_is b)
    have hnc_top : (Subgraph.top (Kblock b).toMultigraph).HasNoCutVertex := by
      intro ⟨v, hv⟩ _ ⟨_, ⟨u, hu⟩, ⟨w, hw⟩, hau, hwu, hnot⟩
      apply hnc_b v hv
      refine ⟨hv, u, w, Finset.mem_erase.mpr ⟨fun h => (Finset.mem_erase.mp hau).1 (Subtype.ext h), hu⟩,
        Finset.mem_erase.mpr ⟨fun h => (Finset.mem_erase.mp hwu).1 (Subtype.ext h), hw⟩, fun hwalk => ?_⟩
      apply hnot
      -- Lift walk in `(Kblock b).deleteVertex v` to `(Subgraph.top (Kblock b).toMultigraph).deleteVertex ⟨v, hv⟩`
      have hlift_w : ∀ {a c : sub.V₀}, ∀ (ha : a ∈ (Kblock b).verts) (hc : c ∈ (Kblock b).verts),
          Relation.ReflTransGen ((Kblock b).deleteVertex v).Adj a c →
          Relation.ReflTransGen ((Subgraph.top (Kblock b).toMultigraph).deleteVertex ⟨v, hv⟩).Adj
            ⟨a, ha⟩ ⟨c, hc⟩ := by
        intro a c ha hc hw_ac
        induction hw_ac with
        | refl => exact Relation.ReflTransGen.refl
        | @tail d c' had hdc ih =>
          rcases hdc with ⟨e, he, hadj⟩
          have heK : e ∈ (Kblock b).edges := (Finset.mem_filter.mp he).1
          have htne : sub.H₀.tail e ≠ v := (Finset.mem_filter.mp he).2.1
          have hhne : sub.H₀.head e ≠ v := (Finset.mem_filter.mp he).2.2
          have hdK : d ∈ (Kblock b).verts := by
            rcases hadj with ⟨ht, _⟩ | ⟨_, hh⟩ <;> [exact ht ▸ (Kblock b).tail_mem heK; exact hh ▸ (Kblock b).head_mem heK]
          refine Relation.ReflTransGen.tail (ih hdK) ⟨⟨e, heK⟩, ?_, ?_⟩
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
              fun h => htne (congrArg Subtype.val h), fun h => hhne (congrArg Subtype.val h)⟩
          · rcases hadj with ⟨ht, hh⟩ | ⟨ht, hh⟩
            · left; exact ⟨Subtype.ext ht, Subtype.ext hh⟩
            · right; exact ⟨Subtype.ext ht, Subtype.ext hh⟩
      exact hlift_w hu hw hwalk
    exact lem_3_4_b (Kblock b).toMultigraph hll_b h3_b (by simpa using hv2_b) hnc_top
  let exp (b : Fin numBlocks) : TruncatedCubicExpansion (Kblock b).toMultigraph :=
    Classical.choice (hexp_exists b)
  -- Disjoint union `Q = ⊔ (exp b).Q`
  let VQ := Σ b : Fin numBlocks, (exp b).VQ
  let EQ := Σ b : Fin numBlocks, (exp b).EQ
  let QG : Multigraph VQ EQ :=
    { tail := fun x => ⟨x.1, (exp x.1).Q.tail x.2⟩
      head := fun x => ⟨x.1, (exp x.1).Q.head x.2⟩ }
  let blockIdxOf (t : sub.E₀) : Fin numBlocks :=
    blockEquiv.symm ⟨blockOf t, Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩⟩
  have hKblock_of : ∀ t : sub.E₀, Kblock (blockIdxOf t) = blockOf t := fun t => by
    simp [Kblock, blockIdxOf]
  have ht_in_Kb : ∀ t : sub.E₀, t ∈ (Kblock (blockIdxOf t)).edges := fun t => by
    rw [hKblock_of t]; exact (hblockOf_spec t).2
  have hsigma_orig_inj : ∀ {b₁ b₂ : Fin numBlocks} {t₁ t₂ : sub.E₀}
      (ht₁ : t₁ ∈ (Kblock b₁).edges) (ht₂ : t₂ ∈ (Kblock b₂).edges),
      (⟨b₁, (exp b₁).origEdge ⟨t₁, ht₁⟩⟩ : EQ) = ⟨b₂, (exp b₂).origEdge ⟨t₂, ht₂⟩⟩ → t₁ = t₂ := by
    intro b₁ b₂ t₁ t₂ ht₁ ht₂ h
    have hb : b₁ = b₂ := congrArg Sigma.fst h
    subst hb
    have h2 : (exp b₁).origEdge ⟨t₁, ht₁⟩ = (exp b₁).origEdge ⟨t₂, ht₂⟩ := eq_of_heq (Sigma.mk.inj h).2
    exact congrArg Subtype.val ((exp b₁).origEdge.injective h2)
  let origEdgeFn : sub.E₀ ↪ EQ :=
    { toFun := fun t => ⟨blockIdxOf t, (exp (blockIdxOf t)).origEdge ⟨t, ht_in_Kb t⟩⟩
      inj' := fun t₁ t₂ h => hsigma_orig_inj (ht_in_Kb t₁) (ht_in_Kb t₂) h }
  refine ⟨flip, hflip_out, H', sub', rfl, rfl, ⟨{
    numBlocks := numBlocks
    VQ := VQ
    EQ := EQ
    Q := QG
    comp := Sigma.fst
    edge_same_comp := fun _ => rfl
    comp_tc3ec := fun b => by
      -- Induced subgraph on component `b` is isomorphic to `(exp b).Q`!
      rcases (exp b).isTC3EC with ⟨V', E', _, _, _, _, Qplus, v, hcub, h3p, h4p, ⟨iso⟩⟩
      let Sub_b := (Subgraph.induced QG (Finset.univ.filter (fun u : VQ => u.1 = b))).toMultigraph
      have hmem_v : ∀ x : (exp b).VQ, (⟨b, x⟩ : VQ) ∈ Finset.univ.filter (fun u : VQ => u.1 = b) :=
        fun _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
      have hmem_e : ∀ e : (exp b).EQ, (⟨b, e⟩ : EQ) ∈ (Subgraph.induced QG (Finset.univ.filter (fun u : VQ => u.1 = b))).edges :=
        fun _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
      let iso_b : Multigraph.Iso Sub_b (exp b).Q :=
        { toVert :=
            { toFun := fun ⟨⟨b', x⟩, h⟩ => (Finset.mem_filter.mp h).2 ▸ x
              invFun := fun x => ⟨⟨b, x⟩, hmem_v x⟩
              left_inv := fun ⟨⟨b', x⟩, h⟩ => by
                have hb : b' = b := (Finset.mem_filter.mp h).2
                subst hb; rfl
              right_inv := fun _ => rfl }
          toEdge :=
            { toFun := fun ⟨⟨b', e⟩, h⟩ => (Finset.mem_filter.mp (Finset.mem_filter.mp h).2.1).2 ▸ e
              invFun := fun e => ⟨⟨b, e⟩, hmem_e e⟩
              left_inv := fun ⟨⟨b', e⟩, h⟩ => by
                have hb : b' = b := (Finset.mem_filter.mp (Finset.mem_filter.mp h).2.1).2
                subst hb; rfl
              right_inv := fun _ => rfl }
          dir := fun _ => false
          tail_eq := fun ⟨⟨b', e⟩, h⟩ => by
            have hb : b' = b := (Finset.mem_filter.mp (Finset.mem_filter.mp h).2.1).2
            subst hb; rfl
          head_eq := fun ⟨⟨b', e⟩, h⟩ => by
            have hb : b' = b := (Finset.mem_filter.mp (Finset.mem_filter.mp h).2.1).2
            subst hb; rfl }
      refine ⟨V', E', inferInstance, inferInstance, inferInstance, inferInstance, Qplus, v, hcub, h3p, h4p,
        ⟨{ toVert := iso_b.toVert.trans iso.toVert
           toEdge := iso_b.toEdge.trans iso.toEdge
           dir := fun e => iso.dir (iso_b.toEdge e)
           tail_eq := fun ⟨⟨b', eq⟩, he⟩ => by
             have hb : b' = b := (Finset.mem_filter.mp (Finset.mem_filter.mp he).2.1).2
             subst hb
             have h1 := iso.tail_eq eq
             simpa [Equiv.trans_apply, iso_b, Sub_b, Subgraph.toMultigraph, QG] using h1
           head_eq := fun ⟨⟨b', eq⟩, he⟩ => by
             have hb : b' = b := (Finset.mem_filter.mp (Finset.mem_filter.mp he).2.1).2
             subst hb
             have h1 := iso.head_eq eq
             simpa [Equiv.trans_apply, iso_b, Sub_b, Subgraph.toMultigraph, QG] using h1 }⟩⟩
    origEdge := origEdgeFn
    contractV := fun x => ((exp x.1).contractV x.2).1
    orig_tail := fun t => by
      dsimp only [QG, origEdgeFn]
      have h := (exp (blockIdxOf t)).orig_tail ⟨t, ht_in_Kb t⟩
      exact congrArg Subtype.val h
    orig_head := fun t => by
      dsimp only [QG, origEdgeFn]
      have h := (exp (blockIdxOf t)).orig_head ⟨t, ht_in_Kb t⟩
      exact congrArg Subtype.val h
    exp_same_contractV := fun x hexp => by
      rcases x with ⟨b, e⟩
      dsimp only [QG]
      have hexp_b : ∀ k : {e // e ∈ (Kblock b).edges}, (exp b).origEdge k ≠ e := by
        intro ⟨t, htK⟩ heq
        have hb_eq : blockIdxOf t = b := hKblock_inj (by rw [hKblock_of t]; exact (hblockOf_uniq t (Kblock b) (hKblock_is b) htK).symm)
        apply hexp t
        exact Sigma.ext hb_eq (by cases hb_eq; exact heq_of_eq heq)
      exact congrArg Subtype.val ((exp b).exp_fiber e hexp_b)
    fiber_connected := fun b x₁ x₂ hb1 hb2 hcv => by
      rcases x₁ with ⟨b₁, u⟩; rcases x₂ with ⟨b₂, v⟩
      dsimp only at hb1 hb2; cases hb1; cases hb2
      have hcv_sub : (exp b).contractV u = (exp b).contractV v := Subtype.ext hcv
      let x := (exp b).contractV u
      rcases (exp b).fiber_cycle_or_singleton x with ⟨hcard1, _⟩ | ⟨C, hCv, hCe, hCcyc⟩
      · -- Singleton fiber: `u = v`
        rw [Finset.card_eq_one] at hcard1
        rcases hcard1 with ⟨w, hw⟩
        have huw : u = w := Finset.mem_singleton.mp (hw ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩)
        have hvw : v = w := Finset.mem_singleton.mp (hw ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcv_sub.symm⟩)
        subst huw; subst hvw; exact Relation.ReflTransGen.refl
      · -- Cycle fiber: `C` is connected on expansion edges!
        have huC : u ∈ C.verts := hCv.symm ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
        have hvC : v ∈ C.verts := hCv.symm ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcv_sub.symm⟩
        have hwalk := hCcyc.1.2 u huC v hvC
        clear hcv hcv_sub hvC
        induction hwalk with
        | refl => exact Relation.ReflTransGen.refl
        | tail _ hstep ih =>
          rcases hstep with ⟨e, heC, hadj⟩
          have heF := (Finset.mem_filter.mp (hCe ▸ heC)).2.1
          refine Relation.ReflTransGen.tail ih ⟨⟨b, e⟩, fun t heq => ?_, ?_⟩
          · have hb_eq : blockIdxOf t = b := congrArg Sigma.fst heq
            have h2 : (exp (blockIdxOf t)).origEdge ⟨t, ht_in_Kb t⟩ ≍ e := (Sigma.mk.inj heq).2
            have heq' : (exp b).origEdge ⟨t, hb_eq ▸ ht_in_Kb t⟩ = e := by
              cases hb_eq; exact eq_of_heq h2
            exact heF ⟨t, hb_eq ▸ ht_in_Kb t⟩ heq'
          · rcases hadj with ⟨ht, hh⟩ | ⟨ht, hh⟩
            · left; exact ⟨Sigma.ext rfl (heq_of_eq ht), Sigma.ext rfl (heq_of_eq hh)⟩
            · right; exact ⟨Sigma.ext rfl (heq_of_eq ht), Sigma.ext rfl (heq_of_eq hh)⟩
    block_subgraph := Kblock
    is_block := hKblock_is
    orig_in_block := fun t b => by
      change t ∈ (Kblock b).edges ↔ blockIdxOf t = b
      constructor
      · intro htK
        exact hKblock_inj (by rw [hKblock_of t]; exact (hblockOf_uniq t (Kblock b) (hKblock_is b) htK).symm)
      · rintro rfl; exact ht_in_Kb t
    thread_aligned := haligned
  }⟩⟩

end Lemma34

end Flow.Proofs
