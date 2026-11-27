module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Flow.Defs.Literature
public import Flow.Proofs.Extraction
public import Flow.Proofs.Blocks
public import Flow.Proofs.FlowsQ
public import Flow.Proofs.Liftable

@[expose] public section

/-!
# Well colourings, 2-constructions, frames, official cycles, and list assignments

This module proves:
- `lem_3_9` (Lemma 3.9(a)): simplicity, connectedness, edge count, red forest, no monochromatic blue edge
- `lem_3_9_bcd` (Lemma 3.9(b)–(d)): stage nesting, unique node, induced stages, stage graphs
- `frame_exists`: existence of a `Frame` from `JLPTWellColouring`
- `lem_3_11` (Lemma 3.11): `(O1)`–`(O6)` for official cycles and free-edge cycles
- `def_3_12_properties`: basic properties of `LamOfFlow` and `PLam`
-/

namespace Flow.Proofs

open Flow

section GraphTreeHelpers

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- A connected subgraph `H` with `H.edges.card + 1 = H.verts.card` is a forest. -/
lemma connected_edges_eq_verts_sub_one_isForest {G : Multigraph V E} (H : G.Subgraph)
    (hconn : H.Connected) (hcard : H.edges.card + 1 = H.verts.card) :
    H.IsForest := by
  intro C hCle hCcyc
  -- Pick an edge `e₀ ∈ C.edges` (exists since `C` is nonempty and 2-regular)
  obtain ⟨v₀, hv₀⟩ := hCcyc.1.1
  have hdeg2 : C.deg v₀ = 2 := hCcyc.2 v₀ hv₀
  have hex_e0 : ∃ e₀ ∈ C.edges, G.tail e₀ = v₀ ∨ G.head e₀ = v₀ := by
    unfold Multigraph.Subgraph.deg at hdeg2
    by_cases ht : 0 < (C.edges.filter (fun e => G.tail e = v₀)).card
    · rcases Finset.card_pos.mp ht with ⟨e, he⟩
      exact ⟨e, (Finset.mem_filter.mp he).1, Or.inl (Finset.mem_filter.mp he).2⟩
    · have hh : 0 < (C.edges.filter (fun e => G.head e = v₀)).card := by omega
      rcases Finset.card_pos.mp hh with ⟨e, he⟩
      exact ⟨e, (Finset.mem_filter.mp he).1, Or.inr (Finset.mem_filter.mp he).2⟩
  rcases hex_e0 with ⟨e₀, he₀C, _⟩
  have he₀H : e₀ ∈ H.edges := hCle.2 he₀C
  -- Define `H' = H - e₀` and `C' = C - e₀`
  let H' : G.Subgraph :=
    { verts := H.verts
      edges := H.edges.erase e₀
      tail_mem := fun he => H.tail_mem (Finset.mem_of_mem_erase he)
      head_mem := fun he => H.head_mem (Finset.mem_of_mem_erase he) }
  -- Show `G.tail e₀` and `G.head e₀` remain connected in `C - e₀` (by cut-parity in 2-regular `C`)
  let C' : G.Subgraph :=
    { verts := C.verts
      edges := C.edges.erase e₀
      tail_mem := fun he => C.tail_mem (Finset.mem_of_mem_erase he)
      head_mem := fun he => C.head_mem (Finset.mem_of_mem_erase he) }
  have hC'_reach : Relation.ReflTransGen C'.Adj (G.tail e₀) (G.head e₀) := by
    by_cases hloop : G.tail e₀ = G.head e₀
    · rw [hloop]
    · classical
      by_contra hnot
      let S : Finset V := C.verts.filter (fun w => Relation.ReflTransGen C'.Adj (G.tail e₀) w)
      have hSsub : S ⊆ C.verts := Finset.filter_subset _ _
      have htS : G.tail e₀ ∈ S :=
        Finset.mem_filter.mpr ⟨C.tail_mem he₀C, Relation.ReflTransGen.refl⟩
      have hhnotS : G.head e₀ ∉ S := fun h => hnot (Finset.mem_filter.mp h).2
      have hcut_eq : C.edges.filter (fun e =>
          (G.tail e ∈ S ∧ G.head e ∉ S) ∨ (G.tail e ∉ S ∧ G.head e ∈ S)) = {e₀} := by
        ext e
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨heC, hcr⟩
          by_contra hne
          have heC' : e ∈ C'.edges := Finset.mem_erase.mpr ⟨hne, heC⟩
          rcases hcr with ⟨ht, hh⟩ | ⟨ht, hh⟩
          · exact hh (Finset.mem_filter.mpr ⟨C.head_mem heC,
              Relation.ReflTransGen.tail (Finset.mem_filter.mp ht).2 ⟨e, heC', Or.inl ⟨rfl, rfl⟩⟩⟩)
          · exact ht (Finset.mem_filter.mpr ⟨C.tail_mem heC,
              Relation.ReflTransGen.tail (Finset.mem_filter.mp hh).2 ⟨e, heC', Or.inr ⟨rfl, rfl⟩⟩⟩)
        · rintro rfl; exact ⟨he₀C, Or.inl ⟨htS, hhnotS⟩⟩
      have hsh := subgraph_cut_handshake C S hSsub
      have hsum : ∑ v ∈ S, C.deg v = 2 * S.card := by
        calc ∑ v ∈ S, C.deg v = ∑ _v ∈ S, 2 := Finset.sum_congr rfl (fun v hv => hCcyc.2 v (hSsub hv))
          _ = 2 * S.card := by simp [mul_comm]
      rw [hsum, hcut_eq, Finset.card_singleton] at hsh
      omega
  have hH'_reach_e0 : Relation.ReflTransGen H'.Adj (G.tail e₀) (G.head e₀) :=
    reflTransGen_mono (fun _ _ ⟨e, he, hadj⟩ =>
      ⟨e, Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp he).1, hCle.2 (Finset.mem_erase.mp he).2⟩, hadj⟩)
      hC'_reach
  -- Hence `H'` is still connected!
  have hH'_conn : H'.Connected := by
    refine ⟨hconn.1, fun u hu v hv => ?_⟩
    have hw := hconn.2 u hu v hv
    clear hu hv
    induction hw with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hstep ih =>
      rcases hstep with ⟨e, heH, hadj⟩
      by_cases he0 : e = e₀
      · subst he0
        rcases hadj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Relation.ReflTransGen.trans ih hH'_reach_e0
        · exact Relation.ReflTransGen.trans ih (subgraph_adj_symm hH'_reach_e0)
      · exact Relation.ReflTransGen.tail ih ⟨e, Finset.mem_erase.mpr ⟨he0, heH⟩, hadj⟩
  have hle := connected_verts_le_edges_succ H' hH'_conn
  have hcard' : H'.edges.card + 1 = H.edges.card := by
    change (H.edges.erase e₀).card + 1 = H.edges.card
    exact Finset.card_erase_add_one he₀H
  change H.verts.card ≤ H'.edges.card + 1 at hle
  omega

/-- Spanning tree of `G` has `|V| - 1` edges. -/
lemma spanningTree_edges_card {G : Multigraph V E} {T : G.Subgraph}
    (hT : T.IsSpanningTree) :
    T.edges.card + 1 = Fintype.card V := by
  have h1 := forest_edges_lt_verts (Fintype.card V) T hT.2.2 hT.2.1.1 (by rw [hT.1, Finset.card_univ])
  have h2 := connected_verts_le_edges_succ T hT.2.1
  rw [hT.1, Finset.card_univ] at h1 h2
  omega

end GraphTreeHelpers

section TwoConstructionLemmas

variable {W F : Type} [DecidableEq W] [DecidableEq F]

/-- Postorder list of nodes of a `2`-construction (children strictly before parent). -/
def postNodes {M : Multigraph W F} :
    ∀ {W₀ : Finset W} {F₀ : Finset F},
      TwoConstruction M W₀ F₀ → List (Finset W × Finset W × F × F)
  | _, _, .single _ => []
  | _, _, .join (W₁ := W₁) (W₂ := W₂) left right e f _ _ _ _ _ _ _ _ _ =>
      postNodes left ++ postNodes right ++ [(W₁, W₂, e, f)]

lemma twoConstr_card {M : Multigraph W F} :
    ∀ {W₀ : Finset W} {F₀ : Finset F}, TwoConstruction M W₀ F₀ →
      W₀.Nonempty ∧ F₀.card = 2 * (W₀.card - 1)
  | _, _, .single w => ⟨Finset.singleton_nonempty w, by simp⟩
  | _, _, .join left right e f hdisjW hdisjF he_ne_f he1 he2 hf1 hf2 _ _ => by
      obtain ⟨hW1, hF1⟩ := twoConstr_card left
      obtain ⟨hW2, hF2⟩ := twoConstr_card right
      have hne1 : 1 ≤ _ := Finset.card_pos.mpr hW1
      have hne2 : 1 ≤ _ := Finset.card_pos.mpr hW2
      have hnot_f : f ∉ _ ∪ _ := fun h => by
        rcases Finset.mem_union.mp h with h | h <;> [exact hf1 h; exact hf2 h]
      have hnot_e : e ∉ insert f (_ ∪ _) := fun h => by
        rcases Finset.mem_insert.mp h with rfl | h'
        · exact he_ne_f rfl
        · rcases Finset.mem_union.mp h' with h' | h' <;> [exact he1 h'; exact he2 h']
      refine ⟨hW1.mono Finset.subset_union_left, ?_⟩
      rw [Finset.card_insert_of_notMem hnot_e, Finset.card_insert_of_notMem hnot_f,
          Finset.card_union_of_disjoint hdisjF, Finset.card_union_of_disjoint hdisjW]
      omega

lemma twoConstr_edges_ends {M : Multigraph W F} :
    ∀ {W₀ : Finset W} {F₀ : Finset F}, TwoConstruction M W₀ F₀ →
      ∀ e ∈ F₀, M.tail e ∈ W₀ ∧ M.head e ∈ W₀ ∧ M.tail e ≠ M.head e
  | _, _, .single _ => fun _ he => absurd he (Finset.notMem_empty _)
  | _, _, .join left right e f hdisjW _ _ _ _ _ _ he_cr hf_cr => fun x hx => by
      rcases Finset.mem_insert.mp hx with rfl | hx
      · rcases he_cr with ⟨ht, hh⟩ | ⟨ht, hh⟩
        · exact ⟨Finset.mem_union_left _ ht, Finset.mem_union_right _ hh,
            fun h => Finset.disjoint_left.mp hdisjW ht (h ▸ hh)⟩
        · exact ⟨Finset.mem_union_right _ ht, Finset.mem_union_left _ hh,
            fun h => Finset.disjoint_left.mp hdisjW hh (h.symm ▸ ht)⟩
      · rcases Finset.mem_insert.mp hx with rfl | hx
        · rcases hf_cr with ⟨ht, hh⟩ | ⟨ht, hh⟩
          · exact ⟨Finset.mem_union_left _ ht, Finset.mem_union_right _ hh,
              fun h => Finset.disjoint_left.mp hdisjW ht (h ▸ hh)⟩
          · exact ⟨Finset.mem_union_right _ ht, Finset.mem_union_left _ hh,
              fun h => Finset.disjoint_left.mp hdisjW hh (h.symm ▸ ht)⟩
        · rcases Finset.mem_union.mp hx with hx | hx
          · obtain ⟨ht, hh, hne⟩ := twoConstr_edges_ends left x hx
            exact ⟨Finset.mem_union_left _ ht, Finset.mem_union_left _ hh, hne⟩
          · obtain ⟨ht, hh, hne⟩ := twoConstr_edges_ends right x hx
            exact ⟨Finset.mem_union_right _ ht, Finset.mem_union_right _ hh, hne⟩

lemma twoConstr_stages_sub {M : Multigraph W F} :
    ∀ {W₀ : Finset W} {F₀ : Finset F} (tc : TwoConstruction M W₀ F₀),
      ∀ s ∈ tc.stages, s.1 ⊆ W₀ ∧ s.2 ⊆ F₀
  | _, _, .single w => fun s hs => by
      simp only [TwoConstruction.stages, List.mem_singleton] at hs
      subst hs; exact ⟨Finset.Subset.rfl, Finset.Subset.rfl⟩
  | _, _, .join left right e f _ _ _ _ _ _ _ _ _ => fun s hs => by
      simp only [TwoConstruction.stages, List.mem_cons, List.mem_append] at hs
      rcases hs with rfl | hs | hs
      · exact ⟨Finset.Subset.rfl, Finset.Subset.rfl⟩
      · obtain ⟨h1, h2⟩ := twoConstr_stages_sub left s hs
        exact ⟨h1.trans Finset.subset_union_left,
          h2.trans (Finset.subset_union_left.trans ((Finset.subset_insert _ _).trans (Finset.subset_insert _ _)))⟩
      · obtain ⟨h1, h2⟩ := twoConstr_stages_sub right s hs
        exact ⟨h1.trans Finset.subset_union_right,
          h2.trans (Finset.subset_union_right.trans ((Finset.subset_insert _ _).trans (Finset.subset_insert _ _)))⟩

lemma twoConstr_nodes_sub {M : Multigraph W F} :
    ∀ {W₀ : Finset W} {F₀ : Finset F} (tc : TwoConstruction M W₀ F₀),
      ∀ nd ∈ tc.nodes, nd.1 ∪ nd.2.1 ⊆ W₀ ∧ nd.2.2.1 ∈ F₀ ∧ nd.2.2.2 ∈ F₀ ∧
        Disjoint nd.1 nd.2.1 ∧ nd.2.2.1 ≠ nd.2.2.2 ∧
        ((M.tail nd.2.2.1 ∈ nd.1 ∧ M.head nd.2.2.1 ∈ nd.2.1) ∨
         (M.tail nd.2.2.1 ∈ nd.2.1 ∧ M.head nd.2.2.1 ∈ nd.1)) ∧
        ((M.tail nd.2.2.2 ∈ nd.1 ∧ M.head nd.2.2.2 ∈ nd.2.1) ∨
         (M.tail nd.2.2.2 ∈ nd.2.1 ∧ M.head nd.2.2.2 ∈ nd.1))
  | _, _, .single _ => fun _ h => by simp [TwoConstruction.nodes] at h
  | _, _, .join left right e f hdisjW _ he_ne_f _ _ _ _ he_cr hf_cr => fun nd hnd => by
      simp only [TwoConstruction.nodes, List.mem_cons, List.mem_append] at hnd
      rcases hnd with rfl | hnd | hnd
      · exact ⟨Finset.Subset.rfl, Finset.mem_insert_self _ _,
          Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), hdisjW, he_ne_f, he_cr, hf_cr⟩
      · obtain ⟨hW, he1, hf1, hd, hne, h1, h2⟩ := twoConstr_nodes_sub left nd hnd
        exact ⟨hW.trans Finset.subset_union_left,
          Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_union_left _ he1)),
          Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_union_left _ hf1)),
          hd, hne, h1, h2⟩
      · obtain ⟨hW, he1, hf1, hd, hne, h1, h2⟩ := twoConstr_nodes_sub right nd hnd
        exact ⟨hW.trans Finset.subset_union_right,
          Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_union_right _ he1)),
          Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_union_right _ hf1)),
          hd, hne, h1, h2⟩

lemma twoConstr_stages_disj_or_nested {M : Multigraph W F} :
    ∀ {W₀ : Finset W} {F₀ : Finset F} (tc : TwoConstruction M W₀ F₀),
      ∀ s₁ ∈ tc.stages, ∀ s₂ ∈ tc.stages, Disjoint s₁.1 s₂.1 ∨ s₁.1 ⊆ s₂.1 ∨ s₂.1 ⊆ s₁.1
  | _, _, .single w => fun s₁ h₁ s₂ h₂ => by
      simp only [TwoConstruction.stages, List.mem_singleton] at h₁ h₂
      subst h₁; subst h₂; right; left; exact Finset.Subset.rfl
  | _, _, .join left right e f hdisjW _ _ _ _ _ _ _ _ => fun s₁ h₁ s₂ h₂ => by
      simp only [TwoConstruction.stages, List.mem_cons, List.mem_append] at h₁ h₂
      rcases h₁ with rfl | h₁ | h₁
      · rcases h₂ with rfl | h₂ | h₂
        · right; left; exact Finset.Subset.rfl
        · right; right; exact (twoConstr_stages_sub left s₂ h₂).1.trans Finset.subset_union_left
        · right; right; exact (twoConstr_stages_sub right s₂ h₂).1.trans Finset.subset_union_right
      · rcases h₂ with rfl | h₂ | h₂
        · right; left; exact (twoConstr_stages_sub left s₁ h₁).1.trans Finset.subset_union_left
        · exact twoConstr_stages_disj_or_nested left s₁ h₁ s₂ h₂
        · left; exact hdisjW.mono (twoConstr_stages_sub left s₁ h₁).1 (twoConstr_stages_sub right s₂ h₂).1
      · rcases h₂ with rfl | h₂ | h₂
        · right; left; exact (twoConstr_stages_sub right s₁ h₁).1.trans Finset.subset_union_right
        · left; exact hdisjW.symm.mono (twoConstr_stages_sub right s₁ h₁).1 (twoConstr_stages_sub left s₂ h₂).1
        · exact twoConstr_stages_disj_or_nested right s₁ h₁ s₂ h₂

lemma twoConstr_edge_unique_node {M : Multigraph W F} :
    ∀ {W₀ : Finset W} {F₀ : Finset F} (tc : TwoConstruction M W₀ F₀),
      ∀ x ∈ F₀, ∃! idx : Fin tc.nodes.length,
        let nd := tc.nodes[idx.1]'idx.2
        x = nd.2.2.1 ∨ x = nd.2.2.2
  | _, _, .single _ => fun _ hx => absurd hx (Finset.notMem_empty _)
  | _, _, .join left right e f hdisjW hdisjF he_ne_f he1 he2 hf1 hf2 he_cr hf_cr => fun x hx => by
      let tc := TwoConstruction.join left right e f hdisjW hdisjF he_ne_f he1 he2 hf1 hf2 he_cr hf_cr
      have hlen : tc.nodes.length = 1 + left.nodes.length + right.nodes.length := by
        simp only [tc, TwoConstruction.nodes, List.length_cons, List.length_append]; omega
      rcases Finset.mem_insert.mp hx with rfl | hx
      · refine ⟨⟨0, by simp [TwoConstruction.nodes]⟩, Or.inl rfl, fun ⟨n, hn⟩ hidx => ?_⟩
        apply Fin.ext; dsimp only
        cases n with
        | zero => rfl
        | succ k =>
          exfalso
          have hk : k < (left.nodes ++ right.nodes).length := by
            simp only [TwoConstruction.nodes, List.length_cons] at hn; omega
          simp only [TwoConstruction.nodes, List.getElem_cons_succ] at hidx
          rcases List.mem_append.mp (List.getElem_mem hk) with hm | hm
          · have hs := twoConstr_nodes_sub left _ hm
            rcases hidx with h | h <;> [exact he1 (h ▸ hs.2.1); exact he1 (h ▸ hs.2.2.1)]
          · have hs := twoConstr_nodes_sub right _ hm
            rcases hidx with h | h <;> [exact he2 (h ▸ hs.2.1); exact he2 (h ▸ hs.2.2.1)]
      · rcases Finset.mem_insert.mp hx with rfl | hx
        · refine ⟨⟨0, by simp [TwoConstruction.nodes]⟩, Or.inr rfl, fun ⟨n, hn⟩ hidx => ?_⟩
          apply Fin.ext; dsimp only
          cases n with
          | zero => rfl
          | succ k =>
            exfalso
            have hk : k < (left.nodes ++ right.nodes).length := by
              simp only [TwoConstruction.nodes, List.length_cons] at hn; omega
            simp only [TwoConstruction.nodes, List.getElem_cons_succ] at hidx
            rcases List.mem_append.mp (List.getElem_mem hk) with hm | hm
            · have hs := twoConstr_nodes_sub left _ hm
              rcases hidx with h | h <;> [exact hf1 (h ▸ hs.2.1); exact hf1 (h ▸ hs.2.2.1)]
            · have hs := twoConstr_nodes_sub right _ hm
              rcases hidx with h | h <;> [exact hf2 (h ▸ hs.2.1); exact hf2 (h ▸ hs.2.2.1)]
        · rcases Finset.mem_union.mp hx with hx | hx
          · obtain ⟨idx₁, hidx₁, huniq₁⟩ := twoConstr_edge_unique_node left x hx
            refine ⟨⟨idx₁.1 + 1, by simp [TwoConstruction.nodes]; omega⟩, ?_, fun ⟨n, hn⟩ hidx => ?_⟩
            · simp only [TwoConstruction.nodes, List.getElem_cons_succ, List.getElem_append_left idx₁.2]
              exact hidx₁
            · apply Fin.ext; dsimp only
              cases n with
              | zero =>
                exfalso; simp only [TwoConstruction.nodes, List.getElem_cons_zero] at hidx
                rcases hidx with h1 | h1 <;> [exact he1 (h1 ▸ hx); exact hf1 (h1 ▸ hx)]
              | succ k =>
                simp only [TwoConstruction.nodes, List.getElem_cons_succ] at hidx
                by_cases hlt : k < left.nodes.length
                · simp only [List.getElem_append_left hlt] at hidx
                  have heq := congrArg Fin.val (huniq₁ ⟨k, hlt⟩ hidx)
                  dsimp only at heq; omega
                · exfalso
                  have hri : k - left.nodes.length < right.nodes.length := by
                    simp only [TwoConstruction.nodes, List.length_cons, List.length_append] at hn; omega
                  simp only [List.getElem_append_right (by omega : left.nodes.length ≤ k)] at hidx
                  have hs := twoConstr_nodes_sub right _ (List.getElem_mem hri)
                  rcases hidx with h | h
                  · exact Finset.disjoint_left.mp hdisjF hx (h ▸ hs.2.1)
                  · exact Finset.disjoint_left.mp hdisjF hx (h ▸ hs.2.2.1)
          · obtain ⟨idx₂, hidx₂, huniq₂⟩ := twoConstr_edge_unique_node right x hx
            refine ⟨⟨left.nodes.length + idx₂.1 + 1, by simp [TwoConstruction.nodes]⟩, ?_, fun ⟨n, hn⟩ hidx => ?_⟩
            · have hle : left.nodes.length ≤ left.nodes.length + idx₂.1 := Nat.le_add_right _ _
              simp only [TwoConstruction.nodes, List.getElem_cons_succ,
                List.getElem_append_right hle, Nat.add_sub_cancel_left]
              exact hidx₂
            · apply Fin.ext; dsimp only
              cases n with
              | zero =>
                exfalso; simp only [TwoConstruction.nodes, List.getElem_cons_zero] at hidx
                rcases hidx with h1 | h1 <;> [exact he2 (h1 ▸ hx); exact hf2 (h1 ▸ hx)]
              | succ k =>
                simp only [TwoConstruction.nodes, List.getElem_cons_succ] at hidx
                by_cases hlt : k < left.nodes.length
                · exfalso
                  simp only [List.getElem_append_left hlt] at hidx
                  have hs := twoConstr_nodes_sub left _ (List.getElem_mem hlt)
                  rcases hidx with h | h
                  · exact Finset.disjoint_right.mp hdisjF hx (h ▸ hs.2.1)
                  · exact Finset.disjoint_right.mp hdisjF hx (h ▸ hs.2.2.1)
                · have hri : k - left.nodes.length < right.nodes.length := by
                    simp only [TwoConstruction.nodes, List.length_cons, List.length_append] at hn; omega
                  simp only [List.getElem_append_right (by omega : left.nodes.length ≤ k)] at hidx
                  have heq := congrArg Fin.val (huniq₂ ⟨k - left.nodes.length, hri⟩ hidx)
                  dsimp only at heq; omega

lemma twoConstr_stage_induced {M : Multigraph W F} :
    ∀ {W₀ : Finset W} {F₀ : Finset F} (tc : TwoConstruction M W₀ F₀),
      ∀ s ∈ tc.stages, ∀ x ∈ F₀, (M.tail x ∈ s.1 ∧ M.head x ∈ s.1) ↔ x ∈ s.2
  | _, _, .single w => fun _ _ _ hx => absurd hx (Finset.notMem_empty _)
  | _, _, .join left right e f hdisjW hdisjF he_ne_f he1 he2 hf1 hf2 he_cr hf_cr => fun s hs x hx => by
      let tc := TwoConstruction.join left right e f hdisjW hdisjF he_ne_f he1 he2 hf1 hf2 he_cr hf_cr
      simp only [TwoConstruction.stages, List.mem_cons, List.mem_append] at hs
      rcases hs with rfl | hs | hs
      · constructor
        · intro _; exact hx
        · intro hx'; exact ⟨(twoConstr_edges_ends tc x hx').1, (twoConstr_edges_ends tc x hx').2.1⟩
      · have hs_sub := twoConstr_stages_sub left s hs
        constructor
        · rintro ⟨ht, hh⟩
          have ht1 : M.tail x ∈ _ := hs_sub.1 ht
          have hh1 : M.head x ∈ _ := hs_sub.1 hh
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exfalso; rcases he_cr with ⟨_, h2⟩ | ⟨h2, _⟩
            · exact Finset.disjoint_left.mp hdisjW hh1 h2
            · exact Finset.disjoint_left.mp hdisjW ht1 h2
          · rcases Finset.mem_insert.mp hx with rfl | hx
            · exfalso; rcases hf_cr with ⟨_, h2⟩ | ⟨h2, _⟩
              · exact Finset.disjoint_left.mp hdisjW hh1 h2
              · exact Finset.disjoint_left.mp hdisjW ht1 h2
            · rcases Finset.mem_union.mp hx with hx | hx
              · exact (twoConstr_stage_induced left s hs x hx).mp ⟨ht, hh⟩
              · exfalso
                exact Finset.disjoint_left.mp hdisjW ht1 (twoConstr_edges_ends right x hx).1
        · intro hxs
          exact (twoConstr_stage_induced left s hs x (hs_sub.2 hxs)).mpr hxs
      · have hs_sub := twoConstr_stages_sub right s hs
        constructor
        · rintro ⟨ht, hh⟩
          have ht2 : M.tail x ∈ _ := hs_sub.1 ht
          have hh2 : M.head x ∈ _ := hs_sub.1 hh
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exfalso; rcases he_cr with ⟨h1, _⟩ | ⟨_, h1⟩
            · exact Finset.disjoint_left.mp hdisjW h1 ht2
            · exact Finset.disjoint_left.mp hdisjW h1 hh2
          · rcases Finset.mem_insert.mp hx with rfl | hx
            · exfalso; rcases hf_cr with ⟨h1, _⟩ | ⟨_, h1⟩
              · exact Finset.disjoint_left.mp hdisjW h1 ht2
              · exact Finset.disjoint_left.mp hdisjW h1 hh2
            · rcases Finset.mem_union.mp hx with hx | hx
              · exfalso
                exact Finset.disjoint_left.mp hdisjW (twoConstr_edges_ends left x hx).1 ht2
              · exact (twoConstr_stage_induced right s hs x hx).mp ⟨ht, hh⟩
        · intro hxs
          exact (twoConstr_stage_induced right s hs x (hs_sub.2 hxs)).mpr hxs

lemma twoConstr_stage_edges_iff_nodes {M : Multigraph W F} :
    ∀ {W₀ : Finset W} {F₀ : Finset F} (tc : TwoConstruction M W₀ F₀),
      ∀ s ∈ tc.stages, ∀ x ∈ F₀,
        x ∈ s.2 ↔ ∃ nd ∈ tc.nodes, (nd.1 ∪ nd.2.1) ⊆ s.1 ∧ (x = nd.2.2.1 ∨ x = nd.2.2.2)
  | _, _, .single _ => fun _ _ _ hx => absurd hx (Finset.notMem_empty _)
  | _, _, .join left right e f hdisjW hdisjF he_ne_f he1 he2 hf1 hf2 he_cr hf_cr => fun s hs x hx => by
      constructor
      · intro hxs
        have hstage_sub := twoConstr_stages_sub (TwoConstruction.join left right e f hdisjW hdisjF he_ne_f he1 he2 hf1 hf2 he_cr hf_cr) s hs
        simp only [TwoConstruction.stages, List.mem_cons, List.mem_append] at hs
        rcases hs with rfl | hs | hs
        · rcases Finset.mem_insert.mp hx with hxe | hx
          · exact ⟨(_, _, e, f), by simp [TwoConstruction.nodes], Finset.Subset.rfl, Or.inl hxe⟩
          · rcases Finset.mem_insert.mp hx with hxf | hx
            · exact ⟨(_, _, e, f), by simp [TwoConstruction.nodes], Finset.Subset.rfl, Or.inr hxf⟩
            · rcases Finset.mem_union.mp hx with hx | hx
              · obtain ⟨idx, hidx, _⟩ := twoConstr_edge_unique_node left x hx
                have hnd_mem := List.getElem_mem idx.2
                have hnd_sub := (twoConstr_nodes_sub left _ hnd_mem).1
                exact ⟨left.nodes[idx.1]'idx.2, by simp [TwoConstruction.nodes, hnd_mem],
                  hnd_sub.trans Finset.subset_union_left, hidx⟩
              · obtain ⟨idx, hidx, _⟩ := twoConstr_edge_unique_node right x hx
                have hnd_mem := List.getElem_mem idx.2
                have hnd_sub := (twoConstr_nodes_sub right _ hnd_mem).1
                exact ⟨right.nodes[idx.1]'idx.2, by simp [TwoConstruction.nodes, hnd_mem],
                  hnd_sub.trans Finset.subset_union_right, hidx⟩
        · have hx1 := (twoConstr_stages_sub left s hs).2 hxs
          obtain ⟨nd, hnd, hsub, hmem⟩ := (twoConstr_stage_edges_iff_nodes left s hs x hx1).mp hxs
          exact ⟨nd, by simp [TwoConstruction.nodes, hnd], hsub, hmem⟩
        · have hx2 := (twoConstr_stages_sub right s hs).2 hxs
          obtain ⟨nd, hnd, hsub, hmem⟩ := (twoConstr_stage_edges_iff_nodes right s hs x hx2).mp hxs
          exact ⟨nd, by simp [TwoConstruction.nodes, hnd], hsub, hmem⟩
      · rintro ⟨nd, hnd, hsub, hmem⟩
        have hnd_info := twoConstr_nodes_sub (TwoConstruction.join left right e f hdisjW hdisjF he_ne_f he1 he2 hf1 hf2 he_cr hf_cr) nd hnd
        rw [← twoConstr_stage_induced (TwoConstruction.join left right e f hdisjW hdisjF he_ne_f he1 he2 hf1 hf2 he_cr hf_cr) s hs x hx]
        rcases hmem with rfl | rfl
        · rcases hnd_info.2.2.2.2.2.1 with ⟨ht, hh⟩ | ⟨ht, hh⟩
          · exact ⟨hsub (Finset.mem_union_left _ ht), hsub (Finset.mem_union_right _ hh)⟩
          · exact ⟨hsub (Finset.mem_union_right _ ht), hsub (Finset.mem_union_left _ hh)⟩
        · rcases hnd_info.2.2.2.2.2.2 with ⟨ht, hh⟩ | ⟨ht, hh⟩
          · exact ⟨hsub (Finset.mem_union_left _ ht), hsub (Finset.mem_union_right _ hh)⟩
          · exact ⟨hsub (Finset.mem_union_right _ ht), hsub (Finset.mem_union_left _ hh)⟩

/-- Helper: `postNodes tc` has the exact same elements as `tc.nodes` (up to order),
every edge in `F₀` belongs to a unique index of `postNodes tc`, and topological nesting holds. -/
lemma postNodes_props {M : Multigraph W F} :
    ∀ {W₀ : Finset W} {F₀ : Finset F} (tc : TwoConstruction M W₀ F₀),
      -- (1) Every edge in `F₀` belongs to a unique index of `postNodes tc`
      (∀ x ∈ F₀, ∃! idx : Fin (postNodes tc).length,
        let nd := (postNodes tc)[idx.1]'idx.2
        x = nd.2.2.1 ∨ x = nd.2.2.2) ∧
      -- (2) Top stage is either a single vertex or the last node
      ((∃ i : Fin (postNodes tc).length, W₀ = ((postNodes tc)[i.1]'i.2).1 ∪ ((postNodes tc)[i.1]'i.2).2.1) ∨
        W₀.card = 1) ∧
      -- (3) Properties of every node `i` in `postNodes tc`
      (∀ i : Fin (postNodes tc).length,
        let nd := (postNodes tc)[i.1]'i.2
        nd.1 ∪ nd.2.1 ⊆ W₀ ∧ Disjoint nd.1 nd.2.1 ∧ nd.1.Nonempty ∧ nd.2.1.Nonempty ∧
        nd.2.2.1 ≠ nd.2.2.2 ∧ nd.2.2.1 ∈ F₀ ∧ nd.2.2.2 ∈ F₀ ∧
        ((M.tail nd.2.2.1 ∈ nd.1 ∧ M.head nd.2.2.1 ∈ nd.2.1) ∨
         (M.tail nd.2.2.1 ∈ nd.2.1 ∧ M.head nd.2.2.1 ∈ nd.1)) ∧
        ((M.tail nd.2.2.2 ∈ nd.1 ∧ M.head nd.2.2.2 ∈ nd.2.1) ∨
         (M.tail nd.2.2.2 ∈ nd.2.1 ∧ M.head nd.2.2.2 ∈ nd.1)) ∧
        -- Crossing edges between `nd.1` and `nd.2.1` are ONLY `nd.2.2.1, nd.2.2.2`
        (∀ x ∈ F₀, ((M.tail x ∈ nd.1 ∧ M.head x ∈ nd.2.1) ∨ (M.tail x ∈ nd.2.1 ∧ M.head x ∈ nd.1)) →
          x = nd.2.2.1 ∨ x = nd.2.2.2) ∧
        -- Blue edges inside `nd.1` or `nd.2.1` belong to nodes `< i`
        (∀ x ∈ F₀, M.tail x ∈ nd.1 → M.head x ∈ nd.1 →
          ∃ j : Fin (postNodes tc).length, j < i ∧
            (x = ((postNodes tc)[j.1]'j.2).2.2.1 ∨ x = ((postNodes tc)[j.1]'j.2).2.2.2)) ∧
        (∀ x ∈ F₀, M.tail x ∈ nd.2.1 → M.head x ∈ nd.2.1 →
          ∃ j : Fin (postNodes tc).length, j < i ∧
            (x = ((postNodes tc)[j.1]'j.2).2.2.1 ∨ x = ((postNodes tc)[j.1]'j.2).2.2.2)) ∧
        -- Each operand is either a prior stage or a singleton
        ((∃ j : Fin (postNodes tc).length, j < i ∧
            nd.1 = ((postNodes tc)[j.1]'j.2).1 ∪ ((postNodes tc)[j.1]'j.2).2.1) ∨ nd.1.card = 1) ∧
        ((∃ j : Fin (postNodes tc).length, j < i ∧
            nd.2.1 = ((postNodes tc)[j.1]'j.2).1 ∪ ((postNodes tc)[j.1]'j.2).2.1) ∨ nd.2.1.card = 1))
  | _, _, .single w =>
      ⟨fun _ hx => absurd hx (Finset.notMem_empty _),
       Or.inr (Finset.card_singleton w),
       fun i => absurd i.2 (by simp [postNodes])⟩
  | _, _, .join (W₁ := W₁) (W₂ := W₂) (F₁ := F₁) (F₂ := F₂)
      left right e f hdisjW hdisjF he_ne_f he1 he2 hf1 hf2 he_cr hf_cr => by
      obtain ⟨hL_uniq, hL_top, hL_nodes⟩ := postNodes_props left
      obtain ⟨hR_uniq, hR_top, hR_nodes⟩ := postNodes_props right
      set L := postNodes left
      set R := postNodes right
      let tc := TwoConstruction.join left right e f hdisjW hdisjF he_ne_f he1 he2 hf1 hf2 he_cr hf_cr
      set P := postNodes tc
      have hP_def : P = L ++ R ++ [(W₁, W₂, e, f)] := rfl
      have hP_len : P.length = L.length + R.length + 1 := by
        rw [hP_def, List.length_append, List.length_append, List.length_singleton]
      have hgetL : ∀ (k : ℕ) (hk : k < L.length), P[k]'(by omega) = L[k]'hk := fun k hk => by
        have h1 : k < (L ++ R).length := by rw [List.length_append]; omega
        show (L ++ R ++ [(W₁, W₂, e, f)])[k]'(by rw [List.length_append, List.length_append, List.length_singleton]; omega) = L[k]'hk
        rw [List.getElem_append_left h1, List.getElem_append_left hk]
      have hgetR : ∀ (k : ℕ) (hk : k < R.length),
          P[L.length + k]'(by omega) = R[k]'hk := fun k hk => by
        have h1 : L.length + k < (L ++ R).length := by rw [List.length_append]; omega
        show (L ++ R ++ [(W₁, W₂, e, f)])[L.length + k]'(by rw [List.length_append, List.length_append, List.length_singleton]; omega) = R[k]'hk
        rw [List.getElem_append_left h1, List.getElem_append_right (Nat.le_add_right L.length k)]
        simp
      have hgetLast : P[L.length + R.length]'(by omega) = (W₁, W₂, e, f) := by
        have hle : (L ++ R).length ≤ L.length + R.length := by rw [List.length_append]
        show (L ++ R ++ [(W₁, W₂, e, f)])[L.length + R.length]'(by rw [List.length_append, List.length_append, List.length_singleton]; omega) = (W₁, W₂, e, f)
        rw [List.getElem_append_right hle]
        simp [List.length_append]
      -- Helper: edges of nodes in `L` lie in `F₁`, in `R` lie in `F₂`
      have hL_in_F1 : ∀ (k : ℕ) (hk : k < L.length),
          (L[k]'hk).2.2.1 ∈ F₁ ∧ (L[k]'hk).2.2.2 ∈ F₁ := fun k hk =>
        ⟨(hL_nodes ⟨k, hk⟩).2.2.2.2.2.1, (hL_nodes ⟨k, hk⟩).2.2.2.2.2.2.1⟩
      have hR_in_F2 : ∀ (k : ℕ) (hk : k < R.length),
          (R[k]'hk).2.2.1 ∈ F₂ ∧ (R[k]'hk).2.2.2 ∈ F₂ := fun k hk =>
        ⟨(hR_nodes ⟨k, hk⟩).2.2.2.2.2.1, (hR_nodes ⟨k, hk⟩).2.2.2.2.2.2.1⟩
      refine ⟨?_, ?_, ?_⟩
      · -- (1) Unique node per edge in `insert e (insert f (F₁ ∪ F₂))`
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · refine ⟨⟨L.length + R.length, by omega⟩, ?_, fun idx hidx => ?_⟩
          · dsimp only; rw [hgetLast]; exact Or.inl rfl
          · apply Fin.ext; dsimp only
            change x = (P[idx.1]'idx.2).2.2.1 ∨ x = (P[idx.1]'idx.2).2.2.2 at hidx
            by_contra hne
            by_cases hltL : idx.1 < L.length
            · rw [hgetL idx.1 hltL] at hidx
              rcases hidx with h | h <;> [exact he1 (h ▸ (hL_in_F1 idx.1 hltL).1); exact he1 (h ▸ (hL_in_F1 idx.1 hltL).2)]
            · have hk : idx.1 - L.length < R.length := by omega
              have hidx_eq : idx.1 = L.length + (idx.1 - L.length) := by omega
              have hg : P[idx.1]'idx.2 = R[idx.1 - L.length]'hk := by
                have := hgetR (idx.1 - L.length) hk; simpa only [← hidx_eq] using this
              rw [hg] at hidx
              rcases hidx with h | h <;> [exact he2 (h ▸ (hR_in_F2 _ hk).1); exact he2 (h ▸ (hR_in_F2 _ hk).2)]
        · rcases Finset.mem_insert.mp hx with rfl | hx
          · refine ⟨⟨L.length + R.length, by omega⟩, ?_, fun idx hidx => ?_⟩
            · dsimp only; rw [hgetLast]; exact Or.inr rfl
            · apply Fin.ext; dsimp only
              change x = (P[idx.1]'idx.2).2.2.1 ∨ x = (P[idx.1]'idx.2).2.2.2 at hidx
              by_contra hne
              by_cases hltL : idx.1 < L.length
              · rw [hgetL idx.1 hltL] at hidx
                rcases hidx with h | h <;> [exact hf1 (h ▸ (hL_in_F1 idx.1 hltL).1); exact hf1 (h ▸ (hL_in_F1 idx.1 hltL).2)]
              · have hk : idx.1 - L.length < R.length := by omega
                have hidx_eq : idx.1 = L.length + (idx.1 - L.length) := by omega
                have hg : P[idx.1]'idx.2 = R[idx.1 - L.length]'hk := by
                  have := hgetR (idx.1 - L.length) hk; simpa only [← hidx_eq] using this
                rw [hg] at hidx
                rcases hidx with h | h <;> [exact hf2 (h ▸ (hR_in_F2 _ hk).1); exact hf2 (h ▸ (hR_in_F2 _ hk).2)]
          · rcases Finset.mem_union.mp hx with hx1 | hx2
            · obtain ⟨idx₁, hidx₁, huniq₁⟩ := hL_uniq x hx1
              refine ⟨⟨idx₁.1, by omega⟩, ?_, fun idx hidx => ?_⟩
              · dsimp only; rw [hgetL idx₁.1 idx₁.2]; exact hidx₁
              · apply Fin.ext; dsimp only
                change x = (P[idx.1]'idx.2).2.2.1 ∨ x = (P[idx.1]'idx.2).2.2.2 at hidx
                by_cases hltL : idx.1 < L.length
                · rw [hgetL idx.1 hltL] at hidx
                  exact congrArg Fin.val (huniq₁ ⟨idx.1, hltL⟩ hidx)
                · by_cases hlast : idx.1 = L.length + R.length
                  · have hg : P[idx.1]'idx.2 = (W₁, W₂, e, f) := by simpa only [hlast] using hgetLast
                    rw [hg] at hidx
                    dsimp only at hidx
                    rcases hidx with rfl | rfl
                    · exact absurd hx1 he1
                    · exact absurd hx1 hf1
                  · have hk : idx.1 - L.length < R.length := by omega
                    have hidx_eq : idx.1 = L.length + (idx.1 - L.length) := by omega
                    have hg : P[idx.1]'idx.2 = R[idx.1 - L.length]'hk := by
                      have := hgetR (idx.1 - L.length) hk; simpa only [← hidx_eq] using this
                    rw [hg] at hidx
                    rcases hidx with h | h
                    · exact absurd (h ▸ (hR_in_F2 _ hk).1) (Finset.disjoint_left.mp hdisjF hx1)
                    · exact absurd (h ▸ (hR_in_F2 _ hk).2) (Finset.disjoint_left.mp hdisjF hx1)
            · obtain ⟨idx₂, hidx₂, huniq₂⟩ := hR_uniq x hx2
              refine ⟨⟨L.length + idx₂.1, by omega⟩, ?_, fun idx hidx => ?_⟩
              · dsimp only; rw [hgetR idx₂.1 idx₂.2]; exact hidx₂
              · apply Fin.ext; dsimp only
                change x = (P[idx.1]'idx.2).2.2.1 ∨ x = (P[idx.1]'idx.2).2.2.2 at hidx
                by_cases hltL : idx.1 < L.length
                · rw [hgetL idx.1 hltL] at hidx
                  rcases hidx with h | h
                  · exact absurd (h ▸ (hL_in_F1 _ hltL).1) (Finset.disjoint_right.mp hdisjF hx2)
                  · exact absurd (h ▸ (hL_in_F1 _ hltL).2) (Finset.disjoint_right.mp hdisjF hx2)
                · by_cases hlast : idx.1 = L.length + R.length
                  · have hg : P[idx.1]'idx.2 = (W₁, W₂, e, f) := by simpa only [hlast] using hgetLast
                    rw [hg] at hidx
                    dsimp only at hidx
                    rcases hidx with rfl | rfl
                    · exact absurd hx2 he2
                    · exact absurd hx2 hf2
                  · have hk : idx.1 - L.length < R.length := by omega
                    have hidx_eq : idx.1 = L.length + (idx.1 - L.length) := by omega
                    have hg : P[idx.1]'idx.2 = R[idx.1 - L.length]'hk := by
                      have := hgetR (idx.1 - L.length) hk; simpa only [← hidx_eq] using this
                    rw [hg] at hidx
                    have heq := congrArg Fin.val (huniq₂ ⟨idx.1 - L.length, hk⟩ hidx)
                    dsimp only at heq; omega
      · -- (2) Top stage is the last node!
        left
        refine ⟨⟨L.length + R.length, by omega⟩, ?_⟩
        dsimp only; rw [hgetLast]
      · -- (3) Node properties for every `i : Fin P.length`
        intro i
        by_cases hltL : i.1 < L.length
        · have hnd_eq : P[i.1]'i.2 = L[i.1]'hltL := hgetL i.1 hltL
          have hp := hL_nodes ⟨i.1, hltL⟩
          dsimp only at hp ⊢
          rw [hnd_eq]
          obtain ⟨hsub, hdisj, hne1, hne2, hneef, heF1, hfF1, hcr1, hcr2, hcross, hop1, hop2, hst1, hst2⟩ := hp
          have hsub1 : (L[i.1]'hltL).1 ⊆ W₁ := Finset.subset_union_left.trans hsub
          have hsub2 : (L[i.1]'hltL).2.1 ⊆ W₁ := Finset.subset_union_right.trans hsub
          have hmemF1 : ∀ x ∈ insert e (insert f (F₁ ∪ F₂)),
              M.tail x ∈ W₁ → M.head x ∈ W₁ → x ∈ F₁ := by
            intro x hx ht1 hh1
            rcases Finset.mem_insert.mp hx with rfl | hx
            · rcases he_cr with ⟨_, h2⟩ | ⟨h2, _⟩
              · exact absurd h2 (Finset.disjoint_left.mp hdisjW hh1)
              · exact absurd h2 (Finset.disjoint_left.mp hdisjW ht1)
            · rcases Finset.mem_insert.mp hx with rfl | hx
              · rcases hf_cr with ⟨_, h2⟩ | ⟨h2, _⟩
                · exact absurd h2 (Finset.disjoint_left.mp hdisjW hh1)
                · exact absurd h2 (Finset.disjoint_left.mp hdisjW ht1)
              · rcases Finset.mem_union.mp hx with hx | hx
                · exact hx
                · exact absurd (twoConstr_edges_ends right x hx).1 (Finset.disjoint_left.mp hdisjW ht1)
          refine ⟨hsub.trans Finset.subset_union_left, hdisj, hne1, hne2, hneef,
            Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_union_left _ heF1)),
            Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_union_left _ hfF1)),
            hcr1, hcr2, ?_, ?_, ?_, ?_, ?_⟩
          · intro x hx hcr
            have hx1 : x ∈ F₁ := by
              rcases hcr with ⟨ht, hh⟩ | ⟨ht, hh⟩
              · exact hmemF1 x hx (hsub1 ht) (hsub2 hh)
              · exact hmemF1 x hx (hsub2 ht) (hsub1 hh)
            exact hcross x hx1 hcr
          · intro x hx ht hh
            obtain ⟨j, hj, hje⟩ := hop1 x (hmemF1 x hx (hsub1 ht) (hsub1 hh)) ht hh
            refine ⟨⟨j.1, by omega⟩, hj, ?_⟩
            dsimp only; rw [hgetL j.1 j.2]; exact hje
          · intro x hx ht hh
            obtain ⟨j, hj, hje⟩ := hop2 x (hmemF1 x hx (hsub2 ht) (hsub2 hh)) ht hh
            refine ⟨⟨j.1, by omega⟩, hj, ?_⟩
            dsimp only; rw [hgetL j.1 j.2]; exact hje
          · rcases hst1 with ⟨j, hj, hjeq⟩ | hcard1
            · left; refine ⟨⟨j.1, by omega⟩, hj, ?_⟩
              dsimp only; rw [hgetL j.1 j.2]; exact hjeq
            · right; exact hcard1
          · rcases hst2 with ⟨j, hj, hjeq⟩ | hcard1
            · left; refine ⟨⟨j.1, by omega⟩, hj, ?_⟩
              dsimp only; rw [hgetL j.1 j.2]; exact hjeq
            · right; exact hcard1
        · by_cases hlast : i.1 = L.length + R.length
          · have hnd_eq : P[i.1]'i.2 = (W₁, W₂, e, f) := by simpa only [hlast] using hgetLast
            dsimp only
            rw [hnd_eq]
            refine ⟨Finset.Subset.rfl, hdisjW, (twoConstr_card left).1, (twoConstr_card right).1,
              he_ne_f, Finset.mem_insert_self _ _,
              Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), he_cr, hf_cr, ?_, ?_, ?_, ?_, ?_⟩
            · intro x hx hcr
              rcases Finset.mem_insert.mp hx with rfl | hx
              · exact Or.inl rfl
              · rcases Finset.mem_insert.mp hx with rfl | hx
                · exact Or.inr rfl
                · exfalso
                  rcases Finset.mem_union.mp hx with hx | hx
                  · obtain ⟨ht1, hh1, _⟩ := twoConstr_edges_ends left x hx
                    rcases hcr with ⟨_, hh2⟩ | ⟨ht2, _⟩
                    · exact Finset.disjoint_left.mp hdisjW hh1 hh2
                    · exact Finset.disjoint_left.mp hdisjW ht1 ht2
                  · obtain ⟨ht2, hh2, _⟩ := twoConstr_edges_ends right x hx
                    rcases hcr with ⟨ht1, _⟩ | ⟨_, hh1⟩
                    · exact Finset.disjoint_left.mp hdisjW ht1 ht2
                    · exact Finset.disjoint_left.mp hdisjW hh1 hh2
            · intro x hx ht1 hh1
              have hx1 : x ∈ F₁ := by
                rcases Finset.mem_insert.mp hx with rfl | hx
                · rcases he_cr with ⟨_, h2⟩ | ⟨h2, _⟩
                  · exact absurd h2 (Finset.disjoint_left.mp hdisjW hh1)
                  · exact absurd h2 (Finset.disjoint_left.mp hdisjW ht1)
                · rcases Finset.mem_insert.mp hx with rfl | hx
                  · rcases hf_cr with ⟨_, h2⟩ | ⟨h2, _⟩
                    · exact absurd h2 (Finset.disjoint_left.mp hdisjW hh1)
                    · exact absurd h2 (Finset.disjoint_left.mp hdisjW ht1)
                  · rcases Finset.mem_union.mp hx with hx | hx
                    · exact hx
                    · exact absurd (twoConstr_edges_ends right x hx).1 (Finset.disjoint_left.mp hdisjW ht1)
              obtain ⟨j, hj, _⟩ := hL_uniq x hx1
              refine ⟨⟨j.1, by omega⟩, by show j.1 < i.1; omega, ?_⟩
              dsimp only; rw [hgetL j.1 j.2]; exact hj
            · intro x hx ht2 hh2
              have hx2 : x ∈ F₂ := by
                rcases Finset.mem_insert.mp hx with rfl | hx
                · rcases he_cr with ⟨h1, _⟩ | ⟨_, h1⟩
                  · exact absurd h1 (Finset.disjoint_right.mp hdisjW ht2)
                  · exact absurd h1 (Finset.disjoint_right.mp hdisjW hh2)
                · rcases Finset.mem_insert.mp hx with rfl | hx
                  · rcases hf_cr with ⟨h1, _⟩ | ⟨_, h1⟩
                    · exact absurd h1 (Finset.disjoint_right.mp hdisjW ht2)
                    · exact absurd h1 (Finset.disjoint_right.mp hdisjW hh2)
                  · rcases Finset.mem_union.mp hx with hx | hx
                    · exact absurd (twoConstr_edges_ends left x hx).1 (Finset.disjoint_right.mp hdisjW ht2)
                    · exact hx
              obtain ⟨j, hj, _⟩ := hR_uniq x hx2
              refine ⟨⟨L.length + j.1, by omega⟩, by show L.length + j.1 < i.1; omega, ?_⟩
              dsimp only; rw [hgetR j.1 j.2]; exact hj
            · rcases hL_top with ⟨j, hjeq⟩ | hcard1
              · left; refine ⟨⟨j.1, by omega⟩, by show j.1 < i.1; omega, ?_⟩
                dsimp only; rw [hgetL j.1 j.2]; exact hjeq
              · right; exact hcard1
            · rcases hR_top with ⟨j, hjeq⟩ | hcard1
              · left; refine ⟨⟨L.length + j.1, by omega⟩, by show L.length + j.1 < i.1; omega, ?_⟩
                dsimp only; rw [hgetR j.1 j.2]; exact hjeq
              · right; exact hcard1
          · -- `i` is in `R`
            have hk : i.1 - L.length < R.length := by omega
            have hi_eq : i.1 = L.length + (i.1 - L.length) := by omega
            have hnd_eq : P[i.1]'i.2 = R[i.1 - L.length]'hk := by
              have := hgetR (i.1 - L.length) hk; simpa only [← hi_eq] using this
            have hp := hR_nodes ⟨i.1 - L.length, hk⟩
            dsimp only at hp ⊢
            rw [hnd_eq]
            obtain ⟨hsub, hdisj, hne1, hne2, hneef, heF2, hfF2, hcr1, hcr2, hcross, hop1, hop2, hst1, hst2⟩ := hp
            have hsub1 : (R[i.1 - L.length]'hk).1 ⊆ W₂ := Finset.subset_union_left.trans hsub
            have hsub2 : (R[i.1 - L.length]'hk).2.1 ⊆ W₂ := Finset.subset_union_right.trans hsub
            have hmemF2 : ∀ x ∈ insert e (insert f (F₁ ∪ F₂)),
                M.tail x ∈ W₂ → M.head x ∈ W₂ → x ∈ F₂ := by
              intro x hx ht2 hh2
              rcases Finset.mem_insert.mp hx with rfl | hx
              · rcases he_cr with ⟨h1, _⟩ | ⟨_, h1⟩
                · exact absurd h1 (Finset.disjoint_right.mp hdisjW ht2)
                · exact absurd h1 (Finset.disjoint_right.mp hdisjW hh2)
              · rcases Finset.mem_insert.mp hx with rfl | hx
                · rcases hf_cr with ⟨h1, _⟩ | ⟨_, h1⟩
                  · exact absurd h1 (Finset.disjoint_right.mp hdisjW ht2)
                  · exact absurd h1 (Finset.disjoint_right.mp hdisjW hh2)
                · rcases Finset.mem_union.mp hx with hx | hx
                  · exact absurd (twoConstr_edges_ends left x hx).1 (Finset.disjoint_right.mp hdisjW ht2)
                  · exact hx
            refine ⟨hsub.trans Finset.subset_union_right, hdisj, hne1, hne2, hneef,
              Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_union_right _ heF2)),
              Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_union_right _ hfF2)),
              hcr1, hcr2, ?_, ?_, ?_, ?_, ?_⟩
            · intro x hx hcr
              have hx2 : x ∈ F₂ := by
                rcases hcr with ⟨ht, hh⟩ | ⟨ht, hh⟩
                · exact hmemF2 x hx (hsub1 ht) (hsub2 hh)
                · exact hmemF2 x hx (hsub2 ht) (hsub1 hh)
              exact hcross x hx2 hcr
            · intro x hx ht hh
              obtain ⟨j, hj, hje⟩ := hop1 x (hmemF2 x hx (hsub1 ht) (hsub1 hh)) ht hh
              refine ⟨⟨L.length + j.1, by omega⟩, by show L.length + j.1 < i.1; have : j.1 < i.1 - L.length := hj; omega, ?_⟩
              dsimp only; rw [hgetR j.1 j.2]; exact hje
            · intro x hx ht hh
              obtain ⟨j, hj, hje⟩ := hop2 x (hmemF2 x hx (hsub2 ht) (hsub2 hh)) ht hh
              refine ⟨⟨L.length + j.1, by omega⟩, by show L.length + j.1 < i.1; have : j.1 < i.1 - L.length := hj; omega, ?_⟩
              dsimp only; rw [hgetR j.1 j.2]; exact hje
            · rcases hst1 with ⟨j, hj, hjeq⟩ | hcard1
              · left; refine ⟨⟨L.length + j.1, by omega⟩, by show L.length + j.1 < i.1; have : j.1 < i.1 - L.length := hj; omega, ?_⟩
                dsimp only; rw [hgetR j.1 j.2]; exact hjeq
              · right; exact hcard1
            · rcases hst2 with ⟨j, hj, hjeq⟩ | hcard1
              · left; refine ⟨⟨L.length + j.1, by omega⟩, by show L.length + j.1 < i.1; have : j.1 < i.1 - L.length := hj; omega, ?_⟩
                dsimp only; rw [hgetR j.1 j.2]; exact hjeq
              · right; exact hcard1

end TwoConstructionLemmas

section Lemma39

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- Helper: a cubic `3`-edge-connected multigraph on `≥ 4` vertices is simple. -/
private lemma cubic_3ec_isSimple {V' E' : Type} [Fintype V'] [Fintype E']
    [DecidableEq V'] [DecidableEq E']
    (G : Multigraph V' E') (hcub : G.IsCubic) (h3 : G.IsEdgeConnected 3)
    (hn : 4 ≤ Fintype.card V') :
    G.IsSimple := by
  have hll : G.IsLoopless := by
    intro e hloop
    let u := G.tail e
    have hcomp : (Finset.univ \ ({u} : Finset V')).Nonempty := by
      have : (Finset.univ \ ({u} : Finset V')).card = Fintype.card V' - 1 := by
        rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Finset.card_singleton]
      exact Finset.card_pos.mp (by omega)
    have hcut := h3 {u} (Finset.singleton_nonempty u) hcomp
    have hsh := subgraph_cut_handshake (Multigraph.Subgraph.top G) {u} (Finset.subset_univ _)
    have hdeg_eq : (Multigraph.Subgraph.top G).deg u = G.deg u := rfl
    rw [Finset.sum_singleton, hdeg_eq, hcub u] at hsh
    have he_in : e ∈ (subgraphRestrict (Multigraph.Subgraph.top G) {u}).edges :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_singleton.mpr rfl,
        Finset.mem_singleton.mpr hloop.symm⟩
    have h1 : 1 ≤ (subgraphRestrict (Multigraph.Subgraph.top G) {u}).edges.card :=
      Finset.card_pos.mpr ⟨e, he_in⟩
    have hcut_eq : (Multigraph.Subgraph.top G).edges.filter (fun e' =>
        (G.tail e' ∈ ({u} : Finset V') ∧ G.head e' ∉ ({u} : Finset V')) ∨
        (G.tail e' ∉ ({u} : Finset V') ∧ G.head e' ∈ ({u} : Finset V'))) = G.cutEdges {u} := rfl
    rw [hcut_eq] at hsh
    omega
  refine ⟨hll, fun e₁ e₂ hsame => ?_⟩
  by_contra hne
  let u := G.tail e₁
  let w := G.head e₁
  have huw : u ≠ w := hll e₁
  let S : Finset V' := {u, w}
  have hScard : S.card = 2 := Finset.card_pair huw
  have hcomp : (Finset.univ \ S).Nonempty := by
    have : (Finset.univ \ S).card = Fintype.card V' - 2 := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, hScard]
    exact Finset.card_pos.mp (by omega)
  have hcut := h3 S ⟨u, Finset.mem_insert_self _ _⟩ hcomp
  have hsh := subgraph_cut_handshake (Multigraph.Subgraph.top G) S (Finset.subset_univ _)
  have hsum : ∑ v ∈ S, (Multigraph.Subgraph.top G).deg v = 6 := by
    calc ∑ v ∈ S, (Multigraph.Subgraph.top G).deg v = ∑ _v ∈ S, 3 :=
          Finset.sum_congr rfl (fun v _ => hcub v)
      _ = 6 := by rw [Finset.sum_const, hScard]; rfl
  have he1_in : e₁ ∈ (subgraphRestrict (Multigraph.Subgraph.top G) S).edges :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_insert_self _ _,
      Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩
  have he2_in : e₂ ∈ (subgraphRestrict (Multigraph.Subgraph.top G) S).edges := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
    · rcases hsame with ⟨ht, _⟩ | ⟨_, hh⟩
      · rw [← ht]; exact Finset.mem_insert_self _ _
      · rw [← hh]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    · rcases hsame with ⟨_, hh⟩ | ⟨ht, _⟩
      · rw [← hh]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      · rw [← ht]; exact Finset.mem_insert_self _ _
  have h2 : 2 ≤ (subgraphRestrict (Multigraph.Subgraph.top G) S).edges.card := by
    calc 2 = ({e₁, e₂} : Finset E').card := (Finset.card_pair hne).symm
      _ ≤ _ := Finset.card_le_card (fun x hx => by
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact he1_in
          · rw [Finset.mem_singleton.mp hx]; exact he2_in)
  have hcut_eq : (Multigraph.Subgraph.top G).edges.filter (fun e' =>
      (G.tail e' ∈ S ∧ G.head e' ∉ S) ∨ (G.tail e' ∉ S ∧ G.head e' ∈ S)) = G.cutEdges S := rfl
  rw [hsum, hcut_eq] at hsh
  omega

/-- Helper: deleting a vertex from a cubic `3`-edge-connected graph on `≥ 4` vertices
leaves a connected graph. -/
private lemma cubic_3ec_deleteVertex_connected {V' E' : Type} [Fintype V'] [Fintype E']
    [DecidableEq V'] [DecidableEq E']
    (G : Multigraph V' E') (hcub : G.IsCubic) (h3 : G.IsEdgeConnected 3)
    (v : V') :
    (G.deleteVertex v).Connected := by
  intro ⟨a, ha⟩ ⟨b, hb⟩
  by_contra hnot
  classical
  let C : Finset V' := Finset.univ.filter (fun w => ∃ hw : w ≠ v, Relation.ReflTransGen (G.deleteVertex v).Adj ⟨a, ha⟩ ⟨w, hw⟩)
  let D : Finset V' := Finset.univ.filter (fun w => w ≠ v ∧ w ∉ C)
  have haC : a ∈ C := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha, Relation.ReflTransGen.refl⟩
  have hbD : b ∈ D := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb, fun h => by
    rcases (Finset.mem_filter.mp h).2 with ⟨_, hr⟩; exact hnot hr⟩
  have hv_notC : v ∉ C := fun h => by rcases (Finset.mem_filter.mp h).2 with ⟨hw, _⟩; exact hw rfl
  have hv_notD : v ∉ D := fun h => (Finset.mem_filter.mp h).2.1 rfl
  have hCcomp : (Finset.univ \ C).Nonempty := ⟨v, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hv_notC⟩⟩
  have hDcomp : (Finset.univ \ D).Nonempty := ⟨v, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hv_notD⟩⟩
  have hcutC := h3 C ⟨a, haC⟩ hCcomp
  have hcutD := h3 D ⟨b, hbD⟩ hDcomp
  -- Every edge in `cutEdges C` has its non-`C` endpoint equal to `v`, and every edge in `cutEdges D` has its non-`D` endpoint equal to `v`!
  have hno_CD : ∀ e : E', (G.tail e ∈ C → G.head e ∉ D) ∧ (G.head e ∈ C → G.tail e ∉ D) := by
    intro e
    constructor
    · intro ht hh
      rcases (Finset.mem_filter.mp ht).2 with ⟨htne, hr⟩
      have hhne : G.head e ≠ v := (Finset.mem_filter.mp hh).2.1
      have hreach : Relation.ReflTransGen (G.deleteVertex v).Adj ⟨a, ha⟩ ⟨G.head e, hhne⟩ :=
        Relation.ReflTransGen.tail hr ⟨⟨e, htne, hhne⟩, Or.inl ⟨rfl, rfl⟩⟩
      exact (Finset.mem_filter.mp hh).2.2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hhne, hreach⟩)
    · intro hh ht
      rcases (Finset.mem_filter.mp hh).2 with ⟨hhne, hr⟩
      have htne : G.tail e ≠ v := (Finset.mem_filter.mp ht).2.1
      have hreach : Relation.ReflTransGen (G.deleteVertex v).Adj ⟨a, ha⟩ ⟨G.tail e, htne⟩ :=
        Relation.ReflTransGen.tail hr ⟨⟨e, htne, hhne⟩, Or.inr ⟨rfl, rfl⟩⟩
      exact (Finset.mem_filter.mp ht).2.2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, htne, hreach⟩)
  have hcutC_v : ∀ e ∈ G.cutEdges C, G.tail e = v ∨ G.head e = v := by
    intro e he
    rcases (Finset.mem_filter.mp he).2 with ⟨ht, hh⟩ | ⟨ht, hh⟩
    · right; by_contra hhne
      exact (hno_CD e).1 ht (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hhne, hh⟩)
    · left; by_contra htne
      exact (hno_CD e).2 hh (Finset.mem_filter.mpr ⟨Finset.mem_univ _, htne, ht⟩)
  have hcutD_v : ∀ e ∈ G.cutEdges D, G.tail e = v ∨ G.head e = v := by
    intro e he
    rcases (Finset.mem_filter.mp he).2 with ⟨ht, hh⟩ | ⟨ht, hh⟩
    · right; by_contra hhne
      by_cases hC : G.head e ∈ C
      · exact (hno_CD e).2 hC ht
      · exact hh (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hhne, hC⟩)
    · left; by_contra htne
      by_cases hC : G.tail e ∈ C
      · exact (hno_CD e).1 hC hh
      · exact ht (Finset.mem_filter.mpr ⟨Finset.mem_univ _, htne, hC⟩)
  have hdisj_CD : Disjoint (G.cutEdges C) (G.cutEdges D) := by
    rw [Finset.disjoint_left]
    intro e heC heD
    rcases (Finset.mem_filter.mp heC).2 with ⟨htC, hhnotC⟩ | ⟨htnotC, hhC⟩
    · rcases (Finset.mem_filter.mp heD).2 with ⟨htD, _⟩ | ⟨_, hhD⟩
      · exact (Finset.mem_filter.mp htD).2.2 htC
      · exact (hno_CD e).1 htC hhD
    · rcases (Finset.mem_filter.mp heD).2 with ⟨htD, _⟩ | ⟨_, hhD⟩
      · exact (hno_CD e).2 hhC htD
      · exact (Finset.mem_filter.mp hhD).2.2 hhC
  have hsub_v : G.cutEdges C ∪ G.cutEdges D ⊆
      Finset.univ.filter (fun e => G.tail e = v) ∪ Finset.univ.filter (fun e => G.head e = v) := by
    intro e he
    have hv : G.tail e = v ∨ G.head e = v := by
      rcases Finset.mem_union.mp he with h | h
      · exact hcutC_v e h
      · exact hcutD_v e h
    rcases hv with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  have hle : (G.cutEdges C).card + (G.cutEdges D).card ≤ G.deg v := by
    rw [← Finset.card_union_of_disjoint hdisj_CD]
    calc (G.cutEdges C ∪ G.cutEdges D).card
        ≤ (Finset.univ.filter (fun e => G.tail e = v) ∪ Finset.univ.filter (fun e => G.head e = v)).card :=
          Finset.card_le_card hsub_v
      _ ≤ (Finset.univ.filter (fun e => G.tail e = v)).card +
          (Finset.univ.filter (fun e => G.head e = v)).card := Finset.card_union_le _ _
      _ = G.deg v := rfl
  have hdeg3 := hcub v
  omega

/-- Helper: isomorphism preserves `IsSimple` and `Connected`. -/
private lemma iso_preserves_simple {V₁ E₁ V₂ E₂ : Type}
    {G₁ : Multigraph V₁ E₁} {G₂ : Multigraph V₂ E₂}
    (iso : Multigraph.Iso G₁ G₂) (h : G₂.IsSimple) : G₁.IsSimple := by
  constructor
  · intro e hloop
    have ht := iso.tail_eq e
    have hh := iso.head_eq e
    cases hdir : iso.dir e <;> simp only [hdir, Bool.false_eq_true, ↓reduceIte] at ht hh
    · exact h.1 (iso.toEdge e) (ht.trans (congrArg iso.toVert hloop |>.trans hh.symm))
    · exact h.1 (iso.toEdge e) (ht.trans (congrArg iso.toVert hloop.symm |>.trans hh.symm))
  · intro e₁ e₂ hsame
    apply iso.toEdge.injective
    apply h.2
    have ht1 := iso.tail_eq e₁; have hh1 := iso.head_eq e₁
    have ht2 := iso.tail_eq e₂; have hh2 := iso.head_eq e₂
    cases hd1 : iso.dir e₁ <;> cases hd2 : iso.dir e₂ <;>
      simp only [hd1, hd2, Bool.false_eq_true, ↓reduceIte] at ht1 hh1 ht2 hh2 <;>
      rcases hsame with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; exact ⟨ht1.trans (congrArg iso.toVert h1 |>.trans ht2.symm), hh1.trans (congrArg iso.toVert h2 |>.trans hh2.symm)⟩
    · right; exact ⟨ht1.trans (congrArg iso.toVert h1 |>.trans hh2.symm), hh1.trans (congrArg iso.toVert h2 |>.trans ht2.symm)⟩
    · right; exact ⟨ht1.trans (congrArg iso.toVert h1 |>.trans hh2.symm), hh1.trans (congrArg iso.toVert h2 |>.trans ht2.symm)⟩
    · left; exact ⟨ht1.trans (congrArg iso.toVert h1 |>.trans ht2.symm), hh1.trans (congrArg iso.toVert h2 |>.trans hh2.symm)⟩
    · right; exact ⟨ht1.trans (congrArg iso.toVert h2 |>.trans hh2.symm), hh1.trans (congrArg iso.toVert h1 |>.trans ht2.symm)⟩
    · left; exact ⟨ht1.trans (congrArg iso.toVert h2 |>.trans ht2.symm), hh1.trans (congrArg iso.toVert h1 |>.trans hh2.symm)⟩
    · left; exact ⟨ht1.trans (congrArg iso.toVert h2 |>.trans ht2.symm), hh1.trans (congrArg iso.toVert h1 |>.trans hh2.symm)⟩
    · right; exact ⟨ht1.trans (congrArg iso.toVert h2 |>.trans hh2.symm), hh1.trans (congrArg iso.toVert h1 |>.trans ht2.symm)⟩

private lemma iso_preserves_connected {V₁ E₁ V₂ E₂ : Type}
    {G₁ : Multigraph V₁ E₁} {G₂ : Multigraph V₂ E₂}
    (iso : Multigraph.Iso G₁ G₂) (h : G₂.Connected) : G₁.Connected := by
  intro u v
  have hw := h (iso.toVert u) (iso.toVert v)
  have hlift : ∀ x y : V₂, Relation.ReflTransGen G₂.Adj x y →
      Relation.ReflTransGen G₁.Adj (iso.toVert.symm x) (iso.toVert.symm y) := by
    intro x y hxy
    induction hxy with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hstep ih =>
      refine Relation.ReflTransGen.tail ih ?_
      rcases hstep with ⟨e₂, hadj⟩
      let e₁ := iso.toEdge.symm e₂
      have he : iso.toEdge e₁ = e₂ := iso.toEdge.apply_symm_apply e₂
      have ht := iso.tail_eq e₁; have hh := iso.head_eq e₁
      rw [he] at ht hh
      refine ⟨e₁, ?_⟩
      cases hd : iso.dir e₁ <;> simp only [hd, Bool.false_eq_true, ↓reduceIte] at ht hh <;>
        rcases hadj with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; exact ⟨iso.toVert.injective (by simp [← ht, h1]), iso.toVert.injective (by simp [← hh, h2])⟩
      · right; exact ⟨iso.toVert.injective (by simp [← ht, h1]), iso.toVert.injective (by simp [← hh, h2])⟩
      · right; exact ⟨iso.toVert.injective (by simp [← hh, h2]), iso.toVert.injective (by simp [← ht, h1])⟩
      · left; exact ⟨iso.toVert.injective (by simp [← hh, h2]), iso.toVert.injective (by simp [← ht, h1])⟩
  have hres := hlift _ _ hw
  simpa only [Equiv.symm_apply_apply] using hres

/-- **Lemma 3.9(a) (Counts and red forest).** -/
theorem lem_3_9
    (Q : Multigraph V E) (hTC : Q.IsTruncatedCubic3EC)
    (wc : WellColouring Q) :
    Q.IsSimple ∧
    Q.Connected ∧
    2 * Fintype.card E = 3 * (Fintype.card V - 1) ∧
    (Multigraph.Subgraph.ofEdges Q Finset.univ (Finset.univ \ wc.blue)
      (fun _ => Finset.mem_univ _) (fun _ => Finset.mem_univ _)).IsForest ∧
    (∀ e ∈ wc.blue,
      Quotient.mk (redSetoid Q wc.blue) (Q.tail e) ≠
      Quotient.mk (redSetoid Q wc.blue) (Q.head e)) := by
  obtain ⟨V', E', _, _, _, _, Qplus, v, hcub, h3, hn4, ⟨iso⟩⟩ := hTC
  have hQp_simple : Qplus.IsSimple := cubic_3ec_isSimple Qplus hcub h3 hn4
  have hdel_simple : (Qplus.deleteVertex v).IsSimple := by
    constructor
    · intro e hloop
      exact hQp_simple.1 e.1 (congrArg Subtype.val hloop)
    · intro e₁ e₂ hsame
      apply Subtype.ext
      apply hQp_simple.2
      rcases hsame with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨congrArg Subtype.val h1, congrArg Subtype.val h2⟩
      · exact Or.inr ⟨congrArg Subtype.val h1, congrArg Subtype.val h2⟩
  have hQ_simple : Q.IsSimple := iso_preserves_simple iso hdel_simple
  have hQ_conn : Q.Connected :=
    iso_preserves_connected iso (cubic_3ec_deleteVertex_connected Qplus hcub h3 v)
  -- Edge count: `2 * |E| = 3 * (|V| - 1)`
  have hcardV : Fintype.card V + 1 = Fintype.card V' := by
    have h1 := Fintype.card_congr iso.toVert
    rw [h1, Fintype.card_subtype_compl, Fintype.card_subtype_eq]
    omega
  have hQp_edges : 2 * Fintype.card E' = 3 * Fintype.card V' := by
    have hsh := subgraph_handshake (Multigraph.Subgraph.top Qplus)
    have hsum : ∑ u ∈ (Multigraph.Subgraph.top Qplus).verts, (Multigraph.Subgraph.top Qplus).deg u =
        3 * Fintype.card V' := by
      calc ∑ u ∈ (Multigraph.Subgraph.top Qplus).verts, (Multigraph.Subgraph.top Qplus).deg u
          = ∑ _u : V', 3 := Finset.sum_congr rfl (fun u _ => hcub u)
        _ = 3 * Fintype.card V' := by simp [mul_comm]
    rw [hsum] at hsh
    change 3 * Fintype.card V' = 2 * Fintype.card E' at hsh
    exact hsh.symm
  have hcardE : Fintype.card E + 3 = Fintype.card E' := by
    have h1 := Fintype.card_congr iso.toEdge
    rw [h1]
    have hdisj : Disjoint (Finset.univ.filter (fun e : E' => Qplus.tail e = v))
        (Finset.univ.filter (fun e : E' => Qplus.head e = v)) := by
      rw [Finset.disjoint_left]; intro e ht hh
      exact hQp_simple.1 e ((Finset.mem_filter.mp ht).2.trans (Finset.mem_filter.mp hh).2.symm)
    have hinc_card : (Finset.univ.filter (fun e : E' => Qplus.tail e = v ∨ Qplus.head e = v)).card = 3 := by
      have hun : Finset.univ.filter (fun e : E' => Qplus.tail e = v ∨ Qplus.head e = v) =
          Finset.univ.filter (fun e : E' => Qplus.tail e = v) ∪
          Finset.univ.filter (fun e : E' => Qplus.head e = v) := by
        ext e; simp
      rw [hun, Finset.card_union_of_disjoint hdisj]
      exact hcub v
    have hcompl := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset E'))
      (p := fun e => Qplus.tail e ≠ v ∧ Qplus.head e ≠ v)
    have hnot_eq : (Finset.univ.filter (fun e : E' => ¬ (Qplus.tail e ≠ v ∧ Qplus.head e ≠ v))) =
        Finset.univ.filter (fun e : E' => Qplus.tail e = v ∨ Qplus.head e = v) := by
      ext e; simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and_or, not_not]
    rw [hnot_eq, hinc_card, Finset.card_univ, ← Fintype.card_subtype] at hcompl
    exact hcompl
  have hedge_count : 2 * Fintype.card E = 3 * (Fintype.card V - 1) := by omega
  -- No blue edge has both ends in one red component
  have hblue_noloop : ∀ e ∈ wc.blue,
      Quotient.mk (redSetoid Q wc.blue) (Q.tail e) ≠
      Quotient.mk (redSetoid Q wc.blue) (Q.head e) := fun e he =>
    (twoConstr_edges_ends wc.twoConstr ⟨e, he⟩ (Finset.mem_univ _)).2.2
  -- Red edges form a forest: count `|R| = n - j` where `j = |V(Q/red)|`
  have hblue_card_tree : wc.blue.card + 1 = Fintype.card V := spanningTree_edges_card wc.blue_tree
  have hblue_card_2c : wc.blue.card = 2 * (Fintype.card (Quotient (redSetoid Q wc.blue)) - 1) := by
    have h2c := (twoConstr_card wc.twoConstr).2
    simpa only [Finset.card_univ, Fintype.card_coe] using h2c
  set R : Finset E := Finset.univ \ wc.blue
  have hR_card : R.card + Fintype.card (Quotient (redSetoid Q wc.blue)) = Fintype.card V := by
    have hR : R.card + wc.blue.card = Fintype.card E := by
      have := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ wc.blue)
      simpa only [Finset.card_univ] using this
    have hj_pos : 1 ≤ Fintype.card (Quotient (redSetoid Q wc.blue)) :=
      Finset.card_pos.mpr (twoConstr_card wc.twoConstr).1
    omega
  let Red : Q.Subgraph :=
    Multigraph.Subgraph.ofEdges Q Finset.univ R (fun _ => Finset.mem_univ _) (fun _ => Finset.mem_univ _)
  have hRed_forest : Red.IsForest := by
    -- Every red component `c` has `V_c` connected by `R_c`, so `|V_c| - 1 ≤ |R_c|`; summing gives equality!
    let Vc (c : Quotient (redSetoid Q wc.blue)) : Finset V :=
      Finset.univ.filter (fun u => Quotient.mk (redSetoid Q wc.blue) u = c)
    let Rc (c : Quotient (redSetoid Q wc.blue)) : Finset E :=
      R.filter (fun e => Quotient.mk (redSetoid Q wc.blue) (Q.tail e) = c)
    have hred_same_c : ∀ e ∈ R,
        Quotient.mk (redSetoid Q wc.blue) (Q.tail e) = Quotient.mk (redSetoid Q wc.blue) (Q.head e) := by
      intro e he
      have hnb : e ∉ wc.blue := (Finset.mem_sdiff.mp he).2
      exact Quotient.sound (Relation.ReflTransGen.single ⟨e, hnb, Or.inl ⟨rfl, rfl⟩⟩)
    let Redc (c : Quotient (redSetoid Q wc.blue)) : Q.Subgraph :=
      Multigraph.Subgraph.ofEdges Q (Vc c) (Rc c)
        (fun he => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp he).2⟩)
        (fun he => Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (hred_same_c _ (Finset.mem_filter.mp he).1).symm.trans (Finset.mem_filter.mp he).2⟩)
    have hRedc_conn : ∀ c, (Redc c).Connected := by
      intro c
      obtain ⟨u₀, rfl⟩ := Quotient.exists_rep c
      refine ⟨⟨u₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩, fun u hu v hv => ?_⟩
      have hu_eq : Quotient.mk (redSetoid Q wc.blue) u = Quotient.mk (redSetoid Q wc.blue) u₀ :=
        (Finset.mem_filter.mp hu).2
      have hv_eq : Quotient.mk (redSetoid Q wc.blue) v = Quotient.mk (redSetoid Q wc.blue) u₀ :=
        (Finset.mem_filter.mp hv).2
      have hrel : Relation.ReflTransGen (redAdj Q wc.blue) u v :=
        Quotient.exact (hu_eq.trans hv_eq.symm)
      clear hu hv hv_eq
      induction hrel with
      | refl => exact Relation.ReflTransGen.refl
      | @tail w z hwz hstep ih =>
        have hw_eq : Quotient.mk (redSetoid Q wc.blue) w = Quotient.mk (redSetoid Q wc.blue) u₀ :=
          (Quotient.sound hwz).symm.trans hu_eq
        rcases hstep with ⟨e, hnb, ⟨ht, hh⟩ | ⟨ht, hh⟩⟩
        · have heR : e ∈ Rc (Quotient.mk (redSetoid Q wc.blue) u₀) :=
            Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnb⟩, ht.symm ▸ hw_eq⟩
          exact Relation.ReflTransGen.tail ih ⟨e, heR, Or.inl ⟨ht, hh⟩⟩
        · have heR : e ∈ Rc (Quotient.mk (redSetoid Q wc.blue) u₀) := by
            have hth := hred_same_c e (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnb⟩)
            exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnb⟩,
              hth.trans (hh.symm ▸ hw_eq)⟩
          exact Relation.ReflTransGen.tail ih ⟨e, heR, Or.inr ⟨ht, hh⟩⟩
    have hle_c : ∀ c, (Vc c).card - 1 ≤ (Rc c).card := fun c => by
      have := connected_verts_le_edges_succ (Redc c) (hRedc_conn c)
      change (Vc c).card ≤ (Rc c).card + 1 at this; omega
    have hsumV : ∑ c : Quotient (redSetoid Q wc.blue), (Vc c).card = Fintype.card V := by
      have := Finset.card_eq_sum_card_fiberwise (f := Quotient.mk (redSetoid Q wc.blue))
        (s := Finset.univ) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
      simpa only [Finset.card_univ] using this.symm
    have hsumR : ∑ c : Quotient (redSetoid Q wc.blue), (Rc c).card = R.card := by
      have := Finset.card_eq_sum_card_fiberwise (f := fun e => Quotient.mk (redSetoid Q wc.blue) (Q.tail e))
        (s := R) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
      exact this.symm
    have hsum_sub : ∑ c : Quotient (redSetoid Q wc.blue), ((Vc c).card - 1) = R.card := by
      have hpos : ∀ c, 1 ≤ (Vc c).card := fun c => Finset.card_pos.mpr (hRedc_conn c).1
      have hadd : (∑ c, ((Vc c).card - 1)) + Fintype.card (Quotient (redSetoid Q wc.blue)) =
          ∑ c, (Vc c).card := by
        calc (∑ c, ((Vc c).card - 1)) + Fintype.card (Quotient (redSetoid Q wc.blue))
            = ∑ c, (((Vc c).card - 1) + 1) := by rw [Finset.sum_add_distrib]; simp
          _ = ∑ c, (Vc c).card := Finset.sum_congr rfl (fun c _ => Nat.sub_add_cancel (hpos c))
      omega
    have heq_c : ∀ c, (Rc c).card + 1 = (Vc c).card := by
      have hall : ∀ c ∈ (Finset.univ : Finset (Quotient (redSetoid Q wc.blue))),
          (Vc c).card - 1 = (Rc c).card :=
        (Finset.sum_eq_sum_iff_of_le (fun c _ => hle_c c)).mp (hsum_sub.trans hsumR.symm)
      intro c
      have h1 := hall c (Finset.mem_univ c)
      have hpos : 1 ≤ (Vc c).card := Finset.card_pos.mpr (hRedc_conn c).1
      omega
    intro C hCle hCcyc
    obtain ⟨v₀, hv₀⟩ := hCcyc.1.1
    let c := Quotient.mk (redSetoid Q wc.blue) v₀
    have hC_sub_Redc : C ≤ Redc c := by
      have hv_in : ∀ u ∈ C.verts, u ∈ Vc c := by
        intro u hu
        have hw := hCcyc.1.2 v₀ hv₀ u hu
        have hrel : Relation.ReflTransGen (redAdj Q wc.blue) v₀ u :=
          reflTransGen_mono (fun _ _ ⟨e, heC, hadj⟩ =>
            ⟨e, (Finset.mem_sdiff.mp (hCle.2 heC)).2, hadj⟩) hw
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Quotient.sound hrel).symm⟩
      refine ⟨hv_in, fun e heC => ?_⟩
      exact Finset.mem_filter.mpr ⟨hCle.2 heC, (Finset.mem_filter.mp (hv_in _ (C.tail_mem heC))).2⟩
    exact connected_edges_eq_verts_sub_one_isForest (Redc c) (hRedc_conn c) (heq_c c) C hC_sub_Redc hCcyc
  exact ⟨hQ_simple, hQ_conn, hedge_count, hRed_forest, hblue_noloop⟩

/-- Helper: for any `2`-construction on `redQuotient Q wc.blue`, each stage graph `Q[stageVerts W₀]` is connected. -/
private lemma twoConstr_stageVerts_connected
    (Q : Multigraph V E) (blue : Finset E) [DecidableEq (Quotient (redSetoid Q blue))] :
    ∀ {W₀ : Finset (Quotient (redSetoid Q blue))} {F₀ : Finset {e : E // e ∈ blue}},
      TwoConstruction (redQuotient Q blue) W₀ F₀ →
      (Multigraph.Subgraph.induced Q (stageVerts Q blue W₀)).Connected
  | _, _, .single c => by
      obtain ⟨u₀, rfl⟩ := Quotient.exists_rep c
      refine ⟨⟨u₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_singleton.mpr rfl⟩⟩,
        fun u hu v hv => ?_⟩
      have hu_eq : Quotient.mk (redSetoid Q blue) u = Quotient.mk (redSetoid Q blue) u₀ :=
        Finset.mem_singleton.mp (Finset.mem_filter.mp hu).2
      have hv_eq : Quotient.mk (redSetoid Q blue) v = Quotient.mk (redSetoid Q blue) u₀ :=
        Finset.mem_singleton.mp (Finset.mem_filter.mp hv).2
      have hrel : Relation.ReflTransGen (redAdj Q blue) u v := Quotient.exact (hu_eq.trans hv_eq.symm)
      clear hu hv hv_eq
      induction hrel with
      | refl => exact Relation.ReflTransGen.refl
      | @tail w z hwz hstep ih =>
        have hw_eq : Quotient.mk (redSetoid Q blue) w = Quotient.mk (redSetoid Q blue) u₀ :=
          (Quotient.sound hwz).symm.trans hu_eq
        rcases hstep with ⟨e, hnb, hadj⟩
        have hz_eq : Quotient.mk (redSetoid Q blue) z = Quotient.mk (redSetoid Q blue) u₀ :=
          (Quotient.sound (Relation.ReflTransGen.single ⟨e, hnb, hadj⟩)).symm.trans hw_eq
        have he_ind : e ∈ (Multigraph.Subgraph.induced Q (stageVerts Q blue {Quotient.mk (redSetoid Q blue) u₀})).edges := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
          · rcases hadj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_singleton.mpr hw_eq⟩
            · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_singleton.mpr hz_eq⟩
          · rcases hadj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_singleton.mpr hz_eq⟩
            · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_singleton.mpr hw_eq⟩
        exact Relation.ReflTransGen.tail ih ⟨e, he_ind, hadj⟩
  | _, _, .join (W₁ := W₁) (W₂ := W₂) left right e f _ _ _ _ _ _ _ he_cr _ => by
      have hL := twoConstr_stageVerts_connected Q blue left
      have hR := twoConstr_stageVerts_connected Q blue right
      have hunion : stageVerts Q blue (W₁ ∪ W₂) = stageVerts Q blue W₁ ∪ stageVerts Q blue W₂ := by
        ext v; simp [stageVerts]
      have hsubL : (Multigraph.Subgraph.induced Q (stageVerts Q blue W₁)).edges ⊆
          (Multigraph.Subgraph.induced Q (stageVerts Q blue (W₁ ∪ W₂))).edges := fun x hx => by
        rw [hunion]; simp only [Multigraph.Subgraph.induced, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        exact ⟨Finset.mem_union_left _ hx.1, Finset.mem_union_left _ hx.2⟩
      have hsubR : (Multigraph.Subgraph.induced Q (stageVerts Q blue W₂)).edges ⊆
          (Multigraph.Subgraph.induced Q (stageVerts Q blue (W₁ ∪ W₂))).edges := fun x hx => by
        rw [hunion]; simp only [Multigraph.Subgraph.induced, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        exact ⟨Finset.mem_union_right _ hx.1, Finset.mem_union_right _ hx.2⟩
      have he_in : e.1 ∈ (Multigraph.Subgraph.induced Q (stageVerts Q blue (W₁ ∪ W₂))).edges := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
        · rcases he_cr with ⟨ht, _⟩ | ⟨ht, _⟩
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_union_left _ ht⟩
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_union_right _ ht⟩
        · rcases he_cr with ⟨_, hh⟩ | ⟨_, hh⟩
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_union_right _ hh⟩
          · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_union_left _ hh⟩
      refine ⟨hL.1.mono (by rw [hunion]; exact Finset.subset_union_left), fun u hu v hv => ?_⟩
      change u ∈ stageVerts Q blue (W₁ ∪ W₂) at hu
      change v ∈ stageVerts Q blue (W₁ ∪ W₂) at hv
      rw [hunion] at hu hv
      have hwalkL : ∀ a ∈ stageVerts Q blue W₁, ∀ b ∈ stageVerts Q blue W₁,
          Relation.ReflTransGen (Multigraph.Subgraph.induced Q (stageVerts Q blue (W₁ ∪ W₂))).Adj a b :=
        fun a ha b hb => reflTransGen_mono (fun _ _ ⟨x, hx, hadj⟩ => ⟨x, hsubL hx, hadj⟩) (hL.2 a ha b hb)
      have hwalkR : ∀ a ∈ stageVerts Q blue W₂, ∀ b ∈ stageVerts Q blue W₂,
          Relation.ReflTransGen (Multigraph.Subgraph.induced Q (stageVerts Q blue (W₁ ∪ W₂))).Adj a b :=
        fun a ha b hb => reflTransGen_mono (fun _ _ ⟨x, hx, hadj⟩ => ⟨x, hsubR hx, hadj⟩) (hR.2 a ha b hb)
      rcases Finset.mem_union.mp hu with hu1 | hu2 <;> rcases Finset.mem_union.mp hv with hv1 | hv2
      · exact hwalkL u hu1 v hv1
      · rcases he_cr with ⟨ht, hh⟩ | ⟨ht, hh⟩
        · exact Relation.ReflTransGen.trans
            (hwalkL u hu1 (Q.tail e.1) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩))
            (Relation.ReflTransGen.head ⟨e.1, he_in, Or.inl ⟨rfl, rfl⟩⟩
              (hwalkR (Q.head e.1) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩) v hv2))
        · exact Relation.ReflTransGen.trans
            (hwalkL u hu1 (Q.head e.1) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩))
            (Relation.ReflTransGen.head ⟨e.1, he_in, Or.inr ⟨rfl, rfl⟩⟩
              (hwalkR (Q.tail e.1) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩) v hv2))
      · rcases he_cr with ⟨ht, hh⟩ | ⟨ht, hh⟩
        · exact Relation.ReflTransGen.trans
            (hwalkR u hu2 (Q.head e.1) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩))
            (Relation.ReflTransGen.head ⟨e.1, he_in, Or.inr ⟨rfl, rfl⟩⟩
              (hwalkL (Q.tail e.1) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩) v hv1))
        · exact Relation.ReflTransGen.trans
            (hwalkR u hu2 (Q.tail e.1) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩))
            (Relation.ReflTransGen.head ⟨e.1, he_in, Or.inl ⟨rfl, rfl⟩⟩
              (hwalkL (Q.head e.1) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩) v hv1))
      · exact hwalkR u hu2 v hv2

private lemma twoConstr_all_stages_connected
    (Q : Multigraph V E) (blue : Finset E) [DecidableEq (Quotient (redSetoid Q blue))] :
    ∀ {W₀ : Finset (Quotient (redSetoid Q blue))} {F₀ : Finset {e : E // e ∈ blue}}
      (tc : TwoConstruction (redQuotient Q blue) W₀ F₀),
      ∀ s ∈ tc.stages, (Multigraph.Subgraph.induced Q (stageVerts Q blue s.1)).Connected
  | _, _, .single c => fun s hs => by
      simp only [TwoConstruction.stages, List.mem_singleton] at hs
      subst hs; exact twoConstr_stageVerts_connected Q blue (.single c)
  | _, _, .join left right e f hdisjW hdisjF he_ne_f he1 he2 hf1 hf2 he_cr hf_cr => fun s hs => by
      simp only [TwoConstruction.stages, List.mem_cons, List.mem_append] at hs
      rcases hs with rfl | hs | hs
      · exact twoConstr_stageVerts_connected Q blue (.join left right e f hdisjW hdisjF he_ne_f he1 he2 hf1 hf2 he_cr hf_cr)
      · exact twoConstr_all_stages_connected Q blue left s hs
      · exact twoConstr_all_stages_connected Q blue right s hs

/-- **Lemma 3.9(b)–(d) (Stages and stage graphs of a `2`-construction).** -/
theorem lem_3_9_bcd
    (Q : Multigraph V E) (_hTC : Q.IsTruncatedCubic3EC)
    (wc : WellColouring Q) :
    let M := redQuotient Q wc.blue
    let stg := wc.twoConstr.stages
    let nds := wc.twoConstr.nodes
    (∀ s₁ ∈ stg, ∀ s₂ ∈ stg, Disjoint s₁.1 s₂.1 ∨ s₁.1 ⊆ s₂.1 ∨ s₂.1 ⊆ s₁.1) ∧
    (∀ e : {e : E // e ∈ wc.blue},
      ∃! idx : Fin nds.length,
        let nd := nds[idx.1]'idx.2
        e = nd.2.2.1 ∨ e = nd.2.2.2) ∧
    (∀ s ∈ stg, ∀ e : {e : E // e ∈ wc.blue},
      (M.tail e ∈ s.1 ∧ M.head e ∈ s.1) ↔ e ∈ s.2) ∧
    (∀ s ∈ stg, ∀ e : {e : E // e ∈ wc.blue},
      e ∈ s.2 ↔ ∃ nd ∈ nds, (nd.1 ∪ nd.2.1) ⊆ s.1 ∧ (e = nd.2.2.1 ∨ e = nd.2.2.2)) ∧
    (∀ s ∈ stg,
      let VU := stageVerts Q wc.blue s.1
      let QU := Multigraph.Subgraph.induced Q VU
      QU.Connected ∧
      ∀ e : E, e ∈ QU.edges ↔
        ((e ∉ wc.blue ∧ Q.tail e ∈ VU ∧ Q.head e ∈ VU) ∨
         ∃ he : e ∈ wc.blue, (⟨e, he⟩ : {e : E // e ∈ wc.blue}) ∈ s.2)) ∧
    (∀ nd ∈ nds,
      let VU' := stageVerts Q wc.blue nd.1
      let VU'' := stageVerts Q wc.blue nd.2.1
      let VU := stageVerts Q wc.blue (nd.1 ∪ nd.2.1)
      VU = VU' ∪ VU'' ∧ Disjoint VU' VU'' ∧
      ((Q.tail nd.2.2.1.1 ∈ VU' ∧ Q.head nd.2.2.1.1 ∈ VU'') ∨
       (Q.tail nd.2.2.1.1 ∈ VU'' ∧ Q.head nd.2.2.1.1 ∈ VU')) ∧
      ((Q.tail nd.2.2.2.1 ∈ VU' ∧ Q.head nd.2.2.2.1 ∈ VU'') ∨
       (Q.tail nd.2.2.2.1 ∈ VU'' ∧ Q.head nd.2.2.2.1 ∈ VU')) ∧
      (Multigraph.Subgraph.induced Q VU).edges =
        (Multigraph.Subgraph.induced Q VU').edges ∪
        (Multigraph.Subgraph.induced Q VU'').edges ∪ {nd.2.2.1.1, nd.2.2.2.1}) := by
  dsimp only
  have hb1 := twoConstr_stages_disj_or_nested wc.twoConstr
  have hb2 : ∀ e : {e : E // e ∈ wc.blue},
      ∃! idx : Fin wc.twoConstr.nodes.length,
        let nd := wc.twoConstr.nodes[idx.1]'idx.2
        e = nd.2.2.1 ∨ e = nd.2.2.2 :=
    fun e => twoConstr_edge_unique_node wc.twoConstr e (Finset.mem_univ e)
  have hb3a : ∀ s ∈ wc.twoConstr.stages, ∀ e : {e : E // e ∈ wc.blue},
      ((redQuotient Q wc.blue).tail e ∈ s.1 ∧ (redQuotient Q wc.blue).head e ∈ s.1) ↔ e ∈ s.2 :=
    fun s hs e => twoConstr_stage_induced wc.twoConstr s hs e (Finset.mem_univ e)
  have hb3b : ∀ s ∈ wc.twoConstr.stages, ∀ e : {e : E // e ∈ wc.blue},
      e ∈ s.2 ↔ ∃ nd ∈ wc.twoConstr.nodes, (nd.1 ∪ nd.2.1) ⊆ s.1 ∧ (e = nd.2.2.1 ∨ e = nd.2.2.2) :=
    fun s hs e => twoConstr_stage_edges_iff_nodes wc.twoConstr s hs e (Finset.mem_univ e)
  refine ⟨hb1, hb2, hb3a, hb3b, ?_, ?_⟩
  · -- (c)
    intro s hs
    refine ⟨twoConstr_all_stages_connected Q wc.blue wc.twoConstr s hs, fun e => ?_⟩
    simp only [Multigraph.Subgraph.induced, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hbe : e ∈ wc.blue
    · constructor
      · rintro ⟨ht, hh⟩
        right; refine ⟨hbe, (hb3a s hs ⟨e, hbe⟩).mp ⟨(Finset.mem_filter.mp ht).2, (Finset.mem_filter.mp hh).2⟩⟩
      · rintro (⟨hnb, _⟩ | ⟨_, hmem⟩)
        · exact absurd hbe hnb
        · obtain ⟨ht, hh⟩ := (hb3a s hs ⟨e, hbe⟩).mpr hmem
          exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩⟩
    · constructor
      · rintro ⟨ht, hh⟩; left; exact ⟨hbe, ht, hh⟩
      · rintro (⟨_, ht, hh⟩ | ⟨hbe', _⟩)
        · exact ⟨ht, hh⟩
        · exact absurd hbe' hbe
  · -- (d)
    intro nd hnd
    have hinfo := twoConstr_nodes_sub wc.twoConstr nd hnd
    have hunion : stageVerts Q wc.blue (nd.1 ∪ nd.2.1) =
        stageVerts Q wc.blue nd.1 ∪ stageVerts Q wc.blue nd.2.1 := by
      ext v; simp [stageVerts]
    have hdisjV : Disjoint (stageVerts Q wc.blue nd.1) (stageVerts Q wc.blue nd.2.1) := by
      rw [Finset.disjoint_left]; intro v h1 h2
      exact Finset.disjoint_left.mp hinfo.2.2.2.1 (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2
    have hcr1 : (Q.tail nd.2.2.1.1 ∈ stageVerts Q wc.blue nd.1 ∧ Q.head nd.2.2.1.1 ∈ stageVerts Q wc.blue nd.2.1) ∨
        (Q.tail nd.2.2.1.1 ∈ stageVerts Q wc.blue nd.2.1 ∧ Q.head nd.2.2.1.1 ∈ stageVerts Q wc.blue nd.1) := by
      rcases hinfo.2.2.2.2.2.1 with ⟨ht, hh⟩ | ⟨ht, hh⟩
      · left; exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩⟩
      · right; exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩⟩
    have hcr2 : (Q.tail nd.2.2.2.1 ∈ stageVerts Q wc.blue nd.1 ∧ Q.head nd.2.2.2.1 ∈ stageVerts Q wc.blue nd.2.1) ∨
        (Q.tail nd.2.2.2.1 ∈ stageVerts Q wc.blue nd.2.1 ∧ Q.head nd.2.2.2.1 ∈ stageVerts Q wc.blue nd.1) := by
      rcases hinfo.2.2.2.2.2.2 with ⟨ht, hh⟩ | ⟨ht, hh⟩
      · left; exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩⟩
      · right; exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩⟩
    -- Helper: any edge crossing between `nd.1` and `nd.2.1` in `Q/red` is `nd.2.2.1` or `nd.2.2.2`
    have hcross_only : ∀ x : {e : E // e ∈ wc.blue},
        (((redQuotient Q wc.blue).tail x ∈ nd.1 ∧ (redQuotient Q wc.blue).head x ∈ nd.2.1) ∨
         ((redQuotient Q wc.blue).tail x ∈ nd.2.1 ∧ (redQuotient Q wc.blue).head x ∈ nd.1)) →
        x = nd.2.2.1 ∨ x = nd.2.2.2 := by
      -- Prove via `postNodes_props`: every node in `tc.nodes` appears in `postNodes tc`!
      have hmem_post : ∀ {W₀ : Finset (Quotient (redSetoid Q wc.blue))} {F₀ : Finset {e : E // e ∈ wc.blue}}
          (tc : TwoConstruction (redQuotient Q wc.blue) W₀ F₀),
          ∀ nd' ∈ tc.nodes, nd' ∈ postNodes tc := by
        intro W₀ F₀ tc
        induction tc with
        | single _ => intro _ h; simp [TwoConstruction.nodes] at h
        | join left right _ _ _ _ _ _ _ _ _ _ _ ihL ihR =>
          intro nd' hnd'
          simp only [TwoConstruction.nodes, List.mem_cons, List.mem_append] at hnd'
          simp only [postNodes, List.mem_append, List.mem_singleton]
          rcases hnd' with rfl | h | h
          · exact Or.inr rfl
          · exact Or.inl (Or.inl (ihL nd' h))
          · exact Or.inl (Or.inr (ihR nd' h))
      obtain ⟨idx, hidx, hnd_eq⟩ := List.getElem_of_mem (hmem_post wc.twoConstr nd hnd)
      have hp := (postNodes_props wc.twoConstr).2.2 ⟨idx, hidx⟩
      dsimp only at hp
      rw [hnd_eq] at hp
      intro x hxcr
      exact hp.2.2.2.2.2.2.2.2.2.1 x (Finset.mem_univ x) hxcr
    refine ⟨hunion, hdisjV, hcr1, hcr2, ?_⟩
    ext e
    simp only [Multigraph.Subgraph.induced, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, hunion]
    constructor
    · rintro ⟨ht, hh⟩
      rcases ht with ht1 | ht2 <;> rcases hh with hh1 | hh2
      · left; left; exact ⟨ht1, hh1⟩
      · right
        by_cases hbe : e ∈ wc.blue
        · have hx := hcross_only ⟨e, hbe⟩ (Or.inl ⟨(Finset.mem_filter.mp ht1).2, (Finset.mem_filter.mp hh2).2⟩)
          rcases hx with h | h <;> [left; right] <;> exact congrArg Subtype.val h
        · exfalso
          have hsame : Quotient.mk (redSetoid Q wc.blue) (Q.tail e) = Quotient.mk (redSetoid Q wc.blue) (Q.head e) :=
            Quotient.sound (Relation.ReflTransGen.single ⟨e, hbe, Or.inl ⟨rfl, rfl⟩⟩)
          exact Finset.disjoint_left.mp hinfo.2.2.2.1 (Finset.mem_filter.mp ht1).2
            (hsame ▸ (Finset.mem_filter.mp hh2).2)
      · right
        by_cases hbe : e ∈ wc.blue
        · have hx := hcross_only ⟨e, hbe⟩ (Or.inr ⟨(Finset.mem_filter.mp ht2).2, (Finset.mem_filter.mp hh1).2⟩)
          rcases hx with h | h <;> [left; right] <;> exact congrArg Subtype.val h
        · exfalso
          have hsame : Quotient.mk (redSetoid Q wc.blue) (Q.tail e) = Quotient.mk (redSetoid Q wc.blue) (Q.head e) :=
            Quotient.sound (Relation.ReflTransGen.single ⟨e, hbe, Or.inl ⟨rfl, rfl⟩⟩)
          exact Finset.disjoint_left.mp hinfo.2.2.2.1 (Finset.mem_filter.mp hh1).2
            (hsame.symm ▸ (Finset.mem_filter.mp ht2).2)
      · left; right; exact ⟨ht2, hh2⟩
    · rintro ((⟨ht1, hh1⟩ | ⟨ht2, hh2⟩) | (rfl | rfl))
      · exact ⟨Or.inl ht1, Or.inl hh1⟩
      · exact ⟨Or.inr ht2, Or.inr hh2⟩
      · rcases hcr1 with ⟨ht, hh⟩ | ⟨ht, hh⟩
        · exact ⟨Or.inl ht, Or.inr hh⟩
        · exact ⟨Or.inr ht, Or.inl hh⟩
      · rcases hcr2 with ⟨ht, hh⟩ | ⟨ht, hh⟩
        · exact ⟨Or.inl ht, Or.inr hh⟩
        · exact ⟨Or.inr ht, Or.inl hh⟩

end Lemma39

section FrameExistence

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

private lemma flatMap_index_bij {α β : Type} [DecidableEq α] (g : α → List β) :
    ∀ (L : List α), L.Nodup →
      ∃ (toGlobal : ∀ b ∈ L, Fin (g b).length → Fin (L.flatMap g).length),
        (∀ b hb k, (L.flatMap g)[(toGlobal b hb k).1]'(toGlobal b hb k).2 = (g b)[k.1]'k.2) ∧
        (∀ b hb (k₁ k₂ : Fin (g b).length), k₁ < k₂ → toGlobal b hb k₁ < toGlobal b hb k₂) ∧
        (∀ i : Fin (L.flatMap g).length, ∃ b hb k, toGlobal b hb k = i) ∧
        (∀ b₁ hb₁ k₁ b₂ hb₂ k₂, toGlobal b₁ hb₁ k₁ = toGlobal b₂ hb₂ k₂ → b₁ = b₂ ∧ k₁.1 = k₂.1) := by
  intro L
  induction L with
  | nil =>
    intro _
    refine ⟨fun _ h => absurd h (by simp), fun _ h => absurd h (by simp),
      fun _ h => absurd h (by simp), fun i => absurd i.2 (by simp),
      fun _ h => absurd h (by simp)⟩
  | cons a tl ih =>
    intro hnod
    obtain ⟨ha_not, htl_nod⟩ := List.nodup_cons.mp hnod
    obtain ⟨toG, hget, hmono, hsurj, hinj⟩ := ih htl_nod
    let f : ∀ b ∈ a :: tl, Fin (g b).length → Fin ((a :: tl).flatMap g).length :=
      fun b hb k =>
        if hba : b = a then
          ⟨k.1, by subst hba; simp only [List.flatMap_cons, List.length_append]; have := k.2; omega⟩
        else
          ⟨(g a).length + (toG b ((List.mem_cons.mp hb).resolve_left hba) k).1,
           by simp only [List.flatMap_cons, List.length_append]
              have := (toG b ((List.mem_cons.mp hb).resolve_left hba) k).2; omega⟩
    refine ⟨f, ?_, ?_, ?_, ?_⟩
    · intro b hb k
      dsimp only [f]
      split_ifs with hba
      · subst hba; simp [List.getElem_append_left k.2]
      · simp [List.getElem_append_right (Nat.le_add_right _ _), hget]
    · intro b hb k₁ k₂ hlt
      dsimp only [f]
      split_ifs with hba
      · exact hlt
      · show (g a).length + _ < (g a).length + _
        have := hmono b ((List.mem_cons.mp hb).resolve_left hba) k₁ k₂ hlt; omega
    · intro i
      by_cases hlt : i.1 < (g a).length
      · refine ⟨a, List.mem_cons_self, ⟨i.1, hlt⟩, ?_⟩
        apply Fin.ext; simp [f]
      · have hi' : i.1 - (g a).length < (tl.flatMap g).length := by
          have := i.2; simp only [List.flatMap_cons, List.length_append] at this; omega
        obtain ⟨b, hb, k, hbk⟩ := hsurj ⟨i.1 - (g a).length, hi'⟩
        have hba : b ≠ a := fun h => ha_not (h ▸ hb)
        refine ⟨b, List.mem_cons_of_mem a hb, k, ?_⟩
        apply Fin.ext; simp only [f, hba, ↓reduceDIte]
        have := congrArg Fin.val hbk; dsimp only at this; omega
    · intro b₁ hb₁ k₁ b₂ hb₂ k₂ heq
      have hval := congrArg Fin.val heq
      by_cases h1 : b₁ = a <;> by_cases h2 : b₂ = a
      · simp only [f, h1, h2, ↓reduceDIte] at hval
        exact ⟨h1.trans h2.symm, hval⟩
      · simp only [f, h1, h2, ↓reduceDIte] at hval
        subst h1; have := k₁.2; omega
      · simp only [f, h1, h2, ↓reduceDIte] at hval
        subst h2; have := k₂.2; omega
      · simp only [f, h1, h2, ↓reduceDIte] at hval
        have htl1 : b₁ ∈ tl := (List.mem_cons.mp hb₁).resolve_left h1
        have htl2 : b₂ ∈ tl := (List.mem_cons.mp hb₂).resolve_left h2
        have hveq : (toG b₁ htl1 k₁).1 = (toG b₂ htl2 k₂).1 := by omega
        exact hinj b₁ htl1 k₁ b₂ htl2 k₂ (Fin.ext hveq)

private lemma frame_red_forest
    {G : Multigraph V E} {H : G.Subgraph} (sub : SubdivisionData G H)
    (aux : AuxGraphData G H sub)
    (wc : ∀ b : Fin aux.numBlocks,
      WellColouring (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).toMultigraph)
    (blue : Finset aux.EQ)
    (hblue_iff : ∀ (b : Fin aux.numBlocks)
      (e : {e : aux.EQ // e ∈ (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).edges}),
      e ∈ (wc b).blue ↔ e.1 ∈ blue) :
    (Multigraph.Subgraph.ofEdges aux.Q Finset.univ (Finset.univ \ blue)
      (fun _ => Finset.mem_univ _) (fun _ => Finset.mem_univ _)).IsForest := by
  let Vb (b : Fin aux.numBlocks) : Finset aux.VQ := Finset.univ.filter (fun v => aux.comp v = b)
  let Qb (b : Fin aux.numBlocks) := (Multigraph.Subgraph.induced aux.Q (Vb b)).toMultigraph
  have hedge_in_Qb : ∀ (b : Fin aux.numBlocks) (e : aux.EQ),
      aux.comp (aux.Q.tail e) = b ↔ e ∈ (Multigraph.Subgraph.induced aux.Q (Vb b)).edges := by
    intro b e
    simp only [Multigraph.Subgraph.induced, Vb, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => ⟨h, (aux.edge_same_comp e).symm.trans h⟩, fun h => h.1⟩
  intro C hCle hCcyc
  obtain ⟨v₀, hv₀⟩ := hCcyc.1.1
  let b := aux.comp v₀
  have hC_in_b : ∀ u ∈ C.verts, aux.comp u = b := by
    intro u hu
    have hw := hCcyc.1.2 v₀ hv₀ u hu
    clear hu
    induction hw with
    | refl => rfl
    | tail _ hstep ih =>
      rcases hstep with ⟨e, _, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · exact (aux.edge_same_comp e).symm.trans ih
      · exact (aux.edge_same_comp e).trans ih
  let Cb : (Qb b).Subgraph :=
    { verts := Finset.univ.filter (fun u => u.1 ∈ C.verts)
      edges := Finset.univ.filter (fun e => e.1 ∈ C.edges)
      tail_mem := fun {e} he => Finset.mem_filter.mpr ⟨Finset.mem_univ _, C.tail_mem (Finset.mem_filter.mp he).2⟩
      head_mem := fun {e} he => Finset.mem_filter.mpr ⟨Finset.mem_univ _, C.head_mem (Finset.mem_filter.mp he).2⟩ }
  have hCb_le : Cb ≤ Multigraph.Subgraph.ofEdges (Qb b) Finset.univ (Finset.univ \ (wc b).blue)
      (fun _ => Finset.mem_univ _) (fun _ => Finset.mem_univ _) := by
    refine ⟨Finset.subset_univ _, fun e he => ?_⟩
    have heC : e.1 ∈ C.edges := (Finset.mem_filter.mp he).2
    have hnb : e.1 ∉ blue := (Finset.mem_sdiff.mp (hCle.2 heC)).2
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hb => hnb ((hblue_iff b e).mp hb)⟩
  have hCb_cyc : Cb.IsCycle := by
    refine ⟨⟨⟨⟨v₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv₀⟩⟩, fun u hu v hv => ?_⟩, fun u hu => ?_⟩
    · have hw := hCcyc.1.2 u.1 (Finset.mem_filter.mp hu).2 v.1 (Finset.mem_filter.mp hv).2
      have hlift : ∀ {x y : aux.VQ} (hx : x ∈ C.verts),
          Relation.ReflTransGen C.Adj x y →
          ∃ hy : y ∈ C.verts,
            Relation.ReflTransGen Cb.Adj
              ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hC_in_b x hx⟩⟩
              ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hC_in_b y hy⟩⟩ := by
        intro x y hx hxy
        induction hxy with
        | refl => exact ⟨hx, Relation.ReflTransGen.refl⟩
        | @tail w z _ hstep ih =>
          rcases ih with ⟨hwC, hwalk⟩
          rcases hstep with ⟨e, heC, hadj⟩
          have hzC : z ∈ C.verts := by
            rcases hadj with ⟨_, rfl⟩ | ⟨rfl, _⟩
            · exact C.head_mem heC
            · exact C.tail_mem heC
          have he_b : e ∈ (Multigraph.Subgraph.induced aux.Q (Vb b)).edges :=
            (hedge_in_Qb b e).mp (hC_in_b _ (C.tail_mem heC))
          refine ⟨hzC, Relation.ReflTransGen.tail hwalk
            ⟨⟨e, he_b⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, heC⟩, ?_⟩⟩
          rcases hadj with ⟨ht, hh⟩ | ⟨ht, hh⟩
          · exact Or.inl ⟨Subtype.ext ht, Subtype.ext hh⟩
          · exact Or.inr ⟨Subtype.ext ht, Subtype.ext hh⟩
      exact (hlift (Finset.mem_filter.mp hu).2 hw).2
    · have hdeg := hCcyc.2 u.1 (Finset.mem_filter.mp hu).2
      unfold Multigraph.Subgraph.deg at hdeg ⊢
      have ht_eq : (Cb.edges.filter (fun e => (Qb b).tail e = u)).card =
          (C.edges.filter (fun e => aux.Q.tail e = u.1)).card := by
        refine Finset.card_bij (fun e _ => e.1)
          (fun e he => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2,
            congrArg Subtype.val (Finset.mem_filter.mp he).2⟩)
          (fun _ _ _ _ h => Subtype.ext h)
          (fun e he => by
            have heC := (Finset.mem_filter.mp he).1
            have he_b : e ∈ (Multigraph.Subgraph.induced aux.Q (Vb b)).edges :=
              (hedge_in_Qb b e).mp (hC_in_b _ (C.tail_mem heC))
            exact ⟨⟨e, he_b⟩, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, heC⟩,
              Subtype.ext (Finset.mem_filter.mp he).2⟩, rfl⟩)
      have hh_eq : (Cb.edges.filter (fun e => (Qb b).head e = u)).card =
          (C.edges.filter (fun e => aux.Q.head e = u.1)).card := by
        refine Finset.card_bij (fun e _ => e.1)
          (fun e he => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2,
            congrArg Subtype.val (Finset.mem_filter.mp he).2⟩)
          (fun _ _ _ _ h => Subtype.ext h)
          (fun e he => by
            have heC := (Finset.mem_filter.mp he).1
            have he_b : e ∈ (Multigraph.Subgraph.induced aux.Q (Vb b)).edges :=
              (hedge_in_Qb b e).mp (hC_in_b _ (C.tail_mem heC))
            exact ⟨⟨e, he_b⟩, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, heC⟩,
              Subtype.ext (Finset.mem_filter.mp he).2⟩, rfl⟩)
      rw [ht_eq, hh_eq]; exact hdeg
  exact (lem_3_9 (Qb b) (aux.comp_tc3ec b) (wc b)).2.2.2.1 Cb hCb_le hCb_cyc

private lemma postNodes_operands_connected
    {W F : Type} [Fintype W] [Fintype F] [DecidableEq W] [DecidableEq F]
    (Q : Multigraph W F) (blue : Finset F) [DecidableEq (Quotient (redSetoid Q blue))] :
    ∀ {W₀ : Finset (Quotient (redSetoid Q blue))} {F₀ : Finset {e : F // e ∈ blue}}
      (tc : TwoConstruction (redQuotient Q blue) W₀ F₀),
      ∀ nd ∈ postNodes tc,
        (Multigraph.Subgraph.induced Q (stageVerts Q blue nd.1)).Connected ∧
        (Multigraph.Subgraph.induced Q (stageVerts Q blue nd.2.1)).Connected
  | _, _, .single _ => fun _ h => by simp [postNodes] at h
  | _, _, .join left right _ _ _ _ _ _ _ _ _ _ _ => fun nd hnd => by
      simp only [postNodes, List.mem_append, List.mem_singleton] at hnd
      rcases hnd with (h | h) | rfl
      · exact postNodes_operands_connected Q blue left nd h
      · exact postNodes_operands_connected Q blue right nd h
      · exact ⟨twoConstr_stageVerts_connected Q blue left,
               twoConstr_stageVerts_connected Q blue right⟩

private def frameLiftW
    {G : Multigraph V E} {H : G.Subgraph} {sub : SubdivisionData G H}
    (aux : AuxGraphData G H sub)
    (blueB : ∀ b : Fin aux.numBlocks,
      Finset {e : aux.EQ // e ∈ (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).edges})
    (b : Fin aux.numBlocks)
    [DecidableEq (Quotient (redSetoid
      (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).toMultigraph (blueB b)))]
    (W : Finset (Quotient (redSetoid
      (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).toMultigraph (blueB b)))) :
    Finset aux.VQ :=
  (stageVerts (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).toMultigraph
    (blueB b) W).image Subtype.val

private lemma frame_edge_in_Qb
    {G : Multigraph V E} {H : G.Subgraph} {sub : SubdivisionData G H}
    (aux : AuxGraphData G H sub) (b : Fin aux.numBlocks) (e : aux.EQ) :
    aux.comp (aux.Q.tail e) = b ↔
      e ∈ (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).edges := by
  simp only [Multigraph.Subgraph.induced, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => ⟨h, (aux.edge_same_comp e).symm.trans h⟩, fun h => h.1⟩

private lemma frame_redAdj_lift
    {G : Multigraph V E} {H : G.Subgraph} {sub : SubdivisionData G H}
    (aux : AuxGraphData G H sub)
    (blueB : ∀ b : Fin aux.numBlocks,
      Finset {e : aux.EQ // e ∈ (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).edges})
    (blue : Finset aux.EQ)
    (hblue_iff : ∀ (b : Fin aux.numBlocks)
      (e : {e : aux.EQ // e ∈ (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).edges}),
      e ∈ blueB b ↔ e.1 ∈ blue)
    (b : Fin aux.numBlocks)
    (u v : {x : aux.VQ // x ∈ (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).verts}) :
    redAdj (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).toMultigraph (blueB b) u v ↔
      redAdj aux.Q blue u.1 v.1 := by
  constructor
  · rintro ⟨e, hnb, hadj⟩
    refine ⟨e.1, fun hb => hnb ((hblue_iff b e).mpr hb), ?_⟩
    rcases hadj with ⟨ht, hh⟩ | ⟨ht, hh⟩
    · exact Or.inl ⟨congrArg Subtype.val ht, congrArg Subtype.val hh⟩
    · exact Or.inr ⟨congrArg Subtype.val ht, congrArg Subtype.val hh⟩
  · rintro ⟨e, hnb, hadj⟩
    have hu_b : aux.comp u.1 = b := (Finset.mem_filter.mp u.2).2
    have he_b : aux.comp (aux.Q.tail e) = b := by
      rcases hadj with ⟨ht, _⟩ | ⟨_, hh⟩
      · exact ht.symm ▸ hu_b
      · exact (aux.edge_same_comp e).trans (hh.symm ▸ hu_b)
    have he_mem := (frame_edge_in_Qb aux b e).mp he_b
    refine ⟨⟨e, he_mem⟩, fun hb => hnb ((hblue_iff b ⟨e, he_mem⟩).mp hb), ?_⟩
    rcases hadj with ⟨ht, hh⟩ | ⟨ht, hh⟩
    · exact Or.inl ⟨Subtype.ext ht, Subtype.ext hh⟩
    · exact Or.inr ⟨Subtype.ext ht, Subtype.ext hh⟩

private lemma frame_redRel_lift
    {G : Multigraph V E} {H : G.Subgraph} {sub : SubdivisionData G H}
    (aux : AuxGraphData G H sub)
    (blueB : ∀ b : Fin aux.numBlocks,
      Finset {e : aux.EQ // e ∈ (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).edges})
    (blue : Finset aux.EQ)
    (hblue_iff : ∀ (b : Fin aux.numBlocks)
      (e : {e : aux.EQ // e ∈ (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).edges}),
      e ∈ blueB b ↔ e.1 ∈ blue)
    (b : Fin aux.numBlocks)
    (u v : {x : aux.VQ // x ∈ (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).verts}) :
    Relation.ReflTransGen
        (redAdj (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).toMultigraph (blueB b)) u v ↔
      Relation.ReflTransGen (redAdj aux.Q blue) u.1 v.1 := by
  constructor
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hstep ih => exact Relation.ReflTransGen.tail ih ((frame_redAdj_lift aux blueB blue hblue_iff b _ _).mp hstep)
  · intro h
    have hlift_gen : ∀ {x y : aux.VQ}
        (hx : x ∈ (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).verts),
        Relation.ReflTransGen (redAdj aux.Q blue) x y →
        ∃ hy : y ∈ (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).verts,
          Relation.ReflTransGen
            (redAdj (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).toMultigraph (blueB b))
            ⟨x, hx⟩ ⟨y, hy⟩ := by
      intro x y hx hxy
      induction hxy with
      | refl => exact ⟨hx, Relation.ReflTransGen.refl⟩
      | @tail w z _ hstep ih =>
        rcases ih with ⟨hw, hwalk⟩
        have hw_b : aux.comp w = b := (Finset.mem_filter.mp hw).2
        rcases hstep with ⟨e, hnb, hadj⟩
        have hz_b : aux.comp z = b := by
          rcases hadj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact (aux.edge_same_comp e).symm.trans hw_b
          · exact (aux.edge_same_comp e).trans hw_b
        have hz : z ∈ (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).verts :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz_b⟩
        exact ⟨hz, Relation.ReflTransGen.tail hwalk
          ((frame_redAdj_lift aux blueB blue hblue_iff b ⟨w, hw⟩ ⟨z, hz⟩).mpr ⟨e, hnb, hadj⟩)⟩
    exact (hlift_gen u.2 h).2

private lemma frameLiftW_sub
    {G : Multigraph V E} {H : G.Subgraph} {sub : SubdivisionData G H}
    (aux : AuxGraphData G H sub)
    (blueB : ∀ b : Fin aux.numBlocks,
      Finset {e : aux.EQ // e ∈ (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).edges})
    (b : Fin aux.numBlocks)
    [DecidableEq (Quotient (redSetoid
      (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).toMultigraph (blueB b)))]
    (W : Finset (Quotient (redSetoid
      (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).toMultigraph (blueB b)))) :
    frameLiftW aux blueB b W ⊆ Finset.univ.filter (fun v => aux.comp v = b) := fun _ hv => by
  dsimp only [frameLiftW] at hv
  rcases Finset.mem_image.mp hv with ⟨u, _, rfl⟩; exact u.2

private lemma frameLiftW_mem
    {G : Multigraph V E} {H : G.Subgraph} {sub : SubdivisionData G H}
    (aux : AuxGraphData G H sub)
    (blueB : ∀ b : Fin aux.numBlocks,
      Finset {e : aux.EQ // e ∈ (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).edges})
    (b : Fin aux.numBlocks)
    [DecidableEq (Quotient (redSetoid
      (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).toMultigraph (blueB b)))]
    (W : Finset (Quotient (redSetoid
      (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).toMultigraph (blueB b))))
    (u : {x : aux.VQ // x ∈ (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).verts}) :
    u.1 ∈ frameLiftW aux blueB b W ↔
      Quotient.mk (redSetoid (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).toMultigraph (blueB b)) u ∈ W := by
  simp only [frameLiftW, stageVerts, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨w, hw, hweq⟩
    have : w = u := Subtype.ext hweq
    exact this ▸ hw
  · intro h; exact ⟨u, h, rfl⟩

private lemma frameLiftW_union
    {G : Multigraph V E} {H : G.Subgraph} {sub : SubdivisionData G H}
    (aux : AuxGraphData G H sub)
    (blueB : ∀ b : Fin aux.numBlocks,
      Finset {e : aux.EQ // e ∈ (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).edges})
    (b : Fin aux.numBlocks)
    [DecidableEq (Quotient (redSetoid
      (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).toMultigraph (blueB b)))]
    (W₁ W₂ : Finset (Quotient (redSetoid
      (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).toMultigraph (blueB b)))) :
    frameLiftW aux blueB b (W₁ ∪ W₂) = frameLiftW aux blueB b W₁ ∪ frameLiftW aux blueB b W₂ := by
  ext v
  simp only [frameLiftW, stageVerts, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨u, h1 | h2, rfl⟩
    · exact Or.inl ⟨u, h1, rfl⟩
    · exact Or.inr ⟨u, h2, rfl⟩
  · rintro (⟨u, h1, rfl⟩ | ⟨u, h2, rfl⟩)
    · exact ⟨u, Or.inl h1, rfl⟩
    · exact ⟨u, Or.inr h2, rfl⟩

private lemma frameLiftW_disj
    {G : Multigraph V E} {H : G.Subgraph} {sub : SubdivisionData G H}
    (aux : AuxGraphData G H sub)
    (blueB : ∀ b : Fin aux.numBlocks,
      Finset {e : aux.EQ // e ∈ (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).edges})
    (b : Fin aux.numBlocks)
    [DecidableEq (Quotient (redSetoid
      (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).toMultigraph (blueB b)))]
    (W₁ W₂ : Finset (Quotient (redSetoid
      (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).toMultigraph (blueB b))))
    (hd : Disjoint W₁ W₂) :
    Disjoint (frameLiftW aux blueB b W₁) (frameLiftW aux blueB b W₂) := by
  rw [Finset.disjoint_left]; intro v h1 h2
  dsimp only [frameLiftW] at h1 h2
  rcases Finset.mem_image.mp h1 with ⟨u₁, hu₁, rfl⟩
  rcases Finset.mem_image.mp h2 with ⟨u₂, hu₂, h12⟩
  have : u₂ = u₁ := Subtype.ext h12
  subst this
  exact Finset.disjoint_left.mp hd (Finset.mem_filter.mp hu₁).2 (Finset.mem_filter.mp hu₂).2

private lemma frameLiftW_ne
    {G : Multigraph V E} {H : G.Subgraph} {sub : SubdivisionData G H}
    (aux : AuxGraphData G H sub)
    (blueB : ∀ b : Fin aux.numBlocks,
      Finset {e : aux.EQ // e ∈ (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).edges})
    (b : Fin aux.numBlocks)
    [DecidableEq (Quotient (redSetoid
      (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).toMultigraph (blueB b)))]
    (W : Finset (Quotient (redSetoid
      (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).toMultigraph (blueB b))))
    (hne : W.Nonempty) :
    (frameLiftW aux blueB b W).Nonempty := by
  rcases hne with ⟨c, hc⟩
  obtain ⟨u, rfl⟩ := Quotient.exists_rep c
  exact ⟨u.1, (frameLiftW_mem aux blueB b W u).mpr hc⟩

private lemma frameLiftW_red_closed
    {G : Multigraph V E} {H : G.Subgraph} {sub : SubdivisionData G H}
    (aux : AuxGraphData G H sub)
    (blueB : ∀ b : Fin aux.numBlocks,
      Finset {e : aux.EQ // e ∈ (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).edges})
    (blue : Finset aux.EQ)
    (hblue_iff : ∀ (b : Fin aux.numBlocks)
      (e : {e : aux.EQ // e ∈ (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).edges}),
      e ∈ blueB b ↔ e.1 ∈ blue)
    (b : Fin aux.numBlocks)
    [DecidableEq (Quotient (redSetoid
      (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).toMultigraph (blueB b)))]
    (W : Finset (Quotient (redSetoid
      (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).toMultigraph (blueB b))))
    (e : aux.EQ) (hnb : e ∉ blue) :
    aux.Q.tail e ∈ frameLiftW aux blueB b W ↔ aux.Q.head e ∈ frameLiftW aux blueB b W := by
  let Qb := (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).toMultigraph
  constructor
  · intro ht
    have ht_b : aux.comp (aux.Q.tail e) = b := (Finset.mem_filter.mp (frameLiftW_sub aux blueB b W ht)).2
    have he_mem := (frame_edge_in_Qb aux b e).mp ht_b
    let ut : {x : aux.VQ // x ∈ (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).verts} :=
      ⟨aux.Q.tail e, (Finset.mem_filter.mp he_mem).2.1⟩
    let uh : {x : aux.VQ // x ∈ (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).verts} :=
      ⟨aux.Q.head e, (Finset.mem_filter.mp he_mem).2.2⟩
    have hsame : Quotient.mk (redSetoid Qb (blueB b)) ut = Quotient.mk (redSetoid Qb (blueB b)) uh :=
      Quotient.sound (Relation.ReflTransGen.single
        ((frame_redAdj_lift aux blueB blue hblue_iff b ut uh).mpr ⟨e, hnb, Or.inl ⟨rfl, rfl⟩⟩))
    exact (frameLiftW_mem aux blueB b W uh).mpr (hsame ▸ (frameLiftW_mem aux blueB b W ut).mp ht)
  · intro hh
    have hh_b : aux.comp (aux.Q.head e) = b := (Finset.mem_filter.mp (frameLiftW_sub aux blueB b W hh)).2
    have ht_b : aux.comp (aux.Q.tail e) = b := (aux.edge_same_comp e).trans hh_b
    have he_mem := (frame_edge_in_Qb aux b e).mp ht_b
    let ut : {x : aux.VQ // x ∈ (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).verts} :=
      ⟨aux.Q.tail e, (Finset.mem_filter.mp he_mem).2.1⟩
    let uh : {x : aux.VQ // x ∈ (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).verts} :=
      ⟨aux.Q.head e, (Finset.mem_filter.mp he_mem).2.2⟩
    have hsame : Quotient.mk (redSetoid Qb (blueB b)) ut = Quotient.mk (redSetoid Qb (blueB b)) uh :=
      Quotient.sound (Relation.ReflTransGen.single
        ((frame_redAdj_lift aux blueB blue hblue_iff b ut uh).mpr ⟨e, hnb, Or.inl ⟨rfl, rfl⟩⟩))
    exact (frameLiftW_mem aux blueB b W ut).mpr (hsame.symm ▸ (frameLiftW_mem aux blueB b W uh).mp hh)

private lemma frameLiftW_conn
    {G : Multigraph V E} {H : G.Subgraph} {sub : SubdivisionData G H}
    (aux : AuxGraphData G H sub)
    (blueB : ∀ b : Fin aux.numBlocks,
      Finset {e : aux.EQ // e ∈ (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).edges})
    (b : Fin aux.numBlocks)
    [DecidableEq (Quotient (redSetoid
      (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).toMultigraph (blueB b)))]
    (W : Finset (Quotient (redSetoid
      (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).toMultigraph (blueB b))))
    (hconn : (Multigraph.Subgraph.induced
      (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).toMultigraph
      (stageVerts (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).toMultigraph
        (blueB b) W)).Connected) :
    (Multigraph.Subgraph.induced aux.Q (frameLiftW aux blueB b W)).Connected := by
  let Qb := (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).toMultigraph
  refine ⟨?_, fun u hu v hv => ?_⟩
  · rcases hconn.1 with ⟨u, hu⟩
    exact ⟨u.1, Finset.mem_image.mpr ⟨u, hu, rfl⟩⟩
  · dsimp only [Multigraph.Subgraph.induced, frameLiftW] at hu hv
    rcases Finset.mem_image.mp hu with ⟨u', hu', rfl⟩
    rcases Finset.mem_image.mp hv with ⟨v', hv', rfl⟩
    have hw := hconn.2 u' hu' v' hv'
    clear hu hu' hv hv'
    induction hw with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hstep ih =>
      rcases hstep with ⟨e, he, hadj⟩
      have ht_in : Qb.tail e ∈ stageVerts Qb (blueB b) W := (Finset.mem_filter.mp he).2.1
      have hh_in : Qb.head e ∈ stageVerts Qb (blueB b) W := (Finset.mem_filter.mp he).2.2
      have he_ind : e.1 ∈ (Multigraph.Subgraph.induced aux.Q (frameLiftW aux blueB b W)).edges :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          Finset.mem_image.mpr ⟨Qb.tail e, ht_in, rfl⟩,
          Finset.mem_image.mpr ⟨Qb.head e, hh_in, rfl⟩⟩
      refine Relation.ReflTransGen.tail ih ⟨e.1, he_ind, ?_⟩
      rcases hadj with ⟨ht, hh⟩ | ⟨ht, hh⟩
      · exact Or.inl ⟨congrArg Subtype.val ht, congrArg Subtype.val hh⟩
      · exact Or.inr ⟨congrArg Subtype.val ht, congrArg Subtype.val hh⟩

private theorem frame_exists_core
    {G : Multigraph V E} {H : G.Subgraph} (sub : SubdivisionData G H)
    (aux : AuxGraphData G H sub)
    (blueB : ∀ b : Fin aux.numBlocks,
      Finset {e : aux.EQ // e ∈ (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).edges})
    [decEqQ : ∀ b : Fin aux.numBlocks, DecidableEq (Quotient (redSetoid
      (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).toMultigraph (blueB b)))]
    [fintypeQ : ∀ b : Fin aux.numBlocks, Fintype (Quotient (redSetoid
      (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).toMultigraph (blueB b)))]
    (blue : Finset aux.EQ)
    (hblue_iff : ∀ (b : Fin aux.numBlocks)
      (e : {e : aux.EQ // e ∈ (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).edges}),
      e ∈ blueB b ↔ e.1 ∈ blue)
    (hcomp_wc : ∀ b : Fin aux.numBlocks,
      ∃ wc : WellColouring (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).toMultigraph,
        ∀ e, e ∈ wc.blue ↔ e.1 ∈ blue)
    (hred_forest : (Multigraph.Subgraph.ofEdges aux.Q Finset.univ (Finset.univ \ blue)
      (fun _ => Finset.mem_univ _) (fun _ => Finset.mem_univ _)).IsForest)
    (pn : ∀ b : Fin aux.numBlocks,
      List (Finset (Quotient (redSetoid (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).toMultigraph (blueB b))) ×
            Finset (Quotient (redSetoid (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).toMultigraph (blueB b))) ×
            {e // e ∈ blueB b} × {e // e ∈ blueB b}))
    (hpn_uniq : ∀ b (x : {e // e ∈ blueB b}), ∃! idx : Fin (pn b).length,
      let nd := (pn b)[idx.1]'idx.2; x = nd.2.2.1 ∨ x = nd.2.2.2)
    (hpn_top : ∀ b,
      (∃ i : Fin (pn b).length, Finset.univ = ((pn b)[i.1]'i.2).1 ∪ ((pn b)[i.1]'i.2).2.1) ∨
      (Finset.univ : Finset (Quotient (redSetoid (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).toMultigraph (blueB b)))).card = 1)
    (hpn_nodes : ∀ b (i : Fin (pn b).length),
      let M := redQuotient (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).toMultigraph (blueB b)
      let nd := (pn b)[i.1]'i.2
      Disjoint nd.1 nd.2.1 ∧ nd.1.Nonempty ∧ nd.2.1.Nonempty ∧ nd.2.2.1 ≠ nd.2.2.2 ∧
      ((M.tail nd.2.2.1 ∈ nd.1 ∧ M.head nd.2.2.1 ∈ nd.2.1) ∨
       (M.tail nd.2.2.1 ∈ nd.2.1 ∧ M.head nd.2.2.1 ∈ nd.1)) ∧
      ((M.tail nd.2.2.2 ∈ nd.1 ∧ M.head nd.2.2.2 ∈ nd.2.1) ∨
       (M.tail nd.2.2.2 ∈ nd.2.1 ∧ M.head nd.2.2.2 ∈ nd.1)) ∧
      (∀ x : {e // e ∈ blueB b}, ((M.tail x ∈ nd.1 ∧ M.head x ∈ nd.2.1) ∨ (M.tail x ∈ nd.2.1 ∧ M.head x ∈ nd.1)) →
        x = nd.2.2.1 ∨ x = nd.2.2.2) ∧
      (∀ x : {e // e ∈ blueB b}, M.tail x ∈ nd.1 → M.head x ∈ nd.1 →
        ∃ j : Fin (pn b).length, j < i ∧ (x = ((pn b)[j.1]'j.2).2.2.1 ∨ x = ((pn b)[j.1]'j.2).2.2.2)) ∧
      (∀ x : {e // e ∈ blueB b}, M.tail x ∈ nd.2.1 → M.head x ∈ nd.2.1 →
        ∃ j : Fin (pn b).length, j < i ∧ (x = ((pn b)[j.1]'j.2).2.2.1 ∨ x = ((pn b)[j.1]'j.2).2.2.2)) ∧
      ((∃ j : Fin (pn b).length, j < i ∧ nd.1 = ((pn b)[j.1]'j.2).1 ∪ ((pn b)[j.1]'j.2).2.1) ∨ nd.1.card = 1) ∧
      ((∃ j : Fin (pn b).length, j < i ∧ nd.2.1 = ((pn b)[j.1]'j.2).1 ∪ ((pn b)[j.1]'j.2).2.1) ∨ nd.2.1.card = 1))
    (hpn_conn : ∀ b (k : Fin (pn b).length),
      (Multigraph.Subgraph.induced aux.Q (frameLiftW aux blueB b ((pn b)[k.1]'k.2).1)).Connected ∧
      (Multigraph.Subgraph.induced aux.Q (frameLiftW aux blueB b ((pn b)[k.1]'k.2).2.1)).Connected)
    (allNodes : List (Fin aux.numBlocks × Finset aux.VQ × Finset aux.VQ × aux.EQ × aux.EQ))
    (toG : ∀ b : Fin aux.numBlocks, Fin (pn b).length → Fin allNodes.length)
    (htoG_get : ∀ b k,
      allNodes[(toG b k).1]'(toG b k).2 =
        (b, frameLiftW aux blueB b ((pn b)[k.1]'k.2).1,
            frameLiftW aux blueB b ((pn b)[k.1]'k.2).2.1,
            ((pn b)[k.1]'k.2).2.2.1.1.1,
            ((pn b)[k.1]'k.2).2.2.2.1.1))
    (htoG_mono : ∀ b (k₁ k₂ : Fin (pn b).length), k₁ < k₂ → toG b k₁ < toG b k₂)
    (htoG_surj : ∀ i : Fin allNodes.length, ∃ b k, toG b k = i) :
    Nonempty (Frame G H sub aux) := by
  have hdecode : ∀ i : Fin allNodes.length,
      ∃ (b : Fin aux.numBlocks) (k : Fin (pn b).length),
        toG b k = i ∧
        allNodes[i.1]'i.2 =
          (b, frameLiftW aux blueB b ((pn b)[k.1]'k.2).1,
              frameLiftW aux blueB b ((pn b)[k.1]'k.2).2.1,
              ((pn b)[k.1]'k.2).2.2.1.1.1,
              ((pn b)[k.1]'k.2).2.2.2.1.1) := by
    intro i
    obtain ⟨b, k, rfl⟩ := htoG_surj i
    exact ⟨b, k, rfl, htoG_get b k⟩
  have h_e_ne_f : ∀ i : Fin allNodes.length,
      (allNodes[i.1]'i.2).2.2.2.1 ≠ (allNodes[i.1]'i.2).2.2.2.2 := fun i => by
    obtain ⟨b, k, _, heq⟩ := hdecode i
    rw [heq]; dsimp only
    obtain ⟨_, _, _, hneef, _⟩ := hpn_nodes b k
    intro h; exact hneef (Subtype.ext (Subtype.ext h))
  have h_e_blue : ∀ i : Fin allNodes.length, (allNodes[i.1]'i.2).2.2.2.1 ∈ blue := fun i => by
    obtain ⟨b, k, _, heq⟩ := hdecode i
    rw [heq]; dsimp only
    exact (hblue_iff b _).mp ((pn b)[k.1]'k.2).2.2.1.2
  have h_f_blue : ∀ i : Fin allNodes.length, (allNodes[i.1]'i.2).2.2.2.2 ∈ blue := fun i => by
    obtain ⟨b, k, _, heq⟩ := hdecode i
    rw [heq]; dsimp only
    exact (hblue_iff b _).mp ((pn b)[k.1]'k.2).2.2.2.2
  have h_blue_unique : ∀ t ∈ blue, ∃! i : Fin allNodes.length,
      t = (allNodes[i.1]'i.2).2.2.2.1 ∨ t = (allNodes[i.1]'i.2).2.2.2.2 := fun t ht => by
    let b := aux.comp (aux.Q.tail t)
    have he_mem := (frame_edge_in_Qb aux b t).mp rfl
    have htb : (⟨t, he_mem⟩ : {e // _}) ∈ blueB b := (hblue_iff b ⟨t, he_mem⟩).mpr ht
    obtain ⟨k, hk, huniq⟩ := hpn_uniq b ⟨⟨t, he_mem⟩, htb⟩
    refine ⟨toG b k, ?_, fun j hj => ?_⟩
    · dsimp only; rw [htoG_get b k]; dsimp only
      rcases hk with h | h <;> [left; right] <;> exact congrArg (fun x => x.1.1) h
    · obtain ⟨b', k', rfl, heq⟩ := hdecode j
      rw [heq] at hj; dsimp only at hj
      have hbb : b' = b := by
        rcases hj with h | h
        · have h1 := (frame_edge_in_Qb aux b' _).mpr ((pn b')[k'.1]'k'.2).2.2.1.1.2
          exact h1.symm.trans (congrArg (fun x => aux.comp (aux.Q.tail x)) h.symm)
        · have h1 := (frame_edge_in_Qb aux b' _).mpr ((pn b')[k'.1]'k'.2).2.2.2.1.2
          exact h1.symm.trans (congrArg (fun x => aux.comp (aux.Q.tail x)) h.symm)
      subst hbb
      have hk' : (⟨⟨t, he_mem⟩, htb⟩ : {e // e ∈ blueB b}) = ((pn b)[k'.1]'k'.2).2.2.1 ∨
          (⟨⟨t, he_mem⟩, htb⟩ : {e // e ∈ blueB b}) = ((pn b)[k'.1]'k'.2).2.2.2 := by
        rcases hj with h | h <;> [left; right] <;> exact Subtype.ext (Subtype.ext h)
      have hkeq := huniq k' hk'
      subst hkeq; rfl
  have h_stage_in_comp : ∀ (i : Fin allNodes.length), ∀ v ∈ (allNodes[i.1]'i.2).2.1 ∪ (allNodes[i.1]'i.2).2.2.1,
      aux.comp v = (allNodes[i.1]'i.2).1 := fun i v hv => by
    obtain ⟨b, k, _, heq⟩ := hdecode i
    rw [heq] at hv ⊢; dsimp only at hv ⊢
    rcases Finset.mem_union.mp hv with h | h
    · exact (Finset.mem_filter.mp (frameLiftW_sub aux blueB b _ h)).2
    · exact (Finset.mem_filter.mp (frameLiftW_sub aux blueB b _ h)).2
  have h_stage_disj : ∀ i : Fin allNodes.length,
      Disjoint (allNodes[i.1]'i.2).2.1 (allNodes[i.1]'i.2).2.2.1 := fun i => by
    obtain ⟨b, k, _, heq⟩ := hdecode i
    rw [heq]; dsimp only
    exact frameLiftW_disj aux blueB b _ _ (hpn_nodes b k).1
  have h_op1_ne : ∀ i : Fin allNodes.length, (allNodes[i.1]'i.2).2.1.Nonempty := fun i => by
    obtain ⟨b, k, _, heq⟩ := hdecode i
    rw [heq]; dsimp only
    exact frameLiftW_ne aux blueB b _ (hpn_nodes b k).2.1
  have h_op2_ne : ∀ i : Fin allNodes.length, (allNodes[i.1]'i.2).2.2.1.Nonempty := fun i => by
    obtain ⟨b, k, _, heq⟩ := hdecode i
    rw [heq]; dsimp only
    exact frameLiftW_ne aux blueB b _ (hpn_nodes b k).2.2.1
  have h_e_cross : ∀ i : Fin allNodes.length,
      (aux.Q.tail (allNodes[i.1]'i.2).2.2.2.1 ∈ (allNodes[i.1]'i.2).2.1 ∧
       aux.Q.head (allNodes[i.1]'i.2).2.2.2.1 ∈ (allNodes[i.1]'i.2).2.2.1) ∨
      (aux.Q.tail (allNodes[i.1]'i.2).2.2.2.1 ∈ (allNodes[i.1]'i.2).2.2.1 ∧
       aux.Q.head (allNodes[i.1]'i.2).2.2.2.1 ∈ (allNodes[i.1]'i.2).2.1) := fun i => by
    obtain ⟨b, k, _, heq⟩ := hdecode i
    rw [heq]; dsimp only
    obtain ⟨_, _, _, _, hcr, _⟩ := hpn_nodes b k
    set e' := ((pn b)[k.1]'k.2).2.2.1
    rcases hcr with ⟨ht, hh⟩ | ⟨ht, hh⟩
    · left; exact ⟨(frameLiftW_mem aux blueB b _ _).mpr ht, (frameLiftW_mem aux blueB b _ _).mpr hh⟩
    · right; exact ⟨(frameLiftW_mem aux blueB b _ _).mpr ht, (frameLiftW_mem aux blueB b _ _).mpr hh⟩
  have h_f_cross : ∀ i : Fin allNodes.length,
      (aux.Q.tail (allNodes[i.1]'i.2).2.2.2.2 ∈ (allNodes[i.1]'i.2).2.1 ∧
       aux.Q.head (allNodes[i.1]'i.2).2.2.2.2 ∈ (allNodes[i.1]'i.2).2.2.1) ∨
      (aux.Q.tail (allNodes[i.1]'i.2).2.2.2.2 ∈ (allNodes[i.1]'i.2).2.2.1 ∧
       aux.Q.head (allNodes[i.1]'i.2).2.2.2.2 ∈ (allNodes[i.1]'i.2).2.1) := fun i => by
    obtain ⟨b, k, _, heq⟩ := hdecode i
    rw [heq]; dsimp only
    obtain ⟨_, _, _, _, _, hcr, _⟩ := hpn_nodes b k
    set f' := ((pn b)[k.1]'k.2).2.2.2
    rcases hcr with ⟨ht, hh⟩ | ⟨ht, hh⟩
    · left; exact ⟨(frameLiftW_mem aux blueB b _ _).mpr ht, (frameLiftW_mem aux blueB b _ _).mpr hh⟩
    · right; exact ⟨(frameLiftW_mem aux blueB b _ _).mpr ht, (frameLiftW_mem aux blueB b _ _).mpr hh⟩
  have h_red_no_cross : ∀ (i : Fin allNodes.length), ∀ e : aux.EQ, e ∉ blue →
      (aux.Q.tail e ∈ (allNodes[i.1]'i.2).2.1 → aux.Q.head e ∉ (allNodes[i.1]'i.2).2.2.1) ∧
      (aux.Q.tail e ∈ (allNodes[i.1]'i.2).2.2.1 → aux.Q.head e ∉ (allNodes[i.1]'i.2).2.1) := fun i e hnb => by
    obtain ⟨b, k, _, heq⟩ := hdecode i
    rw [heq]; dsimp only
    have hd := frameLiftW_disj aux blueB b _ _ (hpn_nodes b k).1
    exact ⟨fun ht hh => Finset.disjoint_left.mp hd ((frameLiftW_red_closed aux blueB blue hblue_iff b _ e hnb).mp ht) hh,
           fun ht hh => Finset.disjoint_left.mp hd hh ((frameLiftW_red_closed aux blueB blue hblue_iff b _ e hnb).mp ht)⟩
  have h_stage_blue_topo : ∀ (i : Fin allNodes.length), ∀ e ∈ blue,
      aux.Q.tail e ∈ (allNodes[i.1]'i.2).2.1 ∪ (allNodes[i.1]'i.2).2.2.1 →
      aux.Q.head e ∈ (allNodes[i.1]'i.2).2.1 ∪ (allNodes[i.1]'i.2).2.2.1 →
      ∃ j : Fin allNodes.length, j ≤ i ∧ (e = (allNodes[j.1]'j.2).2.2.2.1 ∨ e = (allNodes[j.1]'j.2).2.2.2.2) := by
    intro i e hbe ht hh
    obtain ⟨b, k, rfl, heq⟩ := hdecode i
    rw [heq] at ht hh; dsimp only at ht hh
    obtain ⟨_, _, _, _, _, _, hcross, hop1, hop2, _⟩ := hpn_nodes b k
    have he_b := (frame_edge_in_Qb aux b e).mp (by
      rcases Finset.mem_union.mp ht with h | h <;> exact (Finset.mem_filter.mp (frameLiftW_sub aux blueB b _ h)).2)
    have htb : (⟨e, he_b⟩ : {e // _}) ∈ blueB b := (hblue_iff b ⟨e, he_b⟩).mpr hbe
    rcases Finset.mem_union.mp ht with ht1 | ht2 <;> rcases Finset.mem_union.mp hh with hh1 | hh2
    · obtain ⟨j, hj, hje⟩ := hop1 ⟨⟨e, he_b⟩, htb⟩
        ((frameLiftW_mem aux blueB b _ _).mp ht1)
        ((frameLiftW_mem aux blueB b _ _).mp hh1)
      refine ⟨toG b j, le_of_lt (htoG_mono b j k hj), ?_⟩
      rw [htoG_get b j]; dsimp only
      rcases hje with h | h <;> [left; right] <;> exact congrArg (fun x => x.1.1) h
    · have hcr := hcross ⟨⟨e, he_b⟩, htb⟩
        (Or.inl ⟨(frameLiftW_mem aux blueB b _ _).mp ht1, (frameLiftW_mem aux blueB b _ _).mp hh2⟩)
      refine ⟨toG b k, le_rfl, ?_⟩
      rw [heq]; dsimp only
      rcases hcr with h | h <;> [left; right] <;> exact congrArg (fun x => x.1.1) h
    · have hcr := hcross ⟨⟨e, he_b⟩, htb⟩
        (Or.inr ⟨(frameLiftW_mem aux blueB b _ _).mp ht2, (frameLiftW_mem aux blueB b _ _).mp hh1⟩)
      refine ⟨toG b k, le_rfl, ?_⟩
      rw [heq]; dsimp only
      rcases hcr with h | h <;> [left; right] <;> exact congrArg (fun x => x.1.1) h
    · obtain ⟨j, hj, hje⟩ := hop2 ⟨⟨e, he_b⟩, htb⟩
        ((frameLiftW_mem aux blueB b _ _).mp ht2)
        ((frameLiftW_mem aux blueB b _ _).mp hh2)
      refine ⟨toG b j, le_of_lt (htoG_mono b j k hj), ?_⟩
      rw [htoG_get b j]; dsimp only
      rcases hje with h | h <;> [left; right] <;> exact congrArg (fun x => x.1.1) h
  have h_stage_crossing_only : ∀ (i : Fin allNodes.length), ∀ e : aux.EQ,
      ((aux.Q.tail e ∈ (allNodes[i.1]'i.2).2.1 ∧ aux.Q.head e ∈ (allNodes[i.1]'i.2).2.2.1) ∨
       (aux.Q.tail e ∈ (allNodes[i.1]'i.2).2.2.1 ∧ aux.Q.head e ∈ (allNodes[i.1]'i.2).2.1)) →
      e = (allNodes[i.1]'i.2).2.2.2.1 ∨ e = (allNodes[i.1]'i.2).2.2.2.2 := by
    intro i e hcr
    obtain ⟨b, k, _, heq⟩ := hdecode i
    rw [heq] at hcr ⊢; dsimp only at hcr ⊢
    obtain ⟨hdisj, _, _, _, _, _, hcross, _⟩ := hpn_nodes b k
    by_cases hbe : e ∈ blue
    · have he_b := (frame_edge_in_Qb aux b e).mp (by
        rcases hcr with ⟨ht, _⟩ | ⟨ht, _⟩ <;> exact (Finset.mem_filter.mp (frameLiftW_sub aux blueB b _ ht)).2)
      have htb : (⟨e, he_b⟩ : {e // _}) ∈ blueB b := (hblue_iff b ⟨e, he_b⟩).mpr hbe
      have hres := hcross ⟨⟨e, he_b⟩, htb⟩ (by
        rcases hcr with ⟨ht, hh⟩ | ⟨ht, hh⟩
        · exact Or.inl ⟨(frameLiftW_mem aux blueB b _ _).mp ht, (frameLiftW_mem aux blueB b _ _).mp hh⟩
        · exact Or.inr ⟨(frameLiftW_mem aux blueB b _ _).mp ht, (frameLiftW_mem aux blueB b _ _).mp hh⟩)
      rcases hres with h | h <;> [left; right] <;> exact congrArg (fun x => x.1.1) h
    · exfalso
      have hd := frameLiftW_disj aux blueB b _ _ hdisj
      rcases hcr with ⟨ht, hh⟩ | ⟨ht, hh⟩
      · exact Finset.disjoint_left.mp hd ((frameLiftW_red_closed aux blueB blue hblue_iff b _ e hbe).mp ht) hh
      · exact Finset.disjoint_left.mp hd hh ((frameLiftW_red_closed aux blueB blue hblue_iff b _ e hbe).mp ht)
  have h_op1_blue_strict : ∀ (i : Fin allNodes.length), ∀ e ∈ blue,
      aux.Q.tail e ∈ (allNodes[i.1]'i.2).2.1 → aux.Q.head e ∈ (allNodes[i.1]'i.2).2.1 →
      ∃ j : Fin allNodes.length, j < i ∧ (e = (allNodes[j.1]'j.2).2.2.2.1 ∨ e = (allNodes[j.1]'j.2).2.2.2.2) := by
    intro i e hbe ht hh
    obtain ⟨b, k, rfl, heq⟩ := hdecode i
    rw [heq] at ht hh; dsimp only at ht hh
    obtain ⟨_, _, _, _, _, _, _, hop1, _⟩ := hpn_nodes b k
    have he_b := (frame_edge_in_Qb aux b e).mp (Finset.mem_filter.mp (frameLiftW_sub aux blueB b _ ht)).2
    have htb : (⟨e, he_b⟩ : {e // _}) ∈ blueB b := (hblue_iff b ⟨e, he_b⟩).mpr hbe
    obtain ⟨j, hj, hje⟩ := hop1 ⟨⟨e, he_b⟩, htb⟩
      ((frameLiftW_mem aux blueB b _ _).mp ht)
      ((frameLiftW_mem aux blueB b _ _).mp hh)
    refine ⟨toG b j, htoG_mono b j k hj, ?_⟩
    rw [htoG_get b j]; dsimp only
    rcases hje with h | h <;> [left; right] <;> exact congrArg (fun x => x.1.1) h
  have h_op2_blue_strict : ∀ (i : Fin allNodes.length), ∀ e ∈ blue,
      aux.Q.tail e ∈ (allNodes[i.1]'i.2).2.2.1 → aux.Q.head e ∈ (allNodes[i.1]'i.2).2.2.1 →
      ∃ j : Fin allNodes.length, j < i ∧ (e = (allNodes[j.1]'j.2).2.2.2.1 ∨ e = (allNodes[j.1]'j.2).2.2.2.2) := by
    intro i e hbe ht hh
    obtain ⟨b, k, rfl, heq⟩ := hdecode i
    rw [heq] at ht hh; dsimp only at ht hh
    obtain ⟨_, _, _, _, _, _, _, _, hop2, _⟩ := hpn_nodes b k
    have he_b := (frame_edge_in_Qb aux b e).mp (Finset.mem_filter.mp (frameLiftW_sub aux blueB b _ ht)).2
    have htb : (⟨e, he_b⟩ : {e // _}) ∈ blueB b := (hblue_iff b ⟨e, he_b⟩).mpr hbe
    obtain ⟨j, hj, hje⟩ := hop2 ⟨⟨e, he_b⟩, htb⟩
      ((frameLiftW_mem aux blueB b _ _).mp ht)
      ((frameLiftW_mem aux blueB b _ _).mp hh)
    refine ⟨toG b j, htoG_mono b j k hj, ?_⟩
    rw [htoG_get b j]; dsimp only
    rcases hje with h | h <;> [left; right] <;> exact congrArg (fun x => x.1.1) h
  have h_op1_conn : ∀ i : Fin allNodes.length,
      (Multigraph.Subgraph.induced aux.Q (allNodes[i.1]'i.2).2.1).Connected := fun i => by
    obtain ⟨b, k, _, heq⟩ := hdecode i
    rw [heq]; dsimp only
    exact (hpn_conn b k).1
  have h_op2_conn : ∀ i : Fin allNodes.length,
      (Multigraph.Subgraph.induced aux.Q (allNodes[i.1]'i.2).2.2.1).Connected := fun i => by
    obtain ⟨b, k, _, heq⟩ := hdecode i
    rw [heq]; dsimp only
    exact (hpn_conn b k).2
  have h_op1_nest : ∀ i : Fin allNodes.length,
      (∃ j : Fin allNodes.length, j < i ∧ (allNodes[i.1]'i.2).2.1 = (allNodes[j.1]'j.2).2.1 ∪ (allNodes[j.1]'j.2).2.2.1) ∨
      (∀ u ∈ (allNodes[i.1]'i.2).2.1, ∀ v ∈ (allNodes[i.1]'i.2).2.1, Relation.ReflTransGen (redAdj aux.Q blue) u v) := by
    intro i
    obtain ⟨b, k, rfl, heq⟩ := hdecode i
    rw [heq]; dsimp only
    obtain ⟨_, _, _, _, _, _, _, _, _, hst1, _⟩ := hpn_nodes b k
    rcases hst1 with ⟨j, hj, hjeq⟩ | hcard1
    · left
      refine ⟨toG b j, htoG_mono b j k hj, ?_⟩
      rw [htoG_get b j]; dsimp only
      rw [← frameLiftW_union, hjeq]
    · right
      intro u hu v hv
      dsimp only [frameLiftW] at hu hv
      rcases Finset.mem_image.mp hu with ⟨u', hu', rfl⟩
      rcases Finset.mem_image.mp hv with ⟨v', hv', rfl⟩
      obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hcard1
      have hu_c : Quotient.mk (redSetoid _ (blueB b)) u' = c :=
        Finset.mem_singleton.mp (hc ▸ (Finset.mem_filter.mp hu').2)
      have hv_c : Quotient.mk (redSetoid _ (blueB b)) v' = c :=
        Finset.mem_singleton.mp (hc ▸ (Finset.mem_filter.mp hv').2)
      exact (frame_redRel_lift aux blueB blue hblue_iff b u' v').mp (Quotient.exact (hu_c.trans hv_c.symm))
  have h_op2_nest : ∀ i : Fin allNodes.length,
      (∃ j : Fin allNodes.length, j < i ∧ (allNodes[i.1]'i.2).2.2.1 = (allNodes[j.1]'j.2).2.1 ∪ (allNodes[j.1]'j.2).2.2.1) ∨
      (∀ u ∈ (allNodes[i.1]'i.2).2.2.1, ∀ v ∈ (allNodes[i.1]'i.2).2.2.1, Relation.ReflTransGen (redAdj aux.Q blue) u v) := by
    intro i
    obtain ⟨b, k, rfl, heq⟩ := hdecode i
    rw [heq]; dsimp only
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hst2⟩ := hpn_nodes b k
    rcases hst2 with ⟨j, hj, hjeq⟩ | hcard1
    · left
      refine ⟨toG b j, htoG_mono b j k hj, ?_⟩
      rw [htoG_get b j]; dsimp only
      rw [← frameLiftW_union, hjeq]
    · right
      intro u hu v hv
      dsimp only [frameLiftW] at hu hv
      rcases Finset.mem_image.mp hu with ⟨u', hu', rfl⟩
      rcases Finset.mem_image.mp hv with ⟨v', hv', rfl⟩
      obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hcard1
      have hu_c : Quotient.mk (redSetoid _ (blueB b)) u' = c :=
        Finset.mem_singleton.mp (hc ▸ (Finset.mem_filter.mp hu').2)
      have hv_c : Quotient.mk (redSetoid _ (blueB b)) v' = c :=
        Finset.mem_singleton.mp (hc ▸ (Finset.mem_filter.mp hv').2)
      exact (frame_redRel_lift aux blueB blue hblue_iff b u' v').mp (Quotient.exact (hu_c.trans hv_c.symm))
  have h_comp_nest : ∀ b : Fin aux.numBlocks,
      (∃ i : Fin allNodes.length, (allNodes[i.1]'i.2).2.1 ∪ (allNodes[i.1]'i.2).2.2.1 = Finset.univ.filter (fun v => aux.comp v = b)) ∨
      (∀ u v, aux.comp u = b → aux.comp v = b → Relation.ReflTransGen (redAdj aux.Q blue) u v) := by
    intro b
    rcases hpn_top b with ⟨k, hkeq⟩ | hcard1
    · left
      refine ⟨toG b k, ?_⟩
      rw [htoG_get b k]; dsimp only
      rw [← frameLiftW_union, ← hkeq]
      ext v; simp only [frameLiftW, stageVerts, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨u, rfl⟩; exact (Finset.mem_filter.mp u.2).2
      · intro hb; exact ⟨⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩⟩, rfl⟩
    · right
      intro u v hu hv
      obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hcard1
      let u' : {x : aux.VQ // x ∈ (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).verts} :=
        ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩⟩
      let v' : {x : aux.VQ // x ∈ (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).verts} :=
        ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩⟩
      have hu_c : Quotient.mk (redSetoid _ (blueB b)) u' = c :=
        Finset.mem_singleton.mp (hc ▸ Finset.mem_univ _)
      have hv_c : Quotient.mk (redSetoid _ (blueB b)) v' = c :=
        Finset.mem_singleton.mp (hc ▸ Finset.mem_univ _)
      exact (frame_redRel_lift aux blueB blue hblue_iff b u' v').mp (Quotient.exact (hu_c.trans hv_c.symm))
  have h_op1_rc : ∀ (i : Fin allNodes.length), ∀ e : aux.EQ, e ∉ blue →
      (aux.Q.tail e ∈ (allNodes[i.1]'i.2).2.1 ↔ aux.Q.head e ∈ (allNodes[i.1]'i.2).2.1) := fun i e hnb => by
    obtain ⟨b, k, _, heq⟩ := hdecode i
    rw [heq]; dsimp only; exact frameLiftW_red_closed aux blueB blue hblue_iff b _ e hnb
  have h_op2_rc : ∀ (i : Fin allNodes.length), ∀ e : aux.EQ, e ∉ blue →
      (aux.Q.tail e ∈ (allNodes[i.1]'i.2).2.2.1 ↔ aux.Q.head e ∈ (allNodes[i.1]'i.2).2.2.1) := fun i e hnb => by
    obtain ⟨b, k, _, heq⟩ := hdecode i
    rw [heq]; dsimp only; exact frameLiftW_red_closed aux blueB blue hblue_iff b _ e hnb
  exact ⟨{
    blue := blue
    comp_wc := hcomp_wc
    numNodes := allNodes.length
    eNode := fun i => (allNodes[i.1]'i.2).2.2.2.1
    fNode := fun i => (allNodes[i.1]'i.2).2.2.2.2
    stageV := fun i => (allNodes[i.1]'i.2).2.1 ∪ (allNodes[i.1]'i.2).2.2.1
    op1V := fun i => (allNodes[i.1]'i.2).2.1
    op2V := fun i => (allNodes[i.1]'i.2).2.2.1
    nodeComp := fun i => (allNodes[i.1]'i.2).1
    e_ne_f := h_e_ne_f
    e_blue := h_e_blue
    f_blue := h_f_blue
    blue_unique := h_blue_unique
    stage_in_comp := h_stage_in_comp
    stage_union := fun _ => rfl
    stage_disj := h_stage_disj
    op1_nonempty := h_op1_ne
    op2_nonempty := h_op2_ne
    e_cross := h_e_cross
    f_cross := h_f_cross
    red_no_cross := h_red_no_cross
    stage_blue_topo := h_stage_blue_topo
    stage_crossing_only := h_stage_crossing_only
    op1_blue_strict := h_op1_blue_strict
    op2_blue_strict := h_op2_blue_strict
    red_forest := hred_forest
    op1_connected := h_op1_conn
    op2_connected := h_op2_conn
    op1_is_stage_or_red := h_op1_nest
    op2_is_stage_or_red := h_op2_nest
    comp_is_stage_or_red := h_comp_nest
    op1_red_closed := h_op1_rc
    op2_red_closed := h_op2_rc
  }⟩

private theorem frame_exists_of_pn
    {G : Multigraph V E} {H : G.Subgraph} (sub : SubdivisionData G H)
    (aux : AuxGraphData G H sub)
    (blueB : ∀ b : Fin aux.numBlocks,
      Finset {e : aux.EQ // e ∈ (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).edges})
    [decEqQ : ∀ b : Fin aux.numBlocks, DecidableEq (Quotient (redSetoid
      (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).toMultigraph (blueB b)))]
    [fintypeQ : ∀ b : Fin aux.numBlocks, Fintype (Quotient (redSetoid
      (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).toMultigraph (blueB b)))]
    (blue : Finset aux.EQ)
    (hblue_iff : ∀ (b : Fin aux.numBlocks)
      (e : {e : aux.EQ // e ∈ (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).edges}),
      e ∈ blueB b ↔ e.1 ∈ blue)
    (hcomp_wc : ∀ b : Fin aux.numBlocks,
      ∃ wc : WellColouring (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).toMultigraph,
        ∀ e, e ∈ wc.blue ↔ e.1 ∈ blue)
    (hred_forest : (Multigraph.Subgraph.ofEdges aux.Q Finset.univ (Finset.univ \ blue)
      (fun _ => Finset.mem_univ _) (fun _ => Finset.mem_univ _)).IsForest)
    (pn : ∀ b : Fin aux.numBlocks,
      List (Finset (Quotient (redSetoid (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).toMultigraph (blueB b))) ×
            Finset (Quotient (redSetoid (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).toMultigraph (blueB b))) ×
            {e // e ∈ blueB b} × {e // e ∈ blueB b}))
    (hpn_uniq : ∀ b (x : {e // e ∈ blueB b}), ∃! idx : Fin (pn b).length,
      let nd := (pn b)[idx.1]'idx.2; x = nd.2.2.1 ∨ x = nd.2.2.2)
    (hpn_top : ∀ b,
      (∃ i : Fin (pn b).length, Finset.univ = ((pn b)[i.1]'i.2).1 ∪ ((pn b)[i.1]'i.2).2.1) ∨
      (Finset.univ : Finset (Quotient (redSetoid (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).toMultigraph (blueB b)))).card = 1)
    (hpn_nodes : ∀ b (i : Fin (pn b).length),
      let M := redQuotient (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).toMultigraph (blueB b)
      let nd := (pn b)[i.1]'i.2
      Disjoint nd.1 nd.2.1 ∧ nd.1.Nonempty ∧ nd.2.1.Nonempty ∧ nd.2.2.1 ≠ nd.2.2.2 ∧
      ((M.tail nd.2.2.1 ∈ nd.1 ∧ M.head nd.2.2.1 ∈ nd.2.1) ∨
       (M.tail nd.2.2.1 ∈ nd.2.1 ∧ M.head nd.2.2.1 ∈ nd.1)) ∧
      ((M.tail nd.2.2.2 ∈ nd.1 ∧ M.head nd.2.2.2 ∈ nd.2.1) ∨
       (M.tail nd.2.2.2 ∈ nd.2.1 ∧ M.head nd.2.2.2 ∈ nd.1)) ∧
      (∀ x : {e // e ∈ blueB b}, ((M.tail x ∈ nd.1 ∧ M.head x ∈ nd.2.1) ∨ (M.tail x ∈ nd.2.1 ∧ M.head x ∈ nd.1)) →
        x = nd.2.2.1 ∨ x = nd.2.2.2) ∧
      (∀ x : {e // e ∈ blueB b}, M.tail x ∈ nd.1 → M.head x ∈ nd.1 →
        ∃ j : Fin (pn b).length, j < i ∧ (x = ((pn b)[j.1]'j.2).2.2.1 ∨ x = ((pn b)[j.1]'j.2).2.2.2)) ∧
      (∀ x : {e // e ∈ blueB b}, M.tail x ∈ nd.2.1 → M.head x ∈ nd.2.1 →
        ∃ j : Fin (pn b).length, j < i ∧ (x = ((pn b)[j.1]'j.2).2.2.1 ∨ x = ((pn b)[j.1]'j.2).2.2.2)) ∧
      ((∃ j : Fin (pn b).length, j < i ∧ nd.1 = ((pn b)[j.1]'j.2).1 ∪ ((pn b)[j.1]'j.2).2.1) ∨ nd.1.card = 1) ∧
      ((∃ j : Fin (pn b).length, j < i ∧ nd.2.1 = ((pn b)[j.1]'j.2).1 ∪ ((pn b)[j.1]'j.2).2.1) ∨ nd.2.1.card = 1))
    (hpn_conn : ∀ b (k : Fin (pn b).length),
      (Multigraph.Subgraph.induced aux.Q (frameLiftW aux blueB b ((pn b)[k.1]'k.2).1)).Connected ∧
      (Multigraph.Subgraph.induced aux.Q (frameLiftW aux blueB b ((pn b)[k.1]'k.2).2.1)).Connected) :
    Nonempty (Frame G H sub aux) := by
  let compNodes (b : Fin aux.numBlocks) :
      List (Fin aux.numBlocks × Finset aux.VQ × Finset aux.VQ × aux.EQ × aux.EQ) :=
    (pn b).map (fun nd =>
      (b, frameLiftW aux blueB b nd.1, frameLiftW aux blueB b nd.2.1, nd.2.2.1.1.1, nd.2.2.2.1.1))
  let allNodes := (List.finRange aux.numBlocks).flatMap compNodes
  have hcompLen : ∀ b : Fin aux.numBlocks, (compNodes b).length = (pn b).length :=
    fun b => List.length_map _
  obtain ⟨toG', htoG_get', htoG_mono', htoG_surj', _⟩ :=
    flatMap_index_bij compNodes (List.finRange aux.numBlocks) (List.nodup_finRange aux.numBlocks)
  let toG : ∀ b : Fin aux.numBlocks, Fin (pn b).length → Fin allNodes.length :=
    fun b k => toG' b (List.mem_finRange b) ⟨k.1, by rw [hcompLen]; exact k.2⟩
  refine frame_exists_core sub aux blueB blue hblue_iff hcomp_wc hred_forest
    pn hpn_uniq hpn_top hpn_nodes hpn_conn allNodes toG ?_ ?_ ?_
  · intro b k
    change allNodes[(toG' b (List.mem_finRange b) ⟨k.1, _⟩).1]'(toG' b (List.mem_finRange b) ⟨k.1, _⟩).2 = _
    rw [htoG_get' b (List.mem_finRange b) ⟨k.1, by rw [hcompLen]; exact k.2⟩]
    dsimp only [compNodes]
    exact List.getElem_map _
  · intro b k₁ k₂ hlt
    exact htoG_mono' b (List.mem_finRange b) ⟨k₁.1, by rw [hcompLen]; exact k₁.2⟩
      ⟨k₂.1, by rw [hcompLen]; exact k₂.2⟩ hlt
  · intro i
    obtain ⟨b, _, k, rfl⟩ := htoG_surj' i
    exact ⟨b, ⟨k.1, by rw [← hcompLen]; exact k.2⟩, rfl⟩

private theorem frame_exists_of_wc
    {G : Multigraph V E} {H : G.Subgraph} (sub : SubdivisionData G H)
    (aux : AuxGraphData G H sub)
    (wc : ∀ b : Fin aux.numBlocks,
      WellColouring (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).toMultigraph)
    (blue : Finset aux.EQ)
    (hblue_iff : ∀ (b : Fin aux.numBlocks)
      (e : {e : aux.EQ // e ∈ (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).edges}),
      e ∈ (wc b).blue ↔ e.1 ∈ blue) :
    Nonempty (Frame G H sub aux) := by
  refine @frame_exists_of_pn V E _ _ _ _ G H sub aux
    (fun b => (wc b).blue)
    (fun b => (wc b).decEqQuot)
    (fun b => (wc b).fintypeQuot)
    blue hblue_iff
    (fun b => ⟨wc b, hblue_iff b⟩)
    (frame_red_forest sub aux wc blue hblue_iff)
    (fun b => postNodes (wc b).twoConstr)
    (fun b x => (postNodes_props (wc b).twoConstr).1 x (Finset.mem_univ x))
    (fun b => (postNodes_props (wc b).twoConstr).2.1)
    (fun b i => by
      obtain ⟨_, hdisj, hne1, hne2, hneef, _, _, hcr1, hcr2, hcross, hop1, hop2, hst1, hst2⟩ :=
        (postNodes_props (wc b).twoConstr).2.2 i
      exact ⟨hdisj, hne1, hne2, hneef, hcr1, hcr2,
        fun x h => hcross x (Finset.mem_univ x) h,
        fun x ht hh => hop1 x (Finset.mem_univ x) ht hh,
        fun x ht hh => hop2 x (Finset.mem_univ x) ht hh,
        hst1, hst2⟩)
    (fun b k =>
      have hc := postNodes_operands_connected _ (wc b).blue (wc b).twoConstr _ (List.getElem_mem k.2)
      ⟨@frameLiftW_conn V E _ _ _ _ G H sub aux (fun b => (wc b).blue) b (wc b).decEqQuot _ hc.1,
       @frameLiftW_conn V E _ _ _ _ G H sub aux (fun b => (wc b).blue) b (wc b).decEqQuot _ hc.2⟩)

/-- **Frame existence (Section 3, following Lemma 3.9):**
Given `JLPTWellColouring`, every `(SUB)` subdivision `H` with auxiliary graph `aux` admits a `Frame`. -/
theorem frame_exists
    (hJLPT : JLPTWellColouring)
    {G : Multigraph V E} {H : G.Subgraph} (sub : SubdivisionData G H)
    (aux : AuxGraphData G H sub) :
    Nonempty (Frame G H sub aux) := by
  let Vb (b : Fin aux.numBlocks) : Finset aux.VQ :=
    Finset.univ.filter (fun v => aux.comp v = b)
  let Qb (b : Fin aux.numBlocks) :=
    (Multigraph.Subgraph.induced aux.Q (Vb b)).toMultigraph
  let wc (b : Fin aux.numBlocks) : WellColouring (Qb b) :=
    (hJLPT _ _ (Qb b) (aux.comp_tc3ec b)).some
  have hedge_in_Qb : ∀ (b : Fin aux.numBlocks) (e : aux.EQ),
      aux.comp (aux.Q.tail e) = b ↔ e ∈ (Multigraph.Subgraph.induced aux.Q (Vb b)).edges := by
    intro b e
    simp only [Multigraph.Subgraph.induced, Vb, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => ⟨h, (aux.edge_same_comp e).symm.trans h⟩, fun h => h.1⟩
  let blue : Finset aux.EQ :=
    Finset.univ.filter (fun e =>
      let b := aux.comp (aux.Q.tail e)
      (⟨e, (hedge_in_Qb b e).mp rfl⟩ : {e : aux.EQ // e ∈ (Multigraph.Subgraph.induced aux.Q (Vb b)).edges}) ∈ (wc b).blue)
  have hblue_iff : ∀ (b : Fin aux.numBlocks)
      (e : {e : aux.EQ // e ∈ (Multigraph.Subgraph.induced aux.Q (Vb b)).edges}),
      e ∈ (wc b).blue ↔ e.1 ∈ blue := by
    intro b e
    have hb : aux.comp (aux.Q.tail e.1) = b := (hedge_in_Qb b e.1).mpr e.2
    simp only [blue, Finset.mem_filter, Finset.mem_univ, true_and]
    have htr : ∀ {b₁ b₂ : Fin aux.numBlocks} (h : b₁ = b₂) (e' : aux.EQ)
        (h1 : e' ∈ (Multigraph.Subgraph.induced aux.Q (Vb b₁)).edges)
        (h2 : e' ∈ (Multigraph.Subgraph.induced aux.Q (Vb b₂)).edges),
        (⟨e', h1⟩ ∈ (wc b₁).blue) ↔ (⟨e', h2⟩ ∈ (wc b₂).blue) := by
      intro b₁ b₂ h; subst h; intro _ _ _; rfl
    exact (htr hb e.1 _ e.2).symm
  exact frame_exists_of_wc sub aux wc blue hblue_iff

end FrameExistence

section Lemma311AndDef312

variable {V E A : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] [AddCommGroup A]

/-- Helper: `Tg g` restricted to a subset `U` of vertices. -/
private def restrictTg {G : Multigraph V E} {H : G.Subgraph} {sub : SubdivisionData G H}
    {aux : AuxGraphData G H sub} (fr : Frame G H sub aux)
    (g : Fin fr.numNodes → aux.EQ) (U : Finset aux.VQ) : aux.Q.Subgraph :=
  Multigraph.Subgraph.ofEdges aux.Q U
    ((fr.Tg g).edges.filter (fun e => aux.Q.tail e ∈ U ∧ aux.Q.head e ∈ U))
    (fun he => (Finset.mem_filter.mp he).2.1)
    (fun he => (Finset.mem_filter.mp he).2.2)

/-- Helper: if `U` is nonempty, red-closed, and all pairs in `U` are connected by red edges,
then `restrictTg fr g U` is connected. -/
private lemma restrictTg_connected_of_red {G : Multigraph V E} {H : G.Subgraph}
    {sub : SubdivisionData G H} {aux : AuxGraphData G H sub}
    (fr : Frame G H sub aux) (g : Fin fr.numNodes → aux.EQ) (U : Finset aux.VQ)
    (hUne : U.Nonempty)
    (hclosed : ∀ e : aux.EQ, e ∉ fr.blue → (aux.Q.tail e ∈ U ↔ aux.Q.head e ∈ U))
    (hred : ∀ u ∈ U, ∀ v ∈ U, Relation.ReflTransGen (redAdj aux.Q fr.blue) u v) :
    (restrictTg fr g U).Connected := by
  refine ⟨hUne, fun u hu v hv => ?_⟩
  have hr := hred u hu v hv
  have hstay : ∀ {x y : aux.VQ}, x ∈ U → Relation.ReflTransGen (redAdj aux.Q fr.blue) x y →
      y ∈ U ∧ Relation.ReflTransGen (restrictTg fr g U).Adj x y := by
    intro x y hx hxy
    induction hxy with
    | refl => exact ⟨hx, Relation.ReflTransGen.refl⟩
    | @tail w z _ hstep ih =>
      rcases ih with ⟨hw, hwalk⟩
      rcases hstep with ⟨e, hnb, ⟨ht, hh⟩ | ⟨ht, hh⟩⟩
      · have hz : z ∈ U := hh ▸ (hclosed e hnb).mp (ht.symm ▸ hw)
        have he_in : e ∈ (restrictTg fr g U).edges :=
          Finset.mem_filter.mpr ⟨Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnb⟩),
            ht.symm ▸ hw, hh.symm ▸ hz⟩
        exact ⟨hz, Relation.ReflTransGen.tail hwalk ⟨e, he_in, Or.inl ⟨ht, hh⟩⟩⟩
      · have hz : z ∈ U := ht ▸ (hclosed e hnb).mpr (hh.symm ▸ hw)
        have he_in : e ∈ (restrictTg fr g U).edges :=
          Finset.mem_filter.mpr ⟨Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnb⟩),
            ht.symm ▸ hz, hh.symm ▸ hw⟩
        exact ⟨hz, Relation.ReflTransGen.tail hwalk ⟨e, he_in, Or.inr ⟨ht, hh⟩⟩⟩
  exact (hstay hu hr).2

/-- **Lemma 3.11 (Official cycles and free-edge cycles, (O1)–(O6)).** -/
theorem lem_3_11
    {G : Multigraph V E} {H : G.Subgraph} {sub : SubdivisionData G H}
    {aux : AuxGraphData G H sub} (fr : Frame G H sub aux) :
    (∀ g : Fin fr.numNodes → aux.EQ, (∀ i, g i = fr.eNode i ∨ g i = fr.fNode i) →
      (fr.Tg g).IsSpanningForest ∧
      (∀ b : Fin aux.numBlocks,
        let Vb := Finset.univ.filter (fun v => aux.comp v = b)
        (Multigraph.Subgraph.ofEdges aux.Q Vb
          ((fr.Tg g).edges.filter (fun e => aux.Q.tail e ∈ Vb ∧ aux.Q.head e ∈ Vb))
          (fun he => (Finset.mem_filter.mp he).2.1)
          (fun he => (Finset.mem_filter.mp he).2.2)).Connected) ∧
      (∀ i : Fin fr.numNodes,
        (Multigraph.Subgraph.ofEdges aux.Q (fr.stageV i)
          ((fr.Tg g).edges.filter (fun e => aux.Q.tail e ∈ fr.stageV i ∧ aux.Q.head e ∈ fr.stageV i))
          (fun he => (Finset.mem_filter.mp he).2.1)
          (fun he => (Finset.mem_filter.mp he).2.2)).Connected ∧
        (Multigraph.Subgraph.ofEdges aux.Q (fr.op1V i)
          ((fr.Tg g).edges.filter (fun e => aux.Q.tail e ∈ fr.op1V i ∧ aux.Q.head e ∈ fr.op1V i))
          (fun he => (Finset.mem_filter.mp he).2.1)
          (fun he => (Finset.mem_filter.mp he).2.2)).Connected ∧
        (Multigraph.Subgraph.ofEdges aux.Q (fr.op2V i)
          ((fr.Tg g).edges.filter (fun e => aux.Q.tail e ∈ fr.op2V i ∧ aux.Q.head e ∈ fr.op2V i))
          (fun he => (Finset.mem_filter.mp he).2.1)
          (fun he => (Finset.mem_filter.mp he).2.2)).Connected)) ∧
    (∀ i : Fin fr.numNodes, ∃! C : aux.Q.DirectedCycle, fr.IsOfficialCycle i C) ∧
    (∀ (C : Fin fr.numNodes → aux.Q.DirectedCycle),
      (∀ i, fr.IsOfficialCycle i (C i)) →
      (∀ i, (C i).sub.verts ⊆ fr.stageV i ∧
            fr.eNode i ∈ (C i).sub.edges ∧ fr.fNode i ∈ (C i).sub.edges) ∧
      (∀ l i : Fin fr.numNodes, l < i →
            fr.eNode i ∉ (C l).sub.edges ∧ fr.fNode i ∉ (C l).sub.edges) ∧
      (∀ l i : Fin fr.numNodes, i < l → fr.fNode i ∉ (C l).sub.edges) ∧
      (∀ Y : aux.EQ → A, aux.Q.IsFlow Y →
        ∃! x : Fin fr.numNodes → A,
          ∀ eq, Y eq = ∑ i : Fin fr.numNodes, (C i).sign eq • x i)) ∧
    (fr.HProtected.Connected ∧
      (∀ v ∈ H.verts, (∀ t : sub.E₀, fr.IsFree t →
        ¬ (v ∈ (sub.thread t).verts ∧ v ≠ sub.embedV (sub.H₀.tail t) ∧ v ≠ sub.embedV (sub.H₀.head t))) →
        v ∈ fr.HProtected.verts) ∧
      (∀ eps : sub.E₀, fr.IsFree eps →
        ∃ D : G.DirectedCycle,
          D.sub ≤ H ∧
          (∀ e ∈ (sub.thread eps).edges, e ∈ D.sub.edges ∧ D.sign e = 1) ∧
          (∀ t : sub.E₀, fr.IsFree t → t ≠ eps →
            ∀ e ∈ (sub.thread t).edges, e ∉ D.sub.edges))) := by
  classical
  -- Helper: `eNode i` and `fNode i` lie in `nodeComp i`
  have he_comp : ∀ i : Fin fr.numNodes, aux.comp (aux.Q.tail (fr.eNode i)) = fr.nodeComp i := by
    intro i
    rcases fr.e_cross i with ⟨ht, _⟩ | ⟨ht, _⟩
    · exact fr.stage_in_comp i _ (by rw [fr.stage_union]; exact Finset.mem_union_left _ ht)
    · exact fr.stage_in_comp i _ (by rw [fr.stage_union]; exact Finset.mem_union_right _ ht)
  have hf_comp : ∀ i : Fin fr.numNodes, aux.comp (aux.Q.tail (fr.fNode i)) = fr.nodeComp i := by
    intro i
    rcases fr.f_cross i with ⟨ht, _⟩ | ⟨ht, _⟩
    · exact fr.stage_in_comp i _ (by rw [fr.stage_union]; exact Finset.mem_union_left _ ht)
    · exact fr.stage_in_comp i _ (by rw [fr.stage_union]; exact Finset.mem_union_right _ ht)
  -- Helper: distinctness of `eNode i, fNode i` across nodes
  have hnode_inj : ∀ i j : Fin fr.numNodes,
      (fr.eNode i = fr.eNode j ∨ fr.eNode i = fr.fNode j ∨ fr.fNode i = fr.eNode j ∨ fr.fNode i = fr.fNode j) →
      i = j := by
    intro i j h
    rcases h with h | h | h | h
    · obtain ⟨k, _, huniq⟩ := fr.blue_unique (fr.eNode i) (fr.e_blue i)
      exact (huniq i (Or.inl rfl)).trans (huniq j (Or.inl h)).symm
    · obtain ⟨k, _, huniq⟩ := fr.blue_unique (fr.eNode i) (fr.e_blue i)
      exact (huniq i (Or.inl rfl)).trans (huniq j (Or.inr h)).symm
    · obtain ⟨k, _, huniq⟩ := fr.blue_unique (fr.fNode i) (fr.f_blue i)
      exact (huniq i (Or.inr rfl)).trans (huniq j (Or.inl h)).symm
    · obtain ⟨k, _, huniq⟩ := fr.blue_unique (fr.fNode i) (fr.f_blue i)
      exact (huniq i (Or.inr rfl)).trans (huniq j (Or.inr h)).symm
  have hef_disj : ∀ i j : Fin fr.numNodes, fr.eNode i ≠ fr.fNode j := fun i j h =>
    fr.e_ne_f i (hnode_inj i j (Or.inr (Or.inl h)) ▸ h)
  -- ===== Part (O1) =====
  have hO1 : ∀ g : Fin fr.numNodes → aux.EQ, (∀ i, g i = fr.eNode i ∨ g i = fr.fNode i) →
      (fr.Tg g).IsSpanningForest ∧
      (∀ b : Fin aux.numBlocks, (restrictTg fr g (Finset.univ.filter (fun v => aux.comp v = b))).Connected) ∧
      (∀ i : Fin fr.numNodes,
        (restrictTg fr g (fr.stageV i)).Connected ∧
        (restrictTg fr g (fr.op1V i)).Connected ∧
        (restrictTg fr g (fr.op2V i)).Connected) := by
    intro g hg
    -- Step 1: Connectedness on `stageV i`, `op1V i`, `op2V i` by strong induction on `i.1`
    have hstage_conn : ∀ (k : ℕ) (i : Fin fr.numNodes), i.1 < k →
        (restrictTg fr g (fr.stageV i)).Connected ∧
        (restrictTg fr g (fr.op1V i)).Connected ∧
        (restrictTg fr g (fr.op2V i)).Connected := by
      intro k
      induction k with
      | zero => intro i hi; omega
      | succ k ih =>
        intro i hi
        have hop1 : (restrictTg fr g (fr.op1V i)).Connected := by
          rcases fr.op1_is_stage_or_red i with ⟨j, hj, hjeq⟩ | hred
          · rw [hjeq]; exact (ih j (by have : j.1 < i.1 := hj; omega)).1
          · exact restrictTg_connected_of_red fr g (fr.op1V i) (fr.op1_nonempty i)
              (fr.op1_red_closed i) hred
        have hop2 : (restrictTg fr g (fr.op2V i)).Connected := by
          rcases fr.op2_is_stage_or_red i with ⟨j, hj, hjeq⟩ | hred
          · rw [hjeq]; exact (ih j (by have : j.1 < i.1 := hj; omega)).1
          · exact restrictTg_connected_of_red fr g (fr.op2V i) (fr.op2_nonempty i)
              (fr.op2_red_closed i) hred
        have hst : (restrictTg fr g (fr.stageV i)).Connected := by
          have hun := fr.stage_union i
          have hgi_cr : (aux.Q.tail (g i) ∈ fr.op1V i ∧ aux.Q.head (g i) ∈ fr.op2V i) ∨
              (aux.Q.tail (g i) ∈ fr.op2V i ∧ aux.Q.head (g i) ∈ fr.op1V i) := by
            rcases hg i with h | h <;> rw [h]
            · exact fr.e_cross i
            · exact fr.f_cross i
          have hgi_in : g i ∈ (restrictTg fr g (fr.stageV i)).edges := by
            refine Finset.mem_filter.mpr ⟨Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩), ?_, ?_⟩
            · rw [hun]; rcases hgi_cr with ⟨ht, _⟩ | ⟨ht, _⟩
              · exact Finset.mem_union_left _ ht
              · exact Finset.mem_union_right _ ht
            · rw [hun]; rcases hgi_cr with ⟨_, hh⟩ | ⟨_, hh⟩
              · exact Finset.mem_union_right _ hh
              · exact Finset.mem_union_left _ hh
          have hsub1 : (restrictTg fr g (fr.op1V i)).edges ⊆ (restrictTg fr g (fr.stageV i)).edges := fun e he => by
            simp only [restrictTg, Multigraph.Subgraph.ofEdges, Finset.mem_filter, hun] at he ⊢
            exact ⟨he.1, Finset.mem_union_left _ he.2.1, Finset.mem_union_left _ he.2.2⟩
          have hsub2 : (restrictTg fr g (fr.op2V i)).edges ⊆ (restrictTg fr g (fr.stageV i)).edges := fun e he => by
            simp only [restrictTg, Multigraph.Subgraph.ofEdges, Finset.mem_filter, hun] at he ⊢
            exact ⟨he.1, Finset.mem_union_right _ he.2.1, Finset.mem_union_right _ he.2.2⟩
          have hw1 : ∀ a ∈ fr.op1V i, ∀ b ∈ fr.op1V i,
              Relation.ReflTransGen (restrictTg fr g (fr.stageV i)).Adj a b :=
            fun a ha b hb => reflTransGen_mono (fun _ _ ⟨e, he, hadj⟩ => ⟨e, hsub1 he, hadj⟩) (hop1.2 a ha b hb)
          have hw2 : ∀ a ∈ fr.op2V i, ∀ b ∈ fr.op2V i,
              Relation.ReflTransGen (restrictTg fr g (fr.stageV i)).Adj a b :=
            fun a ha b hb => reflTransGen_mono (fun _ _ ⟨e, he, hadj⟩ => ⟨e, hsub2 he, hadj⟩) (hop2.2 a ha b hb)
          refine ⟨(fr.op1_nonempty i).mono (by rw [hun]; exact Finset.subset_union_left), fun u hu v hv => ?_⟩
          change u ∈ fr.stageV i at hu; change v ∈ fr.stageV i at hv
          rw [hun] at hu hv
          rcases Finset.mem_union.mp hu with hu1 | hu2 <;> rcases Finset.mem_union.mp hv with hv1 | hv2
          · exact hw1 u hu1 v hv1
          · rcases hgi_cr with ⟨ht, hh⟩ | ⟨ht, hh⟩
            · exact Relation.ReflTransGen.trans (hw1 u hu1 _ ht)
                (Relation.ReflTransGen.head ⟨g i, hgi_in, Or.inl ⟨rfl, rfl⟩⟩ (hw2 _ hh v hv2))
            · exact Relation.ReflTransGen.trans (hw1 u hu1 _ hh)
                (Relation.ReflTransGen.head ⟨g i, hgi_in, Or.inr ⟨rfl, rfl⟩⟩ (hw2 _ ht v hv2))
          · rcases hgi_cr with ⟨ht, hh⟩ | ⟨ht, hh⟩
            · exact Relation.ReflTransGen.trans (hw2 u hu2 _ hh)
                (Relation.ReflTransGen.head ⟨g i, hgi_in, Or.inr ⟨rfl, rfl⟩⟩ (hw1 _ ht v hv1))
            · exact Relation.ReflTransGen.trans (hw2 u hu2 _ ht)
                (Relation.ReflTransGen.head ⟨g i, hgi_in, Or.inl ⟨rfl, rfl⟩⟩ (hw1 _ hh v hv1))
          · exact hw2 u hu2 v hv2
        exact ⟨hst, hop1, hop2⟩
    have hstage_all : ∀ i : Fin fr.numNodes,
        (restrictTg fr g (fr.stageV i)).Connected ∧
        (restrictTg fr g (fr.op1V i)).Connected ∧
        (restrictTg fr g (fr.op2V i)).Connected := fun i => hstage_conn fr.numNodes i i.2
    -- Step 2: Connectedness on each component `Vb b`
    have hcomp_conn : ∀ b : Fin aux.numBlocks,
        (restrictTg fr g (Finset.univ.filter (fun v => aux.comp v = b))).Connected := by
      intro b
      rcases fr.comp_is_stage_or_red b with ⟨i, hieq⟩ | hred
      · rw [← hieq]; exact (hstage_all i).1
      · -- `Vb b` is nonempty since `Qb b` is truncated cubic 3-edge-connected (hence ≥ 3 vertices)
        have hVb_ne : (Finset.univ.filter (fun v => aux.comp v = b)).Nonempty := by
          obtain ⟨wc, _⟩ := fr.comp_wc b
          obtain ⟨u, _⟩ := wc.blue_tree.2.1.1
          exact ⟨u.1, u.2⟩
        exact restrictTg_connected_of_red fr g _ hVb_ne
          (fun e _ => by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            rw [aux.edge_same_comp e])
          (fun u hu v hv => hred u v (Finset.mem_filter.mp hu).2 (Finset.mem_filter.mp hv).2)
    -- Step 3: `(fr.Tg g).IsSpanningForest`
    have hTg_sf : (fr.Tg g).IsSpanningForest := by
      refine ⟨rfl, ?_, ?_⟩
      · -- Acyclicity: on each component `b`, `restrictTg fr g (Vb b)` is connected with `|Vb b| - 1` edges!
        have hg_inj : Function.Injective g := fun i j hij => by
          rcases hg i with hi | hi <;> rcases hg j with hj | hj
          · exact hnode_inj i j (Or.inl (hi.symm.trans (hij.trans hj)))
          · exact hnode_inj i j (Or.inr (Or.inl (hi.symm.trans (hij.trans hj))))
          · exact hnode_inj i j (Or.inr (Or.inr (Or.inl (hi.symm.trans (hij.trans hj)))))
          · exact hnode_inj i j (Or.inr (Or.inr (Or.inr (hi.symm.trans (hij.trans hj)))))
        have hg_blue : ∀ i, g i ∈ fr.blue := fun i => by
          rcases hg i with h | h <;> rw [h]
          · exact fr.e_blue i
          · exact fr.f_blue i
        have hg_comp : ∀ i, aux.comp (aux.Q.tail (g i)) = fr.nodeComp i := fun i => by
          rcases hg i with h | h <;> rw [h]
          · exact he_comp i
          · exact hf_comp i
        intro C hCle hCcyc
        obtain ⟨v₀, hv₀⟩ := hCcyc.1.1
        let b := aux.comp v₀
        let Vb : Finset aux.VQ := Finset.univ.filter (fun v => aux.comp v = b)
        have hC_in_b : ∀ u ∈ C.verts, u ∈ Vb := fun u hu => by
          have hw := hCcyc.1.2 v₀ hv₀ u hu
          clear hu
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          induction hw with
          | refl => rfl
          | tail _ hstep ih =>
            rcases hstep with ⟨e, _, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
            · exact (aux.edge_same_comp e).symm.trans ih
            · exact (aux.edge_same_comp e).trans ih
        have hC_le_b : C ≤ restrictTg fr g Vb :=
          ⟨hC_in_b, fun e heC => Finset.mem_filter.mpr
            ⟨hCle.2 heC, hC_in_b _ (C.tail_mem heC), hC_in_b _ (C.head_mem heC)⟩⟩
        -- Edge count of `restrictTg fr g Vb`: `red_b + nodes_b = Vb.card - 1`
        obtain ⟨wc, hwc_iff⟩ := fr.comp_wc b
        let Qb := (Multigraph.Subgraph.induced aux.Q Vb).toMultigraph
        have hQb_info := lem_3_9 Qb (aux.comp_tc3ec b) wc
        have hnb : Fintype.card {v : aux.VQ // v ∈ (Multigraph.Subgraph.induced aux.Q Vb).verts} = Vb.card :=
          Fintype.card_coe Vb
        have hblue_b_card : wc.blue.card + 1 = Vb.card := by
          have := spanningTree_edges_card wc.blue_tree; rw [hnb] at this; exact this
        have hmb : 2 * Fintype.card {e : aux.EQ // e ∈ (Multigraph.Subgraph.induced aux.Q Vb).edges} =
            3 * (Vb.card - 1) := by
          have := hQb_info.2.2.1; rw [hnb] at this; exact this
        -- Count blue edges of `Q_b`: `= 2 * #{i | nodeComp i = b}`
        let blue_b : Finset aux.EQ := fr.blue.filter (fun e => aux.comp (aux.Q.tail e) = b)
        have hblue_b_eq : blue_b.card = wc.blue.card := by
          refine Finset.card_bij (fun e he => ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp he).2⟩,
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, (aux.edge_same_comp e).symm.trans (Finset.mem_filter.mp he).2⟩⟩⟩)
            (fun e he => (hwc_iff _).mpr (Finset.mem_filter.mp he).1)
            (fun _ _ _ _ h => congrArg Subtype.val h)
            (fun e he => ⟨e.1, Finset.mem_filter.mpr ⟨(hwc_iff e).mp he,
              (Finset.mem_filter.mp (Finset.mem_filter.mp e.2).2.1).2⟩, Subtype.ext rfl⟩)
        let nodes_b : Finset (Fin fr.numNodes) := Finset.univ.filter (fun i => fr.nodeComp i = b)
        have hblue_pair : blue_b.card = 2 * nodes_b.card := by
          have hun : blue_b = nodes_b.image fr.eNode ∪ nodes_b.image fr.fNode := by
            ext e
            simp only [blue_b, nodes_b, Finset.mem_filter, Finset.mem_union, Finset.mem_image,
              Finset.mem_univ, true_and]
            constructor
            · rintro ⟨hbe, hcb⟩
              obtain ⟨i, hi, _⟩ := fr.blue_unique e hbe
              rcases hi with rfl | rfl
              · left; exact ⟨i, (he_comp i).symm.trans hcb, rfl⟩
              · right; exact ⟨i, (hf_comp i).symm.trans hcb, rfl⟩
            · rintro (⟨i, hcb, rfl⟩ | ⟨i, hcb, rfl⟩)
              · exact ⟨fr.e_blue i, (he_comp i).trans hcb⟩
              · exact ⟨fr.f_blue i, (hf_comp i).trans hcb⟩
          have hd : Disjoint (nodes_b.image fr.eNode) (nodes_b.image fr.fNode) := by
            rw [Finset.disjoint_left]; intro e h1 h2
            rcases Finset.mem_image.mp h1 with ⟨i, _, rfl⟩
            rcases Finset.mem_image.mp h2 with ⟨j, _, hj⟩
            exact hef_disj i j hj.symm
          rw [hun, Finset.card_union_of_disjoint hd,
              Finset.card_image_of_injective _ (fun i j h => hnode_inj i j (Or.inl h)),
              Finset.card_image_of_injective _ (fun i j h => hnode_inj i j (Or.inr (Or.inr (Or.inr h))))]
          omega
        -- Count red edges of `Q_b`: `= |E(Q_b)| - blue_b.card`
        let red_b : Finset aux.EQ := (Finset.univ \ fr.blue).filter (fun e => aux.comp (aux.Q.tail e) = b)
        have hred_b_card : red_b.card + blue_b.card =
            Fintype.card {e : aux.EQ // e ∈ (Multigraph.Subgraph.induced aux.Q Vb).edges} := by
          have hdisj : Disjoint red_b blue_b := by
            rw [Finset.disjoint_left]; intro e h1 h2
            exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp h1).1).2 (Finset.mem_filter.mp h2).1
          rw [← Finset.card_union_of_disjoint hdisj, Fintype.card_coe]
          congr 1; ext e
          simp only [red_b, blue_b, Multigraph.Subgraph.induced, Vb, Finset.mem_union,
            Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
          constructor
          · rintro (⟨_, h⟩ | ⟨_, h⟩) <;> exact ⟨h, (aux.edge_same_comp e).symm.trans h⟩
          · rintro ⟨h, _⟩; by_cases hb : e ∈ fr.blue <;> [exact Or.inr ⟨hb, h⟩; exact Or.inl ⟨hb, h⟩]
        -- Edges of `restrictTg fr g Vb` = `red_b ∪ nodes_b.image g` (disjoint!)
        have hTg_b_eq : (restrictTg fr g Vb).edges = red_b ∪ nodes_b.image g := by
          ext e
          simp only [restrictTg, Frame.Tg, Multigraph.Subgraph.ofEdges, red_b, nodes_b, Vb,
            Finset.mem_filter, Finset.mem_union, Finset.mem_sdiff, Finset.mem_image,
            Finset.mem_univ, true_and]
          constructor
          · rintro ⟨hnb | ⟨i, rfl⟩, ht, _⟩
            · left; exact ⟨hnb, ht⟩
            · right; exact ⟨i, (hg_comp i).symm.trans ht, rfl⟩
          · rintro (⟨hnb, ht⟩ | ⟨i, hcb, rfl⟩)
            · exact ⟨Or.inl hnb, ht, (aux.edge_same_comp e).symm.trans ht⟩
            · exact ⟨Or.inr ⟨i, rfl⟩, (hg_comp i).trans hcb, (aux.edge_same_comp _).symm.trans ((hg_comp i).trans hcb)⟩
        have hdisj_rg : Disjoint red_b (nodes_b.image g) := by
          rw [Finset.disjoint_left]; intro e h1 h2
          rcases Finset.mem_image.mp h2 with ⟨i, _, rfl⟩
          exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp h1).1).2 (hg_blue i)
        have hcard_Tg_b : (restrictTg fr g Vb).edges.card + 1 = (restrictTg fr g Vb).verts.card := by
          rw [hTg_b_eq, Finset.card_union_of_disjoint hdisj_rg, Finset.card_image_of_injective _ hg_inj]
          change red_b.card + nodes_b.card + 1 = Vb.card
          omega
        exact connected_edges_eq_verts_sub_one_isForest (restrictTg fr g Vb) (hcomp_conn b) hcard_Tg_b C hC_le_b hCcyc
      · -- Reachability preservation
        intro u v huv
        have hcomp_eq : aux.comp u = aux.comp v := by
          induction huv with
          | refl => rfl
          | tail _ hstep ih =>
            rcases hstep with ⟨e, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
            · exact ih.trans (aux.edge_same_comp e)
            · exact ih.trans (aux.edge_same_comp e).symm
        let b := aux.comp u
        have hwalk := (hcomp_conn b).2 u (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩)
          v (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcomp_eq.symm⟩)
        exact reflTransGen_mono (fun _ _ ⟨e, he, hadj⟩ => ⟨e, (Finset.mem_filter.mp he).1, hadj⟩) hwalk
    exact ⟨hTg_sf, hcomp_conn, hstage_all⟩
  -- ===== Official cycle existence, uniqueness, and (O2)–(O5) =====
  have hTe_O1 := hO1 fr.eNode (fun _ => Or.inl rfl)
  have hf_not_Te : ∀ i : Fin fr.numNodes, fr.fNode i ∉ fr.Te.edges := fun i hmem => by
    rcases Finset.mem_union.mp hmem with hred | himg
    · exact (Finset.mem_sdiff.mp hred).2 (fr.f_blue i)
    · rcases Finset.mem_image.mp himg with ⟨j, _, hj⟩
      exact hef_disj j i hj
  -- Build canonical official cycle inside `stageV i`
  have hbuild_C : ∀ i : Fin fr.numNodes,
      ∃ C : aux.Q.DirectedCycle, fr.IsOfficialCycle i C ∧ C.sub.verts ⊆ fr.stageV i := by
    intro i
    have hstage_conn := (hTe_O1.2.2 i).1
    have ht_in : aux.Q.tail (fr.fNode i) ∈ fr.stageV i := by
      rw [fr.stage_union]
      rcases fr.f_cross i with ⟨ht, _⟩ | ⟨ht, _⟩
      · exact Finset.mem_union_left _ ht
      · exact Finset.mem_union_right _ ht
    have hh_in : aux.Q.head (fr.fNode i) ∈ fr.stageV i := by
      rw [fr.stage_union]
      rcases fr.f_cross i with ⟨_, hh⟩ | ⟨_, hh⟩
      · exact Finset.mem_union_right _ hh
      · exact Finset.mem_union_left _ hh
    have hne_ends : aux.Q.tail (fr.fNode i) ≠ aux.Q.head (fr.fNode i) := by
      rcases fr.f_cross i with ⟨ht, hh⟩ | ⟨ht, hh⟩
      · exact fun h => Finset.disjoint_left.mp (fr.stage_disj i) ht (h ▸ hh)
      · exact fun h => Finset.disjoint_left.mp (fr.stage_disj i) hh (h.symm ▸ ht)
    obtain ⟨verts, edges, hlen, hv_nodup, hhead, hlast, hedges_in, hstep⟩ :=
      exists_simplePath_of_reflTransGen (hstage_conn.2 _ hh_in _ ht_in)
    have hverts_sub : ∀ v ∈ verts, v ∈ fr.stageV i := by
      intro v hv
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hv
      by_cases h0 : edges.length = 0
      · have hk0 : k = 0 := by omega
        subst hk0
        have hhh := hhead
        rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hhh
        exact (Option.some.inj hhh).symm ▸ hh_in
      · by_cases hkl : k < edges.length
        · have hs := hstep k hkl
          have he := hedges_in _ (List.getElem_mem hkl)
          rcases hs with ⟨ht, _⟩ | ⟨_, hh⟩
          · exact ht ▸ (Finset.mem_filter.mp he).2.1
          · exact hh ▸ (Finset.mem_filter.mp he).2.2
        · have hkl' : k - 1 < edges.length := by omega
          have hs := hstep (k - 1) hkl'
          have hidx : k - 1 + 1 = k := by omega
          have he := hedges_in _ (List.getElem_mem hkl')
          simp only [hidx] at hs
          rcases hs with ⟨_, hh⟩ | ⟨ht, _⟩
          · exact hh ▸ (Finset.mem_filter.mp he).2.2
          · exact ht ▸ (Finset.mem_filter.mp he).2.1
    have hedges_pos : 1 ≤ edges.length := by
      by_contra h0
      have he0 : edges.length = 0 := by omega
      have h1 : verts[0]'(by omega) = aux.Q.head (fr.fNode i) := by
        rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hhead
        exact Option.some.inj hhead
      have h2 : verts[0]'(by omega) = aux.Q.tail (fr.fNode i) := by
        rw [List.getLast?_eq_getElem?] at hlast
        have hidx : verts.length - 1 = 0 := by omega
        rw [hidx, List.getElem?_eq_getElem (by omega)] at hlast
        exact Option.some.inj hlast
      exact hne_ends (h2.symm.trans h1)
    have hpe_nodup := simplePath_edges_nodup hv_nodup hlen hstep
    have hf_not_edges : fr.fNode i ∉ edges := fun hmem =>
      hf_not_Te i (Finset.mem_filter.mp (hedges_in _ hmem)).1
    let eList := edges ++ [fr.fNode i]
    have heList_nodup : eList.Nodup := by
      rw [List.nodup_append]; refine ⟨hpe_nodup, List.nodup_singleton _, fun e he e' he' => ?_⟩
      rw [List.mem_singleton.mp he']; exact fun h => hf_not_edges (h ▸ he)
    have hclosed : ∀ (k : ℕ) (hk : k < eList.length),
        let u := verts[k]'(by simp [eList] at hk; omega)
        let w := verts[(k + 1) % verts.length]'(Nat.mod_lt _ (by omega))
        let e := eList[k]'hk
        (aux.Q.tail e = u ∧ aux.Q.head e = w) ∨ (aux.Q.tail e = w ∧ aux.Q.head e = u) := by
      intro k hk
      simp only [eList, List.length_append, List.length_singleton] at hk
      by_cases hlt : k < edges.length
      · have hmod : (k + 1) % verts.length = k + 1 := Nat.mod_eq_of_lt (by omega)
        simp only [eList, List.getElem_append_left hlt, hmod]
        exact hstep k hlt
      · have hke : k = edges.length := by omega
        have hmod : (k + 1) % verts.length = 0 := by
          have : k + 1 = verts.length := by omega
          rw [this, Nat.mod_self]
        have hlast_eq : verts[k]'(by omega) = aux.Q.tail (fr.fNode i) := by
          rw [List.getLast?_eq_getElem?] at hlast
          have hidx : verts.length - 1 = k := by omega
          rw [hidx, List.getElem?_eq_getElem (by omega)] at hlast
          exact Option.some.inj hlast
        have hfirst_eq : verts[0]'(by omega) = aux.Q.head (fr.fNode i) := by
          rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hhead
          exact Option.some.inj hhead
        have he_eq : eList[k]'(by simp [eList]; omega) = fr.fNode i := by
          simp only [eList]
          rw [List.getElem_append_right (by omega : edges.length ≤ k)]
          simp [hke]
        have hvw_eq : verts[(k + 1) % verts.length]'(Nat.mod_lt _ (by omega)) = aux.Q.head (fr.fNode i) := by
          simp only [hmod, hfirst_eq]
        dsimp only; rw [hvw_eq, hlast_eq, he_eq]
        exact Or.inl ⟨rfl, rfl⟩
    let C0 := directedCycleOfSimpleClosedWalk aux.Q verts eList (by omega)
      (by simp [eList]; omega) hv_nodup heList_nodup hclosed
    -- Check orientation on `fr.fNode i` and reverse if `-1`
    have hf_in_C0 : fr.fNode i ∈ C0.sub.edges := by
      simp [C0, directedCycleOfSimpleClosedWalk, eList]
    have hC0_sub_Te : C0.sub.edges ⊆ insert (fr.fNode i) fr.Te.edges := by
      intro e he
      simp only [C0, directedCycleOfSimpleClosedWalk, List.mem_toFinset, eList, List.mem_append,
        List.mem_singleton] at he
      rcases he with h | rfl
      · exact Finset.mem_insert_of_mem (Finset.mem_filter.mp (hedges_in e h)).1
      · exact Finset.mem_insert_self _ _
    have hC0_verts : C0.sub.verts ⊆ fr.stageV i := by
      intro v hv
      simp only [C0, directedCycleOfSimpleClosedWalk, List.mem_toFinset] at hv
      exact hverts_sub v hv
    rcases C0.sign_mem hf_in_C0 with hpos | hneg
    · exact ⟨C0, ⟨hC0_sub_Te, hpos⟩, hC0_verts⟩
    · exact ⟨C0.reverse, ⟨hC0_sub_Te, by simp [Multigraph.DirectedCycle.reverse, hneg]⟩, hC0_verts⟩
  -- Uniqueness of official cycle `C_i`
  have huniq_C : ∀ i : Fin fr.numNodes, ∀ C₁ C₂ : aux.Q.DirectedCycle,
      fr.IsOfficialCycle i C₁ → fr.IsOfficialCycle i C₂ → C₁ = C₂ := by
    intro i C₁ C₂ h1 h2
    have hdiff_flow : aux.Q.IsFlow (fun e => C₁.sign e - C₂.sign e) :=
      isFlow_sub C₁.isFlow C₂.isFlow
    have hdiff_supp : ∀ e, C₁.sign e - C₂.sign e ≠ 0 → e ∈ fr.Te.edges := by
      intro e hne
      by_cases hfi : e = fr.fNode i
      · subst hfi; exfalso; exact hne (by rw [h1.2, h2.2, sub_self])
      · by_cases h1e : e ∈ C₁.sub.edges
        · exact (Finset.mem_insert.mp (h1.1 h1e)).resolve_left hfi
        · by_cases h2e : e ∈ C₂.sub.edges
          · exact (Finset.mem_insert.mp (h2.1 h2e)).resolve_left hfi
          · exfalso; exact hne (by rw [C₁.sign_zero h1e, C₂.sign_zero h2e, sub_self])
    have hdiff_zero := flow_eq_zero_of_supp_subset_forest hTe_O1.1.2.1 hdiff_flow hdiff_supp
    have hsign_eq : C₁.sign = C₂.sign := funext fun e => sub_eq_zero.mp (hdiff_zero e)
    have hedges_eq : C₁.sub.edges = C₂.sub.edges := by
      ext e
      have hne1 : e ∈ C₁.sub.edges ↔ C₁.sign e ≠ 0 :=
        ⟨fun h => by rcases C₁.sign_mem h with h' | h' <;> omega,
         fun h => by by_contra hnot; exact h (C₁.sign_zero hnot)⟩
      have hne2 : e ∈ C₂.sub.edges ↔ C₂.sign e ≠ 0 :=
        ⟨fun h => by rcases C₂.sign_mem h with h' | h' <;> omega,
         fun h => by by_contra hnot; exact h (C₂.sign_zero hnot)⟩
      rw [hne1, hne2, hsign_eq]
    have hverts_eq : C₁.sub.verts = C₂.sub.verts := by
      ext v
      have hv_iff : ∀ C : aux.Q.DirectedCycle, v ∈ C.sub.verts ↔
          ∃ e ∈ C.sub.edges, aux.Q.tail e = v ∨ aux.Q.head e = v := fun C => by
        constructor
        · intro hv
          have hdeg := C.isCycle.2 v hv
          unfold Multigraph.Subgraph.deg at hdeg
          by_cases ht : 0 < (C.sub.edges.filter (fun e => aux.Q.tail e = v)).card
          · rcases Finset.card_pos.mp ht with ⟨e, he⟩
            exact ⟨e, (Finset.mem_filter.mp he).1, Or.inl (Finset.mem_filter.mp he).2⟩
          · have hh : 0 < (C.sub.edges.filter (fun e => aux.Q.head e = v)).card := by omega
            rcases Finset.card_pos.mp hh with ⟨e, he⟩
            exact ⟨e, (Finset.mem_filter.mp he).1, Or.inr (Finset.mem_filter.mp he).2⟩
        · rintro ⟨e, he, ht | hh⟩
          · exact ht ▸ C.sub.tail_mem he
          · exact hh ▸ C.sub.head_mem he
      rw [hv_iff C₁, hv_iff C₂, hedges_eq]
    exact Multigraph.DirectedCycle.ext (Multigraph.Subgraph.ext hverts_eq hedges_eq) hsign_eq
  have hex_uniq_C : ∀ i : Fin fr.numNodes, ∃! C : aux.Q.DirectedCycle, fr.IsOfficialCycle i C :=
    fun i => by
      obtain ⟨C, hC, _⟩ := hbuild_C i
      exact ⟨C, hC, fun C' hC' => huniq_C i C' C hC' hC⟩
  -- ===== Part (O6) =====
  have hO6 : fr.HProtected.Connected ∧
      (∀ v ∈ H.verts, (∀ t : sub.E₀, fr.IsFree t →
        ¬ (v ∈ (sub.thread t).verts ∧ v ≠ sub.embedV (sub.H₀.tail t) ∧ v ≠ sub.embedV (sub.H₀.head t))) →
        v ∈ fr.HProtected.verts) ∧
      (∀ eps : sub.E₀, fr.IsFree eps →
        ∃ D : G.DirectedCycle,
          D.sub ≤ H ∧
          (∀ e ∈ (sub.thread eps).edges, e ∈ D.sub.edges ∧ D.sign e = 1) ∧
          (∀ t : sub.E₀, fr.IsFree t → t ≠ eps →
            ∀ e ∈ (sub.thread t).edges, e ∉ D.sub.edges)) := by
    -- Step 1: Original blue edges span `sub.H₀` (connected on all `sub.V₀`)
    let H0P : sub.H₀.Subgraph :=
      Multigraph.Subgraph.ofEdges sub.H₀ Finset.univ (Finset.univ.filter (fun t => aux.origEdge t ∈ fr.blue))
        (fun _ => Finset.mem_univ _) (fun _ => Finset.mem_univ _)
    have hH0P_conn : ∀ u₀ v₀ : sub.V₀, Relation.ReflTransGen H0P.Adj u₀ v₀ := by
      have hH0_conn : sub.H₀.Connected := connected_of_edgeConnected (by omega) sub.edgeConn3
      intro u₀ v₀
      have hw := hH0_conn u₀ v₀
      induction hw with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ hstep ih =>
        refine Relation.ReflTransGen.trans ih ?_
        rcases hstep with ⟨t, hadj⟩
        -- Endpoints of `origEdge t` lie in one component `Qb b`, connected by blue spanning tree!
        let b := aux.comp (aux.Q.tail (aux.origEdge t))
        obtain ⟨wc, hwc_iff⟩ := fr.comp_wc b
        let Vb : Finset aux.VQ := Finset.univ.filter (fun v => aux.comp v = b)
        let xt : {v : aux.VQ // v ∈ (Multigraph.Subgraph.induced aux.Q Vb).verts} :=
          ⟨aux.Q.tail (aux.origEdge t), Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
        let xh : {v : aux.VQ // v ∈ (Multigraph.Subgraph.induced aux.Q Vb).verts} :=
          ⟨aux.Q.head (aux.origEdge t), Finset.mem_filter.mpr ⟨Finset.mem_univ _, (aux.edge_same_comp _).symm⟩⟩
        have hblue_walk := wc.blue_tree.2.1.2 xt (Finset.mem_univ _) xh (Finset.mem_univ _)
        have hproj_gen : ∀ a b : {v : aux.VQ // v ∈ (Multigraph.Subgraph.induced aux.Q Vb).verts},
            Relation.ReflTransGen (Multigraph.Subgraph.ofEdges
              (Multigraph.Subgraph.induced aux.Q Vb).toMultigraph Finset.univ wc.blue
              (fun _ => Finset.mem_univ _) (fun _ => Finset.mem_univ _)).Adj a b →
            Relation.ReflTransGen H0P.Adj (aux.contractV a.1) (aux.contractV b.1) := by
          intro a b hab
          induction hab with
          | refl => exact Relation.ReflTransGen.refl
          | tail _ hst ihw =>
            rcases hst with ⟨e, heblue, headj⟩
            have he_fr : e.1 ∈ fr.blue := (hwc_iff e).mp heblue
            by_cases hex : ∃ t' : sub.E₀, aux.origEdge t' = e.1
            · rcases hex with ⟨t', ht'⟩
              have ht'_in : t' ∈ H0P.edges := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht' ▸ he_fr⟩
              refine Relation.ReflTransGen.tail ihw ⟨t', ht'_in, ?_⟩
              rcases headj with ⟨h1, h2⟩ | ⟨h1, h2⟩
              · left
                exact ⟨(aux.orig_tail t').symm.trans (congrArg aux.contractV (ht'.symm ▸ congrArg Subtype.val h1)),
                       (aux.orig_head t').symm.trans (congrArg aux.contractV (ht'.symm ▸ congrArg Subtype.val h2))⟩
              · right
                exact ⟨(aux.orig_tail t').symm.trans (congrArg aux.contractV (ht'.symm ▸ congrArg Subtype.val h1)),
                       (aux.orig_head t').symm.trans (congrArg aux.contractV (ht'.symm ▸ congrArg Subtype.val h2))⟩
            · push Not at hex
              have hsame : aux.contractV (aux.Q.tail e.1) = aux.contractV (aux.Q.head e.1) :=
                aux.exp_same_contractV e.1 hex
              rcases headj with ⟨h1, h2⟩ | ⟨h1, h2⟩
              · have heq : aux.contractV _ = aux.contractV _ :=
                  (congrArg aux.contractV (congrArg Subtype.val h1)).symm.trans
                    (hsame.trans (congrArg aux.contractV (congrArg Subtype.val h2)))
                exact heq ▸ ihw
              · have heq : aux.contractV _ = aux.contractV _ :=
                  (congrArg aux.contractV (congrArg Subtype.val h2)).symm.trans
                    (hsame.symm.trans (congrArg aux.contractV (congrArg Subtype.val h1)))
                exact heq ▸ ihw
        have hproj := hproj_gen xt xh hblue_walk
        dsimp only [xt, xh] at hproj
        rw [aux.orig_tail t, aux.orig_head t] at hproj
        rcases hadj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hproj
        · exact subgraph_adj_symm hproj
    -- Every vertex of `sub.V₀` is incident to some original blue edge (since `2 ≤ |V₀|`)
    have hbranch_mem_HP : ∀ v₀ : sub.V₀, sub.embedV v₀ ∈ fr.HProtected.verts := by
      intro v₀
      have hcard2 := sub.card_ge_two
      obtain ⟨a, b, hab⟩ := Fintype.one_lt_card_iff.mp (by omega : 1 < Fintype.card sub.V₀)
      let w₀ := if v₀ = a then b else a
      have hw₀ : w₀ ≠ v₀ := by
        dsimp only [w₀]; split_ifs with h
        · exact fun h' => hab (h.symm.trans h'.symm)
        · exact fun h' => h h'.symm
      have hw := hH0P_conn v₀ w₀
      generalize hw_def : w₀ = w at hw hw₀
      cases hw using Relation.ReflTransGen.head_induction_on with
      | refl => exact absurd rfl hw₀
      | head hstep _ =>
        rcases hstep with ⟨t, htP, ht | hh⟩
        · have htb : aux.origEdge t ∈ fr.blue := (Finset.mem_filter.mp htP).2
          have hv_in : sub.embedV v₀ ∈ (sub.thread t).verts := by
            have hh0 := (sub.thread t).head_eq
            rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by have := (sub.thread t).verts_len; have := (sub.thread t).len_pos; omega)] at hh0
            have hveq : sub.embedV v₀ = (sub.thread t).verts[0]'(by have := (sub.thread t).verts_len; have := (sub.thread t).len_pos; omega) :=
              (congrArg sub.embedV ht.1.symm).trans (Option.some.inj hh0).symm
            rw [hveq]; exact List.getElem_mem _
          exact Finset.mem_filter.mpr ⟨sub.embedV_mem v₀, t, htb, hv_in⟩
        · have htb : aux.origEdge t ∈ fr.blue := (Finset.mem_filter.mp htP).2
          have hv_in : sub.embedV v₀ ∈ (sub.thread t).verts := by
            have hl0 := (sub.thread t).last_eq
            rw [List.getLast?_eq_getElem?] at hl0
            have hidx : (sub.thread t).verts.length - 1 = (sub.thread t).edges.length := by
              have := (sub.thread t).verts_len; omega
            rw [hidx, List.getElem?_eq_getElem (by have := (sub.thread t).verts_len; omega)] at hl0
            have hveq : sub.embedV v₀ = (sub.thread t).verts[(sub.thread t).edges.length]'(by have := (sub.thread t).verts_len; omega) :=
              (congrArg sub.embedV hh.2.symm).trans (Option.some.inj hl0).symm
            rw [hveq]; exact List.getElem_mem _
          exact Finset.mem_filter.mpr ⟨sub.embedV_mem v₀, t, htb, hv_in⟩
    -- Along any protected thread `t`, every vertex `v ∈ (sub.thread t).verts` is connected in `fr.HProtected` to `embedV (tail t)` and `embedV (head t)`!
    have hthread_reach : ∀ (t : sub.E₀), aux.origEdge t ∈ fr.blue →
        ∀ (k : ℕ) (hk : k < (sub.thread t).verts.length),
          Relation.ReflTransGen fr.HProtected.Adj
            (sub.embedV (sub.H₀.tail t)) ((sub.thread t).verts[k]'hk) := by
      intro t htb k
      induction k with
      | zero =>
        intro hk
        have hh0 := (sub.thread t).head_eq
        rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hk] at hh0
        rw [Option.some.inj hh0]
      | succ k ihk =>
        intro hk
        have hlen := (sub.thread t).verts_len
        have hk_e : k < (sub.thread t).edges.length := by omega
        have hal := aux.thread_aligned t k hk_e
        have he_in : (sub.thread t).edges[k]'hk_e ∈ fr.HProtected.edges :=
          Finset.mem_filter.mpr ⟨(sub.thread t).edges_sub _ (List.getElem_mem hk_e), t, htb, List.getElem_mem hk_e⟩
        exact Relation.ReflTransGen.tail (ihk (by omega)) ⟨_, he_in, Or.inl ⟨hal.1, hal.2⟩⟩
    have hthread_ends : ∀ (t : sub.E₀), aux.origEdge t ∈ fr.blue →
        Relation.ReflTransGen fr.HProtected.Adj
          (sub.embedV (sub.H₀.tail t)) (sub.embedV (sub.H₀.head t)) := by
      intro t htb
      have hlen := (sub.thread t).verts_len
      have hl0 := (sub.thread t).last_eq
      rw [List.getLast?_eq_getElem?] at hl0
      have hidx : (sub.thread t).verts.length - 1 = (sub.thread t).edges.length := by omega
      rw [hidx, List.getElem?_eq_getElem (by omega)] at hl0
      rw [← Option.some.inj hl0]
      exact hthread_reach t htb (sub.thread t).edges.length (by omega)
    have hbranch_reach : ∀ u₀ v₀ : sub.V₀,
        Relation.ReflTransGen fr.HProtected.Adj (sub.embedV u₀) (sub.embedV v₀) := by
      intro u₀ v₀
      have hw := hH0P_conn u₀ v₀
      induction hw with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ hstep ih =>
        rcases hstep with ⟨t, htP, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
        · exact Relation.ReflTransGen.trans ih (hthread_ends t (Finset.mem_filter.mp htP).2)
        · exact Relation.ReflTransGen.trans ih (subgraph_adj_symm (hthread_ends t (Finset.mem_filter.mp htP).2))
    have hHP_conn : fr.HProtected.Connected := by
      obtain ⟨v₀⟩ := Fintype.card_pos_iff.mp (by have := sub.card_ge_two; omega : 0 < Fintype.card sub.V₀)
      refine ⟨⟨sub.embedV v₀, hbranch_mem_HP v₀⟩, fun u hu v hv => ?_⟩
      rcases (Finset.mem_filter.mp hu).2 with ⟨tu, htu_b, hu_mem⟩
      rcases (Finset.mem_filter.mp hv).2 with ⟨tv, htv_b, hv_mem⟩
      obtain ⟨ku, hku, rfl⟩ := List.getElem_of_mem hu_mem
      obtain ⟨kv, hkv, rfl⟩ := List.getElem_of_mem hv_mem
      exact Relation.ReflTransGen.trans
        (subgraph_adj_symm (hthread_reach tu htu_b ku hku))
        (Relation.ReflTransGen.trans
          (hbranch_reach (sub.H₀.tail tu) (sub.H₀.tail tv))
          (hthread_reach tv htv_b kv hkv))
    have hHP_cover : ∀ v ∈ H.verts, (∀ t : sub.E₀, fr.IsFree t →
        ¬ (v ∈ (sub.thread t).verts ∧ v ≠ sub.embedV (sub.H₀.tail t) ∧ v ≠ sub.embedV (sub.H₀.head t))) →
        v ∈ fr.HProtected.verts := by
      intro v hvH hnotfree
      rcases sub.verts_cover v hvH with ⟨v₀, rfl⟩ | ⟨t, hvt⟩
      · exact hbranch_mem_HP v₀
      · by_cases htb : aux.origEdge t ∈ fr.blue
        · exact Finset.mem_filter.mpr ⟨hvH, t, htb, hvt⟩
        · by_cases ht1 : v = sub.embedV (sub.H₀.tail t)
          · exact ht1 ▸ hbranch_mem_HP (sub.H₀.tail t)
          · by_cases ht2 : v = sub.embedV (sub.H₀.head t)
            · exact ht2 ▸ hbranch_mem_HP (sub.H₀.head t)
            · exact absurd ⟨hvt, ht1, ht2⟩ (hnotfree t htb)
    -- Step 2: Free-edge cycle `D_eps` via fundamental cycle in blue tree `T_b` + `lem_3_6_d`!
    have hfree_cycle : ∀ eps : sub.E₀, fr.IsFree eps →
        ∃ D : G.DirectedCycle,
          D.sub ≤ H ∧
          (∀ e ∈ (sub.thread eps).edges, e ∈ D.sub.edges ∧ D.sign e = 1) ∧
          (∀ t : sub.E₀, fr.IsFree t → t ≠ eps →
            ∀ e ∈ (sub.thread t).edges, e ∉ D.sub.edges) := by
      intro eps heps_free
      let b := aux.comp (aux.Q.tail (aux.origEdge eps))
      obtain ⟨wc, hwc_iff⟩ := fr.comp_wc b
      let Vb : Finset aux.VQ := Finset.univ.filter (fun v => aux.comp v = b)
      let Qb := (Multigraph.Subgraph.induced aux.Q Vb).toMultigraph
      have heps_noloop : aux.Q.tail (aux.origEdge eps) ≠ aux.Q.head (aux.origEdge eps) := fun h =>
        sub.loopless eps ((aux.orig_tail eps).symm.trans (congrArg aux.contractV h |>.trans (aux.orig_head eps)))
      -- Build fundamental cycle `C_eps` of `aux.origEdge eps` in the blue spanning tree of `Q_b`
      let xt : {v : aux.VQ // v ∈ (Multigraph.Subgraph.induced aux.Q Vb).verts} :=
        ⟨aux.Q.tail (aux.origEdge eps), Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
      let xh : {v : aux.VQ // v ∈ (Multigraph.Subgraph.induced aux.Q Vb).verts} :=
        ⟨aux.Q.head (aux.origEdge eps), Finset.mem_filter.mpr ⟨Finset.mem_univ _, (aux.edge_same_comp _).symm⟩⟩
      obtain ⟨verts, edges, hlen, hv_nodup, hhead, hlast, hedges_blue, hstep⟩ :=
        exists_simplePath_of_reflTransGen (wc.blue_tree.2.1.2 xh (Finset.mem_univ _) xt (Finset.mem_univ _))
      have hedges_pos : 1 ≤ edges.length := by
        by_contra h0
        have he0 : edges.length = 0 := by omega
        have h1 : verts[0]'(by omega) = xh := by
          rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hhead
          exact Option.some.inj hhead
        have h2 : verts[0]'(by omega) = xt := by
          rw [List.getLast?_eq_getElem?] at hlast
          have hidx : verts.length - 1 = 0 := by omega
          rw [hidx, List.getElem?_eq_getElem (by omega)] at hlast
          exact Option.some.inj hlast
        exact heps_noloop (congrArg Subtype.val (h2.symm.trans h1))
      have hpe_nodup := simplePath_edges_nodup hv_nodup hlen hstep
      let vList : List aux.VQ := verts.map Subtype.val
      let eList : List aux.EQ := edges.map Subtype.val ++ [aux.origEdge eps]
      have hvList_nodup : vList.Nodup := hv_nodup.map Subtype.val_injective
      have heps_not_blue_edges : aux.origEdge eps ∉ edges.map Subtype.val := by
        intro hmem
        rcases List.mem_map.mp hmem with ⟨e', he', heq⟩
        exact heps_free (heq ▸ (hwc_iff e').mp (hedges_blue e' he'))
      have heList_nodup : eList.Nodup := by
        rw [List.nodup_append]
        refine ⟨hpe_nodup.map Subtype.val_injective, List.nodup_singleton _, fun e he e' he' => ?_⟩
        rw [List.mem_singleton.mp he']; exact fun h => heps_not_blue_edges (h ▸ he)
      have hclosed : ∀ (k : ℕ) (hk : k < eList.length),
          let u := vList[k]'(by simp [vList, eList] at hk ⊢; omega)
          let w := vList[(k + 1) % vList.length]'(Nat.mod_lt _ (by simp [vList]; omega))
          let e := eList[k]'hk
          (aux.Q.tail e = u ∧ aux.Q.head e = w) ∨ (aux.Q.tail e = w ∧ aux.Q.head e = u) := by
        intro k hk
        simp only [eList, List.length_append, List.length_map, List.length_singleton] at hk
        by_cases hlt : k < edges.length
        · have hmod : (k + 1) % vList.length = k + 1 := Nat.mod_eq_of_lt (by simp [vList]; omega)
          have hlt' : k < (edges.map Subtype.val).length := by simp [hlt]
          simp only [eList, vList, List.getElem_append_left hlt', List.getElem_map, hmod]
          rcases hstep k hlt with ⟨ht, hh⟩ | ⟨ht, hh⟩
          · exact Or.inl ⟨congrArg Subtype.val ht, congrArg Subtype.val hh⟩
          · exact Or.inr ⟨congrArg Subtype.val ht, congrArg Subtype.val hh⟩
        · have hke : k = edges.length := by omega
          have hmod : (k + 1) % vList.length = 0 := by
            have : k + 1 = vList.length := by simp [vList]; omega
            rw [this, Nat.mod_self]
          have hlast_eq : vList[k]'(by simp [vList]; omega) = aux.Q.tail (aux.origEdge eps) := by
            simp only [vList, List.getElem_map]
            rw [List.getLast?_eq_getElem?] at hlast
            have hidx : verts.length - 1 = k := by omega
            rw [hidx, List.getElem?_eq_getElem (by omega)] at hlast
            exact congrArg Subtype.val (Option.some.inj hlast)
          have hfirst_eq : vList[0]'(by simp [vList]; omega) = aux.Q.head (aux.origEdge eps) := by
            simp only [vList, List.getElem_map]
            rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hhead
            exact congrArg Subtype.val (Option.some.inj hhead)
          have he_eq : eList[k]'(by simp [eList]; omega) = aux.origEdge eps := by
            simp only [eList]
            rw [List.getElem_append_right (by simp; omega)]
            simp [hke]
          have hvw_eq : vList[(k + 1) % vList.length]'(Nat.mod_lt _ (by simp [vList]; omega)) = aux.Q.head (aux.origEdge eps) := by
            simp only [hmod, hfirst_eq]
          dsimp only; rw [hvw_eq, hlast_eq, he_eq]
          exact Or.inl ⟨rfl, rfl⟩
      let Ce0 := directedCycleOfSimpleClosedWalk aux.Q vList eList (by simp [vList]; omega)
        (by simp [vList, eList]; omega) hvList_nodup heList_nodup hclosed
      have heps_in_Ce0 : aux.origEdge eps ∈ Ce0.sub.edges := by
        simp [Ce0, directedCycleOfSimpleClosedWalk, eList]
      let Ce : aux.Q.DirectedCycle :=
        if Ce0.sign (aux.origEdge eps) = 1 then Ce0 else Ce0.reverse
      have hCe_eps : Ce.sign (aux.origEdge eps) = 1 := by
        dsimp only [Ce]; split_ifs with h1
        · exact h1
        · rcases Ce0.sign_mem heps_in_Ce0 with h | h
          · exact absurd h h1
          · simp [Multigraph.DirectedCycle.reverse, h]
      have hCe_other_blue : ∀ eq ∈ Ce.sub.edges, eq ≠ aux.origEdge eps → eq ∈ fr.blue := by
        intro eq heq hne
        have heq0 : eq ∈ Ce0.sub.edges := by
          dsimp only [Ce] at heq; split_ifs at heq <;> exact heq
        simp only [Ce0, directedCycleOfSimpleClosedWalk, List.mem_toFinset, eList, List.mem_append,
          List.mem_map, List.mem_singleton] at heq0
        rcases heq0 with ⟨e', he', rfl⟩ | rfl
        · exact (hwc_iff e').mp (hedges_blue e' he')
        · exact absurd rfl hne
      -- Apply `lem_3_6_d` at `A = ℤ` to `Ce`!
      obtain ⟨cycles, hcyc_le, hcyc_disj, hcyc_sum⟩ := lem_3_6_d (A := ℤ) sub aux Ce
      -- Pick the first edge `e₀` of `sub.thread eps`
      let e₀ := (sub.thread eps).edges[0]'(by have := (sub.thread eps).len_pos; omega)
      have he₀_mem : e₀ ∈ (sub.thread eps).edges := List.getElem_mem _
      have hpi_thread : ∀ (t : sub.E₀) (e : E), e ∈ (sub.thread t).edges →
          aux.pi (fun eq => Ce.sign eq • (1 : ℤ)) e = Ce.sign (aux.origEdge t) := by
        intro t e het
        have hex : ∃ t' : sub.E₀, e ∈ (sub.thread t').edges := ⟨t, het⟩
        simp only [AuxGraphData.pi, hex, ↓reduceDIte, smul_eq_mul, mul_one]
        congr 2; by_contra hne
        exact sub.edges_disjoint _ t hne e hex.choose_spec het
      have hsum_e0 : (cycles.map (fun O => O.sign e₀)).sum = 1 := by
        have h1 := hcyc_sum (1 : ℤ) e₀
        rw [hpi_thread eps e₀ he₀_mem, hCe_eps] at h1
        simpa only [smul_eq_mul, mul_one] using h1.symm
      -- Find `D ∈ cycles` with `e₀ ∈ D.sub.edges` (exists since sum is `1 ≠ 0`)
      have hex_D : ∃ idx : Fin cycles.length, e₀ ∈ (cycles[idx.1]'idx.2).sub.edges := by
        by_contra hall; push Not at hall
        have hz : ∀ x ∈ cycles.map (fun O => O.sign e₀), x = 0 := by
          intro x hx
          rcases List.mem_map.mp hx with ⟨O, hO, rfl⟩
          obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hO
          exact (cycles[k]'hk).sign_zero (hall ⟨k, hk⟩)
        rw [List.sum_eq_zero hz] at hsum_e0; omega
      obtain ⟨idxD, hidxD⟩ := hex_D
      let D := cycles[idxD.1]'idxD.2
      have hD_mem : D ∈ cycles := List.getElem_mem idxD.2
      -- Helper: for any edge `e`, if `e ∈ O.sub.edges` for `O = cycles[k]`, then `(cycles.map (fun O => O.sign e)).sum = O.sign e`!
      have hsum_single : ∀ (e : E) (k : Fin cycles.length), e ∈ (cycles[k.1]'k.2).sub.edges →
          (cycles.map (fun O => O.sign e)).sum = (cycles[k.1]'k.2).sign e := by
        intro e k hk
        have hlist_sum : ∀ (l : List G.DirectedCycle) (m : ℕ) (hm : m < l.length),
            (∀ j (hj : j < l.length), j ≠ m → (l[j]'hj).sign e = 0) →
            (l.map (fun O => O.sign e)).sum = (l[m]'hm).sign e := by
          intro l
          induction l with
          | nil => intro m hm; simp at hm
          | cons a tl ih =>
            intro m hm hall
            cases m with
            | zero =>
              simp only [List.map_cons, List.sum_cons, List.getElem_cons_zero]
              have htl0 : (tl.map (fun O => O.sign e)).sum = 0 := by
                apply List.sum_eq_zero
                intro x hx
                rcases List.mem_map.mp hx with ⟨O, hO, rfl⟩
                obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hO
                exact hall (j + 1) (by simp; omega) (by omega)
              omega
            | succ m =>
              simp only [List.map_cons, List.sum_cons, List.getElem_cons_succ]
              have ha0 : a.sign e = 0 := hall 0 (by simp) (by omega)
              have htl := ih m (by simp at hm; omega) (fun j hj hne =>
                hall (j + 1) (by simp; omega) (by omega))
              omega
        exact hlist_sum cycles k.1 k.2 (fun j hj hne =>
          (cycles[j]'hj).sign_zero (Finset.disjoint_right.mp (hcyc_disj j k.1 hj k.2 hne) hk))
      have hD_e0_sign : D.sign e₀ = 1 := by
        rw [← hsum_single e₀ idxD hidxD, hsum_e0]
      -- Pull `D` down to `H.toMultigraph.DirectedCycle` to apply `lem_3_6_a` (constant sign on threads)!
      have hD_le : D.sub ≤ H := hcyc_le D hD_mem
      let D_H : H.toMultigraph.DirectedCycle :=
        { sub :=
            { verts := Finset.univ.filter (fun v => v.1 ∈ D.sub.verts)
              edges := Finset.univ.filter (fun e => e.1 ∈ D.sub.edges)
              tail_mem := fun {e} he => Finset.mem_filter.mpr ⟨Finset.mem_univ _, D.sub.tail_mem (Finset.mem_filter.mp he).2⟩
              head_mem := fun {e} he => Finset.mem_filter.mpr ⟨Finset.mem_univ _, D.sub.head_mem (Finset.mem_filter.mp he).2⟩ }
          isCycle := by
            refine ⟨⟨?_, ?_⟩, ?_⟩
            · rcases D.isCycle.1.1 with ⟨v, hv⟩
              exact ⟨⟨v, hD_le.1 hv⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩⟩
            · intro u hu v hv
              have hw := D.isCycle.1.2 u.1 (Finset.mem_filter.mp hu).2 v.1 (Finset.mem_filter.mp hv).2
              have hl : ∀ {x y : V} (hx : x ∈ D.sub.verts), Relation.ReflTransGen D.sub.Adj x y →
                  ∃ hy : y ∈ D.sub.verts, Relation.ReflTransGen
                    ({ verts := Finset.univ.filter (fun v : {v // v ∈ H.verts} => v.1 ∈ D.sub.verts)
                       edges := Finset.univ.filter (fun e : {e // e ∈ H.edges} => e.1 ∈ D.sub.edges)
                       tail_mem := fun {e} he => Finset.mem_filter.mpr ⟨Finset.mem_univ _, D.sub.tail_mem (Finset.mem_filter.mp he).2⟩
                       head_mem := fun {e} he => Finset.mem_filter.mpr ⟨Finset.mem_univ _, D.sub.head_mem (Finset.mem_filter.mp he).2⟩ } : H.toMultigraph.Subgraph).Adj
                    ⟨x, hD_le.1 hx⟩ ⟨y, hD_le.1 hy⟩ := by
                intro x y hx hxy
                induction hxy with
                | refl => exact ⟨hx, Relation.ReflTransGen.refl⟩
                | @tail w z _ hstep ih =>
                  rcases ih with ⟨hwD, hwalk⟩
                  rcases hstep with ⟨e, heD, hadj⟩
                  have hzD : z ∈ D.sub.verts := by
                    rcases hadj with ⟨_, rfl⟩ | ⟨rfl, _⟩ <;> [exact D.sub.head_mem heD; exact D.sub.tail_mem heD]
                  refine ⟨hzD, Relation.ReflTransGen.tail hwalk
                    ⟨⟨e, hD_le.2 heD⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, heD⟩, ?_⟩⟩
                  rcases hadj with ⟨ht, hh⟩ | ⟨ht, hh⟩
                  · exact Or.inl ⟨Subtype.ext ht, Subtype.ext hh⟩
                  · exact Or.inr ⟨Subtype.ext ht, Subtype.ext hh⟩
              exact (hl (Finset.mem_filter.mp hu).2 hw).2
            · intro u hu
              have hdeg := D.isCycle.2 u.1 (Finset.mem_filter.mp hu).2
              unfold Multigraph.Subgraph.deg at hdeg ⊢
              have ht_eq : ((Finset.univ.filter (fun e : {e // e ∈ H.edges} => e.1 ∈ D.sub.edges)).filter
                  (fun e => H.toMultigraph.tail e = u)).card =
                  (D.sub.edges.filter (fun e => G.tail e = u.1)).card := by
                refine Finset.card_bij (fun e _ => e.1)
                  (fun e he => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2,
                    congrArg Subtype.val (Finset.mem_filter.mp he).2⟩)
                  (fun _ _ _ _ h => Subtype.ext h)
                  (fun e he => ⟨⟨e, hD_le.2 (Finset.mem_filter.mp he).1⟩,
                    Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp he).1⟩,
                      Subtype.ext (Finset.mem_filter.mp he).2⟩, rfl⟩)
              have hh_eq : ((Finset.univ.filter (fun e : {e // e ∈ H.edges} => e.1 ∈ D.sub.edges)).filter
                  (fun e => H.toMultigraph.head e = u)).card =
                  (D.sub.edges.filter (fun e => G.head e = u.1)).card := by
                refine Finset.card_bij (fun e _ => e.1)
                  (fun e he => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2,
                    congrArg Subtype.val (Finset.mem_filter.mp he).2⟩)
                  (fun _ _ _ _ h => Subtype.ext h)
                  (fun e he => ⟨⟨e, hD_le.2 (Finset.mem_filter.mp he).1⟩,
                    Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp he).1⟩,
                      Subtype.ext (Finset.mem_filter.mp he).2⟩, rfl⟩)
              rw [ht_eq, hh_eq]; exact hdeg
          sign := fun e => D.sign e.1
          sign_mem := fun {e} he => D.sign_mem (Finset.mem_filter.mp he).2
          sign_zero := fun {e} he => D.sign_zero (fun h => he (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
          isFlow := fun u => by
            calc H.toMultigraph.boundary (fun e => D.sign e.1) u
                = G.boundary D.sign u.1 := by
                  rw [boundary_eq_sum_ite, boundary_eq_sum_ite]
                  symm
                  rw [← Finset.sum_subset (Finset.subset_univ H.edges)]
                  · refine Finset.sum_bij (fun e he => ⟨e, he⟩) (fun _ _ => Finset.mem_univ _)
                      (fun _ _ _ _ h => congrArg Subtype.val h)
                      (fun e _ => ⟨e.1, e.2, rfl⟩)
                      (fun e _ => by cases u; simp [Multigraph.Subgraph.toMultigraph])
                  · intro e _ hnot
                    have h0 : D.sign e = 0 := D.sign_zero (fun h => hnot (hD_le.2 h))
                    simp [h0]
              _ = 0 := D.isFlow u.1 }
      obtain ⟨s, _, hs⟩ := (lem_3_6_a (A := ℤ) sub aux).1 D_H eps
      have hs1 : s = 1 := (hs e₀ he₀_mem).symm.trans hD_e0_sign
      refine ⟨D, hD_le, fun e he => ?_, fun t ht_free ht_ne e het => ?_⟩
      · have hse : D.sign e = 1 := (hs e he).trans hs1
        exact ⟨by by_contra hnot; have := D.sign_zero hnot; omega, hse⟩
      · intro heD
        have hsum_t : (cycles.map (fun O => O.sign e)).sum = D.sign e := hsum_single e idxD heD
        have hpi_t := hcyc_sum (1 : ℤ) e
        rw [hpi_thread t e het] at hpi_t
        have hnot_Ce : aux.origEdge t ∉ Ce.sub.edges := fun hmem =>
          ht_free (hCe_other_blue (aux.origEdge t) hmem (fun h => ht_ne (aux.origEdge.injective h)))
        rw [Ce.sign_zero hnot_Ce] at hpi_t
        simp only [smul_eq_mul, mul_one] at hpi_t
        have hD0 : D.sign e = 0 := hsum_t.symm.trans hpi_t.symm
        rcases D.sign_mem heD with h | h <;> omega
    exact ⟨hHP_conn, hHP_cover, hfree_cycle⟩
  -- Assemble all parts of `lem_3_11`!
  refine ⟨hO1, hex_uniq_C, ?_, hO6⟩
  intro C hC
  have hC_verts : ∀ i, (C i).sub.verts ⊆ fr.stageV i := fun i => by
    obtain ⟨C0, hC0, hV0⟩ := hbuild_C i
    rw [huniq_C i (C i) C0 (hC i) hC0]; exact hV0
  -- (O2)
  have hO2 : ∀ i, (C i).sub.verts ⊆ fr.stageV i ∧
      fr.eNode i ∈ (C i).sub.edges ∧ fr.fNode i ∈ (C i).sub.edges := by
    intro i
    have hf_mem : fr.fNode i ∈ (C i).sub.edges := by
      by_contra hnot; have := (C i).sign_zero hnot; have := (hC i).2; omega
    have he_mem : fr.eNode i ∈ (C i).sub.edges := by
      by_contra hnot
      have hcut0 : ∑ v ∈ fr.op1V i, aux.Q.boundary (C i).sign v = 0 :=
        Finset.sum_eq_zero (fun v _ => (C i).isFlow v)
      rw [sum_boundary_eq_cut] at hcut0
      -- Any edge `eq` crossing `op1V i` with `(C i).sign eq ≠ 0` must lie in `Q[stageV i]` hence cross `(op1V i, op2V i)`, hence `= fNode i`!
      have honly_f : ∀ eq : aux.EQ, (C i).sign eq ≠ 0 →
          ((aux.Q.head eq ∈ fr.op1V i ∧ aux.Q.tail eq ∉ fr.op1V i) ∨
           (aux.Q.tail eq ∈ fr.op1V i ∧ aux.Q.head eq ∉ fr.op1V i)) →
          eq = fr.fNode i := by
        intro eq hne hcr
        have heqC : eq ∈ (C i).sub.edges := by
          by_contra h0; exact hne ((C i).sign_zero h0)
        have ht_st : aux.Q.tail eq ∈ fr.stageV i := hC_verts i ((C i).sub.tail_mem heqC)
        have hh_st : aux.Q.head eq ∈ fr.stageV i := hC_verts i ((C i).sub.head_mem heqC)
        rw [fr.stage_union i] at ht_st hh_st
        have hcr12 : (aux.Q.tail eq ∈ fr.op1V i ∧ aux.Q.head eq ∈ fr.op2V i) ∨
            (aux.Q.tail eq ∈ fr.op2V i ∧ aux.Q.head eq ∈ fr.op1V i) := by
          rcases hcr with ⟨hh1, htnot1⟩ | ⟨ht1, hhnot1⟩
          · exact Or.inr ⟨(Finset.mem_union.mp ht_st).resolve_left htnot1, hh1⟩
          · exact Or.inl ⟨ht1, (Finset.mem_union.mp hh_st).resolve_left hhnot1⟩
        exact (fr.stage_crossing_only i eq hcr12).resolve_left (fun h => hnot (h ▸ heqC))
      rcases fr.f_cross i with ⟨htf, hhf⟩ | ⟨htf, hhf⟩
      · have hhf_not : aux.Q.head (fr.fNode i) ∉ fr.op1V i :=
          Finset.disjoint_right.mp (fr.stage_disj i) hhf
        have hsum1 : ∑ eq ∈ Finset.univ.filter (fun eq => aux.Q.head eq ∈ fr.op1V i ∧ aux.Q.tail eq ∉ fr.op1V i),
            (C i).sign eq = 0 := Finset.sum_eq_zero (fun eq heq => by
          by_contra hne
          have hfeq := honly_f eq hne (Or.inl (Finset.mem_filter.mp heq).2)
          exact hhf_not (hfeq ▸ (Finset.mem_filter.mp heq).2.1))
        have hsum2 : ∑ eq ∈ Finset.univ.filter (fun eq => aux.Q.tail eq ∈ fr.op1V i ∧ aux.Q.head eq ∉ fr.op1V i),
            (C i).sign eq = (C i).sign (fr.fNode i) := by
          rw [Finset.sum_eq_single (fr.fNode i)]
          · intro eq heq hne_f
            by_contra hne
            exact hne_f (honly_f eq hne (Or.inr (Finset.mem_filter.mp heq).2))
          · intro hnot_in
            exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, htf, hhf_not⟩) hnot_in
        rw [hsum1, hsum2, (hC i).2] at hcut0; omega
      · have htf_not : aux.Q.tail (fr.fNode i) ∉ fr.op1V i :=
          Finset.disjoint_right.mp (fr.stage_disj i) htf
        have hsum1 : ∑ eq ∈ Finset.univ.filter (fun eq => aux.Q.head eq ∈ fr.op1V i ∧ aux.Q.tail eq ∉ fr.op1V i),
            (C i).sign eq = (C i).sign (fr.fNode i) := by
          rw [Finset.sum_eq_single (fr.fNode i)]
          · intro eq heq hne_f
            by_contra hne
            exact hne_f (honly_f eq hne (Or.inl (Finset.mem_filter.mp heq).2))
          · intro hnot_in
            exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hhf, htf_not⟩) hnot_in
        have hsum2 : ∑ eq ∈ Finset.univ.filter (fun eq => aux.Q.tail eq ∈ fr.op1V i ∧ aux.Q.head eq ∉ fr.op1V i),
            (C i).sign eq = 0 := Finset.sum_eq_zero (fun eq heq => by
          by_contra hne
          have hfeq := honly_f eq hne (Or.inr (Finset.mem_filter.mp heq).2)
          exact htf_not (hfeq ▸ (Finset.mem_filter.mp heq).2.1))
        rw [hsum1, hsum2, (hC i).2] at hcut0; omega
    exact ⟨hC_verts i, he_mem, hf_mem⟩
  -- (O3)
  have hO3 : ∀ l i : Fin fr.numNodes, l < i →
      fr.eNode i ∉ (C l).sub.edges ∧ fr.fNode i ∉ (C l).sub.edges := by
    intro l i hli
    constructor
    · intro hmem
      obtain ⟨j, hjle, hje⟩ := fr.stage_blue_topo l (fr.eNode i) (fr.e_blue i)
        (hC_verts l ((C l).sub.tail_mem hmem)) (hC_verts l ((C l).sub.head_mem hmem))
      have hij : i = j := by
        rcases hje with h | h
        · exact hnode_inj i j (Or.inl h)
        · exact hnode_inj i j (Or.inr (Or.inl h))
      subst hij; exact not_lt.mpr hjle hli
    · intro hmem
      obtain ⟨j, hjle, hje⟩ := fr.stage_blue_topo l (fr.fNode i) (fr.f_blue i)
        (hC_verts l ((C l).sub.tail_mem hmem)) (hC_verts l ((C l).sub.head_mem hmem))
      have hij : i = j := by
        rcases hje with h | h
        · exact hnode_inj i j (Or.inr (Or.inr (Or.inl h)))
        · exact hnode_inj i j (Or.inr (Or.inr (Or.inr h)))
      subst hij; exact not_lt.mpr hjle hli
  -- (O4)
  have hO4 : ∀ l i : Fin fr.numNodes, i < l → fr.fNode i ∉ (C l).sub.edges := by
    intro l i hil hmem
    rcases Finset.mem_insert.mp ((hC l).1 hmem) with hfeq | hTe
    · have := hnode_inj i l (Or.inr (Or.inr (Or.inr hfeq))); subst this; exact lt_irrefl _ hil
    · exact hf_not_Te i hTe
  -- (O5)
  have hO5 : ∀ Y : aux.EQ → A, aux.Q.IsFlow Y →
      ∃! x : Fin fr.numNodes → A,
        ∀ eq, Y eq = ∑ i : Fin fr.numNodes, (C i).sign eq • x i := by
    have hCf_delta : ∀ i j : Fin fr.numNodes, (C i).sign (fr.fNode j) = if i = j then 1 else 0 := by
      intro i j
      by_cases hij : i = j
      · subst hij; simp [(hC i).2]
      · simp only [hij, ↓reduceIte]
        apply (C i).sign_zero
        intro hmem
        rcases Finset.mem_insert.mp ((hC i).1 hmem) with hfeq | hTe
        · exact hij (hnode_inj j i (Or.inr (Or.inr (Or.inr hfeq)))).symm
        · exact hf_not_Te j hTe
    intro Y hY
    refine ⟨fun i => Y (fr.fNode i), ?_, fun x hx => ?_⟩
    · let Z : aux.EQ → A := fun eq => Y eq - ∑ i : Fin fr.numNodes, (C i).sign eq • Y (fr.fNode i)
      have hZ_flow : aux.Q.IsFlow Z :=
        isFlow_sub hY (isFlow_finset_sum Finset.univ (fun i _ => isFlow_zsmul (C i).isFlow (Y (fr.fNode i))))
      have hZ_supp : ∀ eq, Z eq ≠ 0 → eq ∈ fr.Te.edges := by
        intro eq hne
        by_contra hnot
        have hbe : eq ∈ fr.blue := by
          by_contra hnb
          exact hnot (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnb⟩))
        obtain ⟨j, hj, _⟩ := fr.blue_unique eq hbe
        rcases hj with rfl | rfl
        · exact hnot (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩))
        · exfalso; apply hne
          dsimp only [Z]
          simp only [hCf_delta, ite_smul, one_zsmul, zero_zsmul, Finset.sum_ite_eq',
            Finset.mem_univ, ↓reduceIte, sub_self]
      have hZ0 := flow_eq_zero_of_supp_subset_forest hTe_O1.1.2.1 hZ_flow hZ_supp
      intro eq; exact sub_eq_zero.mp (hZ0 eq)
    · funext j
      have h1 := hx (fr.fNode j)
      simp only [hCf_delta, ite_smul, one_zsmul, zero_zsmul, Finset.sum_ite_eq',
        Finset.mem_univ, ↓reduceIte] at h1
      exact h1.symm
  exact ⟨hO2, hO3, hO4, hO5⟩

/-- **Section 3 in-text remark after Definition 3.12:**
For an `H`-good flow `f`, `|Λ_f(t)| ≤ 3`, `0 ∈ P(Λ_f)`, and `Y ∈ P(Λ_f)` holds iff
`u + π(Y)` is non-zero on every edge of every protected thread. -/
theorem def_3_12_properties
    {Γ : Type} [AddCommGroup Γ] (B : AddSubgroup Γ) [DecidableEq (Γ ⧸ B)]
    {G : Multigraph V E} {H : G.Subgraph} {sub : SubdivisionData G H}
    {aux : AuxGraphData G H sub} (fr : Frame G H sub aux)
    (f : G.NZFlow Γ) (hgood : IsHGoodSub fr B f) :
    (∀ t : aux.EQ, ((LamOfFlow B fr f).list t).card ≤ 3) ∧
    (0 : aux.EQ → Γ ⧸ B) ∈ PLam (LamOfFlow B fr f) ∧
    (∀ Y : aux.EQ → Γ ⧸ B, aux.Q.IsFlow Y →
      (Y ∈ PLam (LamOfFlow B fr f) ↔
        ∀ t : sub.E₀, fr.IsProtected t → ∀ e ∈ (sub.thread t).edges,
          quoFlow B f.val e + aux.pi Y e ≠ 0)) := by
  classical
  have hpi_thread : ∀ (Y : aux.EQ → Γ ⧸ B) (t : sub.E₀) (e : E), e ∈ (sub.thread t).edges →
      aux.pi Y e = Y (aux.origEdge t) := by
    intro Y t e het
    have hex : ∃ t' : sub.E₀, e ∈ (sub.thread t').edges := ⟨t, het⟩
    simp only [AuxGraphData.pi, hex, ↓reduceDIte]
    congr 2; by_contra hne
    exact sub.edges_disjoint _ t hne e hex.choose_spec het
  have hlist_orig : ∀ (t : sub.E₀), fr.IsProtected t →
      (LamOfFlow B fr f).list (aux.origEdge t) =
        ((sub.thread t).edges.toFinset).image (fun e' => -quoFlow B f.val e') := by
    intro t ht
    dsimp only [LamOfFlow]
    split_ifs with h
    · have hch : h.2.choose = t := aux.origEdge.injective h.2.choose_spec
      rw [hch]
    · exact absurd ⟨ht, t, rfl⟩ h
  refine ⟨?_, ?_, ?_⟩
  · intro eq
    dsimp only [LamOfFlow]
    split_ifs with h
    · calc (((sub.thread h.2.choose).edges.toFinset).image (fun e' => -quoFlow B f.val e')).card
          ≤ (sub.thread h.2.choose).edges.toFinset.card := Finset.card_image_le
        _ ≤ (sub.thread h.2.choose).edges.length := List.toFinset_card_le _
        _ ≤ 3 := (sub.thread h.2.choose).len_le
    · simp
  · refine ⟨isFlow_zero aux.Q, fun eq heq hmem => ?_⟩
    dsimp only [LamOfFlow] at hmem
    split_ifs at hmem with h
    · rcases Finset.mem_image.mp hmem with ⟨e', he', hneg⟩
      have h0 : quoFlow B f.val e' = 0 := neg_eq_zero.mp hneg
      have ht : fr.IsProtected h.2.choose := by
        unfold Frame.IsProtected; rw [h.2.choose_spec]; exact h.1
      exact hgood h.2.choose ht e' (List.mem_toFinset.mp he') h0
    · exact Finset.notMem_empty _ hmem
  · intro Y hY
    constructor
    · intro hYL t ht e he
      have hnot := hYL.2 (aux.origEdge t) ht
      rw [hlist_orig t ht] at hnot
      rw [hpi_thread Y t e he]
      intro hsum
      apply hnot
      refine Finset.mem_image.mpr ⟨e, List.mem_toFinset.mpr he, ?_⟩
      exact eq_neg_of_add_eq_zero_right hsum |>.symm
    · intro hall
      refine ⟨hY, fun eq heq hmem => ?_⟩
      dsimp only [LamOfFlow] at hmem
      split_ifs at hmem with h
      · rcases Finset.mem_image.mp hmem with ⟨e', he', hneg⟩
        let t := h.2.choose
        have ht_eq : aux.origEdge t = eq := h.2.choose_spec
        have ht_prot : fr.IsProtected t := by
          unfold Frame.IsProtected; rw [ht_eq]; exact heq
        have hne := hall t ht_prot e' (List.mem_toFinset.mp he')
        rw [hpi_thread Y t e' (List.mem_toFinset.mp he'), ht_eq, ← hneg, add_neg_cancel] at hne
        exact hne rfl
      · exact Finset.notMem_empty _ hmem

end Lemma311AndDef312

end Flow.Proofs
