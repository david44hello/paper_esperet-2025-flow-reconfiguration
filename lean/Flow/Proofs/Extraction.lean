module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Flow.Defs.Frames
public import Flow.Proofs.Basic

@[expose] public section

/-!
# Section 3 (Part 1): Forest/connectivity edge counts and Lemma 3.2 (Extraction)

This module proves elementary subgraph edge-count lemmas (`subgraph_handshake`,
`forest_edges_lt_verts`, `connected_verts_le_edges_succ`) and Lemma 3.2 (`lem_3_2`):
every loopless multigraph with `n ≥ 3` vertices and `3 * m + 6 > 4 * n` contains a good
subgraph of type `(CYC)` or `(SUB)`.
-/

namespace Flow.Proofs

open Flow Multigraph

section SubgraphCounts

variable {V E : Type} [DecidableEq V] [DecidableEq E]

/-- Handshake lemma for a subgraph: `∑ v ∈ H.verts, H.deg v = 2 * H.edges.card`. -/
lemma subgraph_handshake {G : Multigraph V E} (H : G.Subgraph) :
    ∑ v ∈ H.verts, H.deg v = 2 * H.edges.card := by
  unfold Subgraph.deg
  simp only [Finset.card_filter]
  rw [Finset.sum_add_distrib]
  rw [Finset.sum_comm (s := H.verts) (t := H.edges)]
  rw [Finset.sum_comm (s := H.verts) (t := H.edges)]
  have h1 : ∑ e ∈ H.edges, ∑ v ∈ H.verts, (if G.tail e = v then 1 else 0) = H.edges.card := by
    have : ∀ e ∈ H.edges, ∑ v ∈ H.verts, (if G.tail e = v then 1 else 0) = 1 := fun e he => by
      simp [H.tail_mem he]
    rw [Finset.sum_congr rfl this]; simp
  have h2 : ∑ e ∈ H.edges, ∑ v ∈ H.verts, (if G.head e = v then 1 else 0) = H.edges.card := by
    have : ∀ e ∈ H.edges, ∑ v ∈ H.verts, (if G.head e = v then 1 else 0) = 1 := fun e he => by
      simp [H.head_mem he]
    rw [Finset.sum_congr rfl this]; simp
  rw [h1, h2]; omega

/-- Deleting a vertex from a loopless subgraph reduces its edge count by `H.deg v`. -/
lemma deleteVertex_edges_card_add_deg {G : Multigraph V E} (hll : G.IsLoopless)
    (H : G.Subgraph) (v : V) :
    (H.deleteVertex v).edges.card + H.deg v = H.edges.card := by
  unfold Subgraph.deleteVertex Subgraph.deg
  have hdisj_th : Disjoint (H.edges.filter (fun e => G.tail e = v))
      (H.edges.filter (fun e => G.head e = v)) := by
    rw [Finset.disjoint_left]
    intro e ht hh
    rw [Finset.mem_filter] at ht hh
    exact hll e (ht.2.trans hh.2.symm)
  have hdisj_inc : Disjoint (H.edges.filter (fun e => G.tail e ≠ v ∧ G.head e ≠ v))
      (H.edges.filter (fun e => G.tail e = v) ∪ H.edges.filter (fun e => G.head e = v)) := by
    rw [Finset.disjoint_left]
    intro e h1 h2
    simp only [Finset.mem_filter, Finset.mem_union] at h1 h2
    rcases h2 with ⟨_, h⟩ | ⟨_, h⟩
    · exact h1.2.1 h
    · exact h1.2.2 h
  have hunion : H.edges.filter (fun e => G.tail e ≠ v ∧ G.head e ≠ v) ∪
      (H.edges.filter (fun e => G.tail e = v) ∪ H.edges.filter (fun e => G.head e = v)) = H.edges := by
    ext e
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨he, _⟩ | ⟨he, _⟩ | ⟨he, _⟩) <;> exact he
    · intro he
      by_cases ht : G.tail e = v
      · right; left; exact ⟨he, ht⟩
      · by_cases hh : G.head e = v
        · right; right; exact ⟨he, hh⟩
        · left; exact ⟨he, ht, hh⟩
  rw [← Finset.card_union_of_disjoint hdisj_th, ← Finset.card_union_of_disjoint hdisj_inc, hunion]

/-- Any cycle subgraph has the same number of edges and vertices. -/
lemma isCycle_edges_eq_verts {G : Multigraph V E} {C : G.Subgraph} (hC : C.IsCycle) :
    C.edges.card = C.verts.card := by
  have hhs := subgraph_handshake C
  have hsum : ∑ v ∈ C.verts, C.deg v = 2 * C.verts.card := by
    rw [Finset.sum_congr rfl (fun v hv => hC.2 v hv)]
    simp [Nat.mul_comm]
  omega

/-- Every forest is loopless on its edges. -/
lemma isForest_no_loop [Fintype E] {G : Multigraph V E} {F : G.Subgraph} (hF : F.IsForest) :
    ∀ e ∈ F.edges, G.tail e ≠ G.head e := by
  intro e he hloop
  let C := directedCycleOfLoop G e hloop
  apply hF C.sub _ C.isCycle
  constructor
  · intro v hv
    simp only [C, directedCycleOfLoop, Finset.mem_singleton] at hv
    subst hv; exact F.tail_mem he
  · intro e' he'
    simp only [C, directedCycleOfLoop, Finset.mem_singleton] at he'
    subst he'; exact he

/-- A nonempty forest on `n` vertices has at most `n - 1` edges (`m + 1 ≤ n`). -/
lemma forest_edges_lt_verts [Fintype V] [Fintype E] {G : Multigraph V E} :
    ∀ (N : ℕ) (F : G.Subgraph), F.IsForest → F.verts.Nonempty → F.verts.card ≤ N →
      F.edges.card + 1 ≤ F.verts.card := by
  intro N
  induction N with
  | zero =>
    intro F _ hne hle
    have := Finset.card_pos.mpr hne; omega
  | succ N ih =>
    intro F hF hne hle
    by_cases he : F.edges.Nonempty
    · obtain ⟨v, hvF, hdeg1⟩ := exists_leaf_of_forest hF he
      let F' := F.deleteVertex v
      have hF'_le : F' ≤ F := ⟨Finset.erase_subset _ _, Finset.filter_subset _ _⟩
      have hF'_forest : F'.IsForest := fun C hC => hF C ⟨hC.1.trans hF'_le.1, hC.2.trans hF'_le.2⟩
      -- Find the unique edge incident to `v` to see `F'.verts` is nonempty
      have hF'_ne : F'.verts.Nonempty := by
        unfold Subgraph.deg at hdeg1
        have hex : ∃ e ∈ F.edges, G.tail e = v ∨ G.head e = v := by
          by_cases ht : 0 < (F.edges.filter (fun e => G.tail e = v)).card
          · rcases Finset.card_pos.mp ht with ⟨e, he'⟩
            exact ⟨e, (Finset.mem_filter.mp he').1, Or.inl (Finset.mem_filter.mp he').2⟩
          · have hh : 0 < (F.edges.filter (fun e => G.head e = v)).card := by omega
            rcases Finset.card_pos.mp hh with ⟨e, he'⟩
            exact ⟨e, (Finset.mem_filter.mp he').1, Or.inr (Finset.mem_filter.mp he').2⟩
        rcases hex with ⟨e, heF, ht | hh⟩
        · have hne_end : G.head e ≠ v := fun h => isForest_no_loop hF e heF (ht.trans h.symm)
          exact ⟨G.head e, Finset.mem_erase.mpr ⟨hne_end, F.head_mem heF⟩⟩
        · have hne_end : G.tail e ≠ v := fun h => isForest_no_loop hF e heF (h.trans hh.symm)
          exact ⟨G.tail e, Finset.mem_erase.mpr ⟨hne_end, F.tail_mem heF⟩⟩
      have hcardV : F'.verts.card + 1 = F.verts.card := by
        simp [F', Subgraph.deleteVertex, Finset.card_erase_of_mem hvF]
        have := Finset.card_pos.mpr hne; omega
      -- Compute `F'.edges.card + 1 = F.edges.card` (since `F` has no loops and `F.deg v = 1`)
      have hcardE : F'.edges.card + 1 = F.edges.card := by
        have hdisj_th : Disjoint (F.edges.filter (fun e => G.tail e = v))
            (F.edges.filter (fun e => G.head e = v)) := by
          rw [Finset.disjoint_left]
          intro e ht hh
          rw [Finset.mem_filter] at ht hh
          exact isForest_no_loop hF e ht.1 (ht.2.trans hh.2.symm)
        have hdisj_inc : Disjoint F'.edges
            (F.edges.filter (fun e => G.tail e = v) ∪ F.edges.filter (fun e => G.head e = v)) := by
          rw [Finset.disjoint_left]
          intro e h1 h2
          simp only [F', Subgraph.deleteVertex, Finset.mem_filter, Finset.mem_union] at h1 h2
          rcases h2 with ⟨_, h⟩ | ⟨_, h⟩
          · exact h1.2.1 h
          · exact h1.2.2 h
        have hunion : F'.edges ∪
            (F.edges.filter (fun e => G.tail e = v) ∪ F.edges.filter (fun e => G.head e = v)) = F.edges := by
          ext e
          simp only [F', Subgraph.deleteVertex, Finset.mem_union, Finset.mem_filter]
          constructor
          · rintro (⟨he, _⟩ | ⟨he, _⟩ | ⟨he, _⟩) <;> exact he
          · intro he
            by_cases ht : G.tail e = v
            · right; left; exact ⟨he, ht⟩
            · by_cases hh : G.head e = v
              · right; right; exact ⟨he, hh⟩
              · left; exact ⟨he, ht, hh⟩
        have hsum := Finset.card_union_of_disjoint hdisj_inc
        rw [hunion, Finset.card_union_of_disjoint hdisj_th] at hsum
        unfold Subgraph.deg at hdeg1
        omega
      have ih' := ih F' hF'_forest hF'_ne (by omega)
      omega
    · rw [Finset.not_nonempty_iff_eq_empty] at he
      have := Finset.card_pos.mpr hne
      simp [he]; omega

/-- Any connected subgraph on `n` vertices has at least `n - 1` edges (`n ≤ m + 1`). -/
lemma connected_verts_le_edges_succ {G : Multigraph V E} (H : G.Subgraph) (hconn : H.Connected) :
    H.verts.card ≤ H.edges.card + 1 := by
  -- Grow a reached set `R` one edge at a time until `R = H.verts`
  have hgrow : ∀ (k : ℕ) (R : Finset V) (F : Finset E),
      R ⊆ H.verts → R.Nonempty → F ⊆ H.edges →
      (∀ e ∈ F, G.tail e ∈ R ∧ G.head e ∈ R) →
      R.card ≤ F.card + 1 →
      H.verts.card - R.card ≤ k →
      H.verts.card ≤ H.edges.card + 1 := by
    intro k
    induction k with
    | zero =>
      intro R F hRsub _ hFsub _ hRF hk0
      have hReq : R = H.verts := Finset.eq_of_subset_of_card_le hRsub (by omega)
      rw [← hReq]
      exact le_trans hRF (Nat.add_le_add_right (Finset.card_le_card hFsub) 1)
    | succ k ih =>
      intro R F hRsub hRne hFsub hFend hRF hk
      by_cases hReq : R = H.verts
      · rw [← hReq]
        exact le_trans hRF (Nat.add_le_add_right (Finset.card_le_card hFsub) 1)
      · -- There is a vertex `w ∈ H.verts \ R`; walk from `v₀ ∈ R` to `w` to find a crossing edge `e ∈ H.edges`
        have hex_out : ∃ w ∈ H.verts, w ∉ R := by
          by_contra hall
          push Not at hall
          exact hReq (Finset.Subset.antisymm hRsub hall)
        rcases hRne with ⟨v₀, hv₀R⟩
        rcases hex_out with ⟨w, hwH, hwR⟩
        have hwalk := hconn.2 v₀ (hRsub hv₀R) w hwH
        have hcross : ∃ u ∈ R, ∃ z ∈ H.verts, z ∉ R ∧ H.Adj u z := by
          clear ih hk hRF hFend hFsub
          induction hwalk with
          | refl => exact absurd hv₀R hwR
          | @tail b c hab hbc ihw =>
            by_cases hbR : b ∈ R
            · exact ⟨b, hbR, c, hwH, hwR, hbc⟩
            · have hbH : b ∈ H.verts := by
                rcases hbc with ⟨e, heH, ⟨ht, _⟩ | ⟨_, hh⟩⟩
                · rw [← ht]; exact H.tail_mem heH
                · rw [← hh]; exact H.head_mem heH
              exact ihw hbH hbR
        rcases hcross with ⟨u, huR, z, hzH, hzR, e, heH, he_adj⟩
        have he_notF : e ∉ F := by
          intro hm
          have ⟨ht, hh⟩ := hFend e hm
          rcases he_adj with ⟨_, hh'⟩ | ⟨ht', _⟩
          · exact hzR (hh' ▸ hh)
          · exact hzR (ht' ▸ ht)
        refine ih (insert z R) (insert e F)
          (Finset.insert_subset hzH hRsub)
          ⟨z, Finset.mem_insert_self _ _⟩
          (Finset.insert_subset heH hFsub)
          (fun e' he' => ?_) ?_ ?_
        · rw [Finset.mem_insert] at he'
          rcases he' with rfl | he'F
          · rcases he_adj with ⟨ht, hh⟩ | ⟨ht, hh⟩
            · exact ⟨ht ▸ Finset.mem_insert_of_mem huR, hh ▸ Finset.mem_insert_self _ _⟩
            · exact ⟨ht ▸ Finset.mem_insert_self _ _, hh ▸ Finset.mem_insert_of_mem huR⟩
          · exact ⟨Finset.mem_insert_of_mem (hFend e' he'F).1,
                   Finset.mem_insert_of_mem (hFend e' he'F).2⟩
        · rw [Finset.card_insert_of_notMem hzR, Finset.card_insert_of_notMem he_notF]; omega
        · rw [Finset.card_insert_of_notMem hzR]
          have hleV : R.card < H.verts.card :=
            Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hRsub, hReq⟩)
          omega
  rcases hconn.1 with ⟨v₀, hv₀⟩
  exact hgrow H.verts.card {v₀} ∅
    (Finset.singleton_subset_iff.mpr hv₀)
    ⟨v₀, Finset.mem_singleton_self _⟩
    (Finset.empty_subset _) (by simp) (by simp) (by omega)

/-- Subgraph restriction of `H` to a vertex subset `U ⊆ H.verts`. -/
def subgraphRestrict {G : Multigraph V E} (H : G.Subgraph) (U : Finset V) : G.Subgraph where
  verts := U
  edges := H.edges.filter (fun e => G.tail e ∈ U ∧ G.head e ∈ U)
  tail_mem he := (Finset.mem_filter.mp he).2.1
  head_mem he := (Finset.mem_filter.mp he).2.2

/-- Handshake for a subset `U ⊆ H.verts`: `∑ v ∈ U, H.deg v = 2 * |(H[U]).edges| + cut`. -/
lemma subgraph_cut_handshake {G : Multigraph V E} (H : G.Subgraph) (U : Finset V)
    (hU : U ⊆ H.verts) :
    ∑ v ∈ U, H.deg v =
      2 * (subgraphRestrict H U).edges.card +
      (H.edges.filter (fun e =>
        (G.tail e ∈ U ∧ G.head e ∉ U) ∨ (G.tail e ∉ U ∧ G.head e ∈ U))).card := by
  have h1 : ∑ v ∈ U, H.deg v =
      ∑ e ∈ H.edges, ((if G.tail e ∈ U then 1 else 0) + (if G.head e ∈ U then 1 else 0)) := by
    unfold Subgraph.deg
    simp only [Finset.card_filter]
    rw [Finset.sum_add_distrib]
    rw [Finset.sum_comm (s := U) (t := H.edges)]
    rw [Finset.sum_comm (s := U) (t := H.edges)]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    simp
  rw [h1]
  have h2 : 2 * (subgraphRestrict H U).edges.card +
      (H.edges.filter (fun e =>
        (G.tail e ∈ U ∧ G.head e ∉ U) ∨ (G.tail e ∉ U ∧ G.head e ∈ U))).card =
      ∑ e ∈ H.edges,
        ((if G.tail e ∈ U ∧ G.head e ∈ U then 2 else 0) +
         (if (G.tail e ∈ U ∧ G.head e ∉ U) ∨ (G.tail e ∉ U ∧ G.head e ∈ U) then 1 else 0)) := by
    simp only [subgraphRestrict, Finset.card_filter, Finset.mul_sum, Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl (fun e _ => ?_)
    split_ifs <;> omega
  rw [h2]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  by_cases ht : G.tail e ∈ U <;> by_cases hh : G.head e ∈ U <;> simp [ht, hh]

end SubgraphCounts

section Extraction

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- **Lemma 3.2 (Extraction).**
Every loopless multigraph `G` with `n ≥ 3` vertices and `3 * m + 6 > 4 * n` contains
a good subgraph. -/
theorem lem_3_2
    (G : Multigraph V E) (hll : G.IsLoopless)
    (hn : 3 ≤ Fintype.card V) (hm : 4 * Fintype.card V < 3 * Fintype.card E + 6) :
    ∃ H : G.Subgraph, IsGoodSubgraph G H := by
  classical
  -- First check for a short cycle (≤ 5 edges)
  by_cases hshort : ∃ C : G.Subgraph, C.IsCycle ∧ C.edges.card ≤ 5
  · rcases hshort with ⟨C, hCcyc, hCle5⟩
    refine ⟨C, Or.inl ⟨hCcyc, hCle5, ?_⟩⟩
    rcases hCcyc.1.1 with ⟨v, hvC⟩
    have hdeg2 := hCcyc.2 v hvC
    have hex : ∃ e ∈ C.edges, G.tail e = v ∨ G.head e = v := by
      unfold Subgraph.deg at hdeg2
      by_cases ht : 0 < (C.edges.filter (fun e => G.tail e = v)).card
      · rcases Finset.card_pos.mp ht with ⟨e, he⟩
        exact ⟨e, (Finset.mem_filter.mp he).1, Or.inl (Finset.mem_filter.mp he).2⟩
      · have hh : 0 < (C.edges.filter (fun e => G.head e = v)).card := by omega
        rcases Finset.card_pos.mp hh with ⟨e, he⟩
        exact ⟨e, (Finset.mem_filter.mp he).1, Or.inr (Finset.mem_filter.mp he).2⟩
    rcases hex with ⟨e, heC, _⟩
    have hsub : ({G.tail e, G.head e} : Finset V) ⊆ C.verts := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact C.tail_mem heC
      · exact C.head_mem heC
    exact le_trans (by rw [Finset.card_pair (hll e)]) (Finset.card_le_card hsub)
  · -- Girth ≥ 6: every cycle has ≥ 6 edges; in particular G is simple
    push Not at hshort
    have hgirth : ∀ C : G.Subgraph, C.IsCycle → 6 ≤ C.edges.card := fun C hC =>
      Nat.succ_le_of_lt (hshort C hC)
    have hsimple : G.IsSimple := by
      refine ⟨hll, fun e₁ e₂ hsame => ?_⟩
      by_contra hne
      -- Two distinct parallel edges form a 2-cycle, contradicting girth ≥ 6
      let C2 : G.Subgraph :=
        { verts := {G.tail e₁, G.head e₁}
          edges := {e₁, e₂}
          tail_mem := fun he => by
            simp only [Finset.mem_insert, Finset.mem_singleton] at he ⊢
            rcases he with rfl | rfl
            · left; rfl
            · rcases hsame with ⟨ht, _⟩ | ⟨_, hh⟩
              · left; exact ht.symm
              · right; exact hh.symm
          head_mem := fun he => by
            simp only [Finset.mem_insert, Finset.mem_singleton] at he ⊢
            rcases he with rfl | rfl
            · right; rfl
            · rcases hsame with ⟨_, hh⟩ | ⟨ht, _⟩
              · right; exact hh.symm
              · left; exact ht.symm }
      have hC2_cyc : C2.IsCycle := by
        refine ⟨⟨⟨G.tail e₁, Finset.mem_insert_self _ _⟩, fun u hu v hv => ?_⟩, fun v hv => ?_⟩
        · simp only [C2, Finset.mem_insert, Finset.mem_singleton] at hu hv
          rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
          · exact Relation.ReflTransGen.refl
          · exact Relation.ReflTransGen.single ⟨e₁, Finset.mem_insert_self _ _, Or.inl ⟨rfl, rfl⟩⟩
          · exact Relation.ReflTransGen.single ⟨e₁, Finset.mem_insert_self _ _, Or.inr ⟨rfl, rfl⟩⟩
          · exact Relation.ReflTransGen.refl
        · simp only [C2, Finset.mem_insert, Finset.mem_singleton] at hv
          unfold Subgraph.deg
          simp only [C2, Finset.card_filter, Finset.sum_pair hne]
          rcases hv with rfl | rfl <;> rcases hsame with ⟨ht, hh⟩ | ⟨ht, hh⟩ <;>
            simp [← ht, ← hh, hll e₁, (hll e₁).symm]
      have hge6 := hgirth C2 hC2_cyc
      have hle2 : C2.edges.card ≤ 2 := by simp [C2, Finset.card_pair hne]
      omega
    -- Simple graph edge bound on ≤ 2 vertices
    have hsimple_edges : ∀ (K : G.Subgraph),
        (K.verts.card = 1 → K.edges.card = 0) ∧ (K.verts.card = 2 → K.edges.card ≤ 1) := by
      intro K
      constructor
      · intro hv1
        rw [Finset.card_eq_one] at hv1
        rcases hv1 with ⟨u, hu⟩
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
        intro e he
        have ht : G.tail e = u := Finset.mem_singleton.mp (hu ▸ K.tail_mem he)
        have hh : G.head e = u := Finset.mem_singleton.mp (hu ▸ K.head_mem he)
        exact hll e (ht.trans hh.symm)
      · intro hv2
        rw [Finset.card_eq_two] at hv2
        rcases hv2 with ⟨u, w, huw, huv⟩
        by_contra hgt1
        have h2 : 1 < K.edges.card := by omega
        obtain ⟨e₁, he₁, e₂, he₂, hne⟩ := Finset.one_lt_card.mp h2
        have hends : ∀ e ∈ K.edges, (G.tail e = u ∧ G.head e = w) ∨ (G.tail e = w ∧ G.head e = u) := by
          intro e he
          have ht := K.tail_mem he; have hh := K.head_mem he
          rw [huv, Finset.mem_insert, Finset.mem_singleton] at ht hh
          rcases ht with ht | ht <;> rcases hh with hh | hh
          · exact absurd (ht.trans hh.symm) (hll e)
          · left; exact ⟨ht, hh⟩
          · right; exact ⟨ht, hh⟩
          · exact absurd (ht.trans hh.symm) (hll e)
        have hsame : G.SameEnds e₁ e₂ := by
          rcases hends e₁ he₁ with ⟨ht1, hh1⟩ | ⟨ht1, hh1⟩ <;>
          rcases hends e₂ he₂ with ⟨ht2, hh2⟩ | ⟨ht2, hh2⟩
          · left; exact ⟨ht1.trans ht2.symm, hh1.trans hh2.symm⟩
          · right; exact ⟨ht1.trans hh2.symm, hh1.trans ht2.symm⟩
          · right; exact ⟨ht1.trans hh2.symm, hh1.trans ht2.symm⟩
          · left; exact ⟨ht1.trans ht2.symm, hh1.trans hh2.symm⟩
        exact hne (hsimple.2 e₁ e₂ hsame)
    -- Pick a dense subgraph `H` minimizing `H.verts.card`
    let IsDense (K : G.Subgraph) : Prop :=
      3 ≤ K.verts.card ∧ 4 * K.verts.card < 3 * K.edges.card + 6
    have hex_dense : ∃ k, ∃ K : G.Subgraph, IsDense K ∧ K.verts.card = k :=
      ⟨Fintype.card V, Subgraph.top G, ⟨hn, hm⟩, by simp [Subgraph.top]⟩
    let minN := Nat.find hex_dense
    obtain ⟨H, hH_dense, hH_card⟩ := Nat.find_spec hex_dense
    have hH_min : ∀ K : G.Subgraph, IsDense K → H.verts.card ≤ K.verts.card := fun K hK => by
      rw [hH_card]; exact Nat.find_min' hex_dense ⟨K, hK, rfl⟩
    -- Step 1: `6 ≤ H.verts.card`, `H.verts.card < H.edges.card`, and `∀ v ∈ H.verts, 2 ≤ H.deg v`
    have hH_not_forest : ¬ H.IsForest := by
      intro hfor
      have hne : H.verts.Nonempty := Finset.card_pos.mp (by omega : 0 < H.verts.card)
      have hle := forest_edges_lt_verts H.verts.card H hfor hne le_rfl
      omega
    have hH_n_ge6 : 6 ≤ H.verts.card := by
      unfold Subgraph.IsForest at hH_not_forest
      push Not at hH_not_forest
      rcases hH_not_forest with ⟨C, hCH, hCcyc⟩
      have h1 := hgirth C hCcyc
      have h2 := isCycle_edges_eq_verts hCcyc
      have h3 := Finset.card_le_card hCH.1
      omega
    have hH_m_gt_n : H.verts.card < H.edges.card := by omega
    have hH_deg_ge2 : ∀ v ∈ H.verts, 2 ≤ H.deg v := by
      intro v hv
      let Hv := H.deleteVertex v
      have hHv_card : Hv.verts.card = H.verts.card - 1 := by
        simp [Hv, Subgraph.deleteVertex, Finset.card_erase_of_mem hv]
      have hHv_not_dense : ¬ IsDense Hv := fun hd => by
        have := hH_min Hv hd; omega
      have hHv_m : 3 * Hv.edges.card + 6 ≤ 4 * Hv.verts.card := by
        by_contra hlt
        exact hHv_not_dense ⟨by omega, by omega⟩
      have hdeg_eq := deleteVertex_edges_card_add_deg hll H v
      dsimp only [Hv] at hHv_m hHv_card
      omega
    -- Step 2: `H` is connected
    have hH_conn : H.Connected := by
      have hH_ne : H.verts.Nonempty := Finset.card_pos.mp (by omega : 0 < H.verts.card)
      refine ⟨hH_ne, fun u hu v hv => ?_⟩
      by_contra hnot
      let V₁ := H.verts.filter (fun w => Relation.ReflTransGen H.Adj u w)
      let V₂ := H.verts \ V₁
      have hu1 : u ∈ V₁ := Finset.mem_filter.mpr ⟨hu, Relation.ReflTransGen.refl⟩
      have hv2 : v ∈ V₂ := Finset.mem_sdiff.mpr ⟨hv, fun h => hnot (Finset.mem_filter.mp h).2⟩
      let H₁ := subgraphRestrict H V₁
      let H₂ := subgraphRestrict H V₂
      have hV1_sub : V₁ ⊆ H.verts := Finset.filter_subset _ _
      have hV2_sub : V₂ ⊆ H.verts := Finset.sdiff_subset
      have hclosed : ∀ e ∈ H.edges, G.tail e ∈ V₁ ↔ G.head e ∈ V₁ := by
        intro e he
        simp only [V₁, Finset.mem_filter]
        constructor
        · rintro ⟨_, h⟩
          exact ⟨H.head_mem he, Relation.ReflTransGen.tail h ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩⟩
        · rintro ⟨_, h⟩
          exact ⟨H.tail_mem he, Relation.ReflTransGen.tail h ⟨e, he, Or.inr ⟨rfl, rfl⟩⟩⟩
      have hdeg_eq1 : ∀ x ∈ V₁, H₁.deg x = H.deg x := by
        intro x hx
        unfold Subgraph.deg H₁ subgraphRestrict
        congr 1 <;> congr 1 <;> ext e <;> simp only [Finset.mem_filter]
        · constructor
          · rintro ⟨⟨he, _, _⟩, ht⟩; exact ⟨he, ht⟩
          · rintro ⟨he, ht⟩
            have ht1 : G.tail e ∈ V₁ := ht ▸ hx
            exact ⟨⟨he, ht1, (hclosed e he).mp ht1⟩, ht⟩
        · constructor
          · rintro ⟨⟨he, _, _⟩, hh⟩; exact ⟨he, hh⟩
          · rintro ⟨he, hh⟩
            have hh1 : G.head e ∈ V₁ := hh ▸ hx
            exact ⟨⟨he, (hclosed e he).mpr hh1, hh1⟩, hh⟩
      have hdeg_eq2 : ∀ x ∈ V₂, H₂.deg x = H.deg x := by
        intro x hx
        have hxH := hV2_sub hx
        have hxnot1 : x ∉ V₁ := (Finset.mem_sdiff.mp hx).2
        unfold Subgraph.deg H₂ subgraphRestrict
        congr 1 <;> congr 1 <;> ext e <;> simp only [Finset.mem_filter]
        · constructor
          · rintro ⟨⟨he, _, _⟩, ht⟩; exact ⟨he, ht⟩
          · rintro ⟨he, ht⟩
            have ht2 : G.tail e ∈ V₂ := ht ▸ hx
            have hh2 : G.head e ∈ V₂ := Finset.mem_sdiff.mpr
              ⟨H.head_mem he, fun hh1 => hxnot1 (ht ▸ (hclosed e he).mpr hh1)⟩
            exact ⟨⟨he, ht2, hh2⟩, ht⟩
        · constructor
          · rintro ⟨⟨he, _, _⟩, hh⟩; exact ⟨he, hh⟩
          · rintro ⟨he, hh⟩
            have hh2 : G.head e ∈ V₂ := hh ▸ hx
            have ht2 : G.tail e ∈ V₂ := Finset.mem_sdiff.mpr
              ⟨H.tail_mem he, fun ht1 => hxnot1 (hh ▸ (hclosed e he).mp ht1)⟩
            exact ⟨⟨he, ht2, hh2⟩, hh⟩
      have hge6_of_deg2 : ∀ (K : G.Subgraph), K.verts.Nonempty → (∀ x ∈ K.verts, 2 ≤ K.deg x) →
          6 ≤ K.verts.card := by
        intro K hKne hKdeg
        have hKe_ne : K.edges.Nonempty := by
          rcases hKne with ⟨x, hx⟩
          have hd := hKdeg x hx
          have hhs := subgraph_handshake K
          have hsum_pos : 0 < ∑ y ∈ K.verts, K.deg y :=
            lt_of_lt_of_le (by omega : 0 < K.deg x)
              (Finset.single_le_sum (f := K.deg) (fun _ _ => Nat.zero_le _) hx)
          exact Finset.card_pos.mp (by omega)
        obtain ⟨C, hCK⟩ := exists_directedCycle_of_no_deg_one K hKe_ne (fun x hx => by have := hKdeg x hx; omega)
        have h1 := hgirth C.sub C.isCycle
        have h2 := isCycle_edges_eq_verts C.isCycle
        have h3 := Finset.card_le_card hCK.1
        omega
      have hn1 : 6 ≤ H₁.verts.card := hge6_of_deg2 H₁ ⟨u, hu1⟩ (fun x hx => by rw [hdeg_eq1 x hx]; exact hH_deg_ge2 x (hV1_sub hx))
      have hn2 : 6 ≤ H₂.verts.card := hge6_of_deg2 H₂ ⟨v, hv2⟩ (fun x hx => by rw [hdeg_eq2 x hx]; exact hH_deg_ge2 x (hV2_sub hx))
      have hcardV_sum : H₁.verts.card + H₂.verts.card = H.verts.card := by
        dsimp only [H₁, H₂, subgraphRestrict, V₂]
        rw [add_comm, Finset.card_sdiff_add_card_eq_card hV1_sub]
      have hcardE_sum : H₁.edges.card + H₂.edges.card = H.edges.card := by
        have hdisj : Disjoint H₁.edges H₂.edges := by
          rw [Finset.disjoint_left]
          intro e he1 he2
          exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp he2).2.1).2 (Finset.mem_filter.mp he1).2.1
        have hunion : H₁.edges ∪ H₂.edges = H.edges := by
          ext e
          simp only [H₁, H₂, subgraphRestrict, Finset.mem_union, Finset.mem_filter]
          constructor
          · rintro (⟨he, _⟩ | ⟨he, _⟩) <;> exact he
          · intro he
            by_cases ht1 : G.tail e ∈ V₁
            · left; exact ⟨he, ht1, (hclosed e he).mp ht1⟩
            · right; exact ⟨he, Finset.mem_sdiff.mpr ⟨H.tail_mem he, ht1⟩,
                Finset.mem_sdiff.mpr ⟨H.head_mem he, fun hh1 => ht1 ((hclosed e he).mpr hh1)⟩⟩
        rw [← Finset.card_union_of_disjoint hdisj, hunion]
      have hnd1 : 3 * H₁.edges.card + 6 ≤ 4 * H₁.verts.card := by
        by_contra hlt; have := hH_min H₁ ⟨by omega, by omega⟩; omega
      have hnd2 : 3 * H₂.edges.card + 6 ≤ 4 * H₂.verts.card := by
        by_contra hlt; have := hH_min H₂ ⟨by omega, by omega⟩; omega
      omega
    -- Step 3: Small edge-cuts
    have hstep3 : ∀ (U : Finset V), U ⊆ H.verts → U.Nonempty → (H.verts \ U).Nonempty →
        (H.edges.filter (fun e =>
          (G.tail e ∈ U ∧ G.head e ∉ U) ∨ (G.tail e ∉ U ∧ G.head e ∈ U))).card ≤ 2 →
        ((U.card ≤ 2 ∧ ∀ x ∈ U, H.deg x = 2) ∨
         ((H.verts \ U).card ≤ 2 ∧ ∀ x ∈ H.verts \ U, H.deg x = 2)) ∧
        (H.edges.filter (fun e =>
          (G.tail e ∈ U ∧ G.head e ∉ U) ∨ (G.tail e ∉ U ∧ G.head e ∈ U))).card = 2 := by
      intro U hU hUne hUcomp hcut_le
      let V₁ := U
      let V₂ := H.verts \ U
      let H₁ := subgraphRestrict H V₁
      let H₂ := subgraphRestrict H V₂
      let Cut := H.edges.filter (fun e =>
        (G.tail e ∈ U ∧ G.head e ∉ U) ∨ (G.tail e ∉ U ∧ G.head e ∈ U))
      have hV_sum : V₁.card + V₂.card = H.verts.card := by
        rw [add_comm]; exact Finset.card_sdiff_add_card_eq_card hU
      have hE_le : H.edges.card ≤ H₁.edges.card + H₂.edges.card + Cut.card := by
        have hsub : H.edges ⊆ H₁.edges ∪ (H₂.edges ∪ Cut) := by
          intro e he
          simp only [H₁, H₂, Cut, subgraphRestrict, V₁, V₂, Finset.mem_union, Finset.mem_filter,
            Finset.mem_sdiff]
          by_cases ht : G.tail e ∈ U <;> by_cases hh : G.head e ∈ U
          · left; exact ⟨he, ht, hh⟩
          · right; right; exact ⟨he, Or.inl ⟨ht, hh⟩⟩
          · right; right; exact ⟨he, Or.inr ⟨ht, hh⟩⟩
          · right; left; exact ⟨he, ⟨H.tail_mem he, ht⟩, ⟨H.head_mem he, hh⟩⟩
        calc H.edges.card ≤ (H₁.edges ∪ (H₂.edges ∪ Cut)).card := Finset.card_le_card hsub
          _ ≤ H₁.edges.card + (H₂.edges ∪ Cut).card := Finset.card_union_le _ _
          _ ≤ H₁.edges.card + (H₂.edges.card + Cut.card) :=
              Nat.add_le_add_left (Finset.card_union_le _ _) _
          _ = H₁.edges.card + H₂.edges.card + Cut.card := by omega
      have hsome_dense : 4 * V₁.card < 3 * H₁.edges.card + 6 ∨ 4 * V₂.card < 3 * H₂.edges.card + 6 := by
        by_contra hboth
        push Not at hboth
        dsimp only [V₁, V₂, H₁, H₂, Cut] at hV_sum hE_le hboth
        omega
      have hsmall_side : ∀ (W : Finset V) (hW : W ⊆ H.verts), W.Nonempty → W.card < H.verts.card →
          4 * W.card < 3 * (subgraphRestrict H W).edges.card + 6 →
          (H.edges.filter (fun e =>
            (G.tail e ∈ W ∧ G.head e ∉ W) ∨ (G.tail e ∉ W ∧ G.head e ∈ W))).card ≤ 2 →
          W.card ≤ 2 ∧ (∀ x ∈ W, H.deg x = 2) ∧
          (H.edges.filter (fun e =>
            (G.tail e ∈ W ∧ G.head e ∉ W) ∨ (G.tail e ∉ W ∧ G.head e ∈ W))).card = 2 := by
        intro W hW hWne hWlt hWdense hWcut
        have hWle2 : W.card ≤ 2 := by
          by_contra hge3
          have hW_isDense : IsDense (subgraphRestrict H W) := ⟨by dsimp [subgraphRestrict]; omega, hWdense⟩
          have := hH_min (subgraphRestrict H W) hW_isDense
          dsimp only [subgraphRestrict] at this; omega
        have hWm : (subgraphRestrict H W).edges.card + 1 ≤ W.card := by
          have h12 := hsimple_edges (subgraphRestrict H W)
          dsimp only [subgraphRestrict] at h12
          have hpos := Finset.card_pos.mpr hWne
          by_cases hc1 : W.card = 1
          · have h0 := h12.1 hc1; dsimp only [subgraphRestrict]; omega
          · have hc2 : W.card = 2 := by omega
            have hle1 := h12.2 hc2; dsimp only [subgraphRestrict]; omega
        have hhs := subgraph_cut_handshake H W hW
        have hsum_ge : 2 * W.card ≤ ∑ x ∈ W, H.deg x := by
          calc 2 * W.card = ∑ _x ∈ W, 2 := by simp [Nat.mul_comm]
            _ ≤ ∑ x ∈ W, H.deg x := Finset.sum_le_sum (fun x hx => hH_deg_ge2 x (hW hx))
        have hcut_eq2 : (H.edges.filter (fun e =>
            (G.tail e ∈ W ∧ G.head e ∉ W) ∨ (G.tail e ∉ W ∧ G.head e ∈ W))).card = 2 := by omega
        have hsum_eq : ∑ x ∈ W, H.deg x = 2 * W.card := by omega
        have hall2 : ∀ x ∈ W, H.deg x = 2 := by
          intro x hx
          by_contra hne2
          have hge3 : 3 ≤ H.deg x := by have := hH_deg_ge2 x (hW hx); omega
          have hsum_gt : 2 * W.card < ∑ y ∈ W, H.deg y := by
            have h1 : ∑ y ∈ W.erase x, 2 ≤ ∑ y ∈ W.erase x, H.deg y :=
              Finset.sum_le_sum (fun y hy => hH_deg_ge2 y (hW (Finset.mem_of_mem_erase hy)))
            rw [← Finset.add_sum_erase W H.deg hx]
            simp only [Finset.sum_const, smul_eq_mul, Finset.card_erase_of_mem hx] at h1
            have := Finset.card_pos.mpr hWne
            omega
          omega
        exact ⟨hWle2, hall2, hcut_eq2⟩
      have hcut_sym : (H.edges.filter (fun e =>
          (G.tail e ∈ V₂ ∧ G.head e ∉ V₂) ∨ (G.tail e ∉ V₂ ∧ G.head e ∈ V₂))) = Cut := by
        ext e
        simp only [Cut, V₂, Finset.mem_filter, Finset.mem_sdiff]
        constructor
        · rintro ⟨he, ⟨⟨_, ht⟩, hh⟩ | ⟨ht, ⟨_, hh⟩⟩⟩
          · refine ⟨he, Or.inr ⟨ht, ?_⟩⟩
            by_contra hnot; exact hh ⟨H.head_mem he, hnot⟩
          · refine ⟨he, Or.inl ⟨?_, hh⟩⟩
            by_contra hnot; exact ht ⟨H.tail_mem he, hnot⟩
        · rintro ⟨he, ⟨ht, hh⟩ | ⟨ht, hh⟩⟩
          · exact ⟨he, Or.inr ⟨fun h => h.2 ht, ⟨H.head_mem he, hh⟩⟩⟩
          · exact ⟨he, Or.inl ⟨⟨H.tail_mem he, ht⟩, fun h => h.2 hh⟩⟩
      rcases hsome_dense with hd1 | hd2
      · have h1lt : V₁.card < H.verts.card := by
          have := Finset.card_pos.mpr hUcomp; dsimp only [V₁, V₂] at hV_sum ⊢; omega
        obtain ⟨h1a, h1b, h1c⟩ := hsmall_side V₁ hU hUne h1lt hd1 hcut_le
        exact ⟨Or.inl ⟨h1a, h1b⟩, h1c⟩
      · have h2lt : V₂.card < H.verts.card := by
          have := Finset.card_pos.mpr hUne; dsimp only [V₁, V₂] at hV_sum ⊢; omega
        obtain ⟨h2a, h2b, h2c⟩ := hsmall_side V₂ Finset.sdiff_subset hUcomp h2lt hd2 (by rw [hcut_sym]; exact hcut_le)
        rw [hcut_sym] at h2c
        exact ⟨Or.inr ⟨h2a, h2b⟩, h2c⟩
    -- Step 4: Decompose `H` into branch vertices `V₀` and threads
    let V₀Fin : Finset V := H.verts.filter (fun v => 3 ≤ H.deg v)
    have hV₀_ne : V₀Fin.Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty] at hempty
      have hall2 : ∀ v ∈ H.verts, H.deg v = 2 := fun v hv => by
        have hge2 := hH_deg_ge2 v hv
        have hlt3 : ¬ 3 ≤ H.deg v := fun h3 => by
          have : v ∈ V₀Fin := Finset.mem_filter.mpr ⟨hv, h3⟩
          rw [hempty] at this; exact Finset.notMem_empty v this
        omega
      have hhs := subgraph_handshake H
      rw [Finset.sum_congr rfl hall2] at hhs
      simp only [Finset.sum_const, smul_eq_mul] at hhs
      omega
    -- Connected components of `H_deg2 = H[H.verts \ V₀Fin]`
    let Hdeg2 := subgraphRestrict H (H.verts \ V₀Fin)
    let compOf (x : V) : Finset V :=
      (H.verts \ V₀Fin).filter (fun y => Relation.ReflTransGen Hdeg2.Adj x y)
    have hcomp_symm : ∀ {a b : V}, Relation.ReflTransGen Hdeg2.Adj a b →
        Relation.ReflTransGen Hdeg2.Adj b a := by
      intro a b hab
      induction hab with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ hstep ih =>
        rcases hstep with ⟨e, he, h | h⟩
        · exact Relation.ReflTransGen.head ⟨e, he, Or.inr h⟩ ih
        · exact Relation.ReflTransGen.head ⟨e, he, Or.inl h⟩ ih
    have hcomp_eq_of_mem : ∀ {x y : V}, x ∈ H.verts \ V₀Fin → y ∈ compOf x → compOf y = compOf x := by
      intro x y _ hy
      have hxy := (Finset.mem_filter.mp hy).2
      ext z; simp only [compOf, Finset.mem_filter]
      exact ⟨fun ⟨hz, hyz⟩ => ⟨hz, Relation.ReflTransGen.trans hxy hyz⟩,
             fun ⟨hz, hxz⟩ => ⟨hz, Relation.ReflTransGen.trans (hcomp_symm hxy) hxz⟩⟩
    -- Analyze each component `I = compOf x` (`x ∈ H.verts \ V₀Fin`)
    have hcomp_props : ∀ x ∈ H.verts \ V₀Fin,
        let I := compOf x
        let CutI := H.edges.filter (fun e =>
          (G.tail e ∈ I ∧ G.head e ∉ I) ∨ (G.tail e ∉ I ∧ G.head e ∈ I))
        I.card ≤ 2 ∧ (subgraphRestrict H I).edges.card + 1 = I.card ∧ CutI.card = 2 ∧
        (∀ e ∈ CutI, (G.tail e ∈ I → G.head e ∈ V₀Fin) ∧ (G.head e ∈ I → G.tail e ∈ V₀Fin)) ∧
        (∀ e₁ ∈ CutI, ∀ e₂ ∈ CutI, e₁ ≠ e₂ →
          (if G.tail e₁ ∈ I then G.head e₁ else G.tail e₁) ≠
          (if G.tail e₂ ∈ I then G.head e₂ else G.tail e₂)) := by
      intro x hx I CutI
      have hIsub : I ⊆ H.verts := fun y hy => Finset.sdiff_subset (Finset.mem_filter.mp hy).1
      have hxI : x ∈ I := Finset.mem_filter.mpr ⟨hx, Relation.ReflTransGen.refl⟩
      have hIne : I.Nonempty := ⟨x, hxI⟩
      have hI_disj_V0 : Disjoint I V₀Fin := by
        rw [Finset.disjoint_left]
        intro y hy hy0
        exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hy).1).2 hy0
      have hV0_in_comp : V₀Fin ⊆ H.verts \ I := fun v hv =>
        Finset.mem_sdiff.mpr ⟨(Finset.mem_filter.mp hv).1, Finset.disjoint_right.mp hI_disj_V0 hv⟩
      have hIcomp_ne : (H.verts \ I).Nonempty := Finset.Nonempty.mono hV0_in_comp hV₀_ne
      -- `H[I]` is connected
      have hHI_conn : (subgraphRestrict H I).Connected := by
        refine ⟨hIne, fun a ha b hb => ?_⟩
        have hwalk : Relation.ReflTransGen Hdeg2.Adj a b :=
          Relation.ReflTransGen.trans (hcomp_symm (Finset.mem_filter.mp ha).2) (Finset.mem_filter.mp hb).2
        have hstep_in : ∀ {p q : V}, p ∈ I → Hdeg2.Adj p q → (subgraphRestrict H I).Adj p q := by
          intro p q hp ⟨e, he2, hadj⟩
          have heH : e ∈ H.edges := (Finset.mem_filter.mp he2).1
          have hq_sdiff : q ∈ H.verts \ V₀Fin := by
            rcases hadj with ⟨_, hh⟩ | ⟨ht, _⟩
            · rw [← hh]; exact (Finset.mem_filter.mp he2).2.2
            · rw [← ht]; exact (Finset.mem_filter.mp he2).2.1
          have hqI : q ∈ I := Finset.mem_filter.mpr ⟨hq_sdiff,
            Relation.ReflTransGen.tail (Finset.mem_filter.mp hp).2 ⟨e, he2, hadj⟩⟩
          refine ⟨e, Finset.mem_filter.mpr ⟨heH, ?_, ?_⟩, hadj⟩
          · rcases hadj with ⟨ht, _⟩ | ⟨ht, _⟩ <;> [exact ht ▸ hp; exact ht ▸ hqI]
          · rcases hadj with ⟨_, hh⟩ | ⟨_, hh⟩ <;> [exact hh ▸ hqI; exact hh ▸ hp]
        -- Induct along `hwalk` keeping current vertex in `I`
        have hlift : ∀ {p q : V}, p ∈ I → Relation.ReflTransGen Hdeg2.Adj p q →
            Relation.ReflTransGen (subgraphRestrict H I).Adj p q := by
          intro p q hp hpq
          induction hpq with
          | refl => exact Relation.ReflTransGen.refl
          | @tail r s hpr hrs ih =>
            have hrI : r ∈ I := by
              clear ih hrs
              induction hpr with
              | refl => exact hp
              | tail _ hstep' ih' =>
                rcases hstep' with ⟨e, he2, ⟨ht, hh⟩ | ⟨ht, hh⟩⟩
                · exact Finset.mem_filter.mpr ⟨hh ▸ (Finset.mem_filter.mp he2).2.2,
                    Relation.ReflTransGen.tail (Finset.mem_filter.mp ih').2 ⟨e, he2, Or.inl ⟨ht, hh⟩⟩⟩
                · exact Finset.mem_filter.mpr ⟨ht ▸ (Finset.mem_filter.mp he2).2.1,
                    Relation.ReflTransGen.tail (Finset.mem_filter.mp ih').2 ⟨e, he2, Or.inr ⟨ht, hh⟩⟩⟩
            exact Relation.ReflTransGen.tail ih (hstep_in hrI hrs)
        exact hlift ha hwalk
      -- Every vertex in `I` has `H.deg = 2`
      have hI_deg2 : ∀ y ∈ I, H.deg y = 2 := fun y hy => by
        have hyH := hIsub hy
        have hge2 := hH_deg_ge2 y hyH
        have hnot0 := Finset.disjoint_left.mp hI_disj_V0 hy
        have hlt3 : ¬ 3 ≤ H.deg y := fun h3 => hnot0 (Finset.mem_filter.mpr ⟨hyH, h3⟩)
        omega
      -- Handshake + connectivity give `CutI.card ≤ 2`
      have hhs := subgraph_cut_handshake H I hIsub
      have hsum2 : ∑ y ∈ I, H.deg y = 2 * I.card := by
        rw [Finset.sum_congr rfl hI_deg2]; simp [Nat.mul_comm]
      have hconn_e := connected_verts_le_edges_succ (subgraphRestrict H I) hHI_conn
      dsimp only [subgraphRestrict] at hconn_e
      have hcut_le2 : CutI.card ≤ 2 := by dsimp only [CutI, subgraphRestrict] at hhs ⊢; omega
      -- Step 3 applies; since `H.verts \ I` contains a vertex of `V₀Fin` (deg ≥ 3), the small side is `I`!
      obtain ⟨hside, hcut_eq2⟩ := hstep3 I hIsub hIne hIcomp_ne hcut_le2
      have hIle2 : I.card ≤ 2 := by
        rcases hside with ⟨h1, _⟩ | ⟨_, h2⟩
        · exact h1
        · rcases hV₀_ne with ⟨v₀, hv₀⟩
          have hd2 := h2 v₀ (hV0_in_comp hv₀)
          have hd3 := (Finset.mem_filter.mp hv₀).2
          omega
      have hHI_edges : (subgraphRestrict H I).edges.card + 1 = I.card := by
        dsimp only [subgraphRestrict] at hhs ⊢; omega
      -- Every edge of `CutI` has its outside endpoint in `V₀Fin`
      have hcut_to_V0 : ∀ e ∈ CutI, (G.tail e ∈ I → G.head e ∈ V₀Fin) ∧ (G.head e ∈ I → G.tail e ∈ V₀Fin) := by
        intro e he
        have heH := (Finset.mem_filter.mp he).1
        have hcr := (Finset.mem_filter.mp he).2
        constructor
        · intro htI
          have hh_notI : G.head e ∉ I := by rcases hcr with ⟨_, h⟩ | ⟨h, _⟩ <;> [exact h; exact absurd htI h]
          by_contra hh_notV0
          have hh_sdiff : G.head e ∈ H.verts \ V₀Fin := Finset.mem_sdiff.mpr ⟨H.head_mem heH, hh_notV0⟩
          have ht_sdiff : G.tail e ∈ H.verts \ V₀Fin := (Finset.mem_filter.mp htI).1
          have he2 : e ∈ Hdeg2.edges := Finset.mem_filter.mpr ⟨heH, ht_sdiff, hh_sdiff⟩
          exact hh_notI (Finset.mem_filter.mpr ⟨hh_sdiff,
            Relation.ReflTransGen.tail (Finset.mem_filter.mp htI).2 ⟨e, he2, Or.inl ⟨rfl, rfl⟩⟩⟩)
        · intro hhI
          have ht_notI : G.tail e ∉ I := by rcases hcr with ⟨_, h⟩ | ⟨h, _⟩ <;> [exact absurd hhI h; exact h]
          by_contra ht_notV0
          have ht_sdiff : G.tail e ∈ H.verts \ V₀Fin := Finset.mem_sdiff.mpr ⟨H.tail_mem heH, ht_notV0⟩
          have hh_sdiff : G.head e ∈ H.verts \ V₀Fin := (Finset.mem_filter.mp hhI).1
          have he2 : e ∈ Hdeg2.edges := Finset.mem_filter.mpr ⟨heH, ht_sdiff, hh_sdiff⟩
          exact ht_notI (Finset.mem_filter.mpr ⟨ht_sdiff,
            Relation.ReflTransGen.tail (Finset.mem_filter.mp hhI).2 ⟨e, he2, Or.inr ⟨rfl, rfl⟩⟩⟩)
      -- The two outside endpoints of `CutI` are distinct (else `I ∪ {u}` gives a cycle of length ≤ 3!)
      have hcut_distinct : ∀ e₁ ∈ CutI, ∀ e₂ ∈ CutI, e₁ ≠ e₂ →
          (if G.tail e₁ ∈ I then G.head e₁ else G.tail e₁) ≠
          (if G.tail e₂ ∈ I then G.head e₂ else G.tail e₂) := by
        intro e₁ he₁ e₂ he₂ hne heq
        let u := if G.tail e₁ ∈ I then G.head e₁ else G.tail e₁
        have hu_notI : u ∉ I := by
          have hcr := (Finset.mem_filter.mp he₁).2
          dsimp only [u]; split_ifs with ht
          · rcases hcr with ⟨_, h⟩ | ⟨h, _⟩ <;> [exact h; exact absurd ht h]
          · rcases hcr with ⟨h, _⟩ | ⟨h, _⟩ <;> [exact absurd h ht; exact h]
        -- Build the subgraph `C = (insert u I, (H[I]).edges ∪ CutI)` — every vertex has degree 2, connected, ≤ 3 edges!
        have hCut_eq : CutI = {e₁, e₂} := by
          symm
          apply Finset.eq_of_subset_of_card_le
          · intro e he; simp only [Finset.mem_insert, Finset.mem_singleton] at he
            rcases he with rfl | rfl <;> assumption
          · rw [Finset.card_pair hne]; exact le_of_eq hcut_eq2
        have he_ends : ∀ e ∈ CutI, (G.tail e ∈ I ∧ G.head e = u) ∨ (G.tail e = u ∧ G.head e ∈ I) := by
          intro e he
          rw [hCut_eq, Finset.mem_insert, Finset.mem_singleton] at he
          rcases he with h | h
          · subst h
            have hcr := (Finset.mem_filter.mp he₁).2
            by_cases ht : G.tail e ∈ I
            · left; exact ⟨ht, by simp [u, ht]⟩
            · right; exact ⟨by simp [u, ht], (hcr.resolve_left (fun h' => ht h'.1)).2⟩
          · subst h
            have hcr := (Finset.mem_filter.mp he₂).2
            by_cases ht : G.tail e ∈ I
            · left; exact ⟨ht, by simp [u, heq, ht]⟩
            · right; exact ⟨by simp [u, heq, ht], (hcr.resolve_left (fun h' => ht h'.1)).2⟩
        let Csub : G.Subgraph :=
          { verts := insert u I
            edges := (subgraphRestrict H I).edges ∪ CutI
            tail_mem := fun {e} he => by
              rw [Finset.mem_union] at he
              rcases he with h1 | h2
              · exact Finset.mem_insert_of_mem (Finset.mem_filter.mp h1).2.1
              · rcases he_ends e h2 with ⟨ht, _⟩ | ⟨ht, _⟩
                · exact Finset.mem_insert_of_mem ht
                · exact ht ▸ Finset.mem_insert_self _ _
            head_mem := fun {e} he => by
              rw [Finset.mem_union] at he
              rcases he with h1 | h2
              · exact Finset.mem_insert_of_mem (Finset.mem_filter.mp h1).2.2
              · rcases he_ends e h2 with ⟨_, hh⟩ | ⟨_, hh⟩
                · exact hh ▸ Finset.mem_insert_self _ _
                · exact Finset.mem_insert_of_mem hh }
        have hCsub_deg : ∀ v ∈ Csub.verts, Csub.deg v = 2 := by
          intro v hv
          rw [Finset.mem_insert] at hv
          rcases hv with rfl | hvI
          · -- `v = u`: only `e₁, e₂ ∈ CutI` meet `u`, each once (loopless)
            unfold Subgraph.deg
            have hdisj_e : Disjoint (subgraphRestrict H I).edges CutI := by
              rw [Finset.disjoint_left]; intro e h1 h2
              have ⟨ht, hh⟩ := (Finset.mem_filter.mp h1).2
              rcases (Finset.mem_filter.mp h2).2 with ⟨_, h⟩ | ⟨h, _⟩ <;> [exact h hh; exact h ht]
            simp only [Csub, Finset.card_filter, Finset.sum_union hdisj_e]
            have h0t : ∑ e ∈ (subgraphRestrict H I).edges, (if G.tail e = u then 1 else 0) = 0 :=
              Finset.sum_eq_zero (fun e he => ite_eq_right_iff.mpr (fun h => absurd (h ▸ (Finset.mem_filter.mp he).2.1) hu_notI))
            have h0h : ∑ e ∈ (subgraphRestrict H I).edges, (if G.head e = u then 1 else 0) = 0 :=
              Finset.sum_eq_zero (fun e he => ite_eq_right_iff.mpr (fun h => absurd (h ▸ (Finset.mem_filter.mp he).2.2) hu_notI))
            rw [h0t, h0h, zero_add, zero_add, hCut_eq, Finset.sum_pair hne, Finset.sum_pair hne]
            have h1 : (if G.tail e₁ = u then 1 else 0) + (if G.head e₁ = u then 1 else 0) = 1 := by
              rcases he_ends e₁ he₁ with ⟨ht, hh⟩ | ⟨ht, hh⟩
              · have hne' : G.tail e₁ ≠ u := fun h => hu_notI (h ▸ ht)
                simp [hne', hh]
              · have hne' : G.head e₁ ≠ u := fun h => hu_notI (h ▸ hh)
                simp [ht, hne']
            have h2 : (if G.tail e₂ = u then 1 else 0) + (if G.head e₂ = u then 1 else 0) = 1 := by
              rcases he_ends e₂ he₂ with ⟨ht, hh⟩ | ⟨ht, hh⟩
              · have hne' : G.tail e₂ ≠ u := fun h => hu_notI (h ▸ ht)
                simp [hne', hh]
              · have hne' : G.head e₂ ≠ u := fun h => hu_notI (h ▸ hh)
                simp [ht, hne']
            omega
          · -- `v ∈ I`: every edge of `H` incident to `v` lies in `Csub.edges`!
            have hdeg_eq : Csub.deg v = H.deg v := by
              unfold Subgraph.deg
              congr 1 <;> congr 1 <;> ext e <;> simp only [Csub, subgraphRestrict, CutI,
                Finset.mem_filter, Finset.mem_union]
              · constructor
                · rintro ⟨⟨he, _⟩ | ⟨he, _⟩, ht⟩ <;> exact ⟨he, ht⟩
                · rintro ⟨he, ht⟩
                  by_cases hh : G.head e ∈ I
                  · exact ⟨Or.inl ⟨he, ht ▸ hvI, hh⟩, ht⟩
                  · exact ⟨Or.inr ⟨he, Or.inl ⟨ht ▸ hvI, hh⟩⟩, ht⟩
              · constructor
                · rintro ⟨⟨he, _⟩ | ⟨he, _⟩, hh⟩ <;> exact ⟨he, hh⟩
                · rintro ⟨he, hh⟩
                  by_cases ht : G.tail e ∈ I
                  · exact ⟨Or.inl ⟨he, ht, hh ▸ hvI⟩, hh⟩
                  · exact ⟨Or.inr ⟨he, Or.inr ⟨ht, hh ▸ hvI⟩⟩, hh⟩
            rw [hdeg_eq, hI_deg2 v hvI]
        -- `Csub` has no vertex of degree 1 and has edges, so contains a cycle of ≤ 3 edges!
        have hCsub_ne : Csub.edges.Nonempty := ⟨e₁, Finset.mem_union_right _ he₁⟩
        obtain ⟨D, hDC⟩ := exists_directedCycle_of_no_deg_one Csub hCsub_ne (fun v hv => by rw [hCsub_deg v hv]; omega)
        have hge6 := hgirth D.sub D.isCycle
        have hle_e : D.sub.edges.card ≤ Csub.edges.card := Finset.card_le_card hDC.2
        have hCsub_e : Csub.edges.card ≤ 3 := by
          calc Csub.edges.card ≤ (subgraphRestrict H I).edges.card + CutI.card := Finset.card_union_le _ _
            _ ≤ 3 := by omega
        omega
      exact ⟨hIle2, hHI_edges, hcut_eq2, hcut_to_V0, hcut_distinct⟩
    -- Build `SubdivisionData G H`!
    -- `V₀` = `{v : V // v ∈ V₀Fin}`
    -- `E₀` = `{e : E // e ∈ H.edges ∧ G.tail e ∈ V₀Fin ∧ G.head e ∈ V₀Fin} ⊕ {I : Finset V // ∃ x ∈ H.verts \ V₀Fin, I = compOf x}`
    let DirectE := {e : E // e ∈ H.edges ∧ G.tail e ∈ V₀Fin ∧ G.head e ∈ V₀Fin}
    let CompSet : Finset (Finset V) := (H.verts \ V₀Fin).image compOf
    let ThreadI := {I : Finset V // I ∈ CompSet}
    let E₀Type := DirectE ⊕ ThreadI
    -- For each `I ∈ CompSet`, build its `u₁, u₂ ∈ V₀Fin` and `ThreadPath` cleanly
    have hcomp_data : ∀ I : ThreadI,
        ∃ (u₁ u₂ : {v : V // v ∈ V₀Fin}) (tp : ThreadPath G H u₁.1 u₂.1),
          u₁ ≠ u₂ ∧
          (∀ v, v ∈ tp.verts ↔ v = u₁.1 ∨ v = u₂.1 ∨ v ∈ I.1) ∧
          (∀ e, e ∈ tp.edges ↔
            e ∈ (subgraphRestrict H I.1).edges ∨
            e ∈ H.edges.filter (fun e =>
              (G.tail e ∈ I.1 ∧ G.head e ∉ I.1) ∨ (G.tail e ∉ I.1 ∧ G.head e ∈ I.1))) := by
      intro ⟨I, hI_mem⟩
      rw [Finset.mem_image] at hI_mem
      rcases hI_mem with ⟨x, hx, rfl⟩
      obtain ⟨hIle2, hHI_edges, hcut_eq2, hcut_to_V0, hcut_distinct⟩ := hcomp_props x hx
      let I' := compOf x
      let CutI := H.edges.filter (fun e =>
        (G.tail e ∈ I' ∧ G.head e ∉ I') ∨ (G.tail e ∉ I' ∧ G.head e ∈ I'))
      have hxI : x ∈ I' := Finset.mem_filter.mpr ⟨hx, Relation.ReflTransGen.refl⟩
      have hI_disj_V0 : Disjoint I' V₀Fin := by
        rw [Finset.disjoint_left]; intro y hy hy0
        exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hy).1).2 hy0
      rw [Finset.card_eq_two] at hcut_eq2
      rcases hcut_eq2 with ⟨ea, eb, heab, hCut_pair⟩
      have hCut_pair' : CutI = {ea, eb} := hCut_pair
      have hea_in : ea ∈ CutI := hCut_pair' ▸ Finset.mem_insert_self _ _
      have heb_in : eb ∈ CutI := hCut_pair' ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      let ua_v := if G.tail ea ∈ I' then G.head ea else G.tail ea
      let ub_v := if G.tail eb ∈ I' then G.head eb else G.tail eb
      have hua_V0 : ua_v ∈ V₀Fin := by
        dsimp only [ua_v]; split_ifs with ht
        · exact (hcut_to_V0 ea hea_in).1 ht
        · have hh : G.head ea ∈ I' := (Finset.mem_filter.mp hea_in).2.resolve_left (fun h => ht h.1) |>.2
          exact (hcut_to_V0 ea hea_in).2 hh
      have hub_V0 : ub_v ∈ V₀Fin := by
        dsimp only [ub_v]; split_ifs with ht
        · exact (hcut_to_V0 eb heb_in).1 ht
        · have hh : G.head eb ∈ I' := (Finset.mem_filter.mp heb_in).2.resolve_left (fun h => ht h.1) |>.2
          exact (hcut_to_V0 eb heb_in).2 hh
      have huab_ne : ua_v ≠ ub_v := hcut_distinct ea hea_in eb heb_in heab
      have hua_notI : ua_v ∉ I' := Finset.disjoint_right.mp hI_disj_V0 hua_V0
      have hub_notI : ub_v ∉ I' := Finset.disjoint_right.mp hI_disj_V0 hub_V0
      have hea_conn : ∀ (z : V), (G.tail ea ∈ I' → G.tail ea = z) → (G.head ea ∈ I' → G.head ea = z) →
          (G.tail ea = ua_v ∧ G.head ea = z) ∨ (G.tail ea = z ∧ G.head ea = ua_v) := by
        intro z htz hhz
        by_cases ht : G.tail ea ∈ I'
        · right; exact ⟨htz ht, by simp [ua_v, ht]⟩
        · left
          have hh : G.head ea ∈ I' := (Finset.mem_filter.mp hea_in).2.resolve_left (fun h => ht h.1) |>.2
          exact ⟨by simp [ua_v, ht], hhz hh⟩
      have heb_conn : ∀ (z : V), (G.tail eb ∈ I' → G.tail eb = z) → (G.head eb ∈ I' → G.head eb = z) →
          (G.tail eb = z ∧ G.head eb = ub_v) ∨ (G.tail eb = ub_v ∧ G.head eb = z) := by
        intro z htz hhz
        by_cases ht : G.tail eb ∈ I'
        · left; exact ⟨htz ht, by simp [ub_v, ht]⟩
        · right
          have hh : G.head eb ∈ I' := (Finset.mem_filter.mp heb_in).2.resolve_left (fun h => ht h.1) |>.2
          exact ⟨by simp [ub_v, ht], hhz hh⟩
      -- Case split `I'.card = 1` vs `I'.card = 2`
      by_cases hI1 : I'.card = 1
      · have hI_eq : I' = {x} := (Finset.card_eq_one.mp hI1).elim (fun y hy => by
          have : x = y := Finset.mem_singleton.mp (hy ▸ hxI)
          subst this; exact hy)
        have hHI_empty : (subgraphRestrict H I').edges = ∅ :=
          Finset.card_eq_zero.mp (by dsimp only [I'] at hI1 ⊢; omega)
        have hxa : x ≠ ua_v := fun h => hua_notI (h ▸ hxI)
        have hxb : x ≠ ub_v := fun h => hub_notI (h ▸ hxI)
        let tp : ThreadPath G H ua_v ub_v :=
          { verts := [ua_v, x, ub_v]
            edges := [ea, eb]
            len_pos := by simp
            len_le := by simp
            verts_len := rfl
            verts_nodup := by simp [huab_ne, hxa.symm, hxb]
            verts_sub := fun v hv => by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
              rcases hv with rfl | rfl | rfl
              · exact (Finset.mem_filter.mp hua_V0).1
              · exact (Finset.mem_sdiff.mp hx).1
              · exact (Finset.mem_filter.mp hub_V0).1
            edges_sub := fun e he => by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at he
              rcases he with rfl | rfl
              · exact (Finset.mem_filter.mp hea_in).1
              · exact (Finset.mem_filter.mp heb_in).1
            head_eq := rfl
            last_eq := rfl
            step_connect := fun i hi => by
              have hi2 : i = 0 ∨ i = 1 := by simp at hi; omega
              rcases hi2 with rfl | rfl
              · exact hea_conn x (fun h => Finset.mem_singleton.mp (hI_eq ▸ h))
                  (fun h => Finset.mem_singleton.mp (hI_eq ▸ h))
              · exact heb_conn x (fun h => Finset.mem_singleton.mp (hI_eq ▸ h))
                  (fun h => Finset.mem_singleton.mp (hI_eq ▸ h)) }
        refine ⟨⟨ua_v, hua_V0⟩, ⟨ub_v, hub_V0⟩, tp, fun h => huab_ne (congrArg Subtype.val h), ?_, ?_⟩
        · intro v
          change v ∈ [ua_v, x, ub_v] ↔ v = ua_v ∨ v = ub_v ∨ v ∈ I'
          rw [hI_eq]
          simp only [List.mem_cons, List.not_mem_nil, or_false, Finset.mem_singleton]
          exact ⟨fun h => by rcases h with rfl | rfl | rfl <;> simp,
                 fun h => by rcases h with rfl | rfl | rfl <;> simp⟩
        · intro e
          change e ∈ [ea, eb] ↔ e ∈ (subgraphRestrict H I').edges ∨ e ∈ CutI
          rw [hHI_empty, hCut_pair']
          simp only [List.mem_cons, List.not_mem_nil, or_false, Finset.notMem_empty, false_or,
            Finset.mem_insert, Finset.mem_singleton]
      · -- `I'.card = 2`: `I' = {y₁, y₂}` with 1 internal edge `em`, `ea` hits `y₁` and `eb` hits `y₂`
        have hI2 : I'.card = 2 := by have := Finset.card_pos.mpr ⟨x, hxI⟩; dsimp only [I'] at hI1 ⊢; omega
        have hHI_e1 : (subgraphRestrict H I').edges.card = 1 := by dsimp only [I'] at hI2 ⊢; omega
        rw [Finset.card_eq_one] at hHI_e1
        rcases hHI_e1 with ⟨em, hem_eq⟩
        have hem_in : em ∈ (subgraphRestrict H I').edges := hem_eq ▸ Finset.mem_singleton_self _
        have hem_H : em ∈ H.edges := (Finset.mem_filter.mp hem_in).1
        have hem_tI : G.tail em ∈ I' := (Finset.mem_filter.mp hem_in).2.1
        have hem_hI : G.head em ∈ I' := (Finset.mem_filter.mp hem_in).2.2
        have hI_pair : I' = {G.tail em, G.head em} := by
          symm
          apply Finset.eq_of_subset_of_card_le
          · intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
            rcases hz with rfl | rfl <;> assumption
          · rw [Finset.card_pair (hll em)]; exact le_of_eq hI2
        -- Let `y₁` be the `I'`-endpoint of `ea` and `y₂` be the other vertex of `I'`
        let y₁ := if G.tail ea ∈ I' then G.tail ea else G.head ea
        have hy₁_I : y₁ ∈ I' := by
          dsimp only [y₁]; split_ifs with ht
          · exact ht
          · exact (Finset.mem_filter.mp hea_in).2.resolve_left (fun h => ht h.1) |>.2
        let y₂ := if y₁ = G.tail em then G.head em else G.tail em
        have hy₂_I : y₂ ∈ I' := by dsimp only [y₂]; split_ifs <;> assumption
        have hy12_ne : y₁ ≠ y₂ := by
          dsimp only [y₂]; split_ifs with h
          · exact h ▸ hll em
          · exact h
        have hI_y12 : I' = {y₁, y₂} := by
          symm
          apply Finset.eq_of_subset_of_card_le
          · intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz
            rcases hz with rfl | rfl <;> assumption
          · rw [Finset.card_pair hy12_ne]; exact le_of_eq hI2
        have hem_y12 : (G.tail em = y₁ ∧ G.head em = y₂) ∨ (G.tail em = y₂ ∧ G.head em = y₁) := by
          have hy1_cases : y₁ = G.tail em ∨ y₁ = G.head em := by
            have := hy₁_I; rw [hI_pair, Finset.mem_insert, Finset.mem_singleton] at this; exact this
          rcases hy1_cases with h | h
          · left; exact ⟨h.symm, by simp [y₂, h]⟩
          · right; exact ⟨by simp [y₂, h, (hll em).symm], h.symm⟩
        -- `eb`'s endpoint inside `I'` MUST be `y₂` (since `H.deg y₁ = 2` and `em, ea` already hit `y₁`!)
        let yb := if G.tail eb ∈ I' then G.tail eb else G.head eb
        have hyb_I : yb ∈ I' := by
          dsimp only [yb]; split_ifs with ht
          · exact ht
          · exact (Finset.mem_filter.mp heb_in).2.resolve_left (fun h => ht h.1) |>.2
        have hyb_eq_y2 : yb = y₂ := by
          have hcases : yb = y₁ ∨ yb = y₂ := by
            have := hyb_I; rw [hI_y12, Finset.mem_insert, Finset.mem_singleton] at this; exact this
          rcases hcases with h1 | h2
          · exfalso
            -- Three distinct edges `em, ea, eb` in `H.edges` all hit `y₁`, contradicting `H.deg y₁ = 2`!
            have hem_ne_ea : em ≠ ea := fun h => by
              have hcr := (Finset.mem_filter.mp hea_in).2
              rw [← h] at hcr
              rcases hcr with ⟨_, hh⟩ | ⟨ht, _⟩ <;> [exact hh hem_hI; exact ht hem_tI]
            have hem_ne_eb : em ≠ eb := fun h => by
              have hcr := (Finset.mem_filter.mp heb_in).2
              rw [← h] at hcr
              rcases hcr with ⟨_, hh⟩ | ⟨ht, _⟩ <;> [exact hh hem_hI; exact ht hem_tI]
            have hinc : ∀ e ∈ ({em, ea, eb} : Finset E), e ∈ H.edges ∧ (G.tail e = y₁ ∨ G.head e = y₁) := by
              intro e he
              simp only [Finset.mem_insert, Finset.mem_singleton] at he
              rcases he with rfl | rfl | rfl
              · exact ⟨hem_H, by rcases hem_y12 with ⟨ht, _⟩ | ⟨_, hh⟩ <;> [exact Or.inl ht; exact Or.inr hh]⟩
              · refine ⟨(Finset.mem_filter.mp hea_in).1, ?_⟩
                dsimp only [y₁]; split_ifs with ht <;> [exact Or.inl rfl; exact Or.inr rfl]
              · refine ⟨(Finset.mem_filter.mp heb_in).1, ?_⟩
                rw [← h1]; dsimp only [yb]; split_ifs with ht <;> [exact Or.inl rfl; exact Or.inr rfl]
            have h3sub : ({em, ea, eb} : Finset E) ⊆
                H.edges.filter (fun e => G.tail e = y₁) ∪ H.edges.filter (fun e => G.head e = y₁) := by
              intro e he
              obtain ⟨heH, ht | hh⟩ := hinc e he
              · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨heH, ht⟩)
              · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨heH, hh⟩)
            have hcard3 : ({em, ea, eb} : Finset E).card = 3 := by
              rw [Finset.card_insert_of_notMem (by simp [hem_ne_ea, hem_ne_eb]), Finset.card_pair heab]
            have hdeg_ge3 : 3 ≤ H.deg y₁ := by
              unfold Subgraph.deg
              calc 3 = ({em, ea, eb} : Finset E).card := hcard3.symm
                _ ≤ (H.edges.filter (fun e => G.tail e = y₁) ∪ H.edges.filter (fun e => G.head e = y₁)).card :=
                    Finset.card_le_card h3sub
                _ ≤ _ := Finset.card_union_le _ _
            have hy1_sdiff := (Finset.mem_filter.mp hy₁_I).1
            exact (Finset.mem_sdiff.mp hy1_sdiff).2 (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hy1_sdiff).1, hdeg_ge3⟩)
          · exact h2
        have hea_y1 : (G.tail ea = ua_v ∧ G.head ea = y₁) ∨ (G.tail ea = y₁ ∧ G.head ea = ua_v) := by
          by_cases ht : G.tail ea ∈ I'
          · right; exact ⟨by simp [y₁, ht], by simp [ua_v, ht]⟩
          · left; exact ⟨by simp [ua_v, ht], by simp [y₁, ht]⟩
        have heb_y2 : (G.tail eb = y₂ ∧ G.head eb = ub_v) ∨ (G.tail eb = ub_v ∧ G.head eb = y₂) := by
          rw [← hyb_eq_y2]
          by_cases ht : G.tail eb ∈ I'
          · left; exact ⟨by simp [yb, ht], by simp [ub_v, ht]⟩
          · right; exact ⟨by simp [ub_v, ht], by simp [yb, ht]⟩
        have hy1_not_ua : y₁ ≠ ua_v := fun h => hua_notI (h ▸ hy₁_I)
        have hy2_not_ua : y₂ ≠ ua_v := fun h => hua_notI (h ▸ hy₂_I)
        have hy1_not_ub : y₁ ≠ ub_v := fun h => hub_notI (h ▸ hy₁_I)
        have hy2_not_ub : y₂ ≠ ub_v := fun h => hub_notI (h ▸ hy₂_I)
        let tp : ThreadPath G H ua_v ub_v :=
          { verts := [ua_v, y₁, y₂, ub_v]
            edges := [ea, em, eb]
            len_pos := by simp
            len_le := by simp
            verts_len := rfl
            verts_nodup := by
              simp [huab_ne, hy1_not_ua.symm, hy2_not_ua.symm, hy12_ne, hy1_not_ub, hy2_not_ub]
            verts_sub := fun v hv => by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
              rcases hv with rfl | rfl | rfl | rfl
              · exact (Finset.mem_filter.mp hua_V0).1
              · exact Finset.sdiff_subset (Finset.mem_filter.mp hy₁_I).1
              · exact Finset.sdiff_subset (Finset.mem_filter.mp hy₂_I).1
              · exact (Finset.mem_filter.mp hub_V0).1
            edges_sub := fun e he => by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at he
              rcases he with rfl | rfl | rfl
              · exact (Finset.mem_filter.mp hea_in).1
              · exact hem_H
              · exact (Finset.mem_filter.mp heb_in).1
            head_eq := rfl
            last_eq := rfl
            step_connect := fun i hi => by
              have hi3 : i = 0 ∨ i = 1 ∨ i = 2 := by simp at hi; omega
              rcases hi3 with rfl | rfl | rfl
              · exact hea_y1
              · exact hem_y12
              · exact heb_y2 }
        refine ⟨⟨ua_v, hua_V0⟩, ⟨ub_v, hub_V0⟩, tp, fun h => huab_ne (congrArg Subtype.val h), ?_, ?_⟩
        · intro v
          change v ∈ [ua_v, y₁, y₂, ub_v] ↔ v = ua_v ∨ v = ub_v ∨ v ∈ I'
          rw [hI_y12]
          simp only [List.mem_cons, List.not_mem_nil, or_false, Finset.mem_insert, Finset.mem_singleton]
          exact ⟨fun h => by rcases h with rfl | rfl | rfl | rfl <;> simp,
                 fun h => by rcases h with rfl | rfl | rfl | rfl <;> simp⟩
        · intro e
          change e ∈ [ea, em, eb] ↔ e ∈ (subgraphRestrict H I').edges ∨ e ∈ CutI
          rw [hem_eq, hCut_pair']
          simp only [List.mem_cons, List.not_mem_nil, or_false, Finset.mem_singleton, Finset.mem_insert]
          exact ⟨fun h => by rcases h with rfl | rfl | rfl <;> simp,
                 fun h => by rcases h with rfl | rfl | rfl <;> simp⟩
    -- Assemble `H₀` and `SubdivisionData G H`
    let H₀G : Multigraph {v : V // v ∈ V₀Fin} E₀Type :=
      { tail := fun t => match t with
          | Sum.inl e => ⟨G.tail e.1, e.2.2.1⟩
          | Sum.inr I => (hcomp_data I).choose
        head := fun t => match t with
          | Sum.inl e => ⟨G.head e.1, e.2.2.2⟩
          | Sum.inr I => (hcomp_data I).choose_spec.choose }
    let threadFn : ∀ t : E₀Type, ThreadPath G H (H₀G.tail t).1 (H₀G.head t).1 := fun t =>
      match t with
      | Sum.inl e =>
        { verts := [G.tail e.1, G.head e.1]
          edges := [e.1]
          len_pos := by simp
          len_le := by simp
          verts_len := rfl
          verts_nodup := by simp [hll e.1]
          verts_sub := fun v hv => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
            rcases hv with rfl | rfl
            · exact H.tail_mem e.2.1
            · exact H.head_mem e.2.1
          edges_sub := fun e' he' => by simp only [List.mem_singleton] at he'; exact he' ▸ e.2.1
          head_eq := rfl
          last_eq := rfl
          step_connect := fun i hi => by
            have hi0 : i = 0 := by simp at hi; omega
            subst hi0; left; exact ⟨rfl, rfl⟩ }
      | Sum.inr I => (hcomp_data I).choose_spec.choose_spec.choose
    have hH0_ll : H₀G.IsLoopless := by
      intro t
      cases t with
      | inl e => intro h; exact hll e.1 (congrArg Subtype.val h)
      | inr I => exact (hcomp_data I).choose_spec.choose_spec.choose_spec.1
    have hH0_card2 : 2 ≤ Fintype.card {v : V // v ∈ V₀Fin} := by
      rcases hV₀_ne with ⟨v₀, hv₀⟩
      -- `v₀` has an incident edge in `H`, hence lies on some thread, whose other end is in `V₀Fin \ {v₀}`!
      have hv₀_deg3 := (Finset.mem_filter.mp hv₀).2
      have hex_e : ∃ e ∈ H.edges, G.tail e = v₀ ∨ G.head e = v₀ := by
        unfold Subgraph.deg at hv₀_deg3
        by_cases ht : 0 < (H.edges.filter (fun e => G.tail e = v₀)).card
        · rcases Finset.card_pos.mp ht with ⟨e, he⟩
          exact ⟨e, (Finset.mem_filter.mp he).1, Or.inl (Finset.mem_filter.mp he).2⟩
        · have hh : 0 < (H.edges.filter (fun e => G.head e = v₀)).card := by omega
          rcases Finset.card_pos.mp hh with ⟨e, he⟩
          exact ⟨e, (Finset.mem_filter.mp he).1, Or.inr (Finset.mem_filter.mp he).2⟩
      rcases hex_e with ⟨e, heH, ht | hh⟩
      · by_cases hh0 : G.head e ∈ V₀Fin
        · have hne : (⟨v₀, hv₀⟩ : {v : V // v ∈ V₀Fin}) ≠ ⟨G.head e, hh0⟩ :=
            fun h => hll e (ht.trans (congrArg Subtype.val h))
          have := Fintype.one_lt_card_iff.mpr
            ⟨(⟨v₀, hv₀⟩ : {v : V // v ∈ V₀Fin}), (⟨G.head e, hh0⟩ : {v : V // v ∈ V₀Fin}), hne⟩
          omega
        · have hx : G.head e ∈ H.verts \ V₀Fin := Finset.mem_sdiff.mpr ⟨H.head_mem heH, hh0⟩
          let I : ThreadI := ⟨compOf (G.head e), Finset.mem_image.mpr ⟨G.head e, hx, rfl⟩⟩
          have hne := hH0_ll (Sum.inr I)
          have := Fintype.one_lt_card_iff.mpr ⟨H₀G.tail (Sum.inr I), H₀G.head (Sum.inr I), hne⟩; omega
      · by_cases ht0 : G.tail e ∈ V₀Fin
        · have hne : (⟨G.tail e, ht0⟩ : {v : V // v ∈ V₀Fin}) ≠ ⟨v₀, hv₀⟩ :=
            fun h => hll e ((congrArg Subtype.val h).trans hh.symm)
          have := Fintype.one_lt_card_iff.mpr
            ⟨(⟨G.tail e, ht0⟩ : {v : V // v ∈ V₀Fin}), (⟨v₀, hv₀⟩ : {v : V // v ∈ V₀Fin}), hne⟩
          omega
        · have hx : G.tail e ∈ H.verts \ V₀Fin := Finset.mem_sdiff.mpr ⟨H.tail_mem heH, ht0⟩
          let I : ThreadI := ⟨compOf (G.tail e), Finset.mem_image.mpr ⟨G.tail e, hx, rfl⟩⟩
          have hne := hH0_ll (Sum.inr I)
          have := Fintype.one_lt_card_iff.mpr ⟨H₀G.tail (Sum.inr I), H₀G.head (Sum.inr I), hne⟩; omega
    -- `H₀G` is 3-edge-connected via Step 3
    have hH0_3ec : H₀G.IsEdgeConnected 3 := by
      intro S hSne hScomp
      -- Lift `S` to `U ⊆ H.verts`: include `S` plus each component `I` whose `tail (inr I) ∈ S`
      let S_V : Finset V := S.image Subtype.val
      let U : Finset V := H.verts.filter (fun v =>
        v ∈ S_V ∨ ∃ (I : ThreadI), v ∈ I.1 ∧ H₀G.tail (Sum.inr I) ∈ S)
      have hUsub : U ⊆ H.verts := Finset.filter_subset _ _
      have hUne : U.Nonempty := by
        rcases hSne with ⟨u, huS⟩
        exact ⟨u.1, Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp u.2).1,
          Or.inl (Finset.mem_image.mpr ⟨u, huS, rfl⟩)⟩⟩
      have hUcomp : (H.verts \ U).Nonempty := by
        rcases hScomp with ⟨w, hwS⟩
        have hw_notS : w ∉ S := (Finset.mem_sdiff.mp hwS).2
        refine ⟨w.1, Finset.mem_sdiff.mpr ⟨(Finset.mem_filter.mp w.2).1, fun hwU => ?_⟩⟩
        rcases (Finset.mem_filter.mp hwU).2 with h1 | ⟨I, hwI, _⟩
        · rcases Finset.mem_image.mp h1 with ⟨u, huS, huw⟩
          exact hw_notS (Subtype.ext huw ▸ huS)
        · rcases Finset.mem_image.mp I.2 with ⟨x, _, hIx⟩
          rw [← hIx] at hwI
          exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hwI).1).2 w.2
      -- Every vertex of `U` and `H.verts \ U` includes a vertex of `V₀Fin` (deg ≥ 3), so Step 3 forces `cut(U) ≥ 3`!
      have hcutU_ge3 : 3 ≤ (H.edges.filter (fun e =>
          (G.tail e ∈ U ∧ G.head e ∉ U) ∨ (G.tail e ∉ U ∧ G.head e ∈ U))).card := by
        by_contra hlt3
        obtain ⟨hside, _⟩ := hstep3 U hUsub hUne hUcomp (by omega)
        rcases hside with ⟨_, hall2⟩ | ⟨_, hall2⟩
        · rcases hSne with ⟨u, huS⟩
          have huU : u.1 ∈ U := Finset.mem_filter.mpr
            ⟨(Finset.mem_filter.mp u.2).1, Or.inl (Finset.mem_image.mpr ⟨u, huS, rfl⟩)⟩
          have hd2 := hall2 u.1 huU
          have hd3 := (Finset.mem_filter.mp u.2).2
          omega
        · rcases hScomp with ⟨w, hwS⟩
          have hw_notS : w ∉ S := (Finset.mem_sdiff.mp hwS).2
          have hw_notU : w.1 ∉ U := fun hwU => by
            rcases (Finset.mem_filter.mp hwU).2 with h1 | ⟨I, hwI, _⟩
            · rcases Finset.mem_image.mp h1 with ⟨u, huS, huw⟩
              exact hw_notS (Subtype.ext huw ▸ huS)
            · rcases Finset.mem_image.mp I.2 with ⟨x, _, hIx⟩
              rw [← hIx] at hwI
              exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hwI).1).2 w.2
          have hd2 := hall2 w.1 (Finset.mem_sdiff.mpr ⟨(Finset.mem_filter.mp w.2).1, hw_notU⟩)
          have hd3 := (Finset.mem_filter.mp w.2).2
          omega
      -- Map each `e ∈ Cut(U)` injectively into `H₀G.cutEdges S`!
      let CutU := H.edges.filter (fun e =>
        (G.tail e ∈ U ∧ G.head e ∉ U) ∨ (G.tail e ∉ U ∧ G.head e ∈ U))
      -- Helper: unique membership of each vertex `v ∈ V₀Fin` in `U ↔ v ∈ S`
      have hV0_in_U : ∀ v : {v : V // v ∈ V₀Fin}, v.1 ∈ U ↔ v ∈ S := by
        intro v
        constructor
        · intro hvU
          rcases (Finset.mem_filter.mp hvU).2 with h1 | ⟨I, hvI, _⟩
          · rcases Finset.mem_image.mp h1 with ⟨u, huS, huv⟩
            exact Subtype.ext huv ▸ huS
          · rcases Finset.mem_image.mp I.2 with ⟨x, _, hIx⟩
            rw [← hIx] at hvI
            exact absurd v.2 (Finset.mem_sdiff.mp (Finset.mem_filter.mp hvI).1).2
        · intro hvS
          exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp v.2).1,
            Or.inl (Finset.mem_image.mpr ⟨v, hvS, rfl⟩)⟩
      -- Helper: for `x ∈ H.verts \ V₀Fin`, `x ∈ U ↔ tail (inr (compOf x)) ∈ S`
      have hcomp_in_U : ∀ (I : ThreadI) (y : V), y ∈ I.1 → (y ∈ U ↔ H₀G.tail (Sum.inr I) ∈ S) := by
        intro I y hyI
        rcases Finset.mem_image.mp I.2 with ⟨x, hx, hIx⟩
        have hy_sdiff : y ∈ H.verts \ V₀Fin := by
          rw [← hIx] at hyI; exact (Finset.mem_filter.mp hyI).1
        constructor
        · intro hyU
          rcases (Finset.mem_filter.mp hyU).2 with h1 | ⟨J, hyJ, hJS⟩
          · rcases Finset.mem_image.mp h1 with ⟨u, _, huy⟩
            exact absurd (huy ▸ u.2) (Finset.mem_sdiff.mp hy_sdiff).2
          · rcases Finset.mem_image.mp J.2 with ⟨x', hx', hJx'⟩
            have hIJ : I = J := Subtype.ext (by
              rw [← hIx, ← hJx']
              have h1 := hcomp_eq_of_mem hx (hIx.symm ▸ hyI)
              have h2 := hcomp_eq_of_mem hx' (hJx'.symm ▸ hyJ)
              exact h1.symm.trans h2)
            exact hIJ ▸ hJS
        · intro hIS
          exact Finset.mem_filter.mpr ⟨Finset.sdiff_subset hy_sdiff, Or.inr ⟨I, hyI, hIS⟩⟩
      -- Every edge `e ∈ CutU` belongs to a thread `t ∈ H₀G.cutEdges S`, and distinct edges of `CutU` map to distinct threads!
      have hmap : ∀ e ∈ CutU, ∃ t ∈ H₀G.cutEdges S, e ∈ (threadFn t).edges := by
        intro e he
        have heH := (Finset.mem_filter.mp he).1
        have hcr := (Finset.mem_filter.mp he).2
        by_cases ht0 : G.tail e ∈ V₀Fin
        · by_cases hh0 : G.head e ∈ V₀Fin
          · refine ⟨Sum.inl ⟨e, heH, ht0, hh0⟩, ?_, by simp [threadFn]⟩
            simp only [Multigraph.cutEdges, Finset.mem_filter, Finset.mem_univ, true_and, H₀G]
            rw [← hV0_in_U ⟨G.tail e, ht0⟩, ← hV0_in_U ⟨G.head e, hh0⟩]
            exact hcr
          · have hx : G.head e ∈ H.verts \ V₀Fin := Finset.mem_sdiff.mpr ⟨H.head_mem heH, hh0⟩
            let I : ThreadI := ⟨compOf (G.head e), Finset.mem_image.mpr ⟨G.head e, hx, rfl⟩⟩
            have hhI : G.head e ∈ I.1 := Finset.mem_filter.mpr ⟨hx, Relation.ReflTransGen.refl⟩
            have ht_notI : G.tail e ∉ I.1 := fun h =>
              (Finset.mem_sdiff.mp (Finset.mem_filter.mp h).1).2 ht0
            have he_tp : e ∈ (threadFn (Sum.inr I)).edges := by
              rw [(hcomp_data I).choose_spec.choose_spec.choose_spec.2.2 e]
              right; exact Finset.mem_filter.mpr ⟨heH, Or.inr ⟨ht_notI, hhI⟩⟩
            have ht_end : G.tail e = (H₀G.tail (Sum.inr I)).1 ∨ G.tail e = (H₀G.head (Sum.inr I)).1 := by
              have hv := (hcomp_data I).choose_spec.choose_spec.choose_spec.2.1 (G.tail e)
              have hmem : G.tail e ∈ (threadFn (Sum.inr I)).verts := by
                obtain ⟨i, hi, he_eq⟩ := List.getElem_of_mem he_tp
                rw [← he_eq]
                rcases (threadFn (Sum.inr I)).step_connect i hi with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
                  rw [h1] <;> exact List.getElem_mem _
              rcases hv.mp hmem with h1 | h1 | h1
              · left; exact h1
              · right; exact h1
              · exact absurd h1 ht_notI
            refine ⟨Sum.inr I, ?_, he_tp⟩
            simp only [Multigraph.cutEdges, Finset.mem_filter, Finset.mem_univ, true_and]
            rw [hcomp_in_U I (G.head e) hhI] at hcr
            rcases ht_end with h1 | h1
            · rw [h1, hV0_in_U (H₀G.tail (Sum.inr I))] at hcr
              exfalso; rcases hcr with ⟨a, b⟩ | ⟨a, b⟩ <;> [exact b a; exact a b]
            · rw [h1, hV0_in_U (H₀G.head (Sum.inr I))] at hcr
              rcases hcr with ⟨a, b⟩ | ⟨a, b⟩ <;> [exact Or.inr ⟨b, a⟩; exact Or.inl ⟨b, a⟩]
        · have hx : G.tail e ∈ H.verts \ V₀Fin := Finset.mem_sdiff.mpr ⟨H.tail_mem heH, ht0⟩
          let I : ThreadI := ⟨compOf (G.tail e), Finset.mem_image.mpr ⟨G.tail e, hx, rfl⟩⟩
          have htI : G.tail e ∈ I.1 := Finset.mem_filter.mpr ⟨hx, Relation.ReflTransGen.refl⟩
          by_cases hh0 : G.head e ∈ V₀Fin
          · have hh_notI : G.head e ∉ I.1 := fun h =>
              (Finset.mem_sdiff.mp (Finset.mem_filter.mp h).1).2 hh0
            have he_tp : e ∈ (threadFn (Sum.inr I)).edges := by
              rw [(hcomp_data I).choose_spec.choose_spec.choose_spec.2.2 e]
              right; exact Finset.mem_filter.mpr ⟨heH, Or.inl ⟨htI, hh_notI⟩⟩
            have hh_end : G.head e = (H₀G.tail (Sum.inr I)).1 ∨ G.head e = (H₀G.head (Sum.inr I)).1 := by
              have hv := (hcomp_data I).choose_spec.choose_spec.choose_spec.2.1 (G.head e)
              have hmem : G.head e ∈ (threadFn (Sum.inr I)).verts := by
                obtain ⟨i, hi, he_eq⟩ := List.getElem_of_mem he_tp
                rw [← he_eq]
                rcases (threadFn (Sum.inr I)).step_connect i hi with ⟨_, h1⟩ | ⟨_, h1⟩ <;>
                  rw [h1] <;> exact List.getElem_mem _
              rcases hv.mp hmem with h1 | h1 | h1
              · left; exact h1
              · right; exact h1
              · exact absurd h1 hh_notI
            refine ⟨Sum.inr I, ?_, he_tp⟩
            simp only [Multigraph.cutEdges, Finset.mem_filter, Finset.mem_univ, true_and]
            rw [hcomp_in_U I (G.tail e) htI] at hcr
            rcases hh_end with h1 | h1
            · rw [h1, hV0_in_U (H₀G.tail (Sum.inr I))] at hcr
              exfalso; rcases hcr with ⟨a, b⟩ | ⟨a, b⟩ <;> [exact b a; exact a b]
            · rw [h1, hV0_in_U (H₀G.head (Sum.inr I))] at hcr
              exact hcr
          · -- Both ends in `H.verts \ V₀Fin` → same component `I` → cannot cross `U`!
            have hh_sdiff : G.head e ∈ H.verts \ V₀Fin := Finset.mem_sdiff.mpr ⟨H.head_mem heH, hh0⟩
            have he2 : e ∈ Hdeg2.edges := Finset.mem_filter.mpr ⟨heH, hx, hh_sdiff⟩
            have hhI : G.head e ∈ I.1 := Finset.mem_filter.mpr ⟨hh_sdiff,
              Relation.ReflTransGen.single ⟨e, he2, Or.inl ⟨rfl, rfl⟩⟩⟩
            rw [hcomp_in_U I (G.tail e) htI, hcomp_in_U I (G.head e) hhI] at hcr
            exfalso; rcases hcr with ⟨a, b⟩ | ⟨a, b⟩ <;> [exact b a; exact a b]
      -- Moreover, each thread `t` contains AT MOST ONE edge of `CutU`!
      have huniq_in_thread : ∀ (t : E₀Type) (e₁ e₂ : E),
          e₁ ∈ CutU → e₂ ∈ CutU → e₁ ∈ (threadFn t).edges → e₂ ∈ (threadFn t).edges → e₁ = e₂ := by
        intro t e₁ e₂ he₁ he₂ h1t h2t
        cases t with
        | inl e =>
          simp only [threadFn, List.mem_singleton] at h1t h2t
          exact h1t.trans h2t.symm
        | inr I =>
          -- Every edge in `CutU` on thread `I` must connect `I` to `H₀G.head (inr I)` (cannot stay in `I`, cannot connect `I` to `tail (inr I)`!)
          have hto_head : ∀ e ∈ CutU, e ∈ (threadFn (Sum.inr I)).edges →
              (G.tail e ∈ I.1 ∧ G.head e = (H₀G.head (Sum.inr I)).1) ∨
              (G.tail e = (H₀G.head (Sum.inr I)).1 ∧ G.head e ∈ I.1) := by
            intro e he het
            have hcr := (Finset.mem_filter.mp he).2
            rw [(hcomp_data I).choose_spec.choose_spec.choose_spec.2.2 e] at het
            rcases het with hin | hcut
            · have htI := (Finset.mem_filter.mp hin).2.1
              have hhI := (Finset.mem_filter.mp hin).2.2
              rw [hcomp_in_U I (G.tail e) htI, hcomp_in_U I (G.head e) hhI] at hcr
              exfalso; rcases hcr with ⟨a, b⟩ | ⟨a, b⟩ <;> [exact b a; exact a b]
            · have hv_mem : ∀ v, v = G.tail e ∨ v = G.head e → v ∈ (threadFn (Sum.inr I)).verts := by
                intro v hv
                have := (hcomp_data I).choose_spec.choose_spec.choose_spec.2.2 e |>.mpr (Or.inr hcut)
                obtain ⟨i, hi, he_eq⟩ := List.getElem_of_mem this
                rcases (threadFn (Sum.inr I)).step_connect i hi with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
                  rcases hv with rfl | rfl <;> rw [← he_eq] <;> [rw [h1]; rw [h2]; rw [h1]; rw [h2]] <;> exact List.getElem_mem _
              rcases (Finset.mem_filter.mp hcut).2 with ⟨htI, hhnot⟩ | ⟨htnot, hhI⟩
              · have hh_or := ((hcomp_data I).choose_spec.choose_spec.choose_spec.2.1 (G.head e)).mp
                  (hv_mem _ (Or.inr rfl))
                rcases hh_or with h1 | h1 | h1
                · rw [hcomp_in_U I (G.tail e) htI, h1, hV0_in_U (H₀G.tail (Sum.inr I))] at hcr
                  exfalso; rcases hcr with ⟨a, b⟩ | ⟨a, b⟩ <;> [exact b a; exact a b]
                · left; exact ⟨htI, h1⟩
                · exact absurd h1 hhnot
              · have ht_or := ((hcomp_data I).choose_spec.choose_spec.choose_spec.2.1 (G.tail e)).mp
                  (hv_mem _ (Or.inl rfl))
                rcases ht_or with h1 | h1 | h1
                · rw [hcomp_in_U I (G.head e) hhI, h1, hV0_in_U (H₀G.tail (Sum.inr I))] at hcr
                  exfalso; rcases hcr with ⟨a, b⟩ | ⟨a, b⟩ <;> [exact b a; exact a b]
                · right; exact ⟨h1, hhI⟩
                · exact absurd h1 htnot
          -- In `CutI`, the two edges have DISTINCT outside endpoints (`hcut_distinct`), so at most ONE hits `head (inr I)`!
          rcases Finset.mem_image.mp I.2 with ⟨x, hx, hIx⟩
          have hdist := (hcomp_props x hx).2.2.2.2
          have hcut_mem : ∀ e ∈ CutU, e ∈ (threadFn (Sum.inr I)).edges →
              e ∈ H.edges.filter (fun e =>
                (G.tail e ∈ compOf x ∧ G.head e ∉ compOf x) ∨
                (G.tail e ∉ compOf x ∧ G.head e ∈ compOf x)) := by
            intro e he het
            have h1 := hto_head e he het
            have heH := (Finset.mem_filter.mp he).1
            have hnotI : (H₀G.head (Sum.inr I)).1 ∉ I.1 := fun h => by
              rw [← hIx] at h
              exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp h).1).2 (H₀G.head (Sum.inr I)).2
            rw [← hIx] at h1 hnotI
            refine Finset.mem_filter.mpr ⟨heH, ?_⟩
            rcases h1 with ⟨htI, hh⟩ | ⟨ht, hhI⟩
            · left; exact ⟨htI, hh ▸ hnotI⟩
            · right; exact ⟨ht ▸ hnotI, hhI⟩
          by_contra hne
          have h1 := hto_head e₁ he₁ h1t
          have h2 := hto_head e₂ he₂ h2t
          have hnotI : (H₀G.head (Sum.inr I)).1 ∉ I.1 := fun h => by
            rw [← hIx] at h
            exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp h).1).2 (H₀G.head (Sum.inr I)).2
          rw [← hIx] at h1 h2 hnotI
          apply hdist e₁ (hcut_mem e₁ he₁ h1t) e₂ (hcut_mem e₂ he₂ h2t) hne
          rcases h1 with ⟨ht1, hh1⟩ | ⟨ht1, hh1⟩ <;> rcases h2 with ⟨ht2, hh2⟩ | ⟨ht2, hh2⟩ <;>
            simp [ht1, hh1, ht2, hh2, hnotI]
      -- Conclude `CutU.card ≤ (H₀G.cutEdges S).card` via `Finset.card_le_card_of_injOn`!
      have hcard_le : CutU.card ≤ (H₀G.cutEdges S).card := by
        have hCutU_pos : 0 < CutU.card := by dsimp only [CutU]; omega
        have hE0_ne : Nonempty E₀Type := by
          rcases Finset.card_pos.mp hCutU_pos with ⟨e, he⟩
          exact ⟨(hmap e he).choose⟩
        let g : E → E₀Type := fun e => if h : e ∈ CutU then (hmap e h).choose else Classical.choice hE0_ne
        refine Finset.card_le_card_of_injOn g ?_ ?_
        · intro e he
          have he' : e ∈ CutU := Finset.mem_coe.mp he
          simp only [g, he', ↓reduceDIte]
          exact Finset.mem_coe.mpr (hmap e he').choose_spec.1
        · intro e₁ he₁ e₂ he₂ heq
          have he₁' : e₁ ∈ CutU := Finset.mem_coe.mp he₁
          have he₂' : e₂ ∈ CutU := Finset.mem_coe.mp he₂
          simp only [g, he₁', he₂', ↓reduceDIte] at heq
          have h1 := (hmap e₁ he₁').choose_spec.2
          have h2 := (hmap e₂ he₂').choose_spec.2
          rw [heq] at h1
          exact huniq_in_thread _ e₁ e₂ he₁' he₂' h1 h2
      dsimp only [CutU] at hcard_le
      omega
    -- Finally, construct `SubdivisionData G H`!
    refine ⟨H, Or.inr ⟨{
      V₀ := {v : V // v ∈ V₀Fin}
      E₀ := E₀Type
      H₀ := H₀G
      loopless := hH0_ll
      edgeConn3 := hH0_3ec
      card_ge_two := hH0_card2
      embedV := Function.Embedding.subtype _
      embedV_mem := fun v₀ => (Finset.mem_filter.mp v₀.2).1
      thread := threadFn
      edges_disjoint := fun t₁ t₂ hne e h1 h2 => by
        cases t₁ with
        | inl e₁ =>
          cases t₂ with
          | inl e₂ =>
            simp only [threadFn, List.mem_singleton] at h1 h2
            exact hne (congrArg Sum.inl (Subtype.ext (h1.symm.trans h2)))
          | inr I₂ =>
            simp only [threadFn, List.mem_singleton] at h1
            subst h1
            rw [(hcomp_data I₂).choose_spec.choose_spec.choose_spec.2.2 e₁.1] at h2
            rcases Finset.mem_image.mp I₂.2 with ⟨x, _, hIx⟩
            rw [← hIx] at h2
            rcases h2 with h2 | h2
            · exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp (Finset.mem_filter.mp h2).2.1).1).2 e₁.2.2.1
            · rcases (Finset.mem_filter.mp h2).2 with ⟨ht, _⟩ | ⟨_, hh⟩
              · exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp ht).1).2 e₁.2.2.1
              · exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hh).1).2 e₁.2.2.2
        | inr I₁ =>
          cases t₂ with
          | inl e₂ =>
            simp only [threadFn, List.mem_singleton] at h2
            subst h2
            rw [(hcomp_data I₁).choose_spec.choose_spec.choose_spec.2.2 e₂.1] at h1
            rcases Finset.mem_image.mp I₁.2 with ⟨x, _, hIx⟩
            rw [← hIx] at h1
            rcases h1 with h1 | h1
            · exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp (Finset.mem_filter.mp h1).2.1).1).2 e₂.2.2.1
            · rcases (Finset.mem_filter.mp h1).2 with ⟨ht, _⟩ | ⟨_, hh⟩
              · exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp ht).1).2 e₂.2.2.1
              · exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hh).1).2 e₂.2.2.2
          | inr I₂ =>
            rw [(hcomp_data I₁).choose_spec.choose_spec.choose_spec.2.2 e] at h1
            rw [(hcomp_data I₂).choose_spec.choose_spec.choose_spec.2.2 e] at h2
            rcases Finset.mem_image.mp I₁.2 with ⟨x₁, hx₁, hIx₁⟩
            rcases Finset.mem_image.mp I₂.2 with ⟨x₂, hx₂, hIx₂⟩
            -- Both `I₁` and `I₂` must contain an endpoint of `e`, and `I₁ ≠ I₂` are disjoint components!
            have hdisj12 : Disjoint I₁.1 I₂.1 := by
              rw [Finset.disjoint_left]
              intro z hz1 hz2
              apply hne; apply congrArg Sum.inr; apply Subtype.ext
              rw [← hIx₁, ← hIx₂]
              exact (hcomp_eq_of_mem hx₁ (hIx₁.symm ▸ hz1)).symm.trans
                (hcomp_eq_of_mem hx₂ (hIx₂.symm ▸ hz2))
            -- Any edge in `threadFn I` has at least one endpoint in `I`, and its other endpoint is either in `I` or in `V₀Fin`!
            have hmem_end : ∀ (I : ThreadI) (x : V) (hx : x ∈ H.verts \ V₀Fin) (hIx : compOf x = I.1),
                (e ∈ (subgraphRestrict H I.1).edges ∨
                  e ∈ H.edges.filter (fun e =>
                    (G.tail e ∈ I.1 ∧ G.head e ∉ I.1) ∨ (G.tail e ∉ I.1 ∧ G.head e ∈ I.1))) →
                (G.tail e ∈ I.1 ∨ G.head e ∈ I.1) ∧
                (G.tail e ∈ I.1 → G.head e ∈ I.1 ∨ G.head e ∈ V₀Fin) ∧
                (G.head e ∈ I.1 → G.tail e ∈ I.1 ∨ G.tail e ∈ V₀Fin) := by
              intro I x hx hIx h
              rcases h with h | h
              · have ⟨ht, hh⟩ := (Finset.mem_filter.mp h).2
                exact ⟨Or.inl ht, fun _ => Or.inl hh, fun _ => Or.inl ht⟩
              · have hcut := (hcomp_props x hx).2.2.2.1 e (hIx ▸ h)
                rcases (Finset.mem_filter.mp h).2 with ⟨ht, _⟩ | ⟨_, hh⟩
                · exact ⟨Or.inl ht, fun _ => Or.inr (hcut.1 (hIx.symm ▸ ht)), fun h' => Or.inl (hIx ▸ hIx.symm ▸ ht)⟩
                · exact ⟨Or.inr hh, fun h' => Or.inl hh, fun _ => Or.inr (hcut.2 (hIx.symm ▸ hh))⟩
            obtain ⟨h1a, h1b, h1c⟩ := hmem_end I₁ x₁ hx₁ hIx₁ h1
            obtain ⟨h2a, _, _⟩ := hmem_end I₂ x₂ hx₂ hIx₂ h2
            have hI2_notV0 : ∀ z ∈ I₂.1, z ∉ V₀Fin := fun z hz => by
              rw [← hIx₂] at hz; exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hz).1).2
            rcases h1a with ht1 | hh1 <;> rcases h2a with ht2 | hh2
            · exact Finset.disjoint_left.mp hdisj12 ht1 ht2
            · rcases h1b ht1 with hh1' | hhV0
              · exact Finset.disjoint_left.mp hdisj12 hh1' hh2
              · exact hI2_notV0 _ hh2 hhV0
            · rcases h1c hh1 with ht1' | htV0
              · exact Finset.disjoint_left.mp hdisj12 ht1' ht2
              · exact hI2_notV0 _ ht2 htV0
            · exact Finset.disjoint_left.mp hdisj12 hh1 hh2
      edges_cover := fun e he => by
        by_cases ht0 : G.tail e ∈ V₀Fin
        · by_cases hh0 : G.head e ∈ V₀Fin
          · exact ⟨Sum.inl ⟨e, he, ht0, hh0⟩, by simp [threadFn]⟩
          · have hx : G.head e ∈ H.verts \ V₀Fin := Finset.mem_sdiff.mpr ⟨H.head_mem he, hh0⟩
            let I : ThreadI := ⟨compOf (G.head e), Finset.mem_image.mpr ⟨G.head e, hx, rfl⟩⟩
            have hhI : G.head e ∈ I.1 := Finset.mem_filter.mpr ⟨hx, Relation.ReflTransGen.refl⟩
            have ht_notI : G.tail e ∉ I.1 := fun h =>
              (Finset.mem_sdiff.mp (Finset.mem_filter.mp h).1).2 ht0
            refine ⟨Sum.inr I, ?_⟩
            rw [(hcomp_data I).choose_spec.choose_spec.choose_spec.2.2 e]
            right; exact Finset.mem_filter.mpr ⟨he, Or.inr ⟨ht_notI, hhI⟩⟩
        · have hx : G.tail e ∈ H.verts \ V₀Fin := Finset.mem_sdiff.mpr ⟨H.tail_mem he, ht0⟩
          let I : ThreadI := ⟨compOf (G.tail e), Finset.mem_image.mpr ⟨G.tail e, hx, rfl⟩⟩
          have htI : G.tail e ∈ I.1 := Finset.mem_filter.mpr ⟨hx, Relation.ReflTransGen.refl⟩
          refine ⟨Sum.inr I, ?_⟩
          rw [(hcomp_data I).choose_spec.choose_spec.choose_spec.2.2 e]
          by_cases hhI : G.head e ∈ I.1
          · left; exact Finset.mem_filter.mpr ⟨he, htI, hhI⟩
          · right; exact Finset.mem_filter.mpr ⟨he, Or.inl ⟨htI, hhI⟩⟩
      interior_disjoint_branch := fun t v hv hnt hnh v₀ heq => by
        cases t with
        | inl e =>
          simp only [threadFn, List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl <;> [exact hnt rfl; exact hnh rfl]
        | inr I =>
          rw [(hcomp_data I).choose_spec.choose_spec.choose_spec.2.1 v] at hv
          rcases hv with h1 | h1 | hvI
          · exact hnt h1
          · exact hnh h1
          · rcases Finset.mem_image.mp I.2 with ⟨x, _, hIx⟩
            rw [← hIx, heq] at hvI
            exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hvI).1).2 v₀.2
      interior_disjoint := fun t₁ t₂ hne v ⟨hv1, hnt1, hnh1⟩ ⟨hv2, hnt2, hnh2⟩ => by
        cases t₁ with
        | inl e₁ =>
          simp only [threadFn, List.mem_cons, List.not_mem_nil, or_false] at hv1
          rcases hv1 with rfl | rfl <;> [exact hnt1 rfl; exact hnh1 rfl]
        | inr I₁ =>
          cases t₂ with
          | inl e₂ =>
            simp only [threadFn, List.mem_cons, List.not_mem_nil, or_false] at hv2
            rcases hv2 with rfl | rfl <;> [exact hnt2 rfl; exact hnh2 rfl]
          | inr I₂ =>
            rw [(hcomp_data I₁).choose_spec.choose_spec.choose_spec.2.1 v] at hv1
            rw [(hcomp_data I₂).choose_spec.choose_spec.choose_spec.2.1 v] at hv2
            have hvI1 : v ∈ I₁.1 := by rcases hv1 with h | h | h <;> [exact absurd h hnt1; exact absurd h hnh1; exact h]
            have hvI2 : v ∈ I₂.1 := by rcases hv2 with h | h | h <;> [exact absurd h hnt2; exact absurd h hnh2; exact h]
            rcases Finset.mem_image.mp I₁.2 with ⟨x₁, hx₁, hIx₁⟩
            rcases Finset.mem_image.mp I₂.2 with ⟨x₂, hx₂, hIx₂⟩
            apply hne; apply congrArg Sum.inr; apply Subtype.ext
            rw [← hIx₁, ← hIx₂]
            exact (hcomp_eq_of_mem hx₁ (hIx₁.symm ▸ hvI1)).symm.trans
              (hcomp_eq_of_mem hx₂ (hIx₂.symm ▸ hvI2))
      verts_cover := fun v hv => by
        by_cases hv0 : v ∈ V₀Fin
        · left; exact ⟨⟨v, hv0⟩, rfl⟩
        · right
          have hx : v ∈ H.verts \ V₀Fin := Finset.mem_sdiff.mpr ⟨hv, hv0⟩
          let I : ThreadI := ⟨compOf v, Finset.mem_image.mpr ⟨v, hx, rfl⟩⟩
          refine ⟨Sum.inr I, ?_⟩
          rw [(hcomp_data I).choose_spec.choose_spec.choose_spec.2.1 v]
          right; right; exact Finset.mem_filter.mpr ⟨hx, Relation.ReflTransGen.refl⟩
    }⟩⟩

end Extraction

end Flow.Proofs
