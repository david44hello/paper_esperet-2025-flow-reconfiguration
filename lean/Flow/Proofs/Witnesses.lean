-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Flow.Defs.Literature
import Mathlib.Tactic

/-!
# Concrete non-vacuity witnesses for truncated cubic graphs, well colourings, and frames
-/

namespace Flow.Proofs

open Flow

/-! ### Witness 1: `K_4 - v = K_3` is truncated cubic `3`-edge-connected and admits a well colouring -/

private def K4Graph : Multigraph (Fin 4) (Fin 6) where
  tail e := match e with
    | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 1 | 5 => 2
  head e := match e with
    | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 3 | 4 => 3 | 5 => 3

private def K3Graph : Multigraph (Fin 3) (Fin 3) where
  tail e := match e with | 0 => 0 | 1 => 1 | 2 => 2
  head e := match e with | 0 => 1 | 1 => 2 | 2 => 0

private lemma K4_cubic : K4Graph.IsCubic := by
  intro v; fin_cases v <;> decide

private lemma K4_edgeConn3 : K4Graph.IsEdgeConnected 3 := by
  intro S hS hSc
  -- Check by case analysis on S ⊆ Fin 4 (finite decidable check)
  have hdec : ∀ T : Finset (Fin 4), T.Nonempty → (Finset.univ \ T).Nonempty →
      3 ≤ (K4Graph.cutEdges T).card := by decide
  exact hdec S hS hSc

private lemma K3_isTC3EC : K3Graph.IsTruncatedCubic3EC := by
  refine ⟨Fin 4, Fin 6, inferInstance, inferInstance, inferInstance, inferInstance,
    K4Graph, 3, K4_cubic, K4_edgeConn3, by decide, ⟨?_⟩⟩
  refine
    { toVert :=
        { toFun := fun i => ⟨⟨i.1, by omega⟩, by
            intro h; have h' := congrArg Fin.val h; dsimp at h'; omega⟩
          invFun := fun u => ⟨u.1.1, by
            have hne : u.1.1 ≠ 3 := fun h => u.2 (Fin.ext h)
            omega⟩
          left_inv := fun i => by ext; rfl
          right_inv := fun u => by ext; rfl }
      toEdge :=
        { toFun := fun e => ⟨⟨e.1, by omega⟩, by fin_cases e <;> decide⟩
          invFun := fun ⟨⟨k, hk⟩, hne⟩ => ⟨k, by
            interval_cases k <;> first | omega | (exfalso; simp [K4Graph] at hne)⟩
          left_inv := fun e => by ext; rfl
          right_inv := fun e => by ext; rfl }
      dir := fun _ => false
      tail_eq := fun e => by fin_cases e <;> rfl
      head_eq := fun e => by fin_cases e <;> rfl }

private lemma K3_wellColouring : Nonempty (WellColouring K3Graph) := by
  classical
  let blue : Finset (Fin 3) := {0, 1}
  -- Spanning tree check for blue = {0, 1} (path 0 - 1 - 2)
  have hblue_tree : (Multigraph.Subgraph.ofEdges K3Graph Finset.univ blue
      (fun _ => Finset.mem_univ _) (fun _ => Finset.mem_univ _)).IsSpanningTree := by
    let T := Multigraph.Subgraph.ofEdges K3Graph Finset.univ blue
      (fun _ => Finset.mem_univ _) (fun _ => Finset.mem_univ _)
    refine ⟨rfl, ⟨⟨0, Finset.mem_univ 0⟩, ?_⟩, ?_⟩
    · intro u _ v _
      have h01 : T.Adj 0 1 := ⟨0, by decide, Or.inl ⟨rfl, rfl⟩⟩
      have h10 : T.Adj 1 0 := ⟨0, by decide, Or.inr ⟨rfl, rfl⟩⟩
      have h12 : T.Adj 1 2 := ⟨1, by decide, Or.inl ⟨rfl, rfl⟩⟩
      have h21 : T.Adj 2 1 := ⟨1, by decide, Or.inr ⟨rfl, rfl⟩⟩
      fin_cases u <;> fin_cases v
      · exact Relation.ReflTransGen.refl
      · exact Relation.ReflTransGen.single h01
      · exact (Relation.ReflTransGen.single h01).tail h12
      · exact Relation.ReflTransGen.single h10
      · exact Relation.ReflTransGen.refl
      · exact Relation.ReflTransGen.single h12
      · exact (Relation.ReflTransGen.single h21).tail h10
      · exact Relation.ReflTransGen.single h21
      · exact Relation.ReflTransGen.refl
    · -- Acyclicity: any subgraph C ≤ T has at most 2 edges, and edge 0 is the only edge at 0
      -- so deg_C(0) ≤ 1, deg_C(2) ≤ 1; hence no vertex in C can have degree 2!
      intro C hCT hcyc
      have hsub : C.edges ⊆ blue := hCT.2
      obtain ⟨v, hv⟩ := hcyc.1.1
      have hdeg := hcyc.2 v hv
      have h0_not : (0 : Fin 3) ∉ C.verts := by
        intro h0
        have hd := hcyc.2 0 h0
        have hle : C.deg 0 ≤ (blue.filter (fun e => K3Graph.tail e = 0)).card +
            (blue.filter (fun e => K3Graph.head e = 0)).card := by
          unfold Multigraph.Subgraph.deg
          exact add_le_add (Finset.card_le_card (Finset.filter_subset_filter _ hsub))
            (Finset.card_le_card (Finset.filter_subset_filter _ hsub))
        have h1 : (blue.filter (fun e => K3Graph.tail e = 0)).card +
            (blue.filter (fun e => K3Graph.head e = 0)).card = 1 := by decide
        omega
      have h2_not : (2 : Fin 3) ∉ C.verts := by
        intro h2
        have hd := hcyc.2 2 h2
        have hle : C.deg 2 ≤ (blue.filter (fun e => K3Graph.tail e = 2)).card +
            (blue.filter (fun e => K3Graph.head e = 2)).card := by
          unfold Multigraph.Subgraph.deg
          exact add_le_add (Finset.card_le_card (Finset.filter_subset_filter _ hsub))
            (Finset.card_le_card (Finset.filter_subset_filter _ hsub))
        have h1 : (blue.filter (fun e => K3Graph.tail e = 2)).card +
            (blue.filter (fun e => K3Graph.head e = 2)).card = 1 := by decide
        omega
      -- Every edge of blue has an endpoint in {0, 2}, so C.edges = ∅, forcing deg_C(v) = 0 ≠ 2!
      have hempty : C.edges = ∅ := by
        ext e
        simp only [Finset.notMem_empty, iff_false]
        intro he
        have heb := hsub he
        fin_cases e
        · exact h0_not (C.tail_mem he)
        · exact h2_not (C.head_mem he)
        · simp [blue] at heb
      simp [Multigraph.Subgraph.deg, hempty] at hdeg
  -- Red components of K3 with blue = {0, 1}: red edge is 2 = (2, 0), so [0] = [2] ≠ [1]
  let c0 : Quotient (redSetoid K3Graph blue) := Quotient.mk (redSetoid K3Graph blue) 0
  let c1 : Quotient (redSetoid K3Graph blue) := Quotient.mk (redSetoid K3Graph blue) 1
  have h20 : Quotient.mk (redSetoid K3Graph blue) 2 = c0 :=
    Quotient.sound (Relation.ReflTransGen.single ⟨2, by decide, Or.inl ⟨rfl, rfl⟩⟩)
  have hc01 : c0 ≠ c1 := by
    intro heq
    have hrel : Relation.ReflTransGen (redAdj K3Graph blue) 0 1 := Quotient.exact heq
    have hstay : ∀ v : Fin 3, Relation.ReflTransGen (redAdj K3Graph blue) 0 v → v = 0 ∨ v = 2 := by
      intro v hv
      induction hv with
      | refl => exact Or.inl rfl
      | tail _ hstep ih =>
        rcases hstep with ⟨e, he, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
        · have he2 : e = 2 := by fin_cases e <;> simp_all [blue]
          subst he2; left; simpa [K3Graph] using h2.symm
        · have he2 : e = 2 := by fin_cases e <;> simp_all [blue]
          subst he2; right; simpa [K3Graph] using h1.symm
    rcases hstay 1 hrel with h | h <;> exact absurd h (by decide)
  have huniv_W : ({c0} ∪ {c1} : Finset (Quotient (redSetoid K3Graph blue))) = Finset.univ := by
    ext q
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_univ, iff_true]
    induction q using Quotient.ind with
    | _ v =>
      fin_cases v
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact Or.inl h20
  let e0 : {e : Fin 3 // e ∈ blue} := ⟨0, by decide⟩
  let e1 : {e : Fin 3 // e ∈ blue} := ⟨1, by decide⟩
  have huniv_E : insert e0 (insert e1 (∅ ∪ ∅ : Finset {e : Fin 3 // e ∈ blue})) = Finset.univ := by
    ext ⟨e, he⟩
    simp only [Finset.union_empty, Finset.mem_insert, Finset.notMem_empty, or_false, Finset.mem_univ,
      iff_true]
    fin_cases e
    · left; rfl
    · right; rfl
    · simp [blue] at he
  let tc : TwoConstruction (redQuotient K3Graph blue) ({c0} ∪ {c1})
      (insert e0 (insert e1 (∅ ∪ ∅))) :=
    TwoConstruction.join
      (TwoConstruction.single c0)
      (TwoConstruction.single c1)
      e0 e1
      (Finset.disjoint_singleton.mpr hc01)
      (Finset.disjoint_empty_left _)
      (by intro h; exact absurd (congrArg Subtype.val h) (by decide))
      (Finset.notMem_empty _) (Finset.notMem_empty _)
      (Finset.notMem_empty _) (Finset.notMem_empty _)
      (Or.inl ⟨Finset.mem_singleton_self c0, Finset.mem_singleton_self c1⟩)
      (Or.inr ⟨Finset.mem_singleton_self c1, by
        change Quotient.mk (redSetoid K3Graph blue) 2 ∈ ({c0} : Finset _)
        rw [h20]; exact Finset.mem_singleton_self c0⟩)
  exact ⟨{ blue := blue
           blue_tree := hblue_tree
           twoConstr := huniv_W ▸ huniv_E ▸ tc }⟩

theorem nonvacuous_tc3ec_and_well_colouring_proved :
    ∃ (V E : Type) (_ : Fintype V) (_ : Fintype E) (_ : DecidableEq V) (_ : DecidableEq E)
      (Q : Multigraph V E), Q.IsTruncatedCubic3EC ∧ Nonempty (WellColouring Q) :=
  ⟨Fin 3, Fin 3, inferInstance, inferInstance, inferInstance, inferInstance,
    K3Graph, K3_isTC3EC, K3_wellColouring⟩

/-! ### Witness 2: 2-vertex, 3-parallel-edge multigraph admits `SubdivisionData`, `AuxGraphData`, and `Frame` -/

private def G3P : Multigraph (Fin 2) (Fin 3) := ⟨fun _ => 0, fun _ => 1⟩

private def Q3Plus : Multigraph (Fin 8) (Fin 12) where
  tail e := match e with
    | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 0 | 4 => 1 | 5 => 2
    | 6 => 3 | 7 => 4 | 8 => 5 | 9 => 1 | 10 => 3 | 11 => 5
  head e := match e with
    | 0 => 6 | 1 => 6 | 2 => 6 | 3 => 1 | 4 => 2 | 5 => 3
    | 6 => 4 | 7 => 5 | 8 => 0 | 9 => 7 | 10 => 7 | 11 => 7

private def Q3Graph : Multigraph (Fin 7) (Fin 9) where
  tail e := match e with
    | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 0 | 4 => 1 | 5 => 2
    | 6 => 3 | 7 => 4 | 8 => 5
  head e := match e with
    | 0 => 6 | 1 => 6 | 2 => 6 | 3 => 1 | 4 => 2 | 5 => 3
    | 6 => 4 | 7 => 5 | 8 => 0

private lemma Q3Plus_cubic : Q3Plus.IsCubic := by
  intro v; fin_cases v <;> decide

private lemma Q3Plus_edgeConn3 : Q3Plus.IsEdgeConnected 3 := by
  -- Use bipartition A = {0, 2, 4, 7}, B = {1, 3, 5, 6}: simple bipartite cubic graph on 8 vertices
  let partA : Finset (Fin 8) := {0, 2, 4, 7}
  let partB : Finset (Fin 8) := {1, 3, 5, 6}
  have hpart_disj : Disjoint partA partB := by decide
  have hpart_union : partA ∪ partB = Finset.univ := by decide
  have hbip : ∀ e : Fin 12,
      (Q3Plus.tail e ∈ partA ∧ Q3Plus.head e ∈ partB) ∨
      (Q3Plus.tail e ∈ partB ∧ Q3Plus.head e ∈ partA) := by
    intro e; fin_cases e <;> decide
  have hsimple : ∀ e₁ e₂ : Fin 12, Q3Plus.SameEnds e₁ e₂ → e₁ = e₂ := by
    have hdec : ∀ e₁ e₂ : Fin 12,
        ((Q3Plus.tail e₁ = Q3Plus.tail e₂ ∧ Q3Plus.head e₁ = Q3Plus.head e₂) ∨
         (Q3Plus.tail e₁ = Q3Plus.head e₂ ∧ Q3Plus.head e₁ = Q3Plus.tail e₂)) → e₁ = e₂ := by decide
    exact fun e₁ e₂ h => hdec e₁ e₂ h
  have hcut_symm : ∀ S : Finset (Fin 8), Q3Plus.cutEdges (Finset.univ \ S) = Q3Plus.cutEdges S := by
    intro S; ext e
    simp only [Multigraph.cutEdges, Finset.mem_filter, Finset.mem_univ, Finset.mem_sdiff, true_and,
      not_not]
    tauto
  have hcut_small : ∀ S : Finset (Fin 8), 1 ≤ S.card → S.card ≤ 4 →
      3 ≤ (Q3Plus.cutEdges S).card := by
    intro S hS1 hS4
    -- Sum of degrees in S equals 2 * |E(S)| + |cutEdges S|
    let inE := Finset.univ.filter (fun e : Fin 12 => Q3Plus.tail e ∈ S ∧ Q3Plus.head e ∈ S)
    have hhand : 3 * S.card = 2 * inE.card + (Q3Plus.cutEdges S).card := by
      have hdeg_sum : ∑ v ∈ S, Q3Plus.deg v = 3 * S.card := by
        calc ∑ v ∈ S, Q3Plus.deg v = ∑ _v ∈ S, 3 := Finset.sum_congr rfl (fun v _ => Q3Plus_cubic v)
          _ = 3 * S.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      rw [← hdeg_sum]
      unfold Multigraph.deg
      rw [Finset.sum_add_distrib]
      have h1 : ∑ v ∈ S, (Finset.univ.filter (fun e : Fin 12 => Q3Plus.tail e = v)).card =
          (Finset.univ.filter (fun e : Fin 12 => Q3Plus.tail e ∈ S)).card := by
        rw [← Finset.card_biUnion]
        · congr 1; ext e; simp
        · intro u _ v _ huv
          dsimp [Function.onFun]
          rw [Finset.disjoint_left]
          intro e hu hv
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
          exact huv (hu.symm.trans hv)
      have h2 : ∑ v ∈ S, (Finset.univ.filter (fun e : Fin 12 => Q3Plus.head e = v)).card =
          (Finset.univ.filter (fun e : Fin 12 => Q3Plus.head e ∈ S)).card := by
        rw [← Finset.card_biUnion]
        · congr 1; ext e; simp
        · intro u _ v _ huv
          dsimp [Function.onFun]
          rw [Finset.disjoint_left]
          intro e hu hv
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
          exact huv (hu.symm.trans hv)
      rw [h1, h2]
      let outE := Finset.univ.filter (fun e : Fin 12 => Q3Plus.tail e ∈ S ∧ Q3Plus.head e ∉ S)
      let inCut := Finset.univ.filter (fun e : Fin 12 => Q3Plus.tail e ∉ S ∧ Q3Plus.head e ∈ S)
      have ht_split : Finset.univ.filter (fun e : Fin 12 => Q3Plus.tail e ∈ S) = inE ∪ outE := by
        ext e; simp only [inE, outE, Finset.mem_filter, Finset.mem_univ, Finset.mem_union, true_and]
        by_cases h : Q3Plus.head e ∈ S <;> simp [h]
      have hh_split : Finset.univ.filter (fun e : Fin 12 => Q3Plus.head e ∈ S) = inE ∪ inCut := by
        ext e; simp only [inE, inCut, Finset.mem_filter, Finset.mem_univ, Finset.mem_union, true_and]
        by_cases h : Q3Plus.tail e ∈ S <;> simp [h]
      have hcut_split : Q3Plus.cutEdges S = outE ∪ inCut := by
        ext e; simp only [Multigraph.cutEdges, outE, inCut, Finset.mem_filter, Finset.mem_univ,
          Finset.mem_union, true_and]
      have hd1 : Disjoint inE outE := Finset.disjoint_left.mpr fun e h1 h2 =>
        (Finset.mem_filter.mp h2).2.2 (Finset.mem_filter.mp h1).2.2
      have hd2 : Disjoint inE inCut := Finset.disjoint_left.mpr fun e h1 h2 =>
        (Finset.mem_filter.mp h2).2.1 (Finset.mem_filter.mp h1).2.1
      have hd3 : Disjoint outE inCut := Finset.disjoint_left.mpr fun e h1 h2 =>
        (Finset.mem_filter.mp h2).2.1 (Finset.mem_filter.mp h1).2.1
      rw [ht_split, hh_split, hcut_split, Finset.card_union_of_disjoint hd1,
        Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd3]
      omega
    -- Bound inE.card ≤ |S ∩ partA| * |S ∩ partB| via injection e ↦ (a-end, b-end)
    let SA := S ∩ partA
    let SB := S ∩ partB
    have hcard_ab : SA.card + SB.card = S.card := by
      have hdj : Disjoint SA SB := Disjoint.mono Finset.inter_subset_right Finset.inter_subset_right hpart_disj
      rw [← Finset.card_union_of_disjoint hdj]
      congr 1; ext v
      simp only [SA, SB, Finset.mem_union, Finset.mem_inter]
      have hv : v ∈ partA ∨ v ∈ partB := by
        have := Finset.mem_univ v; rw [← hpart_union, Finset.mem_union] at this; exact this
      rcases hv with hA | hB
      · simp [hA]; exact fun h _ => h
      · simp [hB]; exact fun h _ => h
    let endPair : Fin 12 → Fin 8 × Fin 8 := fun e =>
      if Q3Plus.tail e ∈ partA then (Q3Plus.tail e, Q3Plus.head e) else (Q3Plus.head e, Q3Plus.tail e)
    have hinE_le : inE.card ≤ SA.card * SB.card := by
      rw [← Finset.card_product]
      refine Finset.card_le_card_of_injOn endPair (fun e he => ?_) (fun e₁ _ e₂ _ heq => ?_)
      · rw [Finset.mem_coe, Finset.mem_filter] at he
        have he1 : Q3Plus.tail e ∈ S := he.2.1
        have he2 : Q3Plus.head e ∈ S := he.2.2
        simp only [Finset.mem_coe, Finset.mem_product, SA, SB, Finset.mem_inter, endPair]
        rcases hbip e with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · simp [h1, he1, he2, h2]
        · have hnot : Q3Plus.tail e ∉ partA := Finset.disjoint_right.mp hpart_disj h1
          simp [hnot, he1, he2, h1, h2]
      · apply hsimple e₁ e₂
        dsimp [endPair] at heq
        split_ifs at heq with h1 h2
        · exact Or.inl (Prod.mk.inj heq)
        · exact Or.inr ⟨(Prod.mk.inj heq).1, (Prod.mk.inj heq).2⟩
        · exact Or.inr ⟨(Prod.mk.inj heq).2, (Prod.mk.inj heq).1⟩
        · exact Or.inl ⟨(Prod.mk.inj heq).2, (Prod.mk.inj heq).1⟩
    have hSA4 : SA.card ≤ 4 := by omega
    have hSB4 : SB.card ≤ 4 := by omega
    have hmul : 2 * (SA.card * SB.card) + 3 ≤ 3 * (SA.card + SB.card) := by
      interval_cases SA.card <;> interval_cases SB.card <;> omega
    omega
  intro S hS hSc
  have htot : S.card + (Finset.univ \ S).card = 8 := by
    have hsd : (Finset.univ \ S).card = (Finset.univ : Finset (Fin 8)).card - S.card := by
      rw [Finset.card_sdiff, Finset.inter_univ]
    rw [hsd, Finset.card_univ, Fintype.card_fin]
    have hle : S.card ≤ 8 := by simpa using Finset.card_le_univ S
    omega
  by_cases hle : S.card ≤ 4
  · exact hcut_small S (Finset.card_pos.mpr hS) hle
  · rw [← hcut_symm S]
    exact hcut_small (Finset.univ \ S) (Finset.card_pos.mpr hSc) (by omega)

private lemma Q3_isTC3EC : Q3Graph.IsTruncatedCubic3EC := by
  refine ⟨Fin 8, Fin 12, inferInstance, inferInstance, inferInstance, inferInstance,
    Q3Plus, 7, Q3Plus_cubic, Q3Plus_edgeConn3, by decide, ⟨?_⟩⟩
  refine
    { toVert :=
        { toFun := fun i => ⟨⟨i.1, by omega⟩, by
            intro h; have h' := congrArg Fin.val h; dsimp at h'; omega⟩
          invFun := fun u => ⟨u.1.1, by
            have hne : u.1.1 ≠ 7 := fun h => u.2 (Fin.ext h)
            omega⟩
          left_inv := fun i => by ext; rfl
          right_inv := fun u => by ext; rfl }
      toEdge :=
        { toFun := fun e => ⟨⟨e.1, by omega⟩, by fin_cases e <;> decide⟩
          invFun := fun ⟨⟨k, hk⟩, hne⟩ => ⟨k, by
            interval_cases k <;> first | omega | (exfalso; simp [Q3Plus] at hne)⟩
          left_inv := fun e => by ext; rfl
          right_inv := fun e => by ext; rfl }
      dir := fun _ => false
      tail_eq := fun e => by fin_cases e <;> rfl
      head_eq := fun e => by fin_cases e <;> rfl }

private def Q3Blue : Finset (Fin 9) := {2, 3, 4, 5, 6, 8}

private lemma Q3_blue_tree :
    (Multigraph.Subgraph.ofEdges Q3Graph Finset.univ Q3Blue
      (fun _ => Finset.mem_univ _) (fun _ => Finset.mem_univ _)).IsSpanningTree := by
  let T := Multigraph.Subgraph.ofEdges Q3Graph Finset.univ Q3Blue
    (fun _ => Finset.mem_univ _) (fun _ => Finset.mem_univ _)
  have h50 : T.Adj 5 0 := ⟨8, by decide, Or.inl ⟨rfl, rfl⟩⟩
  have h01 : T.Adj 0 1 := ⟨3, by decide, Or.inl ⟨rfl, rfl⟩⟩
  have h12 : T.Adj 1 2 := ⟨4, by decide, Or.inl ⟨rfl, rfl⟩⟩
  have h23 : T.Adj 2 3 := ⟨5, by decide, Or.inl ⟨rfl, rfl⟩⟩
  have h34 : T.Adj 3 4 := ⟨6, by decide, Or.inl ⟨rfl, rfl⟩⟩
  have h46 : T.Adj 4 6 := ⟨2, by decide, Or.inl ⟨rfl, rfl⟩⟩
  have hsym : ∀ u v, T.Adj u v → T.Adj v u := by
    rintro u v ⟨e, he, h | h⟩
    · exact ⟨e, he, Or.inr h⟩
    · exact ⟨e, he, Or.inl h⟩
  have hreach5 : ∀ v : Fin 7, Relation.ReflTransGen T.Adj 5 v := by
    intro v; fin_cases v
    · exact Relation.ReflTransGen.single h50
    · exact (Relation.ReflTransGen.single h50).tail h01
    · exact ((Relation.ReflTransGen.single h50).tail h01).tail h12
    · exact (((Relation.ReflTransGen.single h50).tail h01).tail h12).tail h23
    · exact ((((Relation.ReflTransGen.single h50).tail h01).tail h12).tail h23).tail h34
    · exact .refl
    · exact (((((Relation.ReflTransGen.single h50).tail h01).tail h12).tail h23).tail h34).tail h46
  have hsym_rtg : ∀ u v, Relation.ReflTransGen T.Adj u v → Relation.ReflTransGen T.Adj v u := by
    intro u v h
    induction h with
    | refl => exact .refl
    | tail _ hstep ih => exact Relation.ReflTransGen.head (hsym _ _ hstep) ih
  refine ⟨rfl, ⟨⟨0, Finset.mem_univ 0⟩, fun u _ v _ =>
    (hsym_rtg 5 u (hreach5 u)).trans (hreach5 v)⟩, ?_⟩
  -- Acyclicity: peel leaves 5 -> 0 -> 1 -> 2 -> 3 -> 4 -> 6 along the path
  intro C hCT hcyc
  have hsub : C.edges ⊆ Q3Blue := hCT.2
  have hno_vert : ∀ (S : Finset (Fin 9)) (v : Fin 7),
      C.edges ⊆ S →
      (S.filter (fun e => Q3Graph.tail e = v)).card +
      (S.filter (fun e => Q3Graph.head e = v)).card ≤ 1 →
      v ∉ C.verts := by
    intro S v hCS hle hv
    have hd := hcyc.2 v hv
    have hcd : C.deg v ≤ (S.filter (fun e => Q3Graph.tail e = v)).card +
        (S.filter (fun e => Q3Graph.head e = v)).card := by
      unfold Multigraph.Subgraph.deg
      exact add_le_add (Finset.card_le_card (Finset.filter_subset_filter _ hCS))
        (Finset.card_le_card (Finset.filter_subset_filter _ hCS))
    omega
  have hpeel : ∀ (S : Finset (Fin 9)) (v : Fin 7) (e0 : Fin 9),
      C.edges ⊆ S → v ∉ C.verts → (Q3Graph.tail e0 = v ∨ Q3Graph.head e0 = v) →
      C.edges ⊆ S.erase e0 := by
    intro S v e0 hCS hv hinc e he
    refine Finset.mem_erase.mpr ⟨?_, hCS he⟩
    rintro rfl
    rcases hinc with h | h
    · exact hv (h ▸ C.tail_mem he)
    · exact hv (h ▸ C.head_mem he)
  have h5 : (5 : Fin 7) ∉ C.verts := hno_vert Q3Blue 5 hsub (by decide)
  have hS1 : C.edges ⊆ Q3Blue.erase 8 := hpeel Q3Blue 5 8 hsub h5 (Or.inl rfl)
  have h0 : (0 : Fin 7) ∉ C.verts := hno_vert _ 0 hS1 (by decide)
  have hS2 : C.edges ⊆ (Q3Blue.erase 8).erase 3 := hpeel _ 0 3 hS1 h0 (Or.inl rfl)
  have h1 : (1 : Fin 7) ∉ C.verts := hno_vert _ 1 hS2 (by decide)
  have hS3 : C.edges ⊆ ((Q3Blue.erase 8).erase 3).erase 4 := hpeel _ 1 4 hS2 h1 (Or.inl rfl)
  have h2 : (2 : Fin 7) ∉ C.verts := hno_vert _ 2 hS3 (by decide)
  have hS4 : C.edges ⊆ (((Q3Blue.erase 8).erase 3).erase 4).erase 5 := hpeel _ 2 5 hS3 h2 (Or.inl rfl)
  have h3 : (3 : Fin 7) ∉ C.verts := hno_vert _ 3 hS4 (by decide)
  have hS5 : C.edges ⊆ ((((Q3Blue.erase 8).erase 3).erase 4).erase 5).erase 6 := hpeel _ 3 6 hS4 h3 (Or.inl rfl)
  have h4 : (4 : Fin 7) ∉ C.verts := hno_vert _ 4 hS5 (by decide)
  have hS6 : C.edges ⊆ (((((Q3Blue.erase 8).erase 3).erase 4).erase 5).erase 6).erase 2 :=
    hpeel _ 4 2 hS5 h4 (Or.inl rfl)
  have hempty_S : (((((Q3Blue.erase 8).erase 3).erase 4).erase 5).erase 6).erase 2 = ∅ := by decide
  rw [hempty_S, Finset.subset_empty] at hS6
  obtain ⟨v, hv⟩ := hcyc.1.1
  have hd := hcyc.2 v hv
  simp [Multigraph.Subgraph.deg, hS6] at hd

private lemma Q3_red_forest :
    (Multigraph.Subgraph.ofEdges Q3Graph Finset.univ (Finset.univ \ Q3Blue)
      (fun _ => Finset.mem_univ _) (fun _ => Finset.mem_univ _)).IsForest := by
  intro C hCR hcyc
  have hsub : C.edges ⊆ Finset.univ \ Q3Blue := hCR.2
  have hno_vert : ∀ (S : Finset (Fin 9)) (v : Fin 7),
      C.edges ⊆ S →
      (S.filter (fun e => Q3Graph.tail e = v)).card +
      (S.filter (fun e => Q3Graph.head e = v)).card ≤ 1 →
      v ∉ C.verts := by
    intro S v hCS hle hv
    have hd := hcyc.2 v hv
    have hcd : C.deg v ≤ (S.filter (fun e => Q3Graph.tail e = v)).card +
        (S.filter (fun e => Q3Graph.head e = v)).card := by
      unfold Multigraph.Subgraph.deg
      exact add_le_add (Finset.card_le_card (Finset.filter_subset_filter _ hCS))
        (Finset.card_le_card (Finset.filter_subset_filter _ hCS))
    omega
  have h0 : (0 : Fin 7) ∉ C.verts := hno_vert _ 0 hsub (by decide)
  have h2 : (2 : Fin 7) ∉ C.verts := hno_vert _ 2 hsub (by decide)
  have h4 : (4 : Fin 7) ∉ C.verts := hno_vert _ 4 hsub (by decide)
  have hempty : C.edges = ∅ := by
    ext e
    simp only [Finset.notMem_empty, iff_false]
    intro he
    have hmem := hsub he
    fin_cases e
    · exact h0 (C.tail_mem he)
    · exact h2 (C.tail_mem he)
    · simp [Q3Blue] at hmem
    · simp [Q3Blue] at hmem
    · simp [Q3Blue] at hmem
    · simp [Q3Blue] at hmem
    · simp [Q3Blue] at hmem
    · exact h4 (C.tail_mem he)
    · simp [Q3Blue] at hmem
  obtain ⟨v, hv⟩ := hcyc.1.1
  have hd := hcyc.2 v hv
  simp [Multigraph.Subgraph.deg, hempty] at hd

private def Q3RedCompId : Fin 7 → Fin 4
  | 0 => 0 | 2 => 0 | 6 => 0
  | 4 => 1 | 5 => 1
  | 1 => 2
  | 3 => 3

private lemma Q3_redAdj_preserves_comp (u v : Fin 7) (h : redAdj Q3Graph Q3Blue u v) :
    Q3RedCompId u = Q3RedCompId v := by
  rcases h with ⟨e, he, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
  · subst h1; subst h2; fin_cases e <;> simp [Q3Blue, Q3Graph, Q3RedCompId] at he ⊢
  · subst h1; subst h2; fin_cases e <;> simp [Q3Blue, Q3Graph, Q3RedCompId] at he ⊢

private lemma Q3_redRTG_preserves_comp (u v : Fin 7)
    (h : Relation.ReflTransGen (redAdj Q3Graph Q3Blue) u v) :
    Q3RedCompId u = Q3RedCompId v := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact ih.trans (Q3_redAdj_preserves_comp _ _ hstep)

private def Q3StageV : Fin 3 → Finset (Fin 7)
  | 0 => {0, 1, 2, 6}
  | 1 => {0, 1, 2, 4, 5, 6}
  | 2 => Finset.univ

private def Q3Op1V : Fin 3 → Finset (Fin 7)
  | 0 => {0, 2, 6}
  | 1 => {0, 1, 2, 6}
  | 2 => {0, 1, 2, 4, 5, 6}

private def Q3Op2V : Fin 3 → Finset (Fin 7)
  | 0 => {1}
  | 1 => {4, 5}
  | 2 => {3}

private def Q3ENode : Fin 3 → Fin 9
  | 0 => 3 | 1 => 2 | 2 => 5

private def Q3FNode : Fin 3 → Fin 9
  | 0 => 4 | 1 => 8 | 2 => 6

private lemma Q3_blue_unique :
    ∀ t ∈ Q3Blue, ∃! i : Fin 3, t = Q3ENode i ∨ t = Q3FNode i := by
  intro t ht
  fin_cases t
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact ⟨1, Or.inl rfl, fun j hj => by revert j hj; decide⟩
  · exact ⟨0, Or.inl rfl, fun j hj => by revert j hj; decide⟩
  · exact ⟨0, Or.inr rfl, fun j hj => by revert j hj; decide⟩
  · exact ⟨2, Or.inl rfl, fun j hj => by revert j hj; decide⟩
  · exact ⟨2, Or.inr rfl, fun j hj => by revert j hj; decide⟩
  · exact absurd ht (by decide)
  · exact ⟨1, Or.inr rfl, fun j hj => by revert j hj; decide⟩

private lemma Q3_red_no_cross :
    ∀ i : Fin 3, ∀ e : Fin 9, e ∉ Q3Blue →
      (Q3Graph.tail e ∈ Q3Op1V i → Q3Graph.head e ∉ Q3Op2V i) ∧
      (Q3Graph.tail e ∈ Q3Op2V i → Q3Graph.head e ∉ Q3Op1V i) := by decide

private lemma Q3_stage_blue_topo :
    ∀ i : Fin 3, ∀ e ∈ Q3Blue,
      Q3Graph.tail e ∈ Q3StageV i → Q3Graph.head e ∈ Q3StageV i →
      ∃ j : Fin 3, j ≤ i ∧ (e = Q3ENode j ∨ e = Q3FNode j) := by decide

private lemma Q3_stage_crossing_only :
    ∀ i : Fin 3, ∀ e : Fin 9,
      ((Q3Graph.tail e ∈ Q3Op1V i ∧ Q3Graph.head e ∈ Q3Op2V i) ∨
       (Q3Graph.tail e ∈ Q3Op2V i ∧ Q3Graph.head e ∈ Q3Op1V i)) →
      e = Q3ENode i ∨ e = Q3FNode i := by decide

private lemma Q3_op1_blue_strict :
    ∀ i : Fin 3, ∀ e ∈ Q3Blue,
      Q3Graph.tail e ∈ Q3Op1V i → Q3Graph.head e ∈ Q3Op1V i →
      ∃ j : Fin 3, j < i ∧ (e = Q3ENode j ∨ e = Q3FNode j) := by decide

private lemma Q3_op2_blue_strict :
    ∀ i : Fin 3, ∀ e ∈ Q3Blue,
      Q3Graph.tail e ∈ Q3Op2V i → Q3Graph.head e ∈ Q3Op2V i →
      ∃ j : Fin 3, j < i ∧ (e = Q3ENode j ∨ e = Q3FNode j) := by decide

private lemma Q3_op1_red_closed :
    ∀ i : Fin 3, ∀ e : Fin 9, e ∉ Q3Blue →
      (Q3Graph.tail e ∈ Q3Op1V i ↔ Q3Graph.head e ∈ Q3Op1V i) := by decide

private lemma Q3_op2_red_closed :
    ∀ i : Fin 3, ∀ e : Fin 9, e ∉ Q3Blue →
      (Q3Graph.tail e ∈ Q3Op2V i ↔ Q3Graph.head e ∈ Q3Op2V i) := by decide

set_option maxHeartbeats 400000 in
theorem nonvacuous_subdivision_aux_frame_proved :
    let G : Multigraph (Fin 2) (Fin 3) := ⟨fun _ => 0, fun _ => 1⟩
    ∃ (sub : SubdivisionData G (Multigraph.Subgraph.top G))
      (aux : AuxGraphData G (Multigraph.Subgraph.top G) sub),
      Nonempty (Frame G (Multigraph.Subgraph.top G) sub aux) := by
  dsimp only
  change ∃ (sub : SubdivisionData G3P (Multigraph.Subgraph.top G3P))
    (aux : AuxGraphData G3P (Multigraph.Subgraph.top G3P) sub),
    Nonempty (Frame G3P (Multigraph.Subgraph.top G3P) sub aux)
  let sub : SubdivisionData G3P (Multigraph.Subgraph.top G3P) :=
    { V₀ := Fin 2
      E₀ := Fin 3
      H₀ := G3P
      loopless := fun _ => by change (0 : Fin 2) ≠ 1; decide
      edgeConn3 := by
        intro S hS hSc
        have h : ∀ T : Finset (Fin 2), T.Nonempty → (Finset.univ \ T).Nonempty →
            3 ≤ (G3P.cutEdges T).card := by decide
        exact h S hS hSc
      card_ge_two := by decide
      embedV := Function.Embedding.refl (Fin 2)
      embedV_mem := fun _ => Finset.mem_univ _
      thread := fun t =>
        { verts := [0, 1]
          edges := [t]
          len_pos := by simp
          len_le := by simp
          verts_len := by simp
          verts_nodup := by decide
          verts_sub := fun _ _ => Finset.mem_univ _
          edges_sub := fun _ _ => Finset.mem_univ _
          head_eq := rfl
          last_eq := rfl
          step_connect := fun i hi => by
            have hi0 : i = 0 := by simp at hi; omega
            subst hi0; exact Or.inl ⟨rfl, rfl⟩ }
      edges_disjoint := fun t₁ t₂ hne e he => by
        simp at he ⊢; subst he; exact hne
      edges_cover := fun e _ => ⟨e, by simp⟩
      interior_disjoint_branch := fun t v hv h0 h1 => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl
        · exact absurd rfl h0
        · exact absurd rfl h1
      interior_disjoint := fun t₁ t₂ _ v ⟨hv, h0, h1⟩ => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
        rcases hv with rfl | rfl
        · exact absurd rfl h0
        · exact absurd rfl h1
      verts_cover := fun v _ => Or.inl ⟨v, rfl⟩ }
  -- Iso between Q3Graph and (induced Q3Graph univ).toMultigraph
  have hQ3_induced_iso : ∀ b : Fin 1,
      Nonempty (Multigraph.Iso
        (Multigraph.Subgraph.induced Q3Graph (Finset.univ.filter (fun _ : Fin 7 => (0 : Fin 1) = b))).toMultigraph
        Q3Graph) := by
    intro b; fin_cases b
    refine ⟨{
      toVert :=
        { toFun := fun v => v.1
          invFun := fun v => ⟨v, by simp [Multigraph.Subgraph.induced]⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      toEdge :=
        { toFun := fun e => e.1
          invFun := fun e => ⟨e, by simp [Multigraph.Subgraph.induced]⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      dir := fun _ => false
      tail_eq := fun _ => rfl
      head_eq := fun _ => rfl }⟩
  have hcomp_tc3ec : ∀ b : Fin 1,
      (Multigraph.Subgraph.induced Q3Graph (Finset.univ.filter (fun _ : Fin 7 => (0 : Fin 1) = b))).toMultigraph.IsTruncatedCubic3EC := by
    intro b
    obtain ⟨iso⟩ := hQ3_induced_iso b
    rcases Q3_isTC3EC with ⟨V', E', _, _, _, _, Qplus, v, hcub, h3, h4, ⟨iso2⟩⟩
    refine ⟨V', E', inferInstance, inferInstance, inferInstance, inferInstance, Qplus, v, hcub, h3, h4, ⟨?_⟩⟩
    exact
      { toVert := iso.toVert.trans iso2.toVert
        toEdge := iso.toEdge.trans iso2.toEdge
        dir := fun e => xor (iso.dir e) (iso2.dir (iso.toEdge e))
        tail_eq := fun e => by
          have h1 := iso.tail_eq e
          have h2 := iso.head_eq e
          have h3 := iso2.tail_eq (iso.toEdge e)
          have h4 := iso2.head_eq (iso.toEdge e)
          cases hd1 : iso.dir e <;> cases hd2 : iso2.dir (iso.toEdge e) <;>
            simp_all
        head_eq := fun e => by
          have h1 := iso.tail_eq e
          have h2 := iso.head_eq e
          have h3 := iso2.tail_eq (iso.toEdge e)
          have h4 := iso2.head_eq (iso.toEdge e)
          cases hd1 : iso.dir e <;> cases hd2 : iso2.dir (iso.toEdge e) <;>
            simp_all }
  let origEmb : Fin 3 ↪ Fin 9 := ⟨fun t => ⟨t.1, by omega⟩, fun a b h =>
    Fin.ext (by simpa using congrArg Fin.val h)⟩
  let contractV : Fin 7 → Fin 2 := fun v => if v = 6 then 1 else 0
  let aux : AuxGraphData G3P (Multigraph.Subgraph.top G3P) sub :=
    { numBlocks := 1
      VQ := Fin 7
      EQ := Fin 9
      Q := Q3Graph
      comp := fun _ => 0
      edge_same_comp := fun _ => rfl
      comp_tc3ec := hcomp_tc3ec
      origEdge := origEmb
      contractV := contractV
      orig_tail := fun t => by fin_cases t <;> rfl
      orig_head := fun t => by fin_cases t <;> rfl
      exp_same_contractV := fun e hexp => by
        fin_cases e
        · exact absurd rfl (hexp 0)
        · exact absurd rfl (hexp 1)
        · exact absurd rfl (hexp 2)
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
        · rfl
      fiber_connected := fun _ u v _ _ hcv => by
        let R := fun x y : Fin 7 => ∃ e : Fin 9, (∀ t : Fin 3, origEmb t ≠ e) ∧
          ((Q3Graph.tail e = x ∧ Q3Graph.head e = y) ∨ (Q3Graph.tail e = y ∧ Q3Graph.head e = x))
        have hstep : ∀ (e : Fin 9), (∀ t : Fin 3, origEmb t ≠ e) →
            R (Q3Graph.tail e) (Q3Graph.head e) ∧ R (Q3Graph.head e) (Q3Graph.tail e) := fun e he =>
          ⟨⟨e, he, Or.inl ⟨rfl, rfl⟩⟩, ⟨e, he, Or.inr ⟨rfl, rfl⟩⟩⟩
        have h01 : R 0 1 ∧ R 1 0 := hstep 3 (fun t => by fin_cases t <;> decide)
        have h12 : R 1 2 ∧ R 2 1 := hstep 4 (fun t => by fin_cases t <;> decide)
        have h23 : R 2 3 ∧ R 3 2 := hstep 5 (fun t => by fin_cases t <;> decide)
        have h34 : R 3 4 ∧ R 4 3 := hstep 6 (fun t => by fin_cases t <;> decide)
        have h45 : R 4 5 ∧ R 5 4 := hstep 7 (fun t => by fin_cases t <;> decide)
        have hreach0 : ∀ x : Fin 7, x ≠ 6 → Relation.ReflTransGen R 0 x := by
          intro x hx; fin_cases x
          · exact .refl
          · exact Relation.ReflTransGen.single h01.1
          · exact (Relation.ReflTransGen.single h01.1).tail h12.1
          · exact ((Relation.ReflTransGen.single h01.1).tail h12.1).tail h23.1
          · exact (((Relation.ReflTransGen.single h01.1).tail h12.1).tail h23.1).tail h34.1
          · exact ((((Relation.ReflTransGen.single h01.1).tail h12.1).tail h23.1).tail h34.1).tail h45.1
          · exact absurd rfl hx
        have hsym_R : ∀ x y, Relation.ReflTransGen R x y → Relation.ReflTransGen R y x := by
          intro x y h
          induction h with
          | refl => exact .refl
          | tail _ hs ih =>
            rcases hs with ⟨e, he, h1 | h1⟩
            · exact .head ⟨e, he, Or.inr h1⟩ ih
            · exact .head ⟨e, he, Or.inl h1⟩ ih
        by_cases hu : u = 6
        · subst hu
          have hv : v = 6 := by
            by_contra hvn; simp [contractV, hvn] at hcv
          subst hv; exact .refl
        · have hv : v ≠ 6 := by
            intro hv6; subst hv6; simp [contractV, hu] at hcv
          exact (hsym_R 0 u (hreach0 u hu)).trans (hreach0 v hv)
      block_subgraph := fun _ => Multigraph.Subgraph.top G3P
      is_block := fun _ => by
        refine ⟨⟨⟨0, Finset.mem_univ 0⟩, fun u _ v _ => by
          fin_cases u <;> fin_cases v
          · exact .refl
          · exact .single ⟨0, Finset.mem_univ _, Or.inl ⟨rfl, rfl⟩⟩
          · exact .single ⟨0, Finset.mem_univ _, Or.inr ⟨rfl, rfl⟩⟩
          · exact .refl⟩, ?_, ?_⟩
        · rintro v _ ⟨_, u, w, hu, hw, hnr⟩
          simp only [Multigraph.Subgraph.deleteVertex, Multigraph.Subgraph.top,
            Finset.mem_erase, Finset.mem_univ, and_true] at hu hw
          have huw : u = w := by fin_cases v <;> fin_cases u <;> fin_cases w <;> simp_all
          subst huw; exact hnr .refl
        · intro K' hle _ _
          ext x
          · exact ⟨fun _ => Finset.mem_univ _, fun h => hle.1 h⟩
          · exact ⟨fun _ => Finset.mem_univ _, fun h => hle.2 h⟩
      orig_in_block := fun _ b => by fin_cases b; simp [Multigraph.Subgraph.top]
      thread_aligned := fun t i hi => by
        have hi0 : i = 0 := by simp [sub] at hi; omega
        subst hi0; exact ⟨rfl, rfl⟩ }
  -- Now construct Frame on (G3P, top G3P, sub, aux)
  have hcomp_wc : ∀ b : Fin aux.numBlocks,
      let Qb := (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).toMultigraph
      ∃ wc : WellColouring Qb, ∀ e, e ∈ wc.blue ↔ e.1 ∈ Q3Blue := by
    intro b; fin_cases b
    classical
    let Qb := (Multigraph.Subgraph.induced Q3Graph (Finset.univ.filter (fun _ : Fin 7 => (0 : Fin 1) = 0))).toMultigraph
    let blueQb : Finset {e : Fin 9 // e ∈ (Multigraph.Subgraph.induced Q3Graph (Finset.univ.filter (fun _ : Fin 7 => (0 : Fin 1) = 0))).edges} :=
      Finset.univ.filter (fun e => e.1 ∈ Q3Blue)
    -- Transport WellColouring from Q3Graph via the canonical equivalence
    let eV : {v : Fin 7 // v ∈ (Multigraph.Subgraph.induced Q3Graph (Finset.univ.filter (fun _ : Fin 7 => (0 : Fin 1) = 0))).verts} ≃ Fin 7 :=
      { toFun := Subtype.val
        invFun := fun v => ⟨v, by simp [Multigraph.Subgraph.induced]⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    let eE : {e : Fin 9 // e ∈ (Multigraph.Subgraph.induced Q3Graph (Finset.univ.filter (fun _ : Fin 7 => (0 : Fin 1) = 0))).edges} ≃ Fin 9 :=
      { toFun := Subtype.val
        invFun := fun e => ⟨e, by simp [Multigraph.Subgraph.induced]⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have hblue_tree : (Multigraph.Subgraph.ofEdges Qb Finset.univ blueQb
        (fun _ => Finset.mem_univ _) (fun _ => Finset.mem_univ _)).IsSpanningTree := by
      let T := Multigraph.Subgraph.ofEdges Qb Finset.univ blueQb
        (fun _ => Finset.mem_univ _) (fun _ => Finset.mem_univ _)
      let T0 := Multigraph.Subgraph.ofEdges Q3Graph Finset.univ Q3Blue
        (fun _ => Finset.mem_univ _) (fun _ => Finset.mem_univ _)
      have hT0 := Q3_blue_tree
      have hadj : ∀ u v, T0.Adj u v → T.Adj (eV.symm u) (eV.symm v) := by
        rintro u v ⟨e, he, h⟩
        refine ⟨eE.symm e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩, ?_⟩
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨Subtype.ext h1, Subtype.ext h2⟩
        · exact Or.inr ⟨Subtype.ext h1, Subtype.ext h2⟩
      refine ⟨rfl, ⟨⟨eV.symm 0, Finset.mem_univ _⟩, fun u _ v _ => ?_⟩, ?_⟩
      · have hrtg := hT0.2.1.2 u.1 (Finset.mem_univ _) v.1 (Finset.mem_univ _)
        have hlift : ∀ a b, Relation.ReflTransGen T0.Adj a b →
            Relation.ReflTransGen T.Adj (eV.symm a) (eV.symm b) := by
          intro a b hab
          induction hab with
          | refl => exact .refl
          | tail _ hs ih => exact ih.tail (hadj _ _ hs)
        have hres := hlift u.1 v.1 hrtg
        exact hres
      · intro C hCT hcyc
        let C0 : Q3Graph.Subgraph :=
          { verts := C.verts.map eV.toEmbedding
            edges := C.edges.map eE.toEmbedding
            tail_mem := fun he => by
              rw [Finset.mem_map] at he; rcases he with ⟨e, heC, rfl⟩
              exact Finset.mem_map.mpr ⟨Qb.tail e, C.tail_mem heC, rfl⟩
            head_mem := fun he => by
              rw [Finset.mem_map] at he; rcases he with ⟨e, heC, rfl⟩
              exact Finset.mem_map.mpr ⟨Qb.head e, C.head_mem heC, rfl⟩ }
        have hC0le : C0 ≤ T0 := by
          refine ⟨fun _ _ => Finset.mem_univ _, fun e he => ?_⟩
          rw [Finset.mem_map] at he; rcases he with ⟨e', he', rfl⟩
          exact (Finset.mem_filter.mp (hCT.2 he')).2
        have hC0cyc : C0.IsCycle := by
          refine ⟨⟨?_, ?_⟩, ?_⟩
          · obtain ⟨v, hv⟩ := hcyc.1.1
            exact ⟨v.1, Finset.mem_map.mpr ⟨v, hv, rfl⟩⟩
          · intro u hu v hv
            rw [Finset.mem_map] at hu hv
            rcases hu with ⟨u', hu', rfl⟩; rcases hv with ⟨v', hv', rfl⟩
            have hrtg := hcyc.1.2 u' hu' v' hv'
            clear hv'
            induction hrtg with
            | refl => exact .refl
            | tail _ hs ih =>
              rcases hs with ⟨e, heC, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
              · exact ih.tail ⟨e.1, Finset.mem_map.mpr ⟨e, heC, rfl⟩,
                  Or.inl ⟨congrArg Subtype.val h1, congrArg Subtype.val h2⟩⟩
              · exact ih.tail ⟨e.1, Finset.mem_map.mpr ⟨e, heC, rfl⟩,
                  Or.inr ⟨congrArg Subtype.val h1, congrArg Subtype.val h2⟩⟩
          · intro v hv
            rw [Finset.mem_map] at hv; rcases hv with ⟨v', hv', rfl⟩
            have hdeg := hcyc.2 v' hv'
            unfold Multigraph.Subgraph.deg at hdeg ⊢
            have h1 : (C0.edges.filter (fun e => Q3Graph.tail e = v'.1)).card =
                (C.edges.filter (fun e => Qb.tail e = v')).card := by
              refine Finset.card_bij (fun e _ => eE.symm e) (fun e he => ?_) (fun _ _ _ _ h => eE.symm.injective h)
                (fun e he => ⟨e.1, ?_, by simp [eE]⟩)
              · rw [Finset.mem_filter] at he ⊢
                rw [Finset.mem_map] at he
                rcases he.1 with ⟨e', he', rfl⟩
                exact ⟨by simpa [eE] using he', Subtype.ext he.2⟩
              · rw [Finset.mem_filter] at he ⊢
                exact ⟨Finset.mem_map.mpr ⟨e, he.1, rfl⟩, congrArg Subtype.val he.2⟩
            have h2 : (C0.edges.filter (fun e => Q3Graph.head e = v'.1)).card =
                (C.edges.filter (fun e => Qb.head e = v')).card := by
              refine Finset.card_bij (fun e _ => eE.symm e) (fun e he => ?_) (fun _ _ _ _ h => eE.symm.injective h)
                (fun e he => ⟨e.1, ?_, by simp [eE]⟩)
              · rw [Finset.mem_filter] at he ⊢
                rw [Finset.mem_map] at he
                rcases he.1 with ⟨e', he', rfl⟩
                exact ⟨by simpa [eE] using he', Subtype.ext he.2⟩
              · rw [Finset.mem_filter] at he ⊢
                exact ⟨Finset.mem_map.mpr ⟨e, he.1, rfl⟩, congrArg Subtype.val he.2⟩
            change (C0.edges.filter (fun e => Q3Graph.tail e = v'.1)).card +
              (C0.edges.filter (fun e => Q3Graph.head e = v'.1)).card = 2
            rw [h1, h2]; exact hdeg
        exact hT0.2.2 C0 hC0le hC0cyc
    -- Build 2-construction directly on redQuotient Qb blueQb
    have hred_iff : ∀ u v, redAdj Qb blueQb u v ↔ redAdj Q3Graph Q3Blue u.1 v.1 := by
      intro u v; constructor
      · rintro ⟨e, he, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
        · exact ⟨e.1, fun h => he (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩),
            Or.inl ⟨congrArg Subtype.val h1, congrArg Subtype.val h2⟩⟩
        · exact ⟨e.1, fun h => he (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩),
            Or.inr ⟨congrArg Subtype.val h1, congrArg Subtype.val h2⟩⟩
      · rintro ⟨e, he, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
        · exact ⟨eE.symm e, fun h => he (Finset.mem_filter.mp h).2,
            Or.inl ⟨Subtype.ext h1, Subtype.ext h2⟩⟩
        · exact ⟨eE.symm e, fun h => he (Finset.mem_filter.mp h).2,
            Or.inr ⟨Subtype.ext h1, Subtype.ext h2⟩⟩
    have hrtg_iff : ∀ u v, Relation.ReflTransGen (redAdj Qb blueQb) u v ↔
        Relation.ReflTransGen (redAdj Q3Graph Q3Blue) u.1 v.1 := by
      intro u v; constructor
      · intro h; induction h with
        | refl => exact .refl
        | tail _ hs ih => exact ih.tail ((hred_iff _ _).mp hs)
      · intro h
        have hlift : ∀ a b, Relation.ReflTransGen (redAdj Q3Graph Q3Blue) a b →
            Relation.ReflTransGen (redAdj Qb blueQb) (eV.symm a) (eV.symm b) := by
          intro a b hab; induction hab with
          | refl => exact .refl
          | tail _ hs ih => exact ih.tail ((hred_iff _ _).mpr hs)
        simpa [eV] using hlift u.1 v.1 h
    let cA : Quotient (redSetoid Qb blueQb) := Quotient.mk _ (eV.symm 0)
    let cB : Quotient (redSetoid Qb blueQb) := Quotient.mk _ (eV.symm 4)
    let cC : Quotient (redSetoid Qb blueQb) := Quotient.mk _ (eV.symm 1)
    let cD : Quotient (redSetoid Qb blueQb) := Quotient.mk _ (eV.symm 3)
    have h06 : Relation.ReflTransGen (redAdj Q3Graph Q3Blue) 0 6 :=
      .single ⟨0, by decide, Or.inl ⟨rfl, rfl⟩⟩
    have h62 : Relation.ReflTransGen (redAdj Q3Graph Q3Blue) 6 2 :=
      .single ⟨1, by decide, Or.inr ⟨rfl, rfl⟩⟩
    have h45 : Relation.ReflTransGen (redAdj Q3Graph Q3Blue) 4 5 :=
      .single ⟨7, by decide, Or.inl ⟨rfl, rfl⟩⟩
    have hq6 : Quotient.mk (redSetoid Qb blueQb) (eV.symm 6) = cA :=
      (Quotient.sound ((hrtg_iff _ _).mpr h06)).symm
    have hq2 : Quotient.mk (redSetoid Qb blueQb) (eV.symm 2) = cA :=
      (Quotient.sound ((hrtg_iff _ _).mpr (h06.trans h62))).symm
    have hq5 : Quotient.mk (redSetoid Qb blueQb) (eV.symm 5) = cB :=
      (Quotient.sound ((hrtg_iff _ _).mpr h45)).symm
    have hne_of_id : ∀ u v : Fin 7, Q3RedCompId u ≠ Q3RedCompId v →
        Quotient.mk (redSetoid Qb blueQb) (eV.symm u) ≠
        Quotient.mk (redSetoid Qb blueQb) (eV.symm v) := by
      intro u v hne hq
      exact hne (Q3_redRTG_preserves_comp u v ((hrtg_iff _ _).mp (Quotient.exact hq)))
    have hcAC : cA ≠ cC := hne_of_id 0 1 (by decide)
    have hcAB : cA ≠ cB := hne_of_id 0 4 (by decide)
    have hcCB : cC ≠ cB := hne_of_id 1 4 (by decide)
    have hcAD : cA ≠ cD := hne_of_id 0 3 (by decide)
    have hcCD : cC ≠ cD := hne_of_id 1 3 (by decide)
    have hcBD : cB ≠ cD := hne_of_id 4 3 (by decide)
    let mkE : ∀ e : Fin 9, e ∈ Q3Blue → {x // x ∈ blueQb} := fun e he =>
      ⟨eE.symm e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩⟩
    let f2 := mkE 2 (by decide)
    let f3 := mkE 3 (by decide)
    let f4 := mkE 4 (by decide)
    let f5 := mkE 5 (by decide)
    let f6 := mkE 6 (by decide)
    let f8 := mkE 8 (by decide)
    have hne_f : ∀ a b : {x // x ∈ blueQb}, a.1.1 ≠ b.1.1 → a ≠ b :=
      fun _ _ h hab => h (congrArg (fun x => x.1.1) hab)
    let tc0 : TwoConstruction (redQuotient Qb blueQb) ({cA} ∪ {cC})
        (insert f3 (insert f4 (∅ ∪ ∅))) :=
      TwoConstruction.join (.single cA) (.single cC) f3 f4
        (Finset.disjoint_singleton.mpr hcAC) (Finset.disjoint_empty_left _)
        (hne_f f3 f4 (by decide))
        (Finset.notMem_empty _) (Finset.notMem_empty _)
        (Finset.notMem_empty _) (Finset.notMem_empty _)
        (Or.inl ⟨Finset.mem_singleton_self cA, Finset.mem_singleton_self cC⟩)
        (Or.inr ⟨Finset.mem_singleton_self cC, by
          change Quotient.mk (redSetoid Qb blueQb) (eV.symm 2) ∈ ({cA} : Finset _)
          rw [hq2]; exact Finset.mem_singleton_self cA⟩)
    let tc1 : TwoConstruction (redQuotient Qb blueQb) (({cA} ∪ {cC}) ∪ {cB})
        (insert f2 (insert f8 (insert f3 (insert f4 (∅ ∪ ∅)) ∪ ∅))) :=
      TwoConstruction.join tc0 (.single cB) f2 f8
        (by simp [Finset.disjoint_singleton_right, hcAB.symm, hcCB.symm])
        (Finset.disjoint_empty_right _)
        (hne_f f2 f8 (by decide))
        (by simp [f2, f3, f4, mkE, Subtype.ext_iff, eE]) (Finset.notMem_empty _)
        (by simp [f8, f3, f4, mkE, Subtype.ext_iff, eE]) (Finset.notMem_empty _)
        (Or.inr ⟨Finset.mem_singleton_self cB, by
          change Quotient.mk (redSetoid Qb blueQb) (eV.symm 6) ∈ ({cA} ∪ {cC} : Finset _)
          rw [hq6]; simp⟩)
        (Or.inr ⟨by
          change Quotient.mk (redSetoid Qb blueQb) (eV.symm 5) ∈ ({cB} : Finset _)
          rw [hq5]; exact Finset.mem_singleton_self cB, by
          change cA ∈ ({cA} ∪ {cC} : Finset _); simp⟩)
    let tc2 : TwoConstruction (redQuotient Qb blueQb) ((({cA} ∪ {cC}) ∪ {cB}) ∪ {cD})
        (insert f5 (insert f6 (insert f2 (insert f8 (insert f3 (insert f4 (∅ ∪ ∅)) ∪ ∅)) ∪ ∅))) :=
      TwoConstruction.join tc1 (.single cD) f5 f6
        (by simp [Finset.disjoint_singleton_right, hcAD.symm, hcCD.symm, hcBD.symm])
        (Finset.disjoint_empty_right _)
        (hne_f f5 f6 (by decide))
        (by simp [f5, f2, f8, f3, f4, mkE, Subtype.ext_iff, eE]) (Finset.notMem_empty _)
        (by simp [f6, f2, f8, f3, f4, mkE, Subtype.ext_iff, eE]) (Finset.notMem_empty _)
        (Or.inl ⟨by
          change Quotient.mk (redSetoid Qb blueQb) (eV.symm 2) ∈ (({cA} ∪ {cC}) ∪ {cB} : Finset _)
          rw [hq2]; simp, Finset.mem_singleton_self cD⟩)
        (Or.inr ⟨Finset.mem_singleton_self cD, by
          change cB ∈ (({cA} ∪ {cC}) ∪ {cB} : Finset _); simp⟩)
    have huniv_W : ((({cA} ∪ {cC}) ∪ {cB}) ∪ {cD} : Finset (Quotient (redSetoid Qb blueQb))) =
        Finset.univ := by
      ext q
      simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_univ, iff_true]
      induction q using Quotient.ind with
      | _ v =>
        obtain ⟨v, hv⟩ := v
        have hveq : (⟨v, hv⟩ : {x : Fin 7 // _}) = eV.symm v := rfl
        rw [hveq]
        fin_cases v
        · exact Or.inl (Or.inl (Or.inl rfl))
        · exact Or.inl (Or.inl (Or.inr rfl))
        · exact Or.inl (Or.inl (Or.inl hq2))
        · exact Or.inr rfl
        · exact Or.inl (Or.inr rfl)
        · exact Or.inl (Or.inr hq5)
        · exact Or.inl (Or.inl (Or.inl hq6))
    have huniv_E : insert f5 (insert f6 (insert f2 (insert f8 (insert f3 (insert f4 ((∅ : Finset {x // x ∈ blueQb}) ∪ ∅)) ∪ ∅)) ∪ ∅)) =
        Finset.univ := by
      ext ⟨⟨e, he⟩, hmem⟩
      have hbl : e ∈ Q3Blue := (Finset.mem_filter.mp hmem).2
      simp only [Q3Blue, Finset.mem_insert, Finset.mem_singleton] at hbl
      simp only [Finset.mem_univ, iff_true, Finset.union_empty, Finset.mem_insert, Finset.notMem_empty, or_false]
      rcases hbl with rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inr (Or.inr (Or.inl (Subtype.ext (Subtype.ext rfl))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Subtype.ext (Subtype.ext rfl))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Subtype.ext (Subtype.ext rfl))))))
      · exact Or.inl (Subtype.ext (Subtype.ext rfl))
      · exact Or.inr (Or.inl (Subtype.ext (Subtype.ext rfl)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (Subtype.ext (Subtype.ext rfl)))))
    have htc_final : TwoConstruction (redQuotient Qb blueQb) Finset.univ Finset.univ := by
      rw [← huniv_W, ← huniv_E]
      exact tc2
    exact ⟨{ blue := blueQb
             blue_tree := hblue_tree
             twoConstr := htc_final },
           fun e => ⟨fun h => (Finset.mem_filter.mp h).2,
             fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩⟩
  -- Red connectivity helpers for op1/op2
  have hred06 : redAdj Q3Graph Q3Blue 0 6 := ⟨0, by decide, Or.inl ⟨rfl, rfl⟩⟩
  have hred60 : redAdj Q3Graph Q3Blue 6 0 := ⟨0, by decide, Or.inr ⟨rfl, rfl⟩⟩
  have hred26 : redAdj Q3Graph Q3Blue 2 6 := ⟨1, by decide, Or.inl ⟨rfl, rfl⟩⟩
  have hred62 : redAdj Q3Graph Q3Blue 6 2 := ⟨1, by decide, Or.inr ⟨rfl, rfl⟩⟩
  have hred45 : redAdj Q3Graph Q3Blue 4 5 := ⟨7, by decide, Or.inl ⟨rfl, rfl⟩⟩
  have hred54 : redAdj Q3Graph Q3Blue 5 4 := ⟨7, by decide, Or.inr ⟨rfl, rfl⟩⟩
  have hredA : ∀ u ∈ ({0, 2, 6} : Finset (Fin 7)), ∀ v ∈ ({0, 2, 6} : Finset (Fin 7)),
      Relation.ReflTransGen (redAdj Q3Graph Q3Blue) u v := by
    intro u hu v hv
    have hu6 : Relation.ReflTransGen (redAdj Q3Graph Q3Blue) u 6 := by
      fin_cases u <;> simp at hu
      · exact .single hred06
      · exact .single hred26
      · exact .refl
    have h6v : Relation.ReflTransGen (redAdj Q3Graph Q3Blue) 6 v := by
      fin_cases v <;> simp at hv
      · exact .single hred60
      · exact .single hred62
      · exact .refl
    exact hu6.trans h6v
  have hredB : ∀ u ∈ ({4, 5} : Finset (Fin 7)), ∀ v ∈ ({4, 5} : Finset (Fin 7)),
      Relation.ReflTransGen (redAdj Q3Graph Q3Blue) u v := by
    intro u hu v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact .refl
    · exact Relation.ReflTransGen.single hred45
    · exact Relation.ReflTransGen.single hred54
    · exact .refl
  have hconn_of_red : ∀ (U : Finset (Fin 7)), U.Nonempty →
      (∀ u ∈ U, ∀ v ∈ U, Relation.ReflTransGen (redAdj Q3Graph Q3Blue) u v) →
      (∀ e : Fin 9, e ∉ Q3Blue → (Q3Graph.tail e ∈ U ↔ Q3Graph.head e ∈ U)) →
      (Multigraph.Subgraph.induced Q3Graph U).Connected := by
    intro U hUne hred hcl
    refine ⟨hUne, fun u hu v hv => ?_⟩
    have hrtg := hred u hu v hv
    have hgo : ∀ x y, Relation.ReflTransGen (redAdj Q3Graph Q3Blue) x y → x ∈ U →
        Relation.ReflTransGen (Multigraph.Subgraph.induced Q3Graph U).Adj x y ∧ y ∈ U := by
      intro x y hxy hx
      induction hxy with
      | refl => exact ⟨.refl, hx⟩
      | @tail a b _ hstep ih =>
        obtain ⟨hpath, haU⟩ := ih
        rcases hstep with ⟨e, heB, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
        · have hbU : b ∈ U := by rw [← h2, ← hcl e heB, h1]; exact haU
          exact ⟨hpath.tail ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1.symm ▸ haU, h2.symm ▸ hbU⟩,
            Or.inl ⟨h1, h2⟩⟩, hbU⟩
        · have hbU : b ∈ U := by rw [← h1, hcl e heB, h2]; exact haU
          exact ⟨hpath.tail ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1.symm ▸ hbU, h2.symm ▸ haU⟩,
            Or.inr ⟨h1, h2⟩⟩, hbU⟩
    exact (hgo u v hrtg hu).1
  have hconn_s0 : (Multigraph.Subgraph.induced Q3Graph {0, 1, 2, 6}).Connected := by
    let H := Multigraph.Subgraph.induced Q3Graph ({0, 1, 2, 6} : Finset (Fin 7))
    have h01 : H.Adj 0 1 := ⟨3, by decide, Or.inl ⟨rfl, rfl⟩⟩
    have h10 : H.Adj 1 0 := ⟨3, by decide, Or.inr ⟨rfl, rfl⟩⟩
    have h06 : H.Adj 0 6 := ⟨0, by decide, Or.inl ⟨rfl, rfl⟩⟩
    have h60 : H.Adj 6 0 := ⟨0, by decide, Or.inr ⟨rfl, rfl⟩⟩
    have h26 : H.Adj 2 6 := ⟨1, by decide, Or.inl ⟨rfl, rfl⟩⟩
    have h62 : H.Adj 6 2 := ⟨1, by decide, Or.inr ⟨rfl, rfl⟩⟩
    refine ⟨⟨0, by decide⟩, fun u hu v hv => ?_⟩
    have hu0 : Relation.ReflTransGen H.Adj u 0 := by
      simp only [H, Multigraph.Subgraph.induced, Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl | rfl | rfl
      · exact .refl
      · exact Relation.ReflTransGen.single h10
      · exact (Relation.ReflTransGen.single h26).tail h60
      · exact Relation.ReflTransGen.single h60
    have h0v : Relation.ReflTransGen H.Adj 0 v := by
      simp only [H, Multigraph.Subgraph.induced, Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl | rfl
      · exact .refl
      · exact Relation.ReflTransGen.single h01
      · exact (Relation.ReflTransGen.single h06).tail h62
      · exact Relation.ReflTransGen.single h06
    exact hu0.trans h0v
  have hconn_s1 : (Multigraph.Subgraph.induced Q3Graph {0, 1, 2, 4, 5, 6}).Connected := by
    let H := Multigraph.Subgraph.induced Q3Graph ({0, 1, 2, 4, 5, 6} : Finset (Fin 7))
    have h01 : H.Adj 0 1 := ⟨3, by decide, Or.inl ⟨rfl, rfl⟩⟩
    have h10 : H.Adj 1 0 := ⟨3, by decide, Or.inr ⟨rfl, rfl⟩⟩
    have h06 : H.Adj 0 6 := ⟨0, by decide, Or.inl ⟨rfl, rfl⟩⟩
    have h60 : H.Adj 6 0 := ⟨0, by decide, Or.inr ⟨rfl, rfl⟩⟩
    have h26 : H.Adj 2 6 := ⟨1, by decide, Or.inl ⟨rfl, rfl⟩⟩
    have h62 : H.Adj 6 2 := ⟨1, by decide, Or.inr ⟨rfl, rfl⟩⟩
    have h46 : H.Adj 4 6 := ⟨2, by decide, Or.inl ⟨rfl, rfl⟩⟩
    have h64 : H.Adj 6 4 := ⟨2, by decide, Or.inr ⟨rfl, rfl⟩⟩
    have h50 : H.Adj 5 0 := ⟨8, by decide, Or.inl ⟨rfl, rfl⟩⟩
    have h05 : H.Adj 0 5 := ⟨8, by decide, Or.inr ⟨rfl, rfl⟩⟩
    refine ⟨⟨0, by decide⟩, fun u hu v hv => ?_⟩
    have hu0 : Relation.ReflTransGen H.Adj u 0 := by
      simp only [H, Multigraph.Subgraph.induced, Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
      · exact .refl
      · exact Relation.ReflTransGen.single h10
      · exact (Relation.ReflTransGen.single h26).tail h60
      · exact (Relation.ReflTransGen.single h46).tail h60
      · exact Relation.ReflTransGen.single h50
      · exact Relation.ReflTransGen.single h60
    have h0v : Relation.ReflTransGen H.Adj 0 v := by
      simp only [H, Multigraph.Subgraph.induced, Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl
      · exact .refl
      · exact Relation.ReflTransGen.single h01
      · exact (Relation.ReflTransGen.single h06).tail h62
      · exact (Relation.ReflTransGen.single h06).tail h64
      · exact Relation.ReflTransGen.single h05
      · exact Relation.ReflTransGen.single h06
    exact hu0.trans h0v
  have hQ3_e_ne_f : ∀ i : Fin 3, Q3ENode i ≠ Q3FNode i := by decide
  have hQ3_e_blue : ∀ i : Fin 3, Q3ENode i ∈ Q3Blue := by decide
  have hQ3_f_blue : ∀ i : Fin 3, Q3FNode i ∈ Q3Blue := by decide
  have hQ3_stage_union : ∀ i : Fin 3, Q3StageV i = Q3Op1V i ∪ Q3Op2V i := by decide
  have hQ3_stage_disj : ∀ i : Fin 3, Disjoint (Q3Op1V i) (Q3Op2V i) := by decide
  have hQ3_op1_ne : ∀ i : Fin 3, (Q3Op1V i).Nonempty := by decide
  have hQ3_op2_ne : ∀ i : Fin 3, (Q3Op2V i).Nonempty := by decide
  have hQ3_e_cross : ∀ i : Fin 3,
      (Q3Graph.tail (Q3ENode i) ∈ Q3Op1V i ∧ Q3Graph.head (Q3ENode i) ∈ Q3Op2V i) ∨
      (Q3Graph.tail (Q3ENode i) ∈ Q3Op2V i ∧ Q3Graph.head (Q3ENode i) ∈ Q3Op1V i) := by decide
  have hQ3_f_cross : ∀ i : Fin 3,
      (Q3Graph.tail (Q3FNode i) ∈ Q3Op1V i ∧ Q3Graph.head (Q3FNode i) ∈ Q3Op2V i) ∨
      (Q3Graph.tail (Q3FNode i) ∈ Q3Op2V i ∧ Q3Graph.head (Q3FNode i) ∈ Q3Op1V i) := by decide
  refine ⟨sub, aux, ⟨{
    blue := Q3Blue
    comp_wc := hcomp_wc
    numNodes := 3
    eNode := Q3ENode
    fNode := Q3FNode
    stageV := Q3StageV
    op1V := Q3Op1V
    op2V := Q3Op2V
    nodeComp := fun _ => 0
    e_ne_f := hQ3_e_ne_f
    e_blue := hQ3_e_blue
    f_blue := hQ3_f_blue
    blue_unique := Q3_blue_unique
    stage_in_comp := fun _ _ _ => rfl
    stage_union := hQ3_stage_union
    stage_disj := hQ3_stage_disj
    op1_nonempty := hQ3_op1_ne
    op2_nonempty := hQ3_op2_ne
    e_cross := hQ3_e_cross
    f_cross := hQ3_f_cross
    red_no_cross := Q3_red_no_cross
    stage_blue_topo := Q3_stage_blue_topo
    stage_crossing_only := Q3_stage_crossing_only
    op1_blue_strict := Q3_op1_blue_strict
    op2_blue_strict := Q3_op2_blue_strict
    red_forest := Q3_red_forest
    op1_connected := fun i => by
      fin_cases i
      · exact hconn_of_red {0, 2, 6} ⟨0, by decide⟩ hredA (Q3_op1_red_closed 0)
      · exact hconn_s0
      · exact hconn_s1
    op2_connected := fun i => by
      fin_cases i
      · exact hconn_of_red {1} ⟨1, by decide⟩ (fun u hu v hv => by
          simp at hu hv; subst hu; subst hv; exact .refl) (Q3_op2_red_closed 0)
      · exact hconn_of_red {4, 5} ⟨4, by decide⟩ hredB (Q3_op2_red_closed 1)
      · exact hconn_of_red {3} ⟨3, by decide⟩ (fun u hu v hv => by
          simp at hu hv; subst hu; subst hv; exact .refl) (Q3_op2_red_closed 2)
    op1_is_stage_or_red := fun i => by
      fin_cases i
      · exact Or.inr hredA
      · exact Or.inl ⟨0, by decide, rfl⟩
      · exact Or.inl ⟨1, by decide, rfl⟩
    op2_is_stage_or_red := fun i => by
      fin_cases i
      · exact Or.inr (fun u hu v hv => by simp [Q3Op2V] at hu hv; subst hu; subst hv; exact .refl)
      · exact Or.inr hredB
      · exact Or.inr (fun u hu v hv => by simp [Q3Op2V] at hu hv; subst hu; subst hv; exact .refl)
    comp_is_stage_or_red := fun b => by
      fin_cases b; exact Or.inl ⟨2, by ext v; simp [Q3StageV, aux]⟩
    op1_red_closed := Q3_op1_red_closed
    op2_red_closed := Q3_op2_red_closed }⟩⟩

end Flow.Proofs
