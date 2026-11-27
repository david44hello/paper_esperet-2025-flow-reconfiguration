module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Flow.Defs.Literature
public import Flow.Proofs.Basic
public import Flow.Proofs.Frames
public import Mathlib.Tactic

@[expose] public section

/-!
# Proof of the Jaeger–Linial–Payan–Tarsi (1992) Well-Colouring Lemma (`JLPTWellColouring`)

Following Jaeger, Linial, Payan, and Tarsi (1992), *Group connectivity of graphs — a
nonhomogeneous analogue of nowhere-zero flow properties*, J. Combin. Theory Ser. B 56 (1992),
Lemma 3.2 (p. 175) and Lemma 3.3 (p. 177):
every truncated cubic `3`-edge-connected graph `Q ≅ Q⁺ - v₀` admits a well colouring `(blue, red)`
where `blue` is a spanning tree of `Q` and `Q / red` is `2`-constructible.
-/

namespace Flow.Proofs

open Flow

lemma spanningTree_card_edges {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : Multigraph V E) (B : Finset E)
    (hT : (Multigraph.Subgraph.ofEdges G Finset.univ B (fun _ => Finset.mem_univ _) (fun _ => Finset.mem_univ _)).IsSpanningTree) :
    B.card + 1 = Fintype.card V :=
  spanningTree_edges_card hT

lemma isSpanningTree_of_connected_card {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : Multigraph V E) (B : Finset E)
    (hconn : (Multigraph.Subgraph.ofEdges G Finset.univ B (fun _ => Finset.mem_univ _) (fun _ => Finset.mem_univ _)).Connected)
    (hcard : B.card + 1 = Fintype.card V) :
    (Multigraph.Subgraph.ofEdges G Finset.univ B (fun _ => Finset.mem_univ _) (fun _ => Finset.mem_univ _)).IsSpanningTree :=
  ⟨rfl, hconn, connected_edges_eq_verts_sub_one_isForest _ hconn (by change B.card + 1 = (Finset.univ : Finset V).card; rw [Finset.card_univ]; exact hcard)⟩

lemma disjoint_map_of_disjoint {α β : Type} [DecidableEq α] [DecidableEq β]
    {s t : Finset α} (f : α ↪ β) (h : Disjoint s t) : Disjoint (s.map f) (t.map f) := by
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx1
  obtain ⟨b, hb, hab⟩ := Finset.mem_map.mp hx2
  exact Finset.disjoint_left.mp h ha (f.injective hab ▸ hb)

lemma val_eq_of_some_eq {α : Type} {P : α → Prop} {a b : {x : α // P x}}
    (h : (some a : Option {x : α // P x}) = some b) : a.1 = b.1 := by
  cases h; rfl

lemma red_isForest_of_wellColouring {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (Qplus : Multigraph V E) (v₀ : V)
    (hcub : Qplus.IsCubic) (h3 : Qplus.IsEdgeConnected 3) (h4 : 4 ≤ Fintype.card V)
    (wc : WellColouring (Qplus.deleteVertex v₀)) :
    (Multigraph.Subgraph.ofEdges (Qplus.deleteVertex v₀) Finset.univ (Finset.univ \ wc.blue)
      (fun _ => Finset.mem_univ _) (fun _ => Finset.mem_univ _)).IsForest := by
  have hTC : (Qplus.deleteVertex v₀).IsTruncatedCubic3EC :=
    ⟨V, E, inferInstance, inferInstance, inferInstance, inferInstance, Qplus, v₀, hcub, h3, h4,
      ⟨{ toVert := Equiv.refl _, toEdge := Equiv.refl _, dir := fun _ => false,
         tail_eq := fun _ => rfl, head_eq := fun _ => rfl }⟩⟩
  exact (lem_3_9 (Qplus.deleteVertex v₀) hTC wc).2.2.2.1

-- Helpers for Parts 2-4 of JLPTWellColouring.lean (to be combined with part 1)

/-! ### Part 2: General `TwoConstruction` transport & `WellColouring` transport along `Iso` -/

/-- Transport a `TwoConstruction` along vertex/edge bijections preserving unordered endpoints. -/
def twoConstr_map {W₁ F₁ W₂ F₂ : Type} [DecidableEq W₁] [DecidableEq F₁] [DecidableEq W₂] [DecidableEq F₂]
    {M₁ : Multigraph W₁ F₁} {M₂ : Multigraph W₂ F₂}
    (eW : W₁ ≃ W₂) (eF : F₁ ≃ F₂)
    (hend : ∀ f : F₁,
      (M₂.tail (eF f) = eW (M₁.tail f) ∧ M₂.head (eF f) = eW (M₁.head f)) ∨
      (M₂.tail (eF f) = eW (M₁.head f) ∧ M₂.head (eF f) = eW (M₁.tail f))) :
    ∀ {W₀ : Finset W₁} {F₀ : Finset F₁}, TwoConstruction M₁ W₀ F₀ →
      TwoConstruction M₂ (W₀.map eW.toEmbedding) (F₀.map eF.toEmbedding)
  | _, _, .single w => by
    simpa [Finset.map_singleton, Finset.map_empty] using TwoConstruction.single (M := M₂) (eW w)
  | _, _, .join (W₁ := Wa) (W₂ := Wb) (F₁ := Fa) (F₂ := Fb) left right e f hdisjW hdisjF he_ne_f he1 he2 hf1 hf2 he_cr hf_cr => by
    have hW_eq : (Wa ∪ Wb).map eW.toEmbedding = Wa.map eW.toEmbedding ∪ Wb.map eW.toEmbedding :=
      Finset.map_union _ _
    have hF_eq : (insert e (insert f (Fa ∪ Fb))).map eF.toEmbedding =
        insert (eF e) (insert (eF f) (Fa.map eF.toEmbedding ∪ Fb.map eF.toEmbedding)) := by
      simp [Finset.map_insert, Finset.map_union]
    rw [hW_eq, hF_eq]
    refine TwoConstruction.join
      (twoConstr_map eW eF hend left) (twoConstr_map eW eF hend right)
      (eF e) (eF f)
      (disjoint_map_of_disjoint _ hdisjW)
      (disjoint_map_of_disjoint _ hdisjF)
      (fun h => he_ne_f (eF.injective h))
      (by simp [he1]) (by simp [he2])
      (by simp [hf1]) (by simp [hf2])
      ?_ ?_
    · rcases hend e with ⟨ht, hh⟩ | ⟨ht, hh⟩ <;> rcases he_cr with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; exact ⟨ht ▸ Finset.mem_map_of_mem _ h1, hh ▸ Finset.mem_map_of_mem _ h2⟩
      · right; exact ⟨ht ▸ Finset.mem_map_of_mem _ h1, hh ▸ Finset.mem_map_of_mem _ h2⟩
      · right; exact ⟨ht ▸ Finset.mem_map_of_mem _ h2, hh ▸ Finset.mem_map_of_mem _ h1⟩
      · left; exact ⟨ht ▸ Finset.mem_map_of_mem _ h2, hh ▸ Finset.mem_map_of_mem _ h1⟩
    · rcases hend f with ⟨ht, hh⟩ | ⟨ht, hh⟩ <;> rcases hf_cr with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; exact ⟨ht ▸ Finset.mem_map_of_mem _ h1, hh ▸ Finset.mem_map_of_mem _ h2⟩
      · right; exact ⟨ht ▸ Finset.mem_map_of_mem _ h1, hh ▸ Finset.mem_map_of_mem _ h2⟩
      · right; exact ⟨ht ▸ Finset.mem_map_of_mem _ h2, hh ▸ Finset.mem_map_of_mem _ h1⟩
      · left; exact ⟨ht ▸ Finset.mem_map_of_mem _ h2, hh ▸ Finset.mem_map_of_mem _ h1⟩

/-- Pull back a `WellColouring` across a `Multigraph.Iso`. -/
noncomputable def wellColouring_of_iso {V₁ E₁ V₂ E₂ : Type}
    [Fintype V₁] [Fintype E₁] [DecidableEq V₁] [DecidableEq E₁]
    [Fintype V₂] [Fintype E₂] [DecidableEq V₂] [DecidableEq E₂]
    {Q₁ : Multigraph V₁ E₁} {Q₂ : Multigraph V₂ E₂}
    (iso : Multigraph.Iso Q₁ Q₂) (wc₂ : WellColouring Q₂) : WellColouring Q₁ := by
  classical
  let blue₁ : Finset E₁ := Finset.univ.filter (fun e => iso.toEdge e ∈ wc₂.blue)
  have hblue_iff : ∀ e : E₁, e ∈ blue₁ ↔ iso.toEdge e ∈ wc₂.blue := fun e => by
    simp [blue₁]
  have hend_fwd : ∀ e : E₁,
      (Q₂.tail (iso.toEdge e) = iso.toVert (Q₁.tail e) ∧ Q₂.head (iso.toEdge e) = iso.toVert (Q₁.head e)) ∨
      (Q₂.tail (iso.toEdge e) = iso.toVert (Q₁.head e) ∧ Q₂.head (iso.toEdge e) = iso.toVert (Q₁.tail e)) := by
    intro e
    have ht := iso.tail_eq e; have hh := iso.head_eq e
    cases hd : iso.dir e <;> simp [hd] at ht hh
    · exact Or.inl ⟨ht, hh⟩
    · exact Or.inr ⟨ht, hh⟩
  -- 1. blue₁ is a spanning tree of Q₁
  let T₁ := Multigraph.Subgraph.ofEdges Q₁ Finset.univ blue₁ (fun _ => Finset.mem_univ _) (fun _ => Finset.mem_univ _)
  let T₂ := Multigraph.Subgraph.ofEdges Q₂ Finset.univ wc₂.blue (fun _ => Finset.mem_univ _) (fun _ => Finset.mem_univ _)
  have hT₁_conn : T₁.Connected := by
    refine ⟨?_, ?_⟩
    · obtain ⟨v₂, _⟩ := wc₂.blue_tree.2.1.1
      exact ⟨iso.toVert.symm v₂, Finset.mem_univ _⟩
    · intro u _ v _
      have h2 := wc₂.blue_tree.2.1.2 (iso.toVert u) (Finset.mem_univ _) (iso.toVert v) (Finset.mem_univ _)
      have hgo : ∀ a b : V₂, Relation.ReflTransGen T₂.Adj a b →
          Relation.ReflTransGen T₁.Adj (iso.toVert.symm a) (iso.toVert.symm b) := by
        intro a b hab
        induction hab with
        | refl => exact .refl
        | tail _ hs ih =>
          rcases hs with ⟨e₂, he₂, hinc⟩
          let e₁ := iso.toEdge.symm e₂
          have he₂' : e₂ ∈ wc₂.blue := he₂
          have he₁ : e₁ ∈ blue₁ := (hblue_iff e₁).mpr (by simpa [e₁] using he₂')
          have hfe := hend_fwd e₁
          rw [Equiv.apply_symm_apply] at hfe
          refine ih.tail ⟨e₁, he₁, ?_⟩
          rcases hfe with ⟨ht, hh⟩ | ⟨ht, hh⟩ <;> rcases hinc with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · left; exact ⟨by rw [← h1, ht, Equiv.symm_apply_apply], by rw [← h2, hh, Equiv.symm_apply_apply]⟩
          · right; exact ⟨by rw [← h1, ht, Equiv.symm_apply_apply], by rw [← h2, hh, Equiv.symm_apply_apply]⟩
          · right; exact ⟨by rw [← h2, hh, Equiv.symm_apply_apply], by rw [← h1, ht, Equiv.symm_apply_apply]⟩
          · left; exact ⟨by rw [← h2, hh, Equiv.symm_apply_apply], by rw [← h1, ht, Equiv.symm_apply_apply]⟩
      simpa using hgo (iso.toVert u) (iso.toVert v) h2
  have hT₁_card : blue₁.card + 1 = Fintype.card V₁ := by
    have hcard_b : blue₁.card = wc₂.blue.card := by
      refine Finset.card_bij (fun e _ => iso.toEdge e) (fun e he => (hblue_iff e).mp he)
        (fun _ _ _ _ h => iso.toEdge.injective h)
        (fun e₂ he₂ => ⟨iso.toEdge.symm e₂, (hblue_iff _).mpr (by simpa using he₂), by simp⟩)
    rw [hcard_b, Fintype.card_congr iso.toVert]
    exact spanningTree_card_edges Q₂ wc₂.blue wc₂.blue_tree
  have hT₁_tree : T₁.IsSpanningTree := isSpanningTree_of_connected_card Q₁ blue₁ hT₁_conn hT₁_card
  -- 2. Red quotient equivalence
  have hred_iff : ∀ u v : V₁,
      Relation.ReflTransGen (redAdj Q₁ blue₁) u v ↔
      Relation.ReflTransGen (redAdj Q₂ wc₂.blue) (iso.toVert u) (iso.toVert v) := by
    intro u v
    constructor
    · intro h
      induction h with
      | refl => exact .refl
      | tail _ hs ih =>
        rcases hs with ⟨e₁, he₁, hinc⟩
        have he₂ : iso.toEdge e₁ ∉ wc₂.blue := fun hm => he₁ ((hblue_iff e₁).mpr hm)
        refine ih.tail ⟨iso.toEdge e₁, he₂, ?_⟩
        rcases hend_fwd e₁ with ⟨ht, hh⟩ | ⟨ht, hh⟩ <;> rcases hinc with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨by rw [ht, h1], by rw [hh, h2]⟩
        · exact Or.inr ⟨by rw [ht, h1], by rw [hh, h2]⟩
        · exact Or.inr ⟨by rw [ht, h2], by rw [hh, h1]⟩
        · exact Or.inl ⟨by rw [ht, h2], by rw [hh, h1]⟩
    · intro h
      have hgo : ∀ a b : V₂, Relation.ReflTransGen (redAdj Q₂ wc₂.blue) a b →
          Relation.ReflTransGen (redAdj Q₁ blue₁) (iso.toVert.symm a) (iso.toVert.symm b) := by
        intro a b hab
        induction hab with
        | refl => exact .refl
        | tail _ hs ih =>
          rcases hs with ⟨e₂, he₂, hinc⟩
          let e₁ := iso.toEdge.symm e₂
          have he₁ : e₁ ∉ blue₁ := fun hm => he₂ (by simpa [e₁] using (hblue_iff e₁).mp hm)
          have hfe := hend_fwd e₁; rw [Equiv.apply_symm_apply] at hfe
          refine ih.tail ⟨e₁, he₁, ?_⟩
          rcases hfe with ⟨ht, hh⟩ | ⟨ht, hh⟩ <;> rcases hinc with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inl ⟨by rw [← h1, ht, Equiv.symm_apply_apply], by rw [← h2, hh, Equiv.symm_apply_apply]⟩
          · exact Or.inr ⟨by rw [← h1, ht, Equiv.symm_apply_apply], by rw [← h2, hh, Equiv.symm_apply_apply]⟩
          · exact Or.inr ⟨by rw [← h2, hh, Equiv.symm_apply_apply], by rw [← h1, ht, Equiv.symm_apply_apply]⟩
          · exact Or.inl ⟨by rw [← h2, hh, Equiv.symm_apply_apply], by rw [← h1, ht, Equiv.symm_apply_apply]⟩
      simpa using hgo (iso.toVert u) (iso.toVert v) h
  let qEq : Quotient (redSetoid Q₂ wc₂.blue) ≃ Quotient (redSetoid Q₁ blue₁) :=
    { toFun := Quotient.lift (fun v₂ => Quotient.mk (redSetoid Q₁ blue₁) (iso.toVert.symm v₂)) (fun a b hab =>
        Quotient.sound ((hred_iff _ _).mpr (by
          have h' : Relation.ReflTransGen (redAdj Q₂ wc₂.blue) a b := hab
          simpa using h')))
      invFun := Quotient.lift (fun v₁ => Quotient.mk (redSetoid Q₂ wc₂.blue) (iso.toVert v₁)) (fun a b hab =>
        Quotient.sound ((hred_iff a b).mp (hab : Relation.ReflTransGen (redAdj Q₁ blue₁) a b)))
      left_inv := fun q => by obtain ⟨v, rfl⟩ := Quotient.exists_rep q; simp
      right_inv := fun q => by obtain ⟨v, rfl⟩ := Quotient.exists_rep q; simp }
  let eEq : {e : E₂ // e ∈ wc₂.blue} ≃ {e : E₁ // e ∈ blue₁} :=
    { toFun := fun e => ⟨iso.toEdge.symm e.1, (hblue_iff _).mpr (by simpa using e.2)⟩
      invFun := fun e => ⟨iso.toEdge e.1, (hblue_iff _).mp e.2⟩
      left_inv := fun e => Subtype.ext (by simp)
      right_inv := fun e => Subtype.ext (by simp) }
  have htc1 : TwoConstruction (redQuotient Q₁ blue₁)
      (Finset.univ.map qEq.toEmbedding) (Finset.univ.map eEq.toEmbedding) :=
    twoConstr_map qEq eEq (fun e₂ => by
      have hfe := hend_fwd (iso.toEdge.symm e₂.1)
      rw [Equiv.apply_symm_apply] at hfe
      dsimp only [redQuotient, qEq, eEq]
      rcases hfe with ⟨ht, hh⟩ | ⟨ht, hh⟩
      · left; exact ⟨by rw [ht]; simp, by rw [hh]; simp⟩
      · right; exact ⟨by rw [hh]; simp, by rw [ht]; simp⟩) wc₂.twoConstr
  have hW_univ : Finset.univ.map qEq.toEmbedding = Finset.univ := by
    ext q; simp only [Finset.mem_map, Finset.mem_univ, true_and, iff_true]
    exact ⟨qEq.symm q, by simp⟩
  have hF_univ : Finset.univ.map eEq.toEmbedding = Finset.univ := by
    ext e; simp only [Finset.mem_map, Finset.mem_univ, true_and, iff_true]
    exact ⟨eEq.symm e, by simp⟩
  rw [hW_univ, hF_univ] at htc1
  exact { blue := blue₁, blue_tree := hT₁_tree, twoConstr := htc1 }

-- Helpers for Parts 3-4 of JLPTWellColouring.lean

/-! ### Part 3: Structural facts on cubic `3`-edge-connected graphs & base case `|V| = 4` -/

/-- Handshake lemma for multigraphs: `∑ v, G.deg v = 2 * |E|`. -/
lemma sum_deg_eq_two_mul_card_edges {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : Multigraph V E) :
    ∑ v : V, G.deg v = 2 * Fintype.card E := by
  unfold Multigraph.deg
  rw [Finset.sum_add_distrib]
  have h1 : ∑ v : V, (Finset.univ.filter (fun e : E => G.tail e = v)).card = Fintype.card E := by
    rw [← Finset.card_biUnion]
    · have hun : Finset.univ.biUnion (fun v : V => Finset.univ.filter (fun e : E => G.tail e = v)) = Finset.univ := by
        ext e; simp
      rw [hun, Finset.card_univ]
    · intro a _ b _ hab; dsimp [Function.onFun]; rw [Finset.disjoint_left]
      intro e ha hb; exact hab ((Finset.mem_filter.mp ha).2.symm.trans (Finset.mem_filter.mp hb).2)
  have h2 : ∑ v : V, (Finset.univ.filter (fun e : E => G.head e = v)).card = Fintype.card E := by
    rw [← Finset.card_biUnion]
    · have hun : Finset.univ.biUnion (fun v : V => Finset.univ.filter (fun e : E => G.head e = v)) = Finset.univ := by
        ext e; simp
      rw [hun, Finset.card_univ]
    · intro a _ b _ hab; dsimp [Function.onFun]; rw [Finset.disjoint_left]
      intro e ha hb; exact hab ((Finset.mem_filter.mp ha).2.symm.trans (Finset.mem_filter.mp hb).2)
  rw [h1, h2]; omega

/-- In a cubic multigraph, `2 * |E| = 3 * |V|`. -/
lemma cubic_two_mul_edges {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : Multigraph V E) (hcub : G.IsCubic) :
    2 * Fintype.card E = 3 * Fintype.card V := by
  have h := sum_deg_eq_two_mul_card_edges G
  have h3 : ∑ v : V, G.deg v = 3 * Fintype.card V := by
    calc ∑ v : V, G.deg v = ∑ _v : V, 3 := Finset.sum_congr rfl fun v _ => hcub v
    _ = Fintype.card V * 3 := by simp
    _ = 3 * Fintype.card V := Nat.mul_comm _ _
  omega

/-- Cut-degree identity: for any subset `S`,
`∑ v ∈ S, G.deg v = (G.cutEdges S).card + 2 * |{e : tail e ∈ S ∧ head e ∈ S}|`. -/
lemma sum_deg_eq_cut_add_two_internal {V E : Type} [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : Multigraph V E) (S : Finset V) :
    ∑ v ∈ S, G.deg v =
      (G.cutEdges S).card +
      2 * (Finset.univ.filter (fun e : E => G.tail e ∈ S ∧ G.head e ∈ S)).card := by
  unfold Multigraph.deg
  rw [Finset.sum_add_distrib]
  have ht : ∑ v ∈ S, (Finset.univ.filter (fun e : E => G.tail e = v)).card =
      (Finset.univ.filter (fun e : E => G.tail e ∈ S)).card := by
    rw [← Finset.card_biUnion]
    · congr 1; ext e; simp
    · intro a _ b _ hab; dsimp [Function.onFun]; rw [Finset.disjoint_left]
      intro e ha hb; exact hab ((Finset.mem_filter.mp ha).2.symm.trans (Finset.mem_filter.mp hb).2)
  have hh : ∑ v ∈ S, (Finset.univ.filter (fun e : E => G.head e = v)).card =
      (Finset.univ.filter (fun e : E => G.head e ∈ S)).card := by
    rw [← Finset.card_biUnion]
    · congr 1; ext e; simp
    · intro a _ b _ hab; dsimp [Function.onFun]; rw [Finset.disjoint_left]
      intro e ha hb; exact hab ((Finset.mem_filter.mp ha).2.symm.trans (Finset.mem_filter.mp hb).2)
  rw [ht, hh]
  let A1 := Finset.univ.filter (fun e : E => G.tail e ∈ S ∧ G.head e ∉ S)
  let A2 := Finset.univ.filter (fun e : E => G.tail e ∉ S ∧ G.head e ∈ S)
  let B := Finset.univ.filter (fun e : E => G.tail e ∈ S ∧ G.head e ∈ S)
  have h1 : Finset.univ.filter (fun e : E => G.tail e ∈ S) = A1 ∪ B := by
    ext e; simp only [A1, B, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases h : G.head e ∈ S <;> simp [h]
  have h2 : Finset.univ.filter (fun e : E => G.head e ∈ S) = A2 ∪ B := by
    ext e; simp only [A2, B, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases h : G.tail e ∈ S <;> simp [h]
  have hcut : G.cutEdges S = A1 ∪ A2 := by
    ext e; simp only [Multigraph.cutEdges, A1, A2, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  have hd1 : Disjoint A1 B := by
    rw [Finset.disjoint_left]; intro e h1 h2; exact (Finset.mem_filter.mp h1).2.2 (Finset.mem_filter.mp h2).2.2
  have hd2 : Disjoint A2 B := by
    rw [Finset.disjoint_left]; intro e h1 h2; exact (Finset.mem_filter.mp h1).2.1 (Finset.mem_filter.mp h2).2.1
  have hd12 : Disjoint A1 A2 := by
    rw [Finset.disjoint_left]; intro e h1 h2; exact (Finset.mem_filter.mp h2).2.1 (Finset.mem_filter.mp h1).2.1
  rw [h1, h2, hcut, Finset.card_union_of_disjoint hd1, Finset.card_union_of_disjoint hd2,
      Finset.card_union_of_disjoint hd12]
  dsimp only [B]
  omega

/-- Every cubic `3`-edge-connected multigraph on `≥ 4` vertices is simple (loopless, no parallel edges). -/
lemma cubic_3ec_isSimple {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : Multigraph V E) (hcub : G.IsCubic) (h3 : G.IsEdgeConnected 3) (h4 : 4 ≤ Fintype.card V) :
    G.IsSimple := by
  have hll : G.IsLoopless := by
    intro e hlp
    let v := G.tail e
    have hS : ({v} : Finset V).Nonempty := Finset.singleton_nonempty v
    have hSc : (Finset.univ \ ({v} : Finset V)).Nonempty := by
      rw [← Finset.card_pos, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Finset.card_singleton]
      omega
    have hcut3 := h3 {v} hS hSc
    have hdeg := sum_deg_eq_cut_add_two_internal G {v}
    rw [Finset.sum_singleton, hcub v] at hdeg
    have hpos : 1 ≤ (Finset.univ.filter (fun e' : E => G.tail e' ∈ ({v} : Finset V) ∧ G.head e' ∈ ({v} : Finset V))).card :=
      Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_singleton_self _, by simp [v, hlp]⟩⟩
    omega
  refine ⟨hll, fun e₁ e₂ hsame => ?_⟩
  by_contra hne
  let u := G.tail e₁
  let v := G.head e₁
  have huv : u ≠ v := hll e₁
  let S : Finset V := {u, v}
  have hScard : S.card = 2 := Finset.card_pair huv
  have hSne : S.Nonempty := ⟨u, Finset.mem_insert_self _ _⟩
  have hScne : (Finset.univ \ S).Nonempty := by
    rw [← Finset.card_pos, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, hScard]; omega
  have hcut3 := h3 S hSne hScne
  have hdeg := sum_deg_eq_cut_add_two_internal G S
  rw [Finset.sum_pair huv, hcub u, hcub v] at hdeg
  have he1_in : e₁ ∈ Finset.univ.filter (fun e : E => G.tail e ∈ S ∧ G.head e ∈ S) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_insert_self _ _, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩
  have he2_in : e₂ ∈ Finset.univ.filter (fun e : E => G.tail e ∈ S ∧ G.head e ∈ S) := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rcases hsame with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨h1.symm ▸ Finset.mem_insert_self _ _, h2.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩
    · exact ⟨h2.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _), h1.symm ▸ Finset.mem_insert_self _ _⟩
  have hpair_sub : ({e₁, e₂} : Finset E) ⊆ Finset.univ.filter (fun e : E => G.tail e ∈ S ∧ G.head e ∈ S) := by
    intro e he; rw [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl; exact he1_in; exact he2_in
  have hge2 : 2 ≤ (Finset.univ.filter (fun e : E => G.tail e ∈ S ∧ G.head e ∈ S)).card := by
    rw [← Finset.card_pair hne]; exact Finset.card_le_card hpair_sub
  omega

/-- Number of edges of `Qplus.deleteVertex v₀` when `Qplus` is cubic and loopless. -/
lemma card_edges_deleteVertex_cubic {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : Multigraph V E) (hcub : G.IsCubic) (hll : G.IsLoopless) (v₀ : V) :
    Fintype.card {e : E // G.tail e ≠ v₀ ∧ G.head e ≠ v₀} + 3 = Fintype.card E := by
  let inc := Finset.univ.filter (fun e : E => G.tail e = v₀ ∨ G.head e = v₀)
  have hinc_card : inc.card = 3 := by
    have hdisj : Disjoint (Finset.univ.filter (fun e : E => G.tail e = v₀))
        (Finset.univ.filter (fun e : E => G.head e = v₀)) := by
      rw [Finset.disjoint_left]; intro e ht hh
      exact hll e ((Finset.mem_filter.mp ht).2.trans (Finset.mem_filter.mp hh).2.symm)
    have hun : inc = Finset.univ.filter (fun e : E => G.tail e = v₀) ∪
        Finset.univ.filter (fun e : E => G.head e = v₀) := by
      ext e; simp [inc]
    rw [hun, Finset.card_union_of_disjoint hdisj]
    exact hcub v₀
  have hcompl : Fintype.card {e : E // G.tail e ≠ v₀ ∧ G.head e ≠ v₀} =
      (Finset.univ \ inc).card := by
    rw [Fintype.card_subtype]
    congr 1; ext e; simp [inc, not_or]
  rw [hcompl, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, hinc_card]
  have hle : inc.card ≤ Fintype.card E := (Finset.card_le_univ inc)
  omega

/-- Base case `|V| = 4`: `Qplus.deleteVertex v₀ ≅ K_3` admits a `WellColouring`. -/
lemma wellColouring_base_four {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (Qplus : Multigraph V E) (v₀ : V)
    (hcub : Qplus.IsCubic) (h3 : Qplus.IsEdgeConnected 3) (hcard4 : Fintype.card V = 4) :
    Nonempty (WellColouring (Qplus.deleteVertex v₀)) := by
  classical
  let Q := Qplus.deleteVertex v₀
  have hsimp := cubic_3ec_isSimple Qplus hcub h3 (by omega)
  have h2E := cubic_two_mul_edges Qplus hcub
  have hEQ := card_edges_deleteVertex_cubic Qplus hcub hsimp.1 v₀
  have hVQ : Fintype.card {u : V // u ≠ v₀} = 3 := by
    rw [Fintype.card_subtype_compl, show Fintype.card {u : V // u = v₀} = 1 from Fintype.card_unique, hcard4]
  have hEQ3 : Fintype.card {e : E // Qplus.tail e ≠ v₀ ∧ Qplus.head e ≠ v₀} = 3 := by omega
  have hQ_ll : Q.IsLoopless := fun e h => hsimp.1 e.1 (congrArg Subtype.val h)
  have hQ_simp : ∀ e₁ e₂ : {e : E // Qplus.tail e ≠ v₀ ∧ Qplus.head e ≠ v₀}, Q.SameEnds e₁ e₂ → e₁ = e₂ := by
    intro e₁ e₂ hs
    refine Subtype.ext (hsimp.2 e₁.1 e₂.1 ?_)
    rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨congrArg Subtype.val h1, congrArg Subtype.val h2⟩
    · exact Or.inr ⟨congrArg Subtype.val h1, congrArg Subtype.val h2⟩
  -- Pick any single edge e_red; set blue = univ.erase e_red (2 edges)!
  obtain ⟨e_red⟩ : Nonempty {e : E // Qplus.tail e ≠ v₀ ∧ Qplus.head e ≠ v₀} :=
    Fintype.card_pos_iff.mp (by omega)
  let blue := (Finset.univ : Finset {e : E // Qplus.tail e ≠ v₀ ∧ Qplus.head e ≠ v₀}).erase e_red
  have hblue_card : blue.card = 2 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hEQ3]
  obtain ⟨b₁, b₂, hb12, hblue_eq⟩ := Finset.card_eq_two.mp hblue_card
  have hb1_ne : b₁ ≠ e_red := by
    have hmem : b₁ ∈ blue := hblue_eq ▸ Finset.mem_insert_self _ _
    exact Finset.ne_of_mem_erase hmem
  have hb2_ne : b₂ ≠ e_red := by
    have hmem : b₂ ∈ blue := hblue_eq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    exact Finset.ne_of_mem_erase hmem
  -- The 3 vertices of Q are tail e_red, head e_red, and a unique third vertex w!
  let u := Q.tail e_red
  let v := Q.head e_red
  have huv : u ≠ v := hQ_ll e_red
  have hw_ex : (Finset.univ \ ({u, v} : Finset {x : V // x ≠ v₀})).card = 1 := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, hVQ, Finset.card_pair huv]
  obtain ⟨w, hw_eq⟩ := Finset.card_eq_one.mp hw_ex
  have hwu : w ≠ u := fun h => by
    have hm : w ∈ Finset.univ \ ({u, v} : Finset {x : V // x ≠ v₀}) := hw_eq ▸ Finset.mem_singleton_self _
    exact (Finset.mem_sdiff.mp hm).2 (h ▸ Finset.mem_insert_self _ _)
  have hwv : w ≠ v := fun h => by
    have hm : w ∈ Finset.univ \ ({u, v} : Finset {x : V // x ≠ v₀}) := hw_eq ▸ Finset.mem_singleton_self _
    exact (Finset.mem_sdiff.mp hm).2 (h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hall_v : ∀ x : {x : V // x ≠ v₀}, x = u ∨ x = v ∨ x = w := by
    intro x
    by_cases h1 : x = u; · exact Or.inl h1
    by_cases h2 : x = v; · exact Or.inr (Or.inl h2)
    right; right
    have hm : x ∈ Finset.univ \ ({u, v} : Finset {x : V // x ≠ v₀}) :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by simp [h1, h2]⟩
    rw [hw_eq, Finset.mem_singleton] at hm; exact hm
  -- Each of b₁, b₂ has w as one endpoint and {u, v} as the other (since neither has SameEnds with e_red)!
  have hb_ends : ∀ b : {e : E // Qplus.tail e ≠ v₀ ∧ Qplus.head e ≠ v₀}, b ≠ e_red →
      (Q.tail b = w ∧ (Q.head b = u ∨ Q.head b = v)) ∨
      (Q.head b = w ∧ (Q.tail b = u ∨ Q.tail b = v)) := by
    intro b hne
    have hll_b := hQ_ll b
    have hns : ¬ Q.SameEnds b e_red := fun hs => hne (hQ_simp b e_red hs)
    rcases hall_v (Q.tail b) with ht | ht | ht <;> rcases hall_v (Q.head b) with hh | hh | hh
    · exact absurd (ht.trans hh.symm) hll_b
    · exact absurd (Or.inl ⟨ht, hh⟩) hns
    · exact Or.inr ⟨hh, Or.inl ht⟩
    · exact absurd (Or.inr ⟨ht, hh⟩) hns
    · exact absurd (ht.trans hh.symm) hll_b
    · exact Or.inr ⟨hh, Or.inr ht⟩
    · exact Or.inl ⟨ht, Or.inl hh⟩
    · exact Or.inl ⟨ht, Or.inr hh⟩
    · exact absurd (ht.trans hh.symm) hll_b
  -- Moreover b₁ and b₂ connect w to BOTH u and v (since ¬ SameEnds b₁ b₂)!
  let T := Multigraph.Subgraph.ofEdges Q Finset.univ blue (fun _ => Finset.mem_univ _) (fun _ => Finset.mem_univ _)
  have hb1_mem : b₁ ∈ blue := hblue_eq ▸ Finset.mem_insert_self _ _
  have hb2_mem : b₂ ∈ blue := hblue_eq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hreach_w : ∀ x : {x : V // x ≠ v₀}, Relation.ReflTransGen T.Adj w x := by
    have hns12 : ¬ Q.SameEnds b₁ b₂ := fun hs => hb12 (hQ_simp b₁ b₂ hs)
    have hwu_reach : Relation.ReflTransGen T.Adj w u := by
      rcases hb_ends b₁ hb1_ne with ⟨ht1, hu1 | hv1⟩ | ⟨hh1, hu1 | hv1⟩
      · exact Relation.ReflTransGen.single ⟨b₁, hb1_mem, Or.inl ⟨ht1, hu1⟩⟩
      · rcases hb_ends b₂ hb2_ne with ⟨ht2, hu2 | hv2⟩ | ⟨hh2, hu2 | hv2⟩
        · exact Relation.ReflTransGen.single ⟨b₂, hb2_mem, Or.inl ⟨ht2, hu2⟩⟩
        · exact absurd (Or.inl ⟨ht1.trans ht2.symm, hv1.trans hv2.symm⟩) hns12
        · exact Relation.ReflTransGen.single ⟨b₂, hb2_mem, Or.inr ⟨hu2, hh2⟩⟩
        · exact absurd (Or.inr ⟨ht1.trans hh2.symm, hv1.trans hv2.symm⟩) hns12
      · exact Relation.ReflTransGen.single ⟨b₁, hb1_mem, Or.inr ⟨hu1, hh1⟩⟩
      · rcases hb_ends b₂ hb2_ne with ⟨ht2, hu2 | hv2⟩ | ⟨hh2, hu2 | hv2⟩
        · exact Relation.ReflTransGen.single ⟨b₂, hb2_mem, Or.inl ⟨ht2, hu2⟩⟩
        · exact absurd (Or.inr ⟨hv1.trans hv2.symm, hh1.trans ht2.symm⟩) hns12
        · exact Relation.ReflTransGen.single ⟨b₂, hb2_mem, Or.inr ⟨hu2, hh2⟩⟩
        · exact absurd (Or.inl ⟨hv1.trans hv2.symm, hh1.trans hh2.symm⟩) hns12
    have hwv_reach : Relation.ReflTransGen T.Adj w v := by
      rcases hb_ends b₁ hb1_ne with ⟨ht1, hu1 | hv1⟩ | ⟨hh1, hu1 | hv1⟩
      · rcases hb_ends b₂ hb2_ne with ⟨ht2, hu2 | hv2⟩ | ⟨hh2, hu2 | hv2⟩
        · exact absurd (Or.inl ⟨ht1.trans ht2.symm, hu1.trans hu2.symm⟩) hns12
        · exact Relation.ReflTransGen.single ⟨b₂, hb2_mem, Or.inl ⟨ht2, hv2⟩⟩
        · exact absurd (Or.inr ⟨ht1.trans hh2.symm, hu1.trans hu2.symm⟩) hns12
        · exact Relation.ReflTransGen.single ⟨b₂, hb2_mem, Or.inr ⟨hv2, hh2⟩⟩
      · exact Relation.ReflTransGen.single ⟨b₁, hb1_mem, Or.inl ⟨ht1, hv1⟩⟩
      · rcases hb_ends b₂ hb2_ne with ⟨ht2, hu2 | hv2⟩ | ⟨hh2, hu2 | hv2⟩
        · exact absurd (Or.inr ⟨hu1.trans hu2.symm, hh1.trans ht2.symm⟩) hns12
        · exact Relation.ReflTransGen.single ⟨b₂, hb2_mem, Or.inl ⟨ht2, hv2⟩⟩
        · exact absurd (Or.inl ⟨hu1.trans hu2.symm, hh1.trans hh2.symm⟩) hns12
        · exact Relation.ReflTransGen.single ⟨b₂, hb2_mem, Or.inr ⟨hv2, hh2⟩⟩
      · exact Relation.ReflTransGen.single ⟨b₁, hb1_mem, Or.inr ⟨hv1, hh1⟩⟩
    intro x; rcases hall_v x with rfl | rfl | rfl
    · exact hwu_reach
    · exact hwv_reach
    · exact .refl
  have hT_conn : T.Connected := by
    refine ⟨⟨w, Finset.mem_univ _⟩, fun a _ b _ => ?_⟩
    have hsym : ∀ y, Relation.ReflTransGen T.Adj w y → Relation.ReflTransGen T.Adj y w := fun y h => by
      induction h with
      | refl => exact .refl
      | tail _ hs ih =>
        rcases hs with ⟨e, he, h1 | h1⟩
        · exact Relation.ReflTransGen.head ⟨e, he, Or.inr h1⟩ ih
        · exact Relation.ReflTransGen.head ⟨e, he, Or.inl h1⟩ ih
    exact (hsym a (hreach_w a)).trans (hreach_w b)
  have hT_tree : T.IsSpanningTree := isSpanningTree_of_connected_card Q blue hT_conn (by omega)
  -- Red quotient has exactly 2 vertices: ⟦u⟧ (= ⟦v⟧) and ⟦w⟧!
  let c₁ : Quotient (redSetoid Q blue) := Quotient.mk _ u
  let c₂ : Quotient (redSetoid Q blue) := Quotient.mk _ w
  have huv_red : Quotient.mk (redSetoid Q blue) v = c₁ :=
    Quotient.sound (Relation.ReflTransGen.single ⟨e_red, Finset.notMem_erase _ _, Or.inr ⟨rfl, rfl⟩⟩)
  have hc12 : c₁ ≠ c₂ := by
    intro heq
    have hrel : Relation.ReflTransGen (redAdj Q blue) u w := Quotient.exact heq
    have hstay : ∀ x, Relation.ReflTransGen (redAdj Q blue) u x → x = u ∨ x = v := by
      intro x hx
      induction hx with
      | refl => exact Or.inl rfl
      | tail _ hs ih =>
        rcases hs with ⟨e, heR, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
        · have he_eq : e = e_red := by
            by_contra hne; exact heR (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩)
          subst he_eq; exact Or.inr h2.symm
        · have he_eq : e = e_red := by
            by_contra hne; exact heR (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩)
          subst he_eq; exact Or.inl h1.symm
    rcases hstay w hrel with h | h
    · exact hwu h
    · exact hwv h
  have hW_eq : (Finset.univ : Finset (Quotient (redSetoid Q blue))) = {c₁} ∪ {c₂} := by
    ext q; simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_singleton, true_iff]
    obtain ⟨x, rfl⟩ := Quotient.exists_rep q
    rcases hall_v x with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inl huv_red
    · exact Or.inr rfl
  have hF_eq : (Finset.univ : Finset {e // e ∈ blue}) =
      insert ⟨b₁, hb1_mem⟩ (insert ⟨b₂, hb2_mem⟩ (∅ ∪ ∅)) := by
    ext ⟨e, he⟩
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.union_idempotent, Finset.notMem_empty,
      or_false, Subtype.mk.injEq, true_iff]
    rw [hblue_eq, Finset.mem_insert, Finset.mem_singleton] at he; exact he
  have hcross : ∀ (b : {e // e ∈ blue}), b.1 ≠ e_red →
      ((redQuotient Q blue).tail b ∈ ({c₁} : Finset _) ∧ (redQuotient Q blue).head b ∈ ({c₂} : Finset _)) ∨
      ((redQuotient Q blue).tail b ∈ ({c₂} : Finset _) ∧ (redQuotient Q blue).head b ∈ ({c₁} : Finset _)) := by
    intro b hne
    dsimp only [redQuotient]
    rcases hb_ends b.1 hne with ⟨ht, hu | hv⟩ | ⟨hh, hu | hv⟩
    · right; rw [ht, hu]; exact ⟨Finset.mem_singleton_self _, Finset.mem_singleton_self _⟩
    · right; rw [ht, hv]; exact ⟨Finset.mem_singleton_self _, by simp [huv_red]⟩
    · left; rw [hu, hh]; exact ⟨Finset.mem_singleton_self _, Finset.mem_singleton_self _⟩
    · left; rw [hv, hh]; exact ⟨by simp [huv_red], Finset.mem_singleton_self _⟩
  refine ⟨{ blue := blue, blue_tree := hT_tree, twoConstr := ?_ }⟩
  rw [hW_eq, hF_eq]
  exact TwoConstruction.join (TwoConstruction.single c₁) (TwoConstruction.single c₂)
    ⟨b₁, hb1_mem⟩ ⟨b₂, hb2_mem⟩
    (Finset.disjoint_singleton.mpr hc12) (Finset.disjoint_empty_left _)
    (fun h => hb12 (congrArg Subtype.val h))
    (Finset.notMem_empty _) (Finset.notMem_empty _)
    (Finset.notMem_empty _) (Finset.notMem_empty _)
    (hcross ⟨b₁, hb1_mem⟩ hb1_ne) (hcross ⟨b₂, hb2_mem⟩ hb2_ne)

-- Part 4: `twoConstr_subst` and `contractSide_cubic_3ec` for Sticking (Case 1)

/-! ### Part 4: Substitution into a `TwoConstruction` and 3-edge-cut Sticking -/

/-- Substitute a `TwoConstruction M W_sub F_sub` in place of a single vertex `w₀` inside a
`TwoConstruction M₁ W₁ F₁`, given a projection `ψ : W → W₁` whose fiber over `w₀` is `W_sub`
and which is bijective outside `w₀`, together with an edge embedding `embF : F₁ ↪ F` whose image
is disjoint from `F_sub` and preserves endpoints modulo `ψ`. -/
noncomputable def twoConstr_subst {W F W₁ F₁ : Type} [DecidableEq W] [DecidableEq F] [DecidableEq W₁] [DecidableEq F₁]
    {M : Multigraph W F} {M₁ : Multigraph W₁ F₁}
    (w₀ : W₁) (W_sub : Finset W) (F_sub : Finset F)
    (tc_sub : TwoConstruction M W_sub F_sub)
    (ψ : W → W₁) (inv : ∀ w₁ : W₁, w₁ ≠ w₀ → W)
    (hψ_sub : ∀ w : W, w ∈ W_sub ↔ ψ w = w₀)
    (hψ_inv : ∀ (w₁ : W₁) (h : w₁ ≠ w₀), ψ (inv w₁ h) = w₁)
    (hinv_ψ : ∀ (w : W) (h : ψ w ≠ w₀), inv (ψ w) h = w)
    (embF : F₁ ↪ F)
    (hF_disj : ∀ f₁ : F₁, embF f₁ ∉ F_sub)
    (hend : ∀ f₁ : F₁,
      (ψ (M.tail (embF f₁)) = M₁.tail f₁ ∧ ψ (M.head (embF f₁)) = M₁.head f₁) ∨
      (ψ (M.tail (embF f₁)) = M₁.head f₁ ∧ ψ (M.head (embF f₁)) = M₁.tail f₁))
    [Fintype W] :
    ∀ {Wa : Finset W₁} {Fa : Finset F₁}, TwoConstruction M₁ Wa Fa →
      TwoConstruction M
        (Finset.univ.filter (fun w => ψ w ∈ Wa))
        (if w₀ ∈ Wa then F_sub ∪ Fa.map embF else Fa.map embF) := by
  intro Wa Fa tc₁
  induction tc₁ with
  | single w₁ =>
    by_cases hw : w₀ = w₁
    · subst hw
      have hW : Finset.univ.filter (fun w : W => ψ w ∈ ({w₀} : Finset W₁)) = W_sub := by
        ext w; simp [hψ_sub]
      have hF : (if w₀ ∈ ({w₀} : Finset W₁) then F_sub ∪ (∅ : Finset F₁).map embF else (∅ : Finset F₁).map embF) = F_sub := by
        simp
      rw [hW, hF]; exact tc_sub
    · have hW : Finset.univ.filter (fun w : W => ψ w ∈ ({w₁} : Finset W₁)) = {inv w₁ (Ne.symm hw)} := by
        ext w; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro h; have hne : ψ w ≠ w₀ := h ▸ Ne.symm hw
          have := hinv_ψ w hne
          simpa [h] using this.symm
        · intro h; rw [h, hψ_inv]
      have hF : (if w₀ ∈ ({w₁} : Finset W₁) then F_sub ∪ (∅ : Finset F₁).map embF else (∅ : Finset F₁).map embF) = ∅ := by
        simp [hw]
      rw [hW, hF]; exact TwoConstruction.single (inv w₁ (Ne.symm hw))
  | @join Wa Wb Fa Fb left right e f hdisjW hdisjF he_ne_f he1 he2 hf1 hf2 he_cr hf_cr ihl ihr =>
    let Wa' := Finset.univ.filter (fun w : W => ψ w ∈ Wa)
    let Wb' := Finset.univ.filter (fun w : W => ψ w ∈ Wb)
    let Fa' := if w₀ ∈ Wa then F_sub ∪ Fa.map embF else Fa.map embF
    let Fb' := if w₀ ∈ Wb then F_sub ∪ Fb.map embF else Fb.map embF
    have hW_eq : Finset.univ.filter (fun w : W => ψ w ∈ Wa ∪ Wb) = Wa' ∪ Wb' := by
      ext w; simp [Wa', Wb']
    have hdisjW' : Disjoint Wa' Wb' := by
      rw [Finset.disjoint_left]; intro w h1 h2
      exact Finset.disjoint_left.mp hdisjW (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2
    have hdisjF' : Disjoint Fa' Fb' := by
      rw [Finset.disjoint_left]; intro x hx1 hx2
      dsimp only [Fa', Fb'] at hx1 hx2
      by_cases h1 : w₀ ∈ Wa <;> by_cases h2 : w₀ ∈ Wb
      · exact Finset.disjoint_left.mp hdisjW h1 h2
      · rw [if_pos h1, Finset.mem_union] at hx1; rw [if_neg h2] at hx2
        obtain ⟨y, hyb, rfl⟩ := Finset.mem_map.mp hx2
        rcases hx1 with hsub | hm
        · exact hF_disj y hsub
        · obtain ⟨z, hza, hze⟩ := Finset.mem_map.mp hm
          exact Finset.disjoint_left.mp hdisjF hza (embF.injective hze ▸ hyb)
      · rw [if_neg h1] at hx1; rw [if_pos h2, Finset.mem_union] at hx2
        obtain ⟨y, hya, rfl⟩ := Finset.mem_map.mp hx1
        rcases hx2 with hsub | hm
        · exact hF_disj y hsub
        · obtain ⟨z, hzb, hze⟩ := Finset.mem_map.mp hm
          exact Finset.disjoint_left.mp hdisjF hya (embF.injective hze ▸ hzb)
      · rw [if_neg h1] at hx1; rw [if_neg h2] at hx2
        obtain ⟨y, hya, rfl⟩ := Finset.mem_map.mp hx1
        obtain ⟨z, hzb, hze⟩ := Finset.mem_map.mp hx2
        exact Finset.disjoint_left.mp hdisjF hya (embF.injective hze ▸ hzb)
    have hF_eq : (if w₀ ∈ Wa ∪ Wb then F_sub ∪ (insert e (insert f (Fa ∪ Fb))).map embF
        else (insert e (insert f (Fa ∪ Fb))).map embF) =
        insert (embF e) (insert (embF f) (Fa' ∪ Fb')) := by
      have hmap : (insert e (insert f (Fa ∪ Fb))).map embF =
          insert (embF e) (insert (embF f) (Fa.map embF ∪ Fb.map embF)) := by
        simp only [Finset.map_insert, Finset.map_union]
      rw [hmap]
      by_cases h1 : w₀ ∈ Wa <;> by_cases h2 : w₀ ∈ Wb
      · exact absurd h2 (Finset.disjoint_left.mp hdisjW h1)
      · have h12 : w₀ ∈ Wa ∪ Wb := Finset.mem_union_left _ h1
        dsimp only [Fa', Fb']; simp only [h12, h1, h2, ↓reduceIte]
        ext x; simp only [Finset.mem_union, Finset.mem_insert]
        constructor
        · rintro (h | rfl | rfl | h | h)
          · exact Or.inr (Or.inr (Or.inl (Or.inl h)))
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (Or.inl (Or.inr h)))
          · exact Or.inr (Or.inr (Or.inr h))
        · rintro (rfl | rfl | (h | h) | h)
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (Or.inl rfl))
          · exact Or.inl h
          · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
      · have h12 : w₀ ∈ Wa ∪ Wb := Finset.mem_union_right _ h2
        dsimp only [Fa', Fb']; simp only [h12, h1, h2, ↓reduceIte]
        ext x; simp only [Finset.mem_union, Finset.mem_insert]
        constructor
        · rintro (h | rfl | rfl | h | h)
          · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
        · rintro (rfl | rfl | h | (h | h))
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (Or.inl rfl))
          · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
          · exact Or.inl h
          · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
      · have h12 : w₀ ∉ Wa ∪ Wb := fun hm => by rcases Finset.mem_union.mp hm with h | h; exact h1 h; exact h2 h
        dsimp only [Fa', Fb']; simp only [h12, h1, h2, ↓reduceIte]
    have hnot : ∀ (g : F₁) (S : Finset F₁) (b : Prop) [Decidable b],
        g ∉ S → embF g ∉ (if b then F_sub ∪ S.map embF else S.map embF) := by
      intro g S b _ hg hm
      split_ifs at hm
      · rw [Finset.mem_union] at hm
        rcases hm with hsub | hmap
        · exact hF_disj g hsub
        · obtain ⟨z, hz, hze⟩ := Finset.mem_map.mp hmap
          exact hg (embF.injective hze ▸ hz)
      · obtain ⟨z, hz, hze⟩ := Finset.mem_map.mp hm
        exact hg (embF.injective hze ▸ hz)
    have hcr : ∀ g : F₁,
        ((M₁.tail g ∈ Wa ∧ M₁.head g ∈ Wb) ∨ (M₁.tail g ∈ Wb ∧ M₁.head g ∈ Wa)) →
        ((M.tail (embF g) ∈ Wa' ∧ M.head (embF g) ∈ Wb') ∨
         (M.tail (embF g) ∈ Wb' ∧ M.head (embF g) ∈ Wa')) := by
      intro g hg
      simp only [Wa', Wb', Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hend g with ⟨ht, hh⟩ | ⟨ht, hh⟩ <;> rcases hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; exact ⟨ht ▸ h1, hh ▸ h2⟩
      · right; exact ⟨ht ▸ h1, hh ▸ h2⟩
      · right; exact ⟨ht ▸ h2, hh ▸ h1⟩
      · left; exact ⟨ht ▸ h2, hh ▸ h1⟩
    rw [hW_eq, hF_eq]
    exact TwoConstruction.join ihl ihr (embF e) (embF f) hdisjW' hdisjF'
      (fun h => he_ne_f (embF.injective h))
      (hnot e Fa (w₀ ∈ Wa) he1) (hnot e Fb (w₀ ∈ Wb) he2)
      (hnot f Fa (w₀ ∈ Wa) hf1) (hnot f Fb (w₀ ∈ Wb) hf2)
      (hcr e he_cr) (hcr f hf_cr)

/-- Contracting the complement of `A` to a single vertex `none` in a cubic `3`-edge-connected graph
with `|A| ≥ 2`, `|V \ A| ≥ 2`, and `|δ(A)| = 3` yields a strictly smaller cubic `3`-edge-connected
graph on `≥ 4` vertices. -/
def contractSide {V E : Type} [DecidableEq V] (G : Multigraph V E) (A : Finset V) :
    Multigraph (Option {v : V // v ∈ A}) {e : E // G.tail e ∈ A ∨ G.head e ∈ A} where
  tail e := if h : G.tail e.1 ∈ A then some ⟨G.tail e.1, h⟩ else none
  head e := if h : G.head e.1 ∈ A then some ⟨G.head e.1, h⟩ else none

lemma contractSide_props {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : Multigraph V E) (hcub : G.IsCubic) (h3 : G.IsEdgeConnected 3)
    (A : Finset V) (hA2 : 2 ≤ A.card) (hB2 : 2 ≤ (Finset.univ \ A).card)
    (hcut3 : (G.cutEdges A).card ≤ 3) :
    (contractSide G A).IsCubic ∧
    (contractSide G A).IsEdgeConnected 3 ∧
    4 ≤ Fintype.card (Option {v : V // v ∈ A}) ∧
    Fintype.card (Option {v : V // v ∈ A}) < Fintype.card V := by
  have hcut_eq : (G.cutEdges A).card = 3 := by
    have hge := h3 A (Finset.card_pos.mp (by omega)) (Finset.card_pos.mp (by omega))
    omega
  have hcard_lt : Fintype.card (Option {v : V // v ∈ A}) < Fintype.card V := by
    rw [Fintype.card_option, Fintype.card_coe]
    have hsd : (Finset.univ \ A).card = Fintype.card V - A.card := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
    omega
  have hcub' : (contractSide G A).IsCubic := by
    intro v
    cases v with
    | none =>
      unfold Multigraph.deg
      have ht : (Finset.univ.filter (fun e : {e : E // G.tail e ∈ A ∨ G.head e ∈ A} =>
          (contractSide G A).tail e = none)).card =
          (Finset.univ.filter (fun e : E => G.tail e ∉ A ∧ G.head e ∈ A)).card := by
        refine Finset.card_bij (fun e _ => e.1) (fun e he => ?_) (fun _ _ _ _ h => Subtype.ext h)
          (fun e he => ⟨⟨e, Or.inr (Finset.mem_filter.mp he).2.2⟩, ?_, rfl⟩)
        · have h := (Finset.mem_filter.mp he).2
          dsimp only [contractSide] at h
          have hnt : G.tail e.1 ∉ A := fun hm => by simp [hm] at h
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnt, e.2.resolve_left hnt⟩
        · have ⟨hnt, _⟩ := (Finset.mem_filter.mp he).2
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [contractSide, hnt]⟩
      have hh : (Finset.univ.filter (fun e : {e : E // G.tail e ∈ A ∨ G.head e ∈ A} =>
          (contractSide G A).head e = none)).card =
          (Finset.univ.filter (fun e : E => G.tail e ∈ A ∧ G.head e ∉ A)).card := by
        refine Finset.card_bij (fun e _ => e.1) (fun e he => ?_) (fun _ _ _ _ h => Subtype.ext h)
          (fun e he => ⟨⟨e, Or.inl (Finset.mem_filter.mp he).2.1⟩, ?_, rfl⟩)
        · have h := (Finset.mem_filter.mp he).2
          dsimp only [contractSide] at h
          have hnh : G.head e.1 ∉ A := fun hm => by simp [hm] at h
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, e.2.resolve_right hnh, hnh⟩
        · have ⟨_, hnh⟩ := (Finset.mem_filter.mp he).2
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [contractSide, hnh]⟩
      rw [ht, hh]
      have hd : Disjoint (Finset.univ.filter (fun e : E => G.tail e ∉ A ∧ G.head e ∈ A))
          (Finset.univ.filter (fun e : E => G.tail e ∈ A ∧ G.head e ∉ A)) := by
        rw [Finset.disjoint_left]; intro e h1 h2
        exact (Finset.mem_filter.mp h1).2.1 (Finset.mem_filter.mp h2).2.1
      rw [← Finset.card_union_of_disjoint hd]
      have hun : Finset.univ.filter (fun e : E => G.tail e ∉ A ∧ G.head e ∈ A) ∪
          Finset.univ.filter (fun e : E => G.tail e ∈ A ∧ G.head e ∉ A) = G.cutEdges A := by
        ext e; simp only [Multigraph.cutEdges, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        tauto
      rw [hun, hcut_eq]
    | some a =>
      unfold Multigraph.deg
      have ht : (Finset.univ.filter (fun e : {e : E // G.tail e ∈ A ∨ G.head e ∈ A} =>
          (contractSide G A).tail e = some a)).card =
          (Finset.univ.filter (fun e : E => G.tail e = a.1)).card := by
        refine Finset.card_bij (fun e _ => e.1) (fun e he => ?_) (fun _ _ _ _ h => Subtype.ext h)
          (fun e he => ⟨⟨e, Or.inl ((Finset.mem_filter.mp he).2 ▸ a.2)⟩, ?_, rfl⟩)
        · have h := (Finset.mem_filter.mp he).2
          dsimp only [contractSide] at h
          by_cases hm : G.tail e.1 ∈ A
          · rw [dif_pos hm] at h; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, val_eq_of_some_eq (h)⟩
          · rw [dif_neg hm] at h; simp at h
        · have h := (Finset.mem_filter.mp he).2
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          dsimp only [contractSide]; rw [dif_pos (h ▸ a.2)]; exact congrArg some (Subtype.ext h)
      have hh : (Finset.univ.filter (fun e : {e : E // G.tail e ∈ A ∨ G.head e ∈ A} =>
          (contractSide G A).head e = some a)).card =
          (Finset.univ.filter (fun e : E => G.head e = a.1)).card := by
        refine Finset.card_bij (fun e _ => e.1) (fun e he => ?_) (fun _ _ _ _ h => Subtype.ext h)
          (fun e he => ⟨⟨e, Or.inr ((Finset.mem_filter.mp he).2 ▸ a.2)⟩, ?_, rfl⟩)
        · have h := (Finset.mem_filter.mp he).2
          dsimp only [contractSide] at h
          by_cases hm : G.head e.1 ∈ A
          · rw [dif_pos hm] at h; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, val_eq_of_some_eq (h)⟩
          · rw [dif_neg hm] at h; simp at h
        · have h := (Finset.mem_filter.mp he).2
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          dsimp only [contractSide]; rw [dif_pos (h ▸ a.2)]; exact congrArg some (Subtype.ext h)
      rw [ht, hh]; exact hcub a.1
  have h4 : 4 ≤ Fintype.card (Option {v : V // v ∈ A}) := by
    have h2e := cubic_two_mul_edges (contractSide G A) hcub'
    rw [Fintype.card_option, Fintype.card_coe] at h2e ⊢
    omega
  have h3' : (contractSide G A).IsEdgeConnected 3 := by
    intro S₁ hS₁ne hS₁cne
    let proj : V → Option {v : V // v ∈ A} := fun v => if h : v ∈ A then some ⟨v, h⟩ else none
    let S : Finset V := Finset.univ.filter (fun v => proj v ∈ S₁)
    have hSne : S.Nonempty := by
      obtain ⟨w, hw⟩ := hS₁ne
      cases w with
      | none =>
        obtain ⟨b, hb⟩ := Finset.card_pos.mp (by omega : 0 < (Finset.univ \ A).card)
        have hnb : b ∉ A := (Finset.mem_sdiff.mp hb).2
        exact ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [proj, hnb, hw]⟩⟩
      | some a =>
        exact ⟨a.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [proj, a.2, hw]⟩⟩
    have hScne : (Finset.univ \ S).Nonempty := by
      obtain ⟨w, hw⟩ := hS₁cne
      have hw' : w ∉ S₁ := (Finset.mem_sdiff.mp hw).2
      cases w with
      | none =>
        obtain ⟨b, hb⟩ := Finset.card_pos.mp (by omega : 0 < (Finset.univ \ A).card)
        have hnb : b ∉ A := (Finset.mem_sdiff.mp hb).2
        exact ⟨b, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by simp [S, proj, hnb, hw']⟩⟩
      | some a =>
        exact ⟨a.1, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by simp [S, proj, a.2, hw']⟩⟩
    have hcut_eq' : ((contractSide G A).cutEdges S₁).card = (G.cutEdges S).card := by
      refine Finset.card_bij (fun e _ => e.1) (fun e he => ?_) (fun _ _ _ _ h => Subtype.ext h)
        (fun e he => ?_)
      · have h := (Finset.mem_filter.mp he).2
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        simpa [S, proj, contractSide] using h
      · have h := (Finset.mem_filter.mp he).2
        have hor : G.tail e ∈ A ∨ G.head e ∈ A := by
          by_contra hno; push Not at hno
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, proj, hno.1, hno.2, ↓reduceDIte] at h
          rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩; exact h2 h1; exact h1 h2
        refine ⟨⟨e, hor⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
        simpa [S, proj, contractSide] using h
    rw [hcut_eq']; exact h3 S hSne hScne
  exact ⟨hcub', h3', h4, hcard_lt⟩

-- Part 5: Complete Sticking lemma (Case 1) for JLPTWellColouring.lean

/-! ### Part 5: Sticking (`wellColouring_sticking`, Case 1: non-trivial 3-edge-cut) -/

set_option maxHeartbeats 800000 in
/-- Sticking lemma: given a cubic `3`-edge-connected graph `Qplus` on `≥ 6` vertices with
a non-trivial `3`-edge-cut `A` (`v₀ ∈ A`, `|A| ≥ 2`, `|V \ A| ≥ 2`, `|δ(A)| ≤ 3`),
well colourings of the two contracted sides glue to a well colouring of `Qplus.deleteVertex v₀`. -/
lemma wellColouring_sticking {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (Qplus : Multigraph V E) (v₀ : V)
    (hcub : Qplus.IsCubic) (h3 : Qplus.IsEdgeConnected 3) (h4 : 4 ≤ Fintype.card V)
    (A : Finset V) (hv₀A : v₀ ∈ A) (hA2 : 2 ≤ A.card) (hB2 : 2 ≤ (Finset.univ \ A).card)
    (hcut3 : (Qplus.cutEdges A).card ≤ 3)
    (wc₁ : WellColouring ((contractSide Qplus A).deleteVertex (some ⟨v₀, hv₀A⟩)))
    (wc₂ : WellColouring ((contractSide Qplus (Finset.univ \ A)).deleteVertex none)) :
    Nonempty (WellColouring (Qplus.deleteVertex v₀)) := by
  classical
  let B := Finset.univ \ A
  have hB_iff : ∀ v : V, v ∈ B ↔ v ∉ A := fun v => by simp [B]
  have hcutB : (Qplus.cutEdges B).card ≤ 3 := by
    have heq : Qplus.cutEdges B = Qplus.cutEdges A := by
      ext e; simp only [Multigraph.cutEdges, Finset.mem_filter, Finset.mem_univ, true_and, hB_iff]; tauto
    rw [heq]; exact hcut3
  have hB_compl : Finset.univ \ B = A := by ext v; simp [B]
  have hP1 := contractSide_props Qplus hcub h3 A hA2 hB2 hcut3
  have hP2 := contractSide_props Qplus hcub h3 B hB2 (by rw [hB_compl]; exact hA2) hcutB
  let Q := Qplus.deleteVertex v₀
  let Q₁ := (contractSide Qplus A).deleteVertex (some ⟨v₀, hv₀A⟩)
  let Q₂ := (contractSide Qplus B).deleteVertex none
  -- Edge routing: every edge e of Q goes into Q₂ (if both ends in B) or Q₁ (otherwise)
  have hnotB_iff : ∀ e : {e : E // Qplus.tail e ≠ v₀ ∧ Qplus.head e ≠ v₀},
      (¬ (Qplus.tail e.1 ∈ B ∧ Qplus.head e.1 ∈ B)) ↔ (Qplus.tail e.1 ∈ A ∨ Qplus.head e.1 ∈ A) := by
    intro e; simp only [hB_iff]; tauto
  let toE₂ (e : {e : E // Qplus.tail e ≠ v₀ ∧ Qplus.head e ≠ v₀})
      (h : Qplus.tail e.1 ∈ B ∧ Qplus.head e.1 ∈ B) :
      {e' : {e : E // Qplus.tail e ∈ B ∨ Qplus.head e ∈ B} //
        (contractSide Qplus B).tail e' ≠ none ∧ (contractSide Qplus B).head e' ≠ none} :=
    ⟨⟨e.1, Or.inl h.1⟩, by simp [contractSide, h.1], by simp [contractSide, h.2]⟩
  let toE₁ (e : {e : E // Qplus.tail e ≠ v₀ ∧ Qplus.head e ≠ v₀})
      (h : ¬ (Qplus.tail e.1 ∈ B ∧ Qplus.head e.1 ∈ B)) :
      {e' : {e : E // Qplus.tail e ∈ A ∨ Qplus.head e ∈ A} //
        (contractSide Qplus A).tail e' ≠ some ⟨v₀, hv₀A⟩ ∧ (contractSide Qplus A).head e' ≠ some ⟨v₀, hv₀A⟩} :=
    ⟨⟨e.1, (hnotB_iff e).mp h⟩,
     by dsimp only [contractSide]; split_ifs with ht
        · intro heq; exact e.2.1 (val_eq_of_some_eq (heq))
        · simp,
     by dsimp only [contractSide]; split_ifs with hh
        · intro heq; exact e.2.2 (val_eq_of_some_eq (heq))
        · simp⟩
  let blue : Finset {e : E // Qplus.tail e ≠ v₀ ∧ Qplus.head e ≠ v₀} :=
    Finset.univ.filter fun e =>
      if h : Qplus.tail e.1 ∈ B ∧ Qplus.head e.1 ∈ B then toE₂ e h ∈ wc₂.blue
      else toE₁ e h ∈ wc₁.blue
  -- Bijections between blue_2 / blue_1 and the two disjoint pieces of blue
  let blueB := blue.filter (fun e => Qplus.tail e.1 ∈ B ∧ Qplus.head e.1 ∈ B)
  let blueA := blue.filter (fun e => ¬ (Qplus.tail e.1 ∈ B ∧ Qplus.head e.1 ∈ B))
  have hblueB_card : blueB.card = wc₂.blue.card := by
    refine Finset.card_bij
      (fun e he => toE₂ e (Finset.mem_filter.mp he).2)
      (fun e he => by
        have h1 := (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2
        have h2 := (Finset.mem_filter.mp he).2
        simpa [h2] using h1)
      (fun e₁ _ e₂ _ heq => Subtype.ext (congrArg (fun x => x.1.1) heq))
      (fun e₂ he₂ => ?_)
    have htB : Qplus.tail e₂.1.1 ∈ B := by
      by_contra hnot; exact e₂.2.1 (by dsimp only [contractSide]; rw [dif_neg hnot])
    have hhB : Qplus.head e₂.1.1 ∈ B := by
      by_contra hnot; exact e₂.2.2 (by dsimp only [contractSide]; rw [dif_neg hnot])
    have hnt0 : Qplus.tail e₂.1.1 ≠ v₀ := fun h => (hB_iff _).mp htB (h.symm ▸ hv₀A)
    have hnh0 : Qplus.head e₂.1.1 ≠ v₀ := fun h => (hB_iff _).mp hhB (h.symm ▸ hv₀A)
    let eQ : {e : E // Qplus.tail e ≠ v₀ ∧ Qplus.head e ≠ v₀} := ⟨e₂.1.1, hnt0, hnh0⟩
    refine ⟨eQ, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, htB, hhB⟩, Subtype.ext (Subtype.ext rfl)⟩
    rw [dif_pos ⟨htB, hhB⟩]; exact he₂
  have hblueA_card : blueA.card = wc₁.blue.card := by
    refine Finset.card_bij
      (fun e he => toE₁ e (Finset.mem_filter.mp he).2)
      (fun e he => by
        have h1 := (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2
        have h2 := (Finset.mem_filter.mp he).2
        simpa [h2] using h1)
      (fun e₁ _ e₂ _ heq => Subtype.ext (congrArg (fun x => x.1.1) heq))
      (fun e₁ he₁ => ?_)
    have hnt0 : Qplus.tail e₁.1.1 ≠ v₀ := fun h =>
      e₁.2.1 (by dsimp only [contractSide]; rw [dif_pos (by rw [h]; exact hv₀A)]; exact congrArg some (Subtype.ext h))
    have hnh0 : Qplus.head e₁.1.1 ≠ v₀ := fun h =>
      e₁.2.2 (by dsimp only [contractSide]; rw [dif_pos (by rw [h]; exact hv₀A)]; exact congrArg some (Subtype.ext h))
    let eQ : {e : E // Qplus.tail e ≠ v₀ ∧ Qplus.head e ≠ v₀} := ⟨e₁.1.1, hnt0, hnh0⟩
    have hnotB : ¬ (Qplus.tail eQ.1 ∈ B ∧ Qplus.head eQ.1 ∈ B) := (hnotB_iff eQ).mpr e₁.1.2
    refine ⟨eQ, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hnotB⟩, Subtype.ext (Subtype.ext rfl)⟩
    rw [dif_neg hnotB]; exact he₁
  have hblue_card : blue.card + 1 = Fintype.card {u : V // u ≠ v₀} := by
    have hun : blue = blueB ∪ blueA := by ext e; simp only [blueB, blueA, Finset.mem_union, Finset.mem_filter]; tauto
    have hdisj : Disjoint blueB blueA := by
      rw [Finset.disjoint_left]; intro e h1 h2; exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
    have h1 := spanningTree_card_edges Q₁ wc₁.blue wc₁.blue_tree
    have h2 := spanningTree_card_edges Q₂ wc₂.blue wc₂.blue_tree
    have hV1 : Fintype.card {u : Option {v : V // v ∈ A} // u ≠ some ⟨v₀, hv₀A⟩} = A.card := by
      rw [Fintype.card_subtype_compl, show Fintype.card {u : Option {v : V // v ∈ A} // u = some ⟨v₀, hv₀A⟩} = 1 from Fintype.card_unique,
          Fintype.card_option, Fintype.card_coe]; omega
    have hV2 : Fintype.card {u : Option {v : V // v ∈ B} // u ≠ none} = B.card := by
      rw [Fintype.card_subtype_compl, show Fintype.card {u : Option {v : V // v ∈ B} // u = none} = 1 from Fintype.card_unique,
          Fintype.card_option, Fintype.card_coe]; omega
    have hVQ : Fintype.card {u : V // u ≠ v₀} + 1 = Fintype.card V := by
      rw [Fintype.card_subtype_compl, show Fintype.card {u : V // u = v₀} = 1 from Fintype.card_unique]; omega
    have hAB : A.card + B.card = Fintype.card V := by
      have hsd : B.card = Fintype.card V - A.card := by rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
      have hle : A.card ≤ Fintype.card V := Finset.card_le_univ _
      omega
    rw [hun, Finset.card_union_of_disjoint hdisj, hblueB_card, hblueA_card]; omega
  -- 1. Spanning tree: prove T = ofEdges Q univ blue is connected!
  let T := Multigraph.Subgraph.ofEdges Q Finset.univ blue (fun _ => Finset.mem_univ _) (fun _ => Finset.mem_univ _)
  let T₁ := Multigraph.Subgraph.ofEdges Q₁ Finset.univ wc₁.blue (fun _ => Finset.mem_univ _) (fun _ => Finset.mem_univ _)
  let T₂ := Multigraph.Subgraph.ofEdges Q₂ Finset.univ wc₂.blue (fun _ => Finset.mem_univ _) (fun _ => Finset.mem_univ _)
  have hB_conn : ∀ (b₁ b₂ : {u : V // u ≠ v₀}), b₁.1 ∈ B → b₂.1 ∈ B → Relation.ReflTransGen T.Adj b₁ b₂ := by
    intro b₁ b₂ hb1 hb2
    have h2 := wc₂.blue_tree.2.1.2 ⟨some ⟨b₁.1, hb1⟩, by simp⟩ (Finset.mem_univ _)
      ⟨some ⟨b₂.1, hb2⟩, by simp⟩ (Finset.mem_univ _)
    have hlift : ∀ x y : {u : Option {v : V // v ∈ B} // u ≠ none},
        Relation.ReflTransGen T₂.Adj x y →
        ∀ (x' y' : {u : V // u ≠ v₀}), (hx : x'.1 ∈ B) → (hy : y'.1 ∈ B) →
          x.1 = some ⟨x'.1, hx⟩ → y.1 = some ⟨y'.1, hy⟩ →
          Relation.ReflTransGen T.Adj x' y' := by
      intro x y hxy
      induction hxy with
      | refl =>
        intro x' y' hx hy hx' hy'
        have : x' = y' := Subtype.ext (by have h_tmp := Option.some.inj (hx'.symm.trans hy'); rw [Subtype.ext_iff] at h_tmp; exact h_tmp)
        rw [this]
      | @tail p q _ hs ih =>
        intro x' y' hx hy hx' hy'
        rcases hs with ⟨e₂, he₂, hinc⟩
        have htB : Qplus.tail e₂.1.1 ∈ B := by by_contra h; exact e₂.2.1 (by dsimp only [contractSide]; rw [dif_neg h])
        have hhB : Qplus.head e₂.1.1 ∈ B := by by_contra h; exact e₂.2.2 (by dsimp only [contractSide]; rw [dif_neg h])
        have hnt0 : Qplus.tail e₂.1.1 ≠ v₀ := fun h => (hB_iff _).mp htB (h.symm ▸ hv₀A)
        have hnh0 : Qplus.head e₂.1.1 ≠ v₀ := fun h => (hB_iff _).mp hhB (h.symm ▸ hv₀A)
        let eQ : {e : E // Qplus.tail e ≠ v₀ ∧ Qplus.head e ≠ v₀} := ⟨e₂.1.1, hnt0, hnh0⟩
        have heQ_bl : eQ ∈ blue := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [dif_pos ⟨htB, hhB⟩]; exact he₂⟩
        cases hp : p.1 with
        | none => exact absurd hp p.2
        | some bp =>
          have hbp0 : bp.1 ≠ v₀ := fun h => (hB_iff _).mp bp.2 (h.symm ▸ hv₀A)
          let p' : {u : V // u ≠ v₀} := ⟨bp.1, hbp0⟩
          have hprev := ih x' p' hx bp.2 hx' hp
          refine hprev.tail ⟨eQ, heQ_bl, ?_⟩
          rcases hinc with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · left
            have ht_eq := congrArg Subtype.val h1; have hh_eq := congrArg Subtype.val h2
            simp only [Q₂, Multigraph.deleteVertex, contractSide, htB, hhB, ↓reduceDIte] at ht_eq hh_eq
            rw [hp] at ht_eq; rw [hy'] at hh_eq
            exact ⟨Subtype.ext (by have h_tmp := Option.some.inj (ht_eq); rw [Subtype.ext_iff] at h_tmp; exact h_tmp),
                   Subtype.ext (by have h_tmp := Option.some.inj (hh_eq); rw [Subtype.ext_iff] at h_tmp; exact h_tmp)⟩
          · right
            have ht_eq := congrArg Subtype.val h1; have hh_eq := congrArg Subtype.val h2
            simp only [Q₂, Multigraph.deleteVertex, contractSide, htB, hhB, ↓reduceDIte] at ht_eq hh_eq
            rw [hy'] at ht_eq; rw [hp] at hh_eq
            exact ⟨Subtype.ext (by have h_tmp := Option.some.inj (ht_eq); rw [Subtype.ext_iff] at h_tmp; exact h_tmp),
                   Subtype.ext (by have h_tmp := Option.some.inj (hh_eq); rw [Subtype.ext_iff] at h_tmp; exact h_tmp)⟩
    exact hlift _ _ h2 b₁ b₂ hb1 hb2 rfl rfl
  obtain ⟨b₀_val, hb₀_mem⟩ := Finset.card_pos.mp (by dsimp only [B]; omega : 0 < B.card)
  let b₀ : {u : V // u ≠ v₀} := ⟨b₀_val, fun h => (hB_iff _).mp hb₀_mem (h.symm ▸ hv₀A)⟩
  have hreach_b₀ : ∀ u : {u : V // u ≠ v₀}, Relation.ReflTransGen T.Adj u b₀ := by
    intro u
    by_cases huB : u.1 ∈ B
    · exact hB_conn u b₀ huB hb₀_mem
    · have huA : u.1 ∈ A := by rwa [hB_iff, not_not] at huB
      have hne_v0 : (some ⟨u.1, huA⟩ : Option {v : V // v ∈ A}) ≠ some ⟨v₀, hv₀A⟩ := fun h =>
        u.2 (val_eq_of_some_eq (h))
      have h1 := wc₁.blue_tree.2.1.2 ⟨some ⟨u.1, huA⟩, hne_v0⟩ (Finset.mem_univ _)
        ⟨none, by simp⟩ (Finset.mem_univ _)
      -- Walk in T₁ from some u to none: lift until first hit of none!
      have hlift1 : ∀ x y : {u : Option {v : V // v ∈ A} // u ≠ some ⟨v₀, hv₀A⟩},
          Relation.ReflTransGen T₁.Adj x y →
          ∀ (x' : {u : V // u ≠ v₀}) (hxA : x'.1 ∈ A), x.1 = some ⟨x'.1, hxA⟩ →
          (y.1 = none → Relation.ReflTransGen T.Adj x' b₀) ∧
          (∀ (y' : {u : V // u ≠ v₀}) (hyA : y'.1 ∈ A), y.1 = some ⟨y'.1, hyA⟩ →
            Relation.ReflTransGen T.Adj x' y' ∨ Relation.ReflTransGen T.Adj x' b₀) := by
        intro x y hxy
        induction hxy with
        | refl =>
          intro x' hxA hx'
          refine ⟨fun hy => by rw [hx'] at hy; simp at hy, fun y' hyA hy' => Or.inl ?_⟩
          have : x' = y' := Subtype.ext (by have h_tmp := Option.some.inj (hx'.symm.trans hy'); rw [Subtype.ext_iff] at h_tmp; exact h_tmp)
          rw [this]
        | @tail p q _ hs ih =>
          intro x' hxA hx'
          have hih := ih x' hxA hx'
          cases hp : p.1 with
          | none =>
            have hreach : Relation.ReflTransGen T.Adj x' b₀ := hih.1 hp
            exact ⟨fun _ => hreach, fun _ _ _ => Or.inr hreach⟩
          | some ap =>
            have hap0 : ap.1 ≠ v₀ := fun h => p.2 (hp.trans (congrArg some (Subtype.ext h)))
            let p' : {u : V // u ≠ v₀} := ⟨ap.1, hap0⟩
            rcases hih.2 p' ap.2 hp with hxp | hxb
            · rcases hs with ⟨e₁, he₁, hinc⟩
              have hnt0 : Qplus.tail e₁.1.1 ≠ v₀ := fun h =>
                e₁.2.1 (by dsimp only [contractSide]; rw [dif_pos (by rw [h]; exact hv₀A)]; exact congrArg some (Subtype.ext h))
              have hnh0 : Qplus.head e₁.1.1 ≠ v₀ := fun h =>
                e₁.2.2 (by dsimp only [contractSide]; rw [dif_pos (by rw [h]; exact hv₀A)]; exact congrArg some (Subtype.ext h))
              let eQ : {e : E // Qplus.tail e ≠ v₀ ∧ Qplus.head e ≠ v₀} := ⟨e₁.1.1, hnt0, hnh0⟩
              have hnotB : ¬ (Qplus.tail eQ.1 ∈ B ∧ Qplus.head eQ.1 ∈ B) := (hnotB_iff eQ).mpr e₁.1.2
              have heQ_bl : eQ ∈ blue := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [dif_neg hnotB]; exact he₁⟩
              refine ⟨fun hq => ?_, fun y' hyA hy' => Or.inl ?_⟩
              · rcases hinc with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
                · have ht_eq := congrArg Subtype.val h1'; have hh_eq := congrArg Subtype.val h2'
                  dsimp only [Q₁, Multigraph.deleteVertex, contractSide] at ht_eq hh_eq
                  rw [hp] at ht_eq; rw [hq] at hh_eq
                  have htA : Qplus.tail e₁.1.1 ∈ A := by by_contra h; rw [dif_neg h] at ht_eq; simp at ht_eq
                  have hhB : Qplus.head e₁.1.1 ∈ B := by
                    rw [hB_iff]; intro h; rw [dif_pos h] at hh_eq; simp at hh_eq
                  rw [dif_pos htA] at ht_eq
                  have hp_t : Q.tail eQ = p' := Subtype.ext (by have h_tmp := Option.some.inj (ht_eq); rw [Subtype.ext_iff] at h_tmp; exact h_tmp)
                  exact (hxp.tail ⟨eQ, heQ_bl, Or.inl ⟨hp_t, rfl⟩⟩).trans (hB_conn (Q.head eQ) b₀ hhB hb₀_mem)
                · have ht_eq := congrArg Subtype.val h1'; have hh_eq := congrArg Subtype.val h2'
                  dsimp only [Q₁, Multigraph.deleteVertex, contractSide] at ht_eq hh_eq
                  rw [hq] at ht_eq; rw [hp] at hh_eq
                  have hhA : Qplus.head e₁.1.1 ∈ A := by by_contra h; rw [dif_neg h] at hh_eq; simp at hh_eq
                  have htB : Qplus.tail e₁.1.1 ∈ B := by
                    rw [hB_iff]; intro h; rw [dif_pos h] at ht_eq; simp at ht_eq
                  rw [dif_pos hhA] at hh_eq
                  have hp_h : Q.head eQ = p' := Subtype.ext (by have h_tmp := Option.some.inj (hh_eq); rw [Subtype.ext_iff] at h_tmp; exact h_tmp)
                  exact (hxp.tail ⟨eQ, heQ_bl, Or.inr ⟨rfl, hp_h⟩⟩).trans (hB_conn (Q.tail eQ) b₀ htB hb₀_mem)
              · rcases hinc with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
                · have ht_eq := congrArg Subtype.val h1'; have hh_eq := congrArg Subtype.val h2'
                  dsimp only [Q₁, Multigraph.deleteVertex, contractSide] at ht_eq hh_eq
                  rw [hp] at ht_eq; rw [hy'] at hh_eq
                  have htA : Qplus.tail e₁.1.1 ∈ A := by by_contra h; rw [dif_neg h] at ht_eq; simp at ht_eq
                  have hhA : Qplus.head e₁.1.1 ∈ A := by by_contra h; rw [dif_neg h] at hh_eq; simp at hh_eq
                  rw [dif_pos htA] at ht_eq; rw [dif_pos hhA] at hh_eq
                  exact hxp.tail ⟨eQ, heQ_bl, Or.inl ⟨Subtype.ext (by have h_tmp := Option.some.inj (ht_eq); rw [Subtype.ext_iff] at h_tmp; exact h_tmp),
                    Subtype.ext (by have h_tmp := Option.some.inj (hh_eq); rw [Subtype.ext_iff] at h_tmp; exact h_tmp)⟩⟩
                · have ht_eq := congrArg Subtype.val h1'; have hh_eq := congrArg Subtype.val h2'
                  dsimp only [Q₁, Multigraph.deleteVertex, contractSide] at ht_eq hh_eq
                  rw [hy'] at ht_eq; rw [hp] at hh_eq
                  have htA : Qplus.tail e₁.1.1 ∈ A := by by_contra h; rw [dif_neg h] at ht_eq; simp at ht_eq
                  have hhA : Qplus.head e₁.1.1 ∈ A := by by_contra h; rw [dif_neg h] at hh_eq; simp at hh_eq
                  rw [dif_pos htA] at ht_eq; rw [dif_pos hhA] at hh_eq
                  exact hxp.tail ⟨eQ, heQ_bl, Or.inr ⟨Subtype.ext (by have h_tmp := Option.some.inj (ht_eq); rw [Subtype.ext_iff] at h_tmp; exact h_tmp),
                    Subtype.ext (by have h_tmp := Option.some.inj (hh_eq); rw [Subtype.ext_iff] at h_tmp; exact h_tmp)⟩⟩
            · exact ⟨fun _ => hxb, fun _ _ _ => Or.inr hxb⟩
      exact (hlift1 _ _ h1 u huA rfl).1 rfl
  have hT_conn : T.Connected := by
    refine ⟨⟨b₀, Finset.mem_univ _⟩, fun u _ v _ => ?_⟩
    have hsym : ∀ a b, Relation.ReflTransGen T.Adj a b → Relation.ReflTransGen T.Adj b a := fun a b h => by
      induction h with
      | refl => exact .refl
      | tail _ hs ih =>
        rcases hs with ⟨e, he, h1 | h1⟩
        · exact Relation.ReflTransGen.head ⟨e, he, Or.inr h1⟩ ih
        · exact Relation.ReflTransGen.head ⟨e, he, Or.inl h1⟩ ih
    exact (hreach_b₀ u).trans (hsym _ _ (hreach_b₀ v))
  have hT_tree : T.IsSpanningTree := isSpanningTree_of_connected_card Q blue hT_conn hblue_card
    -- 2. Red quotient gluing via red_isForest_of_wellColouring + twoConstr_subst!
  have hR1_forest := red_isForest_of_wellColouring (contractSide Qplus A) (some ⟨v₀, hv₀A⟩)
    hP1.1 hP1.2.1 hP1.2.2.1 wc₁
  -- Map Q₂ / red₂ → Q / red
  let embV₂ (u : {u : Option {v : V // v ∈ B} // u ≠ none}) : {u : V // u ≠ v₀} :=
    ⟨(u.1.get (Option.isSome_iff_ne_none.mpr u.2)).1,
      fun h0 => (hB_iff _).mp (u.1.get (Option.isSome_iff_ne_none.mpr u.2)).2 (h0.symm ▸ hv₀A)⟩
  have hembV₂_some : ∀ (u : {u : Option {v : V // v ∈ B} // u ≠ none}) (b : {v : V // v ∈ B}),
      u.1 = some b → (embV₂ u).1 = b.1 := fun u b hu => by
    dsimp only [embV₂]; generalize Option.isSome_iff_ne_none.mpr u.2 = hs; revert hs; rw [hu]; intro _; rfl
  have hembV₂_B : ∀ u, (embV₂ u).1 ∈ B := fun u => (u.1.get (Option.isSome_iff_ne_none.mpr u.2)).2
  have hembV₂_red : ∀ u v, Relation.ReflTransGen (redAdj Q₂ wc₂.blue) u v →
      Relation.ReflTransGen (redAdj Q blue) (embV₂ u) (embV₂ v) := by
    intro u v huv
    induction huv with
    | refl => exact .refl
    | @tail p q _ hs ih =>
      rcases hs with ⟨e₂, he₂R, hinc⟩
      have htB : Qplus.tail e₂.1.1 ∈ B := by by_contra h; exact e₂.2.1 (by dsimp only [contractSide]; rw [dif_neg h])
      have hhB : Qplus.head e₂.1.1 ∈ B := by by_contra h; exact e₂.2.2 (by dsimp only [contractSide]; rw [dif_neg h])
      have hnt0 : Qplus.tail e₂.1.1 ≠ v₀ := fun h => (hB_iff _).mp htB (h.symm ▸ hv₀A)
      have hnh0 : Qplus.head e₂.1.1 ≠ v₀ := fun h => (hB_iff _).mp hhB (h.symm ▸ hv₀A)
      let eQ : {e : E // Qplus.tail e ≠ v₀ ∧ Qplus.head e ≠ v₀} := ⟨e₂.1.1, hnt0, hnh0⟩
      have heQ_R : eQ ∉ blue := fun hm => by
        have h := (Finset.mem_filter.mp hm).2; rw [dif_pos ⟨htB, hhB⟩] at h; exact he₂R h
      refine ih.tail ⟨eQ, heQ_R, ?_⟩
      cases hp : p.1 with
      | none => exact absurd hp p.2
      | some bp =>
        cases hq : q.1 with
        | none => exact absurd hq q.2
        | some bq =>
          rcases hinc with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · left
            have ht := congrArg Subtype.val h1; have hh := congrArg Subtype.val h2
            simp only [Q₂, Multigraph.deleteVertex, contractSide, htB, hhB, ↓reduceDIte] at ht hh
            rw [hp] at ht; rw [hq] at hh
            exact ⟨Subtype.ext (by dsimp only [Q, Multigraph.deleteVertex]; rw [hembV₂_some p bp hp]; exact val_eq_of_some_eq ht),
                   Subtype.ext (by dsimp only [Q, Multigraph.deleteVertex]; rw [hembV₂_some q bq hq]; exact val_eq_of_some_eq hh)⟩
          · right
            have ht := congrArg Subtype.val h1; have hh := congrArg Subtype.val h2
            simp only [Q₂, Multigraph.deleteVertex, contractSide, htB, hhB, ↓reduceDIte] at ht hh
            rw [hq] at ht; rw [hp] at hh
            exact ⟨Subtype.ext (by dsimp only [Q, Multigraph.deleteVertex]; rw [hembV₂_some q bq hq]; exact val_eq_of_some_eq ht),
                   Subtype.ext (by dsimp only [Q, Multigraph.deleteVertex]; rw [hembV₂_some p bp hp]; exact val_eq_of_some_eq hh)⟩
  let φ : Quotient (redSetoid Q₂ wc₂.blue) → Quotient (redSetoid Q blue) :=
    Quotient.lift (fun u => Quotient.mk (redSetoid Q blue) (embV₂ u))
      (fun _ _ h => Quotient.sound (hembV₂_red _ _ h))
  -- Prove φ is INJECTIVE: any simple red path in Q between two vertices of B stays inside B!
  have hφ_inj : Function.Injective φ := by
    -- Helper: by strong induction on path length, any simple red path in Q between b1, b2 ∈ B
    -- yields a red₂-walk in Q₂!
    let RQ := Multigraph.Subgraph.ofEdges Q Finset.univ (Finset.univ \ blue)
      (fun _ => Finset.mem_univ _) (fun _ => Finset.mem_univ _)
    have hpath_B : ∀ (len : ℕ) (vs : List {u : V // u ≠ v₀}) (es : List {e : E // Qplus.tail e ≠ v₀ ∧ Qplus.head e ≠ v₀}),
        es.length = len → ∀ (hvs_len : vs.length = es.length + 1), vs.Nodup →
        (∀ e ∈ es, e ∈ RQ.edges) →
        (∀ (i : ℕ) (hi : i < es.length),
          (Q.tail (es[i]'hi) = vs[i]'(by omega) ∧ Q.head (es[i]'hi) = vs[i + 1]'(by omega)) ∨
          (Q.tail (es[i]'hi) = vs[i + 1]'(by omega) ∧ Q.head (es[i]'hi) = vs[i]'(by omega))) →
        ∀ (hb0 : (vs[0]'(by omega)).1 ∈ B) (hbl : (vs[es.length]'(by omega)).1 ∈ B),
        Relation.ReflTransGen (redAdj Q₂ wc₂.blue)
          ⟨some ⟨(vs[0]'(by omega)).1, hb0⟩, by simp⟩
          ⟨some ⟨(vs[es.length]'(by omega)).1, hbl⟩, by simp⟩ := by
      intro len
      induction len using Nat.strong_induction_on with
      | _ len ih =>
        intro vs es hlen hvs_len hnd hes hstep hb0 hbl
        cases es with
        | nil =>
          simp only [List.length_nil] at hbl ⊢; exact .refl
        | cons e0 es' =>
          have h1lt : 1 < vs.length := by simp at hvs_len; omega
          by_cases hb1 : (vs[1]'h1lt).1 ∈ B
          · -- First step stays inside B!
            have he0_notbl : e0 ∉ blue := (Finset.mem_sdiff.mp (hes e0 (List.mem_cons_self ..))).2
            have hst0 := hstep 0 (by simp)
            have htB : Qplus.tail e0.1 ∈ B ∧ Qplus.head e0.1 ∈ B := by
              rcases hst0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
              · have h1v : Qplus.tail e0.1 = (vs[0]'(by omega)).1 := congrArg Subtype.val h1
                have h2v : Qplus.head e0.1 = (vs[1]'h1lt).1 := congrArg Subtype.val h2
                exact ⟨h1v.symm ▸ hb0, h2v.symm ▸ hb1⟩
              · have h1v : Qplus.tail e0.1 = (vs[1]'h1lt).1 := congrArg Subtype.val h1
                have h2v : Qplus.head e0.1 = (vs[0]'(by omega)).1 := congrArg Subtype.val h2
                exact ⟨h1v.symm ▸ hb1, h2v.symm ▸ hb0⟩
            have he0_R2 : toE₂ e0 htB ∉ wc₂.blue := fun hm =>
              he0_notbl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [dif_pos htB]; exact hm⟩)
            have hstep0_Q2 : redAdj Q₂ wc₂.blue
                ⟨some ⟨(vs[0]'(by omega)).1, hb0⟩, by simp⟩
                ⟨some ⟨(vs[1]'h1lt).1, hb1⟩, by simp⟩ := by
              refine ⟨toE₂ e0 htB, he0_R2, ?_⟩
              rcases hst0 with ⟨h1, h2⟩ | ⟨h1, h2⟩
              · have h1v : Qplus.tail e0.1 = (vs[0]'(by omega)).1 := congrArg Subtype.val h1
                have h2v : Qplus.head e0.1 = (vs[1]'h1lt).1 := congrArg Subtype.val h2
                left; constructor <;> (refine Subtype.ext ?_; dsimp only [Q₂, Multigraph.deleteVertex, contractSide, toE₂])
                · rw [dif_pos htB.1]; exact congrArg some (Subtype.ext h1v)
                · rw [dif_pos htB.2]; exact congrArg some (Subtype.ext h2v)
              · have h1v : Qplus.tail e0.1 = (vs[1]'h1lt).1 := congrArg Subtype.val h1
                have h2v : Qplus.head e0.1 = (vs[0]'(by omega)).1 := congrArg Subtype.val h2
                right; constructor <;> (refine Subtype.ext ?_; dsimp only [Q₂, Multigraph.deleteVertex, contractSide, toE₂])
                · rw [dif_pos htB.1]; exact congrArg some (Subtype.ext h1v)
                · rw [dif_pos htB.2]; exact congrArg some (Subtype.ext h2v)
            -- Recurse on vs.tail and es'
            cases vs with
            | nil => simp at hvs_len
            | cons v0 vs' =>
              have htail := ih es'.length (by simp at hlen; omega) vs' es' rfl
                (by simp at hvs_len; omega) (List.Nodup.of_cons hnd)
                (fun e he => hes e (List.mem_cons_of_mem e0 he))
                (fun i hi => by
                  have h := hstep (i + 1) (by simp; omega)
                  simpa only [List.getElem_cons_succ] using h)
                hb1 (by simpa using hbl)
              exact Relation.ReflTransGen.head hstep0_Q2 htail
          · -- vs[1] ∉ B: find least j > 0 with vs[j] ∈ B, producing a red₁-cycle in Q₁ (contradicting hR1_forest!)
            exfalso
            have hex_j : ∃ k : ℕ, ∃ hk : k < (e0 :: es').length, (vs[k + 1]'(by omega)).1 ∈ B :=
              ⟨es'.length, by simp, by simpa using hbl⟩
            let j0 := Nat.find hex_j
            have hj0_spec : ∃ hk : j0 < (e0 :: es').length, (vs[j0 + 1]'(by omega)).1 ∈ B := Nat.find_spec hex_j
            obtain ⟨hj0_lt, hj0_B⟩ := hj0_spec
            have hj0_pos : 0 < j0 := by
              by_contra h0; have hj0_0 : j0 = 0 := by omega
              simp only [hj0_0, zero_add] at hj0_B; exact hb1 hj0_B
            have hj0_min : ∀ (k : ℕ) (hk : k < j0), (vs[k + 1]'(by have : k < (e0 :: es').length := lt_trans hk hj0_lt; omega)).1 ∉ B :=
              fun k hk hB => Nat.find_min hex_j hk ⟨lt_trans hk hj0_lt, hB⟩
            -- Build a cycle C₁ in R₁ on {none} ∪ {some vs[1], ..., some vs[j0]} with edges e₁[0], ..., e₁[j0]!
            let m := j0 + 1
            have hm_ge2 : 2 ≤ m := by omega
            have hm_le : m ≤ (e0 :: es').length := by omega
            have hnodup_e := simplePath_edges_nodup hnd hvs_len hstep
            let toV₁ (u : {u : V // u ≠ v₀}) : {u : Option {v : V // v ∈ A} // u ≠ some ⟨v₀, hv₀A⟩} :=
              if h : u.1 ∈ A then ⟨some ⟨u.1, h⟩, fun heq => u.2 (val_eq_of_some_eq (heq))⟩
              else ⟨none, by simp⟩
            have hmid_A : ∀ (k : ℕ) (hk : 1 ≤ k ∧ k < m), (vs[k]'(by omega)).1 ∈ A := fun k hk => by
              have hnb := hj0_min (k - 1) (by omega)
              have hk' : k - 1 + 1 = k := by omega
              rw [hB_iff, not_not] at hnb; simpa [hk'] using hnb
            have hend_notB : ∀ (k : ℕ) (hk : k < m),
                ¬ (Qplus.tail ((e0 :: es')[k]'(by omega)).1 ∈ B ∧
                   Qplus.head ((e0 :: es')[k]'(by omega)).1 ∈ B) := by
              intro k hk ⟨htB, hhB⟩
              have hst := hstep k (by omega)
              by_cases hk0 : k = 0
              · subst hk0
                rcases hst with ⟨_, h2⟩ | ⟨h1, _⟩
                · exact hb1 (congrArg Subtype.val h2 ▸ hhB)
                · exact hb1 (congrArg Subtype.val h1 ▸ htB)
              · have hkA := hmid_A k ⟨by omega, hk⟩
                rcases hst with ⟨h1, _⟩ | ⟨_, h2⟩
                · have h1v : Qplus.tail ((e0 :: es')[k]'(by omega)).1 = (vs[k]'(by omega)).1 := congrArg Subtype.val h1
                  exact (hB_iff _).mp htB (h1v.symm ▸ hkA)
                · have h2v : Qplus.head ((e0 :: es')[k]'(by omega)).1 = (vs[k]'(by omega)).1 := congrArg Subtype.val h2
                  exact (hB_iff _).mp hhB (h2v.symm ▸ hkA)
            let edgeAt (k : Fin m) :
                {e' : {e : E // Qplus.tail e ∈ A ∨ Qplus.head e ∈ A} //
                  (contractSide Qplus A).tail e' ≠ some ⟨v₀, hv₀A⟩ ∧ (contractSide Qplus A).head e' ≠ some ⟨v₀, hv₀A⟩} :=
              toE₁ ((e0 :: es')[k.1]'(by omega)) (hend_notB k.1 k.2)
            have hedgeAt_inj : Function.Injective edgeAt := by
              intro a b hab
              have hval : (e0 :: es')[a.1]'(by omega) = (e0 :: es')[b.1]'(by omega) :=
                Subtype.ext (congrArg (fun x => x.1.1) hab)
              exact Fin.ext ((List.Nodup.getElem_inj_iff hnodup_e).mp hval)
            have hedgeAt_red : ∀ k : Fin m, edgeAt k ∉ wc₁.blue := by
              intro k hm
              have he_notbl := (Finset.mem_sdiff.mp (hes ((e0 :: es')[k.1]'(by omega)) (List.getElem_mem _))).2
              exact he_notbl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [dif_neg (hend_notB k.1 k.2)]; exact hm⟩)
            let vertAt (k : Fin m) : {u : Option {v : V // v ∈ A} // u ≠ some ⟨v₀, hv₀A⟩} :=
              toV₁ (vs[k.1]'(by omega))
            have hvertAt_inj : Function.Injective vertAt := by
              intro a b hab
              by_cases ha : a.1 = 0 <;> by_cases hb : b.1 = 0
              · exact Fin.ext (ha.trans hb.symm)
              · exfalso
                have haB : (vs[a.1]'(by omega)).1 ∉ A := (hB_iff _).mp (by simpa [ha] using hb0)
                have hbA : (vs[b.1]'(by omega)).1 ∈ A := hmid_A b.1 ⟨by omega, b.2⟩
                have h := congrArg Subtype.val hab
                simp [vertAt, toV₁, haB, hbA] at h
              · exfalso
                have haA : (vs[a.1]'(by omega)).1 ∈ A := hmid_A a.1 ⟨by omega, a.2⟩
                have hbB : (vs[b.1]'(by omega)).1 ∉ A := (hB_iff _).mp (by simpa [hb] using hb0)
                have h := congrArg Subtype.val hab
                simp [vertAt, toV₁, haA, hbB] at h
              · have haA := hmid_A a.1 ⟨by omega, a.2⟩
                have hbA := hmid_A b.1 ⟨by omega, b.2⟩
                have h := congrArg Subtype.val hab
                simp only [vertAt, toV₁, haA, hbA, ↓reduceDIte, Option.some.injEq, Subtype.mk.injEq] at h
                exact Fin.ext ((List.Nodup.getElem_inj_iff hnd).mp (Subtype.ext h))
            have hstep_Q1 : ∀ k : Fin m,
                let nxt : Fin m := ⟨(k.1 + 1) % m, Nat.mod_lt _ (by omega)⟩
                (Q₁.tail (edgeAt k) = vertAt k ∧ Q₁.head (edgeAt k) = vertAt nxt) ∨
                (Q₁.tail (edgeAt k) = vertAt nxt ∧ Q₁.head (edgeAt k) = vertAt k) := by
              intro k
              have hst := hstep k.1 (by omega)
              have htoV1_t : Q₁.tail (edgeAt k) = toV₁ (Q.tail ((e0 :: es')[k.1]'(by omega))) := by
                refine Subtype.ext ?_; dsimp only [Q₁, Q, Multigraph.deleteVertex, edgeAt, toE₁, toV₁, contractSide]
                by_cases h : Qplus.tail ((e0 :: es')[k.1]'(by omega)).1 ∈ A <;> simp [h]
              have htoV1_h : Q₁.head (edgeAt k) = toV₁ (Q.head ((e0 :: es')[k.1]'(by omega))) := by
                refine Subtype.ext ?_; dsimp only [Q₁, Q, Multigraph.deleteVertex, edgeAt, toE₁, toV₁, contractSide]
                by_cases h : Qplus.head ((e0 :: es')[k.1]'(by omega)).1 ∈ A <;> simp [h]
              have hnxt_eq : toV₁ (vs[k.1 + 1]'(by omega)) = vertAt ⟨(k.1 + 1) % m, Nat.mod_lt _ (by omega)⟩ := by
                by_cases hlast : k.1 + 1 = m
                · have hmod : (k.1 + 1) % m = 0 := by rw [hlast, Nat.mod_self]
                  have hkj : k.1 = j0 := by dsimp only [m] at hlast; omega
                  have hmB : (vs[k.1 + 1]'(by omega)).1 ∉ A := (hB_iff _).mp (by
                    have hidx : (vs[k.1 + 1]'(by omega)).1 = (vs[j0 + 1]'(by omega)).1 := by congr 1; simp [hkj]
                    rw [hidx]; exact hj0_B)
                  have h0B : (vs[0]'(by omega)).1 ∉ A := (hB_iff _).mp hb0
                  refine Subtype.ext ?_; simp [vertAt, toV₁, hmod, hmB, h0B]
                · have hmod : (k.1 + 1) % m = k.1 + 1 := Nat.mod_eq_of_lt (by omega)
                  simp [vertAt, hmod]
              rw [htoV1_t, htoV1_h]
              rcases hst with ⟨h1, h2⟩ | ⟨h1, h2⟩
              · left; rw [h1, h2, hnxt_eq]; exact ⟨rfl, rfl⟩
              · right; rw [h1, h2, hnxt_eq]; exact ⟨rfl, rfl⟩
            -- Build C₁ : Q₁.Subgraph on Finset.univ.image vertAt, Finset.univ.image edgeAt
            let C₁ : Q₁.Subgraph :=
              { verts := Finset.univ.image vertAt
                edges := Finset.univ.image edgeAt
                tail_mem := fun he => by
                  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp he
                  rcases hstep_Q1 k with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1] <;> exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
                head_mem := fun he => by
                  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp he
                  rcases hstep_Q1 k with ⟨_, h2⟩ | ⟨_, h2⟩ <;> rw [h2] <;> exact Finset.mem_image_of_mem _ (Finset.mem_univ _) }
            have hC₁_le : C₁ ≤ Multigraph.Subgraph.ofEdges Q₁ Finset.univ (Finset.univ \ wc₁.blue)
                (fun _ => Finset.mem_univ _) (fun _ => Finset.mem_univ _) := by
              refine ⟨fun _ _ => Finset.mem_univ _, fun e he => ?_⟩
              obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp he
              exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hedgeAt_red k⟩
            have hC₁_cyc : C₁.IsCycle := by
              refine ⟨⟨⟨vertAt ⟨0, by omega⟩, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩, ?_⟩, ?_⟩
              · have hreach0 : ∀ (t : ℕ) (ht : t < m), Relation.ReflTransGen C₁.Adj (vertAt ⟨0, by omega⟩) (vertAt ⟨t, ht⟩) := by
                  intro t
                  induction t with
                  | zero => intro _; exact .refl
                  | succ t iht =>
                    intro ht
                    have hst := hstep_Q1 ⟨t, by omega⟩
                    have hmod : (t + 1) % m = t + 1 := Nat.mod_eq_of_lt ht
                    have hst' : (Q₁.tail (edgeAt ⟨t, by omega⟩) = vertAt ⟨t, by omega⟩ ∧
                                 Q₁.head (edgeAt ⟨t, by omega⟩) = vertAt ⟨t + 1, ht⟩) ∨
                                (Q₁.tail (edgeAt ⟨t, by omega⟩) = vertAt ⟨t + 1, ht⟩ ∧
                                 Q₁.head (edgeAt ⟨t, by omega⟩) = vertAt ⟨t, by omega⟩) := by
                      simpa [hmod] using hst
                    exact (iht (by omega)).tail ⟨edgeAt ⟨t, by omega⟩, Finset.mem_image_of_mem _ (Finset.mem_univ _), hst'⟩
                have hsym : ∀ a b, Relation.ReflTransGen C₁.Adj a b → Relation.ReflTransGen C₁.Adj b a := fun a b h => by
                  induction h with
                  | refl => exact .refl
                  | tail _ hs ihs =>
                    rcases hs with ⟨x, hx, h1 | h1⟩
                    · exact Relation.ReflTransGen.head ⟨x, hx, Or.inr h1⟩ ihs
                    · exact Relation.ReflTransGen.head ⟨x, hx, Or.inl h1⟩ ihs
                intro u hu v hv
                obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hu
                obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hv
                exact (hsym _ _ (hreach0 a.1 a.2)).trans (hreach0 b.1 b.2)
              · -- Degree of vertAt k in C₁ is 2: incident edges are precisely edgeAt k and edgeAt (k - 1 mod m)!
                intro u hu
                obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hu
                let prev : Fin m := ⟨(k.1 + m - 1) % m, Nat.mod_lt _ (by omega)⟩
                have hprev_nxt : (prev.1 + 1) % m = k.1 := by
                  dsimp only [prev]
                  by_cases hk0 : k.1 = 0
                  · rw [hk0, zero_add, Nat.mod_eq_of_lt (by omega : m - 1 < m), show m - 1 + 1 = m by omega, Nat.mod_self]
                  · have h1 : (k.1 + m - 1) % m = k.1 - 1 := by
                      have : k.1 + m - 1 = (k.1 - 1) + m := by omega
                      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
                    rw [h1, show k.1 - 1 + 1 = k.1 by omega, Nat.mod_eq_of_lt k.2]
                have hprev_ne : prev ≠ k := by
                  intro h
                  have h' := hprev_nxt; rw [congrArg Fin.val h] at h'
                  have hlt : k.1 < m := k.2
                  by_cases hkm : k.1 + 1 = m
                  · rw [hkm, Nat.mod_self] at h'; omega
                  · rw [Nat.mod_eq_of_lt (by omega)] at h'; omega
                have hll_edge : ∀ r : Fin m, Q₁.tail (edgeAt r) ≠ Q₁.head (edgeAt r) := fun r h => by
                  rcases hstep_Q1 r with ⟨h1, h2⟩ | ⟨h1, h2⟩
                  · have hval : r.1 = (r.1 + 1) % m := congrArg Fin.val (hvertAt_inj (h1.symm.trans (h.trans h2)))
                    by_cases hr : r.1 + 1 = m
                    · rw [hr, Nat.mod_self] at hval; omega
                    · rw [Nat.mod_eq_of_lt (by omega)] at hval; omega
                  · have hval : r.1 = (r.1 + 1) % m := congrArg Fin.val (hvertAt_inj (h2.symm.trans (h.symm.trans h1)))
                    by_cases hr : r.1 + 1 = m
                    · rw [hr, Nat.mod_self] at hval; omega
                    · rw [Nat.mod_eq_of_lt (by omega)] at hval; omega
                have hinc_iff : ∀ r : Fin m, (Q₁.tail (edgeAt r) = vertAt k ∨ Q₁.head (edgeAt r) = vertAt k) ↔ (r = k ∨ r = prev) := by
                  intro r
                  constructor
                  · intro hor
                    rcases hstep_Q1 r with ⟨h1, h2⟩ | ⟨h1, h2⟩
                    · rcases hor with h | h
                      · exact Or.inl (hvertAt_inj (h1.symm.trans h))
                      · right; have heq : (r.1 + 1) % m = k.1 := congrArg Fin.val (hvertAt_inj (h2.symm.trans h))
                        refine Fin.ext ?_; dsimp only [prev]
                        by_cases hr : r.1 + 1 = m
                        · rw [hr, Nat.mod_self] at heq; rw [← heq, zero_add, Nat.mod_eq_of_lt (by omega : m - 1 < m)]; omega
                        · rw [Nat.mod_eq_of_lt (by omega)] at heq
                          rw [← heq, show r.1 + 1 + m - 1 = r.1 + m by omega, Nat.add_mod_right, Nat.mod_eq_of_lt r.2]
                    · rcases hor with h | h
                      · right; have heq : (r.1 + 1) % m = k.1 := congrArg Fin.val (hvertAt_inj (h1.symm.trans h))
                        refine Fin.ext ?_; dsimp only [prev]
                        by_cases hr : r.1 + 1 = m
                        · rw [hr, Nat.mod_self] at heq; rw [← heq, zero_add, Nat.mod_eq_of_lt (by omega : m - 1 < m)]; omega
                        · rw [Nat.mod_eq_of_lt (by omega)] at heq
                          rw [← heq, show r.1 + 1 + m - 1 = r.1 + m by omega, Nat.add_mod_right, Nat.mod_eq_of_lt r.2]
                      · exact Or.inl (hvertAt_inj (h2.symm.trans h))
                  · intro hor; rcases hor with rfl | rfl
                    · rcases hstep_Q1 r with ⟨h1, _⟩ | ⟨_, h2⟩; exact Or.inl h1; exact Or.inr h2
                    · have hnxt : (⟨(prev.1 + 1) % m, Nat.mod_lt _ (by omega)⟩ : Fin m) = k := Fin.ext hprev_nxt
                      rcases hstep_Q1 prev with ⟨_, h2⟩ | ⟨h1, _⟩
                      · right; rw [hnxt] at h2; exact h2
                      · left; rw [hnxt] at h1; exact h1
                unfold Multigraph.Subgraph.deg
                have hdisj : Disjoint (C₁.edges.filter (fun e => Q₁.tail e = vertAt k))
                    (C₁.edges.filter (fun e => Q₁.head e = vertAt k)) := by
                  rw [Finset.disjoint_left]; intro e ht hh
                  obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp ht).1
                  exact hll_edge r ((Finset.mem_filter.mp ht).2.trans (Finset.mem_filter.mp hh).2.symm)
                rw [← Finset.card_union_of_disjoint hdisj]
                have hun : C₁.edges.filter (fun e => Q₁.tail e = vertAt k) ∪
                    C₁.edges.filter (fun e => Q₁.head e = vertAt k) = {edgeAt k, edgeAt prev} := by
                  ext e; simp only [C₁, Finset.mem_union, Finset.mem_filter, Finset.mem_image, Finset.mem_univ,
                    true_and, Finset.mem_insert, Finset.mem_singleton]
                  constructor
                  · rintro (⟨⟨r, rfl⟩, ht⟩ | ⟨⟨r, rfl⟩, hh⟩)
                    · rcases (hinc_iff r).mp (Or.inl ht) with rfl | rfl; exact Or.inl rfl; exact Or.inr rfl
                    · rcases (hinc_iff r).mp (Or.inr hh) with rfl | rfl; exact Or.inl rfl; exact Or.inr rfl
                  · rintro (rfl | rfl)
                    · rcases (hinc_iff k).mpr (Or.inl rfl) with h | h
                      · exact Or.inl ⟨⟨k, rfl⟩, h⟩
                      · exact Or.inr ⟨⟨k, rfl⟩, h⟩
                    · rcases (hinc_iff prev).mpr (Or.inr rfl) with h | h
                      · exact Or.inl ⟨⟨prev, rfl⟩, h⟩
                      · exact Or.inr ⟨⟨prev, rfl⟩, h⟩
                rw [hun, Finset.card_pair (fun h => hprev_ne (hedgeAt_inj h).symm)]
            exact hR1_forest C₁ hC₁_le hC₁_cyc
    -- Finish hφ_inj from hpath_B
    intro q1 q2 heq
    obtain ⟨u1, rfl⟩ := Quotient.exists_rep q1
    obtain ⟨u2, rfl⟩ := Quotient.exists_rep q2
    have hrel : Relation.ReflTransGen (redAdj Q blue) (embV₂ u1) (embV₂ u2) := Quotient.exact heq
    have hrelRQ : Relation.ReflTransGen RQ.Adj (embV₂ u1) (embV₂ u2) := by
      have hgo : ∀ x y, Relation.ReflTransGen (redAdj Q blue) x y → Relation.ReflTransGen RQ.Adj x y := fun x y h => by
        induction h with
        | refl => exact .refl
        | tail _ hs ih => rcases hs with ⟨e, heR, hinc⟩; exact ih.tail ⟨e, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, heR⟩, hinc⟩
      exact hgo _ _ hrel
    obtain ⟨vs, es, hlen, hnd, hhd, hlst, hes, hstep⟩ := exists_simplePath_of_reflTransGen hrelRQ
    have h0 : vs[0]'(by omega) = embV₂ u1 := by
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega), Option.some.injEq] at hhd; exact hhd
    have hl : vs[es.length]'(by omega) = embV₂ u2 := by
      rw [List.getLast?_eq_getElem?, show vs.length - 1 = es.length by omega,
          List.getElem?_eq_getElem (by omega), Option.some.injEq] at hlst; exact hlst
    have hb0 : (vs[0]'(by omega)).1 ∈ B := h0 ▸ hembV₂_B u1
    have hbl : (vs[es.length]'(by omega)).1 ∈ B := hl ▸ hembV₂_B u2
    have hres := hpath_B es.length vs es rfl hlen hnd hes hstep hb0 hbl
    have hu1_eq : (⟨some ⟨(vs[0]'(by omega)).1, hb0⟩, by simp⟩ : {u : Option {v : V // v ∈ B} // u ≠ none}) = u1 := by
      cases hu : u1.1 with
      | none => exact absurd hu u1.2
      | some b =>
        refine Subtype.ext ?_; dsimp only; rw [hu]; congr 1; apply Subtype.ext
        exact (congrArg Subtype.val h0).trans (hembV₂_some u1 b hu)
    have hu2_eq : (⟨some ⟨(vs[es.length]'(by omega)).1, hbl⟩, by simp⟩ : {u : Option {v : V // v ∈ B} // u ≠ none}) = u2 := by
      cases hu : u2.1 with
      | none => exact absurd hu u2.2
      | some b =>
        refine Subtype.ext ?_; dsimp only; rw [hu]; congr 1; apply Subtype.ext
        exact (congrArg Subtype.val hl).trans (hembV₂_some u2 b hu)
    rw [hu1_eq, hu2_eq] at hres
    exact Quotient.sound hres
  -- Now define ψ : Q / red → Q₁ / red₁ and apply twoConstr_subst!
  let projV₁ (u : {u : V // u ≠ v₀}) : {u : Option {v : V // v ∈ A} // u ≠ some ⟨v₀, hv₀A⟩} :=
    if h : u.1 ∈ A then ⟨some ⟨u.1, h⟩, fun heq => u.2 (val_eq_of_some_eq (heq))⟩
    else ⟨none, by simp⟩
  let ψ : Quotient (redSetoid Q blue) → Quotient (redSetoid Q₁ wc₁.blue) :=
    Quotient.lift (fun u => Quotient.mk (redSetoid Q₁ wc₁.blue) (projV₁ u)) (fun a b hab => by
      apply Quotient.sound
      induction hab with
      | refl => exact .refl
      | @tail x y _ hs ih =>
        rcases hs with ⟨e, heR, hinc⟩
        by_cases hB : Qplus.tail e.1 ∈ B ∧ Qplus.head e.1 ∈ B
        · have hxA : x.1 ∉ A := by
            rcases hinc with ⟨h1, _⟩ | ⟨_, h2⟩
            · exact (hB_iff _).mp (congrArg Subtype.val h1 ▸ hB.1)
            · exact (hB_iff _).mp (congrArg Subtype.val h2 ▸ hB.2)
          have hyA : y.1 ∉ A := by
            rcases hinc with ⟨_, h2⟩ | ⟨h1, _⟩
            · exact (hB_iff _).mp (congrArg Subtype.val h2 ▸ hB.2)
            · exact (hB_iff _).mp (congrArg Subtype.val h1 ▸ hB.1)
          have hxy : projV₁ x = projV₁ y := by simp [projV₁, hxA, hyA]
          rw [← hxy]; exact ih
        · have he1R : toE₁ e hB ∉ wc₁.blue := fun hm =>
            heR (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [dif_neg hB]; exact hm⟩)
          refine ih.tail ⟨toE₁ e hB, he1R, ?_⟩
          have ht : Q₁.tail (toE₁ e hB) = projV₁ (Q.tail e) := by
            refine Subtype.ext ?_; dsimp only [Q₁, Q, Multigraph.deleteVertex, toE₁, projV₁, contractSide]; split_ifs <;> rfl
          have hh : Q₁.head (toE₁ e hB) = projV₁ (Q.head e) := by
            refine Subtype.ext ?_; dsimp only [Q₁, Q, Multigraph.deleteVertex, toE₁, projV₁, contractSide]; split_ifs <;> rfl
          rw [ht, hh]
          rcases hinc with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inl ⟨congrArg projV₁ h1, congrArg projV₁ h2⟩
          · exact Or.inr ⟨congrArg projV₁ h1, congrArg projV₁ h2⟩)
  let w₀ : Quotient (redSetoid Q₁ wc₁.blue) := Quotient.mk _ ⟨none, by simp⟩
  let W_sub : Finset (Quotient (redSetoid Q blue)) := Finset.univ.image φ
  have hψ_sub : ∀ q : Quotient (redSetoid Q blue), q ∈ W_sub ↔ ψ q = w₀ := by
    intro q
    constructor
    · intro hq
      obtain ⟨q₂, _, rfl⟩ := Finset.mem_image.mp hq
      obtain ⟨u₂, rfl⟩ := Quotient.exists_rep q₂
      have hnb : (embV₂ u₂).1 ∉ A := (hB_iff _).mp (hembV₂_B u₂)
      simp [ψ, φ, projV₁, hnb, w₀]
    · intro hq
      obtain ⟨u, rfl⟩ := Quotient.exists_rep q
      by_cases huB : u.1 ∈ B
      · refine Finset.mem_image.mpr ⟨Quotient.mk _ ⟨some ⟨u.1, huB⟩, by simp⟩, Finset.mem_univ _, ?_⟩
        simp [φ, embV₂]
      · have huA : u.1 ∈ A := by rwa [hB_iff, not_not] at huB
        have hrel : Relation.ReflTransGen (redAdj Q₁ wc₁.blue) (projV₁ u) ⟨none, by simp⟩ := Quotient.exact hq
        -- Lift walk in Q₁ from projV₁ u to none until first hit of none -> reaches some b ∈ B in red(Q)!
        have hliftR : ∀ x y : {u : Option {v : V // v ∈ A} // u ≠ some ⟨v₀, hv₀A⟩},
            Relation.ReflTransGen (redAdj Q₁ wc₁.blue) x y →
            ∀ (x' : {u : V // u ≠ v₀}) (hxA : x'.1 ∈ A), x.1 = some ⟨x'.1, hxA⟩ →
            (y.1 = none → ∃ b : {u : V // u ≠ v₀}, b.1 ∈ B ∧ Relation.ReflTransGen (redAdj Q blue) x' b) ∧
            (∀ (y' : {u : V // u ≠ v₀}) (hyA : y'.1 ∈ A), y.1 = some ⟨y'.1, hyA⟩ →
              Relation.ReflTransGen (redAdj Q blue) x' y' ∨
              ∃ b : {u : V // u ≠ v₀}, b.1 ∈ B ∧ Relation.ReflTransGen (redAdj Q blue) x' b) := by
          intro x y hxy
          induction hxy with
          | refl =>
            intro x' hxA hx'
            refine ⟨fun hy => by rw [hx'] at hy; simp at hy, fun y' hyA hy' => Or.inl ?_⟩
            have : x' = y' := Subtype.ext (by have h_tmp := Option.some.inj (hx'.symm.trans hy'); rw [Subtype.ext_iff] at h_tmp; exact h_tmp)
            rw [this]
          | @tail p q _ hs ih =>
            intro x' hxA hx'
            have hih := ih x' hxA hx'
            cases hp : p.1 with
            | none => exact ⟨fun _ => hih.1 hp, fun _ _ _ => Or.inr (hih.1 hp)⟩
            | some ap =>
              have hap0 : ap.1 ≠ v₀ := fun h => p.2 (hp.trans (congrArg some (Subtype.ext h)))
              let p' : {u : V // u ≠ v₀} := ⟨ap.1, hap0⟩
              rcases hih.2 p' ap.2 hp with hxp | hxb
              · rcases hs with ⟨e₁, he₁R, hinc⟩
                have hnt0 : Qplus.tail e₁.1.1 ≠ v₀ := fun h =>
                  e₁.2.1 (by dsimp only [contractSide]; rw [dif_pos (by rw [h]; exact hv₀A)]; exact congrArg some (Subtype.ext h))
                have hnh0 : Qplus.head e₁.1.1 ≠ v₀ := fun h =>
                  e₁.2.2 (by dsimp only [contractSide]; rw [dif_pos (by rw [h]; exact hv₀A)]; exact congrArg some (Subtype.ext h))
                let eQ : {e : E // Qplus.tail e ≠ v₀ ∧ Qplus.head e ≠ v₀} := ⟨e₁.1.1, hnt0, hnh0⟩
                have hnotB : ¬ (Qplus.tail eQ.1 ∈ B ∧ Qplus.head eQ.1 ∈ B) := (hnotB_iff eQ).mpr e₁.1.2
                have heQ_R : eQ ∉ blue := fun hm => by
                  have h := (Finset.mem_filter.mp hm).2; rw [dif_neg hnotB] at h; exact he₁R h
                refine ⟨fun hq => ?_, fun y' hyA hy' => Or.inl ?_⟩
                · rcases hinc with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
                  · have ht := congrArg Subtype.val h1'; have hh := congrArg Subtype.val h2'
                    dsimp only [Q₁, Multigraph.deleteVertex, contractSide] at ht hh; rw [hp] at ht; rw [hq] at hh
                    have htA : Qplus.tail e₁.1.1 ∈ A := by by_contra h; rw [dif_neg h] at ht; simp at ht
                    have hhB : Qplus.head e₁.1.1 ∈ B := by rw [hB_iff]; intro h; rw [dif_pos h] at hh; simp at hh
                    rw [dif_pos htA] at ht
                    exact ⟨Q.head eQ, hhB, hxp.tail ⟨eQ, heQ_R, Or.inl ⟨Subtype.ext (by have h_tmp := Option.some.inj (ht); rw [Subtype.ext_iff] at h_tmp; exact h_tmp), rfl⟩⟩⟩
                  · have ht := congrArg Subtype.val h1'; have hh := congrArg Subtype.val h2'
                    dsimp only [Q₁, Multigraph.deleteVertex, contractSide] at ht hh; rw [hq] at ht; rw [hp] at hh
                    have hhA : Qplus.head e₁.1.1 ∈ A := by by_contra h; rw [dif_neg h] at hh; simp at hh
                    have htB : Qplus.tail e₁.1.1 ∈ B := by rw [hB_iff]; intro h; rw [dif_pos h] at ht; simp at ht
                    rw [dif_pos hhA] at hh
                    exact ⟨Q.tail eQ, htB, hxp.tail ⟨eQ, heQ_R, Or.inr ⟨rfl, Subtype.ext (by have h_tmp := Option.some.inj (hh); rw [Subtype.ext_iff] at h_tmp; exact h_tmp)⟩⟩⟩
                · rcases hinc with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
                  · have ht := congrArg Subtype.val h1'; have hh := congrArg Subtype.val h2'
                    dsimp only [Q₁, Multigraph.deleteVertex, contractSide] at ht hh; rw [hp] at ht; rw [hy'] at hh
                    have htA : Qplus.tail e₁.1.1 ∈ A := by by_contra h; rw [dif_neg h] at ht; simp at ht
                    have hhA : Qplus.head e₁.1.1 ∈ A := by by_contra h; rw [dif_neg h] at hh; simp at hh
                    rw [dif_pos htA] at ht; rw [dif_pos hhA] at hh
                    exact hxp.tail ⟨eQ, heQ_R, Or.inl ⟨Subtype.ext (by have h_tmp := Option.some.inj (ht); rw [Subtype.ext_iff] at h_tmp; exact h_tmp),
                      Subtype.ext (by have h_tmp := Option.some.inj (hh); rw [Subtype.ext_iff] at h_tmp; exact h_tmp)⟩⟩
                  · have ht := congrArg Subtype.val h1'; have hh := congrArg Subtype.val h2'
                    dsimp only [Q₁, Multigraph.deleteVertex, contractSide] at ht hh; rw [hy'] at ht; rw [hp] at hh
                    have htA : Qplus.tail e₁.1.1 ∈ A := by by_contra h; rw [dif_neg h] at ht; simp at ht
                    have hhA : Qplus.head e₁.1.1 ∈ A := by by_contra h; rw [dif_neg h] at hh; simp at hh
                    rw [dif_pos htA] at ht; rw [dif_pos hhA] at hh
                    exact hxp.tail ⟨eQ, heQ_R, Or.inr ⟨Subtype.ext (by have h_tmp := Option.some.inj (ht); rw [Subtype.ext_iff] at h_tmp; exact h_tmp),
                      Subtype.ext (by have h_tmp := Option.some.inj (hh); rw [Subtype.ext_iff] at h_tmp; exact h_tmp)⟩⟩
              · exact ⟨fun _ => hxb, fun _ _ _ => Or.inr hxb⟩
        obtain ⟨b, hbB, hrb⟩ := (hliftR _ _ hrel u huA (by simp [projV₁, huA])).1 rfl
        refine Finset.mem_image.mpr ⟨Quotient.mk _ ⟨some ⟨b.1, hbB⟩, by simp⟩, Finset.mem_univ _, ?_⟩
        have hb_eq : embV₂ ⟨some ⟨b.1, hbB⟩, by simp⟩ = b := Subtype.ext (hembV₂_some ⟨some ⟨b.1, hbB⟩, by simp⟩ ⟨b.1, hbB⟩ rfl)
        exact Quotient.sound ((redSetoid Q blue).symm (hb_eq.symm ▸ hrb))
  -- Outside w₀, ψ has an explicit inverse inv!
  have hψ_surj : ∀ q₁ : Quotient (redSetoid Q₁ wc₁.blue), q₁ ≠ w₀ → ∃ q : Quotient (redSetoid Q blue), ψ q = q₁ := by
    intro q₁ hne
    obtain ⟨x, rfl⟩ := Quotient.exists_rep q₁
    cases hx : x.1 with
    | none => exact absurd (congrArg (Quotient.mk _) (Subtype.ext hx)) hne
    | some a =>
      have ha0 : a.1 ≠ v₀ := fun h => x.2 (hx.trans (congrArg some (Subtype.ext h)))
      refine ⟨Quotient.mk _ ⟨a.1, ha0⟩, ?_⟩
      apply congrArg (Quotient.mk _); refine Subtype.ext ?_; simp [projV₁, a.2, hx]
  have hψ_inj_out : ∀ q a : Quotient (redSetoid Q blue), ψ q ≠ w₀ → ψ q = ψ a → q = a := by
    intro q a hne heq
    obtain ⟨u, rfl⟩ := Quotient.exists_rep q
    obtain ⟨v, rfl⟩ := Quotient.exists_rep a
    have huA : u.1 ∈ A := by by_contra h; exact hne (by simp [ψ, projV₁, h, w₀])
    have hvA : v.1 ∈ A := by by_contra h; exact hne (heq.trans (by simp [ψ, projV₁, h, w₀]))
    have hrel : Relation.ReflTransGen (redAdj Q₁ wc₁.blue) (projV₁ u) (projV₁ v) := Quotient.exact heq
    -- Reuse the walk lift: since ψ ⟦u⟧ ≠ w₀, no vertex on the walk can be none!
    have hlift_no_none : ∀ x y : {u : Option {v : V // v ∈ A} // u ≠ some ⟨v₀, hv₀A⟩},
        Relation.ReflTransGen (redAdj Q₁ wc₁.blue) x y →
        ∀ (x' : {u : V // u ≠ v₀}) (hxA : x'.1 ∈ A), x.1 = some ⟨x'.1, hxA⟩ →
        Quotient.mk (redSetoid Q₁ wc₁.blue) x ≠ w₀ →
        ∀ (y' : {u : V // u ≠ v₀}) (hyA : y'.1 ∈ A), y.1 = some ⟨y'.1, hyA⟩ →
        Relation.ReflTransGen (redAdj Q blue) x' y' := by
      intro x y hxy
      induction hxy with
      | refl =>
        intro x' hxA hx' _ y' hyA hy'
        have : x' = y' := Subtype.ext (by have h_tmp := Option.some.inj (hx'.symm.trans hy'); rw [Subtype.ext_iff] at h_tmp; exact h_tmp)
        rw [this]
      | @tail p q _ hs ih =>
        intro x' hxA hx' hne_w0 y' hyA hy'
        cases hp : p.1 with
        | none =>
          have hxp : Quotient.mk (redSetoid Q₁ wc₁.blue) x = w₀ :=
            (Quotient.sound (by assumption)).trans (congrArg (Quotient.mk _) (Subtype.ext hp))
          exact absurd hxp hne_w0
        | some ap =>
          have hap0 : ap.1 ≠ v₀ := fun h => p.2 (hp.trans (congrArg some (Subtype.ext h)))
          let p' : {u : V // u ≠ v₀} := ⟨ap.1, hap0⟩
          have hprev := ih x' hxA hx' hne_w0 p' ap.2 hp
          rcases hs with ⟨e₁, he₁R, hinc⟩
          have hnt0 : Qplus.tail e₁.1.1 ≠ v₀ := fun h =>
            e₁.2.1 (by dsimp only [contractSide]; rw [dif_pos (by rw [h]; exact hv₀A)]; exact congrArg some (Subtype.ext h))
          have hnh0 : Qplus.head e₁.1.1 ≠ v₀ := fun h =>
            e₁.2.2 (by dsimp only [contractSide]; rw [dif_pos (by rw [h]; exact hv₀A)]; exact congrArg some (Subtype.ext h))
          let eQ : {e : E // Qplus.tail e ≠ v₀ ∧ Qplus.head e ≠ v₀} := ⟨e₁.1.1, hnt0, hnh0⟩
          have hnotB : ¬ (Qplus.tail eQ.1 ∈ B ∧ Qplus.head eQ.1 ∈ B) := (hnotB_iff eQ).mpr e₁.1.2
          have heQ_R : eQ ∉ blue := fun hm => by
            have h := (Finset.mem_filter.mp hm).2; rw [dif_neg hnotB] at h; exact he₁R h
          rcases hinc with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
          · have ht := congrArg Subtype.val h1'; have hh := congrArg Subtype.val h2'
            dsimp only [Q₁, Multigraph.deleteVertex, contractSide] at ht hh; rw [hp] at ht; rw [hy'] at hh
            have htA : Qplus.tail e₁.1.1 ∈ A := by by_contra h; rw [dif_neg h] at ht; simp at ht
            have hhA : Qplus.head e₁.1.1 ∈ A := by by_contra h; rw [dif_neg h] at hh; simp at hh
            rw [dif_pos htA] at ht; rw [dif_pos hhA] at hh
            exact hprev.tail ⟨eQ, heQ_R, Or.inl ⟨Subtype.ext (by have h_tmp := Option.some.inj (ht); rw [Subtype.ext_iff] at h_tmp; exact h_tmp),
              Subtype.ext (by have h_tmp := Option.some.inj (hh); rw [Subtype.ext_iff] at h_tmp; exact h_tmp)⟩⟩
          · have ht := congrArg Subtype.val h1'; have hh := congrArg Subtype.val h2'
            dsimp only [Q₁, Multigraph.deleteVertex, contractSide] at ht hh; rw [hy'] at ht; rw [hp] at hh
            have htA : Qplus.tail e₁.1.1 ∈ A := by by_contra h; rw [dif_neg h] at ht; simp at ht
            have hhA : Qplus.head e₁.1.1 ∈ A := by by_contra h; rw [dif_neg h] at hh; simp at hh
            rw [dif_pos htA] at ht; rw [dif_pos hhA] at hh
            exact hprev.tail ⟨eQ, heQ_R, Or.inr ⟨Subtype.ext (by have h_tmp := Option.some.inj (ht); rw [Subtype.ext_iff] at h_tmp; exact h_tmp),
              Subtype.ext (by have h_tmp := Option.some.inj (hh); rw [Subtype.ext_iff] at h_tmp; exact h_tmp)⟩⟩
    exact Quotient.sound (hlift_no_none _ _ hrel u huA (by simp [projV₁, huA]) hne v hvA (by simp [projV₁, hvA]))
  -- Embed blue₂ and blue₁ into {e // e ∈ blue}
  let embF₂ : {e // e ∈ wc₂.blue} ↪ {e // e ∈ blue} :=
    { toFun := fun e₂ =>
        have htB : Qplus.tail e₂.1.1.1 ∈ B := by by_contra h; exact e₂.1.2.1 (by dsimp only [contractSide]; rw [dif_neg h])
        have hhB : Qplus.head e₂.1.1.1 ∈ B := by by_contra h; exact e₂.1.2.2 (by dsimp only [contractSide]; rw [dif_neg h])
        have hnt0 : Qplus.tail e₂.1.1.1 ≠ v₀ := fun h => (hB_iff _).mp htB (h.symm ▸ hv₀A)
        have hnh0 : Qplus.head e₂.1.1.1 ≠ v₀ := fun h => (hB_iff _).mp hhB (h.symm ▸ hv₀A)
        ⟨⟨e₂.1.1.1, hnt0, hnh0⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [dif_pos ⟨htB, hhB⟩]; exact e₂.2⟩⟩
      inj' := fun a b h => Subtype.ext (Subtype.ext (Subtype.ext (congrArg (fun x => x.1.1) h))) }
  let embF₁ : {e // e ∈ wc₁.blue} ↪ {e // e ∈ blue} :=
    { toFun := fun e₁ =>
        have hnt0 : Qplus.tail e₁.1.1.1 ≠ v₀ := fun h =>
          e₁.1.2.1 (by dsimp only [contractSide]; rw [dif_pos (by rw [h]; exact hv₀A)]; exact congrArg some (Subtype.ext h))
        have hnh0 : Qplus.head e₁.1.1.1 ≠ v₀ := fun h =>
          e₁.1.2.2 (by dsimp only [contractSide]; rw [dif_pos (by rw [h]; exact hv₀A)]; exact congrArg some (Subtype.ext h))
        have hnotB : ¬ (Qplus.tail e₁.1.1.1 ∈ B ∧ Qplus.head e₁.1.1.1 ∈ B) :=
          (hnotB_iff ⟨e₁.1.1.1, hnt0, hnh0⟩).mpr e₁.1.1.2
        ⟨⟨e₁.1.1.1, hnt0, hnh0⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [dif_neg hnotB]; exact e₁.2⟩⟩
      inj' := fun a b h => Subtype.ext (Subtype.ext (Subtype.ext (congrArg (fun x => x.1.1) h))) }
  -- Map wc₂.twoConstr into Q / red on (W_sub, F_sub)!
  let F_sub : Finset {e // e ∈ blue} := Finset.univ.map embF₂
  have htc_sub : TwoConstruction (redQuotient Q blue) W_sub F_sub := by
    -- Build via structural recursion on wc₂.twoConstr using φ (injective!) and embF₂
    have hgo : ∀ {Wa : Finset (Quotient (redSetoid Q₂ wc₂.blue))} {Fa : Finset {e // e ∈ wc₂.blue}},
        TwoConstruction (redQuotient Q₂ wc₂.blue) Wa Fa →
        TwoConstruction (redQuotient Q blue) (Wa.image φ) (Fa.map embF₂) := by
      intro Wa Fa tc
      induction tc with
      | single w =>
        simpa [Finset.image_singleton, Finset.map_empty] using TwoConstruction.single (M := redQuotient Q blue) (φ w)
      | @join Wa Wb Fa Fb _ _ e f hdisjW hdisjF he_ne_f he1 he2 hf1 hf2 he_cr hf_cr ihl ihr =>
        rw [Finset.image_union, Finset.map_insert, Finset.map_insert, Finset.map_union]
        have hdisjW' : Disjoint (Wa.image φ) (Wb.image φ) := by
          rw [Finset.disjoint_left]; intro x hx1 hx2
          obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx1
          obtain ⟨b, hb, hab⟩ := Finset.mem_image.mp hx2
          exact Finset.disjoint_left.mp hdisjW ha (hφ_inj hab ▸ hb)
        have hend2 : ∀ g : {e // e ∈ wc₂.blue},
            (redQuotient Q blue).tail (embF₂ g) = φ ((redQuotient Q₂ wc₂.blue).tail g) ∧
            (redQuotient Q blue).head (embF₂ g) = φ ((redQuotient Q₂ wc₂.blue).head g) := fun g => by
          have htB : Qplus.tail g.1.1.1 ∈ B := by by_contra h; exact g.1.2.1 (by dsimp only [contractSide]; rw [dif_neg h])
          have hhB : Qplus.head g.1.1.1 ∈ B := by by_contra h; exact g.1.2.2 (by dsimp only [contractSide]; rw [dif_neg h])
          constructor <;> (dsimp only [redQuotient, φ, embF₂]; apply congrArg (Quotient.mk _); refine Subtype.ext ?_)
          · dsimp only [Q, Q₂, Multigraph.deleteVertex]
            exact (hembV₂_some _ ⟨Qplus.tail g.1.1.1, htB⟩ (by dsimp only [contractSide]; rw [dif_pos htB])).symm
          · dsimp only [Q, Q₂, Multigraph.deleteVertex]
            exact (hembV₂_some _ ⟨Qplus.head g.1.1.1, hhB⟩ (by dsimp only [contractSide]; rw [dif_pos hhB])).symm
        refine TwoConstruction.join ihl ihr (embF₂ e) (embF₂ f) hdisjW'
          (disjoint_map_of_disjoint _ hdisjF) (fun h => he_ne_f (embF₂.injective h))
          (by simp [he1]) (by simp [he2]) (by simp [hf1]) (by simp [hf2]) ?_ ?_
        · rcases he_cr with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · left; rw [(hend2 e).1, (hend2 e).2]; exact ⟨Finset.mem_image_of_mem _ h1, Finset.mem_image_of_mem _ h2⟩
          · right; rw [(hend2 e).1, (hend2 e).2]; exact ⟨Finset.mem_image_of_mem _ h1, Finset.mem_image_of_mem _ h2⟩
        · rcases hf_cr with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · left; rw [(hend2 f).1, (hend2 f).2]; exact ⟨Finset.mem_image_of_mem _ h1, Finset.mem_image_of_mem _ h2⟩
          · right; rw [(hend2 f).1, (hend2 f).2]; exact ⟨Finset.mem_image_of_mem _ h1, Finset.mem_image_of_mem _ h2⟩
    exact hgo wc₂.twoConstr
  -- Now apply twoConstr_subst to wc₁.twoConstr and htc_sub!
  let inv (w₁ : Quotient (redSetoid Q₁ wc₁.blue)) (h : w₁ ≠ w₀) : Quotient (redSetoid Q blue) :=
    (hψ_surj w₁ h).choose
  have htc_full := twoConstr_subst w₀ W_sub F_sub htc_sub ψ inv hψ_sub
    (fun w₁ h => (hψ_surj w₁ h).choose_spec)
    (fun w h => hψ_inj_out _ _ (by rw [(hψ_surj (ψ w) h).choose_spec]; exact h) (hψ_surj (ψ w) h).choose_spec)
    embF₁
    (fun f₁ hm => by
      obtain ⟨f₂, _, hf12⟩ := Finset.mem_map.mp hm
      have heq : f₂.1.1.1 = f₁.1.1.1 := congrArg (fun x => x.1.1) hf12
      have htB : Qplus.tail f₂.1.1.1 ∈ B := by by_contra h; exact f₂.1.2.1 (by dsimp only [contractSide]; rw [dif_neg h])
      have hhB : Qplus.head f₂.1.1.1 ∈ B := by by_contra h; exact f₂.1.2.2 (by dsimp only [contractSide]; rw [dif_neg h])
      rw [heq] at htB hhB
      rcases f₁.1.1.2 with htA | hhA
      · exact (hB_iff _).mp htB htA
      · exact (hB_iff _).mp hhB hhA)
    (fun f₁ => Or.inl (by
      constructor <;> (dsimp only [redQuotient, ψ]; apply congrArg (Quotient.mk _); refine Subtype.ext ?_)
      · change (if h : Qplus.tail f₁.1.1.1 ∈ A then
            (⟨some ⟨Qplus.tail f₁.1.1.1, h⟩, _⟩ : {u : Option {v : V // v ∈ A} // u ≠ some ⟨v₀, hv₀A⟩})
          else ⟨none, by simp⟩).1 =
          if h : Qplus.tail f₁.1.1.1 ∈ A then some ⟨Qplus.tail f₁.1.1.1, h⟩ else none
        by_cases h : Qplus.tail f₁.1.1.1 ∈ A
        · rw [dif_pos h, dif_pos h]
        · rw [dif_neg h, dif_neg h]
      · change (if h : Qplus.head f₁.1.1.1 ∈ A then
            (⟨some ⟨Qplus.head f₁.1.1.1, h⟩, _⟩ : {u : Option {v : V // v ∈ A} // u ≠ some ⟨v₀, hv₀A⟩})
          else ⟨none, by simp⟩).1 =
          if h : Qplus.head f₁.1.1.1 ∈ A then some ⟨Qplus.head f₁.1.1.1, h⟩ else none
        by_cases h : Qplus.head f₁.1.1.1 ∈ A
        · rw [dif_pos h, dif_pos h]
        · rw [dif_neg h, dif_neg h]))
    wc₁.twoConstr
  have hW_univ : Finset.univ.filter (fun w : Quotient (redSetoid Q blue) => ψ w ∈ (Finset.univ : Finset _)) = Finset.univ := by
    ext w; simp
  have hF_univ : (if w₀ ∈ (Finset.univ : Finset _) then F_sub ∪ Finset.univ.map embF₁ else Finset.univ.map embF₁) = Finset.univ := by
    rw [if_pos (Finset.mem_univ _)]
    ext ⟨e, he⟩; simp only [F_sub, Finset.mem_union, Finset.mem_map, Finset.mem_univ, true_and, iff_true]
    by_cases hB : Qplus.tail e.1 ∈ B ∧ Qplus.head e.1 ∈ B
    · left
      have he2 : toE₂ e hB ∈ wc₂.blue := by have h := (Finset.mem_filter.mp he).2; rwa [dif_pos hB] at h
      exact ⟨⟨toE₂ e hB, he2⟩, Subtype.ext (Subtype.ext rfl)⟩
    · right
      have he1 : toE₁ e hB ∈ wc₁.blue := by have h := (Finset.mem_filter.mp he).2; rwa [dif_neg hB] at h
      exact ⟨⟨toE₁ e hB, he1⟩, Subtype.ext (Subtype.ext rfl)⟩
  rw [hW_univ, hF_univ] at htc_full
  exact ⟨{ blue := blue, blue_tree := hT_tree, twoConstr := htc_full }⟩

-- Part 6: Growing (Case 2) + main theorem `jlpt_wellColouring_proved`

/-! ### Part 6: Growing (`wellColouring_growing`, Case 2: no non-trivial 3-edge-cut) -/

/-- A cubic simple graph on `≥ 6` vertices with no non-trivial `3`-edge-cut is triangle-free. -/
lemma cubic_no_nontrivial_3cut_triangle_free {V E : Type} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (G : Multigraph V E) (hcub : G.IsCubic) (h6 : 6 ≤ Fintype.card V)
    (hno3 : ∀ S : Finset V, 2 ≤ S.card → 2 ≤ (Finset.univ \ S).card → 4 ≤ (G.cutEdges S).card)
    {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (e1 e2 e3 : E)
    (he1 : (G.tail e1 = a ∧ G.head e1 = b) ∨ (G.tail e1 = b ∧ G.head e1 = a))
    (he2 : (G.tail e2 = b ∧ G.head e2 = c) ∨ (G.tail e2 = c ∧ G.head e2 = b))
    (he3 : (G.tail e3 = c ∧ G.head e3 = a) ∨ (G.tail e3 = a ∧ G.head e3 = c)) : False := by
  let S : Finset V := {a, b, c}
  have hScard : S.card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac]), Finset.card_pair hbc]
  have hSccard : (Finset.univ \ S).card = Fintype.card V - 3 := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, hScard]
  have hcut4 := hno3 S (by omega) (by omega)
  have hdeg := sum_deg_eq_cut_add_two_internal G S
  have hsum9 : ∑ v ∈ S, G.deg v = 9 := by
    rw [Finset.sum_insert (by simp [hab, hac]), Finset.sum_pair hbc, hcub a, hcub b, hcub c]; omega
  have hne12 : e1 ≠ e2 := fun h => by
    subst h; rcases he1 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases he2 with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · exact hab (h1.symm.trans h3)
    · exact hac (h1.symm.trans h3)
    · exact hac (h2.symm.trans h4)
    · exact hbc (h1.symm.trans h3)
  have hne13 : e1 ≠ e3 := fun h => by
    subst h; rcases he1 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases he3 with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · exact hac (h1.symm.trans h3)
    · exact hbc (h2.symm.trans h4)
    · exact hbc (h1.symm.trans h3)
    · exact hab (h1.symm.trans h3).symm
  have hne23 : e2 ≠ e3 := fun h => by
    subst h; rcases he2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases he3 with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · exact hbc (h1.symm.trans h3)
    · exact hab (h1.symm.trans h3).symm
    · exact hab (h2.symm.trans h4).symm
    · exact hac (h1.symm.trans h3).symm
  have hin : ∀ e ∈ ({e1, e2, e3} : Finset E), e ∈ Finset.univ.filter (fun e : E => G.tail e ∈ S ∧ G.head e ∈ S) := by
    intro e he; simp only [Finset.mem_insert, Finset.mem_singleton] at he
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rcases he with rfl | rfl | rfl
    · rcases he1 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [S, h1, h2]
    · rcases he2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [S, h1, h2]
    · rcases he3 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [S, h1, h2]
  have hge3 : 3 ≤ (Finset.univ.filter (fun e : E => G.tail e ∈ S ∧ G.head e ∈ S)).card := by
    have hc : ({e1, e2, e3} : Finset E).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hne12, hne13]), Finset.card_pair hne23]
    rw [← hc]; exact Finset.card_le_card hin
  omega

/-- Helper: in a simple cubic graph, every vertex `v` has exactly 3 incident edges with 3 distinct neighbors. -/
lemma cubic_simple_three_edges {V E : Type} [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : Multigraph V E) (hcub : G.IsCubic) (hsimp : G.IsSimple) (v : V) :
    (Finset.univ.filter (fun e : E => G.tail e = v ∨ G.head e = v)).card = 3 := by
  have hdisj : Disjoint (Finset.univ.filter (fun e : E => G.tail e = v))
      (Finset.univ.filter (fun e : E => G.head e = v)) := by
    rw [Finset.disjoint_left]; intro e ht hh
    exact hsimp.1 e ((Finset.mem_filter.mp ht).2.trans (Finset.mem_filter.mp hh).2.symm)
  have hun : Finset.univ.filter (fun e : E => G.tail e = v ∨ G.head e = v) =
      Finset.univ.filter (fun e : E => G.tail e = v) ∪ Finset.univ.filter (fun e : E => G.head e = v) := by
    ext e; simp
  rw [hun, Finset.card_union_of_disjoint hdisj]
  exact hcub v

/-- Other endpoint of an edge incident to `v`. -/
def otherEnd {V E : Type} [DecidableEq V] (G : Multigraph V E) (v : V) (e : E) : V :=
  if G.tail e = v then G.head e else G.tail e

lemma otherEnd_spec {V E : Type} [DecidableEq V] (G : Multigraph V E) (hll : G.IsLoopless)
    (v : V) (e : E) (hinc : G.tail e = v ∨ G.head e = v) :
    otherEnd G v e ≠ v ∧
    ((G.tail e = v ∧ G.head e = otherEnd G v e) ∨ (G.tail e = otherEnd G v e ∧ G.head e = v)) := by
  dsimp only [otherEnd]
  by_cases ht : G.tail e = v
  · rw [if_pos ht]; exact ⟨fun h => hll e (ht.trans h.symm), Or.inl ⟨ht, rfl⟩⟩
  · rw [if_neg ht]
    have hh : G.head e = v := hinc.resolve_left ht
    exact ⟨ht, Or.inr ⟨rfl, hh⟩⟩

lemma otherEnd_inj {V E : Type} [DecidableEq V] (G : Multigraph V E) (hsimp : G.IsSimple)
    (v : V) {e₁ e₂ : E} (h1 : G.tail e₁ = v ∨ G.head e₁ = v) (h2 : G.tail e₂ = v ∨ G.head e₂ = v)
    (heq : otherEnd G v e₁ = otherEnd G v e₂) : e₁ = e₂ := by
  apply hsimp.2
  have s1 := (otherEnd_spec G hsimp.1 v e₁ h1).2
  have s2 := (otherEnd_spec G hsimp.1 v e₂ h2).2
  rw [heq] at s1
  rcases s1 with ⟨a1, b1⟩ | ⟨a1, b1⟩ <;> rcases s2 with ⟨a2, b2⟩ | ⟨a2, b2⟩
  · exact Or.inl ⟨a1.trans a2.symm, b1.trans b2.symm⟩
  · exact Or.inr ⟨a1.trans b2.symm, b1.trans a2.symm⟩
  · exact Or.inr ⟨a1.trans b2.symm, b1.trans a2.symm⟩
  · exact Or.inl ⟨a1.trans a2.symm, b1.trans b2.symm⟩

set_option maxHeartbeats 800000 in
/-- Growing lemma (Case 2): when `Qplus` is cubic, `3`-EC, `|V| ≥ 6`, with NO non-trivial `3`-edge-cut,
deleting a neighbor `z` of `v₀` and a neighbor `w` of `z` and adding edges `v₀-u` and `x-y` yields a
smaller cubic `3`-edge-connected graph `Hplus` (`|V| - 2` vertices), and any `WellColouring` of
`Hplus.deleteVertex v₀` lifts to a `WellColouring` of `Qplus.deleteVertex v₀`. -/
lemma wellColouring_growing {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (Qplus : Multigraph V E) (v₀ : V)
    (hcub : Qplus.IsCubic) (h3 : Qplus.IsEdgeConnected 3) (h6 : 6 ≤ Fintype.card V)
    (hno3 : ∀ S : Finset V, 2 ≤ S.card → 2 ≤ (Finset.univ \ S).card → 4 ≤ (Qplus.cutEdges S).card)
    (ih : ∀ (V' E' : Type) [Fintype V'] [Fintype E'] [DecidableEq V'] [DecidableEq E']
      (Hplus : Multigraph V' E') (v' : V'),
      Fintype.card V' < Fintype.card V → Hplus.IsCubic → Hplus.IsEdgeConnected 3 → 4 ≤ Fintype.card V' →
      Nonempty (WellColouring (Hplus.deleteVertex v'))) :
    Nonempty (WellColouring (Qplus.deleteVertex v₀)) := by
  classical
  have hsimp := cubic_3ec_isSimple Qplus hcub h3 (by omega)
  -- Step 1: Pick neighbor z of v₀, then z's other 2 neighbors u, w, then w's other 2 neighbors x, y
  have hinc_v0 := cubic_simple_three_edges Qplus hcub hsimp v₀
  obtain ⟨e_v0z, he_v0z_mem⟩ := Finset.card_pos.mp (by omega : 0 < (Finset.univ.filter (fun e : E => Qplus.tail e = v₀ ∨ Qplus.head e = v₀)).card)
  have he_v0z_inc : Qplus.tail e_v0z = v₀ ∨ Qplus.head e_v0z = v₀ := (Finset.mem_filter.mp he_v0z_mem).2
  let z := otherEnd Qplus v₀ e_v0z
  have hz_spec := otherEnd_spec Qplus hsimp.1 v₀ e_v0z he_v0z_inc
  have hz_ne_v0 : z ≠ v₀ := hz_spec.1
  have he_v0z_ends : (Qplus.tail e_v0z = v₀ ∧ Qplus.head e_v0z = z) ∨ (Qplus.tail e_v0z = z ∧ Qplus.head e_v0z = v₀) := hz_spec.2
  have he_v0z_inc_z : Qplus.tail e_v0z = z ∨ Qplus.head e_v0z = z := by
    rcases he_v0z_ends with ⟨_, h⟩ | ⟨h, _⟩; exact Or.inr h; exact Or.inl h
  have hinc_z := cubic_simple_three_edges Qplus hcub hsimp z
  have hz_other2 : ((Finset.univ.filter (fun e : E => Qplus.tail e = z ∨ Qplus.head e = z)).erase e_v0z).card = 2 := by
    have hm : e_v0z ∈ Finset.univ.filter (fun e : E => Qplus.tail e = z ∨ Qplus.head e = z) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, he_v0z_inc_z⟩
    rw [Finset.card_erase_of_mem hm, hinc_z]
  obtain ⟨e_zu, e_zw, he_zu_ne_zw, hz_eq2⟩ := Finset.card_eq_two.mp hz_other2
  have he_zu_mem : e_zu ∈ (Finset.univ.filter (fun e : E => Qplus.tail e = z ∨ Qplus.head e = z)).erase e_v0z :=
    hz_eq2 ▸ Finset.mem_insert_self _ _
  have he_zw_mem : e_zw ∈ (Finset.univ.filter (fun e : E => Qplus.tail e = z ∨ Qplus.head e = z)).erase e_v0z :=
    hz_eq2 ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have he_zu_inc : Qplus.tail e_zu = z ∨ Qplus.head e_zu = z := (Finset.mem_filter.mp (Finset.mem_of_mem_erase he_zu_mem)).2
  have he_zw_inc : Qplus.tail e_zw = z ∨ Qplus.head e_zw = z := (Finset.mem_filter.mp (Finset.mem_of_mem_erase he_zw_mem)).2
  have he_zu_ne_v0z : e_zu ≠ e_v0z := Finset.ne_of_mem_erase he_zu_mem
  have he_zw_ne_v0z : e_zw ≠ e_v0z := Finset.ne_of_mem_erase he_zw_mem
  let u := otherEnd Qplus z e_zu
  let w := otherEnd Qplus z e_zw
  have hu_spec := otherEnd_spec Qplus hsimp.1 z e_zu he_zu_inc
  have hw_spec := otherEnd_spec Qplus hsimp.1 z e_zw he_zw_inc
  have hu_ne_z : u ≠ z := hu_spec.1
  have hw_ne_z : w ≠ z := hw_spec.1
  have hu_ne_w : u ≠ w := fun h => he_zu_ne_zw (otherEnd_inj Qplus hsimp z he_zu_inc he_zw_inc h)
  have hu_ne_v0 : u ≠ v₀ := fun h => by
    have : otherEnd Qplus z e_v0z = v₀ := by
      dsimp only [otherEnd]; rcases he_v0z_ends with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [if_neg (fun ht => hz_ne_v0 (ht.symm.trans h1))]; exact h1
      · rw [if_pos h1]; exact h2
    exact he_zu_ne_v0z (otherEnd_inj Qplus hsimp z he_zu_inc he_v0z_inc_z (h.trans this.symm))
  have hw_ne_v0 : w ≠ v₀ := fun h => by
    have : otherEnd Qplus z e_v0z = v₀ := by
      dsimp only [otherEnd]; rcases he_v0z_ends with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [if_neg (fun ht => hz_ne_v0 (ht.symm.trans h1))]; exact h1
      · rw [if_pos h1]; exact h2
    exact he_zw_ne_v0z (otherEnd_inj Qplus hsimp z he_zw_inc he_v0z_inc_z (h.trans this.symm))
  -- Now extract w's other 2 incident edges e_wx, e_wy and neighbors x, y
  have he_zw_inc_w : Qplus.tail e_zw = w ∨ Qplus.head e_zw = w := by
    rcases hw_spec.2 with ⟨_, h⟩ | ⟨h, _⟩; exact Or.inr h; exact Or.inl h
  have hinc_w := cubic_simple_three_edges Qplus hcub hsimp w
  have hw_other2 : ((Finset.univ.filter (fun e : E => Qplus.tail e = w ∨ Qplus.head e = w)).erase e_zw).card = 2 := by
    have hm : e_zw ∈ Finset.univ.filter (fun e : E => Qplus.tail e = w ∨ Qplus.head e = w) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, he_zw_inc_w⟩
    rw [Finset.card_erase_of_mem hm, hinc_w]
  obtain ⟨e_wx, e_wy, he_wx_ne_wy, hw_eq2⟩ := Finset.card_eq_two.mp hw_other2
  have he_wx_mem : e_wx ∈ (Finset.univ.filter (fun e : E => Qplus.tail e = w ∨ Qplus.head e = w)).erase e_zw :=
    hw_eq2 ▸ Finset.mem_insert_self _ _
  have he_wy_mem : e_wy ∈ (Finset.univ.filter (fun e : E => Qplus.tail e = w ∨ Qplus.head e = w)).erase e_zw :=
    hw_eq2 ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have he_wx_inc : Qplus.tail e_wx = w ∨ Qplus.head e_wx = w := (Finset.mem_filter.mp (Finset.mem_of_mem_erase he_wx_mem)).2
  have he_wy_inc : Qplus.tail e_wy = w ∨ Qplus.head e_wy = w := (Finset.mem_filter.mp (Finset.mem_of_mem_erase he_wy_mem)).2
  have he_wx_ne_zw : e_wx ≠ e_zw := Finset.ne_of_mem_erase he_wx_mem
  have he_wy_ne_zw : e_wy ≠ e_zw := Finset.ne_of_mem_erase he_wy_mem
  let x := otherEnd Qplus w e_wx
  let y := otherEnd Qplus w e_wy
  have hx_spec := otherEnd_spec Qplus hsimp.1 w e_wx he_wx_inc
  have hy_spec := otherEnd_spec Qplus hsimp.1 w e_wy he_wy_inc
  have hx_ne_w : x ≠ w := hx_spec.1
  have hy_ne_w : y ≠ w := hy_spec.1
  have hx_ne_y : x ≠ y := fun h => he_wx_ne_wy (otherEnd_inj Qplus hsimp w he_wx_inc he_wy_inc h)
  have hother_zw : otherEnd Qplus w e_zw = z := by
    dsimp only [otherEnd]; rcases hw_spec.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [if_neg (fun ht => hw_ne_z (ht.symm.trans h1))]; exact h1
    · rw [if_pos h1]; exact h2
  have hx_ne_z : x ≠ z := fun h => he_wx_ne_zw (otherEnd_inj Qplus hsimp w he_wx_inc he_zw_inc_w (h.trans hother_zw.symm))
  have hy_ne_z : y ≠ z := fun h => he_wy_ne_zw (otherEnd_inj Qplus hsimp w he_wy_inc he_zw_inc_w (h.trans hother_zw.symm))
  -- Triangle-freeness forces x, y ∉ {v₀, u}!
  have hx_ne_v0 : x ≠ v₀ := fun h =>
    cubic_no_nontrivial_3cut_triangle_free Qplus hcub h6 hno3 hz_ne_v0.symm hw_ne_v0.symm hw_ne_z.symm
      e_v0z e_zw e_wx he_v0z_ends hw_spec.2 (by simpa [x, h] using hx_spec.2)
  have hy_ne_v0 : y ≠ v₀ := fun h =>
    cubic_no_nontrivial_3cut_triangle_free Qplus hcub h6 hno3 hz_ne_v0.symm hw_ne_v0.symm hw_ne_z.symm
      e_v0z e_zw e_wy he_v0z_ends hw_spec.2 (by simpa [y, h] using hy_spec.2)
  have hx_ne_u : x ≠ u := fun h =>
    cubic_no_nontrivial_3cut_triangle_free Qplus hcub h6 hno3 hu_ne_z hu_ne_w hw_ne_z.symm
      e_zu e_zw e_wx (by rcases hu_spec.2 with h1 | h1; exact Or.inr h1; exact Or.inl h1)
      hw_spec.2 (by simpa [x, h] using hx_spec.2)
  have hy_ne_u : y ≠ u := fun h =>
    cubic_no_nontrivial_3cut_triangle_free Qplus hcub h6 hno3 hu_ne_z hu_ne_w hw_ne_z.symm
      e_zu e_zw e_wy (by rcases hu_spec.2 with h1 | h1; exact Or.inr h1; exact Or.inl h1)
      hw_spec.2 (by simpa [y, h] using hy_spec.2)
  -- The 5 removed edges are ALL edges incident to z or w!
  let remE : Finset E := {e_v0z, e_zu, e_zw, e_wx, e_wy}
  have hrem_iff : ∀ e : E, e ∈ remE ↔ (Qplus.tail e = z ∨ Qplus.head e = z ∨ Qplus.tail e = w ∨ Qplus.head e = w) := by
    intro e
    constructor
    · intro he
      simp only [remE, Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl | rfl | rfl
      · rcases he_v0z_inc_z with h | h; exact Or.inl h; exact Or.inr (Or.inl h)
      · rcases he_zu_inc with h | h; exact Or.inl h; exact Or.inr (Or.inl h)
      · rcases he_zw_inc with h | h; exact Or.inl h; exact Or.inr (Or.inl h)
      · rcases he_wx_inc with h | h; exact Or.inr (Or.inr (Or.inl h)); exact Or.inr (Or.inr (Or.inr h))
      · rcases he_wy_inc with h | h; exact Or.inr (Or.inr (Or.inl h)); exact Or.inr (Or.inr (Or.inr h))
    · intro hor
      rcases hor with ht | hh | ht | hh
      · by_cases h0 : e = e_v0z
        · rw [h0]; simp [remE]
        · have hm : e ∈ (Finset.univ.filter (fun e : E => Qplus.tail e = z ∨ Qplus.head e = z)).erase e_v0z :=
            Finset.mem_erase.mpr ⟨h0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ht⟩⟩
          rw [hz_eq2, Finset.mem_insert, Finset.mem_singleton] at hm
          rcases hm with rfl | rfl <;> simp [remE]
      · by_cases h0 : e = e_v0z
        · rw [h0]; simp [remE]
        · have hm : e ∈ (Finset.univ.filter (fun e : E => Qplus.tail e = z ∨ Qplus.head e = z)).erase e_v0z :=
            Finset.mem_erase.mpr ⟨h0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr hh⟩⟩
          rw [hz_eq2, Finset.mem_insert, Finset.mem_singleton] at hm
          rcases hm with rfl | rfl <;> simp [remE]
      · by_cases h0 : e = e_zw
        · rw [h0]; simp [remE]
        · have hm : e ∈ (Finset.univ.filter (fun e : E => Qplus.tail e = w ∨ Qplus.head e = w)).erase e_zw :=
            Finset.mem_erase.mpr ⟨h0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ht⟩⟩
          rw [hw_eq2, Finset.mem_insert, Finset.mem_singleton] at hm
          rcases hm with rfl | rfl <;> simp [remE]
      · by_cases h0 : e = e_zw
        · rw [h0]; simp [remE]
        · have hm : e ∈ (Finset.univ.filter (fun e : E => Qplus.tail e = w ∨ Qplus.head e = w)).erase e_zw :=
            Finset.mem_erase.mpr ⟨h0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr hh⟩⟩
          rw [hw_eq2, Finset.mem_insert, Finset.mem_singleton] at hm
          rcases hm with rfl | rfl <;> simp [remE]
  -- Pairwise distinctness of the 5 removed edges
  have he_v0z_ne_wx : e_v0z ≠ e_wx := fun h => by
    subst h; rcases he_v0z_ends with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hx_spec.2 with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · exact hw_ne_v0 (h3.symm.trans h1)
    · exact hx_ne_v0 (h3.symm.trans h1)
    · exact hw_ne_z (h3.symm.trans h1)
    · exact hx_ne_z (h3.symm.trans h1)
  have he_v0z_ne_wy : e_v0z ≠ e_wy := fun h => by
    subst h; rcases he_v0z_ends with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hy_spec.2 with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · exact hw_ne_v0 (h3.symm.trans h1)
    · exact hy_ne_v0 (h3.symm.trans h1)
    · exact hw_ne_z (h3.symm.trans h1)
    · exact hy_ne_z (h3.symm.trans h1)
  have he_zu_ne_wx : e_zu ≠ e_wx := fun h => by
    subst h; rcases hu_spec.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hx_spec.2 with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · exact hw_ne_z (h3.symm.trans h1)
    · exact hx_ne_z (h3.symm.trans h1)
    · exact hu_ne_w (h1.symm.trans h3)
    · exact hx_ne_u (h3.symm.trans h1)
  have he_zu_ne_wy : e_zu ≠ e_wy := fun h => by
    subst h; rcases hu_spec.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hy_spec.2 with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · exact hw_ne_z (h3.symm.trans h1)
    · exact hy_ne_z (h3.symm.trans h1)
    · exact hu_ne_w (h1.symm.trans h3)
    · exact hy_ne_u (h3.symm.trans h1)
  -- Step 2: Construct Hplus on VH = {a : V // a ≠ z ∧ a ≠ w} and EH = Option (Option {e : E // e ∉ remE})
  let VH := {a : V // a ≠ z ∧ a ≠ w}
  let EH := Option (Option {e : E // e ∉ remE})
  let v₀H : VH := ⟨v₀, hz_ne_v0.symm, hw_ne_v0.symm⟩
  let uH : VH := ⟨u, hu_ne_z, hu_ne_w⟩
  let xH : VH := ⟨x, hx_ne_z, hx_ne_w⟩
  let yH : VH := ⟨y, hy_ne_z, hy_ne_w⟩
  have hkeep_ends : ∀ e : {e : E // e ∉ remE},
      (Qplus.tail e.1 ≠ z ∧ Qplus.tail e.1 ≠ w) ∧ (Qplus.head e.1 ≠ z ∧ Qplus.head e.1 ≠ w) := fun e => by
    have h := mt (hrem_iff e.1).mpr e.2
    push Not at h
    exact ⟨⟨h.1, h.2.2.1⟩, ⟨h.2.1, h.2.2.2⟩⟩
  let Hplus : Multigraph VH EH :=
    { tail := fun e => match e with
        | none => v₀H
        | some none => xH
        | some (some e') => ⟨Qplus.tail e'.1, (hkeep_ends e').1⟩
      head := fun e => match e with
        | none => uH
        | some none => yH
        | some (some e') => ⟨Qplus.head e'.1, (hkeep_ends e').2⟩ }
  -- Card VH = |V| - 2 (so 4 ≤ |VH| < |V|)
  have hVH_card : Fintype.card VH = Fintype.card V - 2 := by
    have heq : Fintype.card VH = (Finset.univ \ ({z, w} : Finset V)).card := by
      rw [Fintype.card_subtype]; congr 1; ext a; simp [not_or]
    rw [heq, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Finset.card_pair hw_ne_z.symm]
  -- Hplus is cubic!
  have hH_cub : Hplus.IsCubic := by
    intro a
    -- In Qplus, deg a.1 = (# incident edges in remE) + (# incident edges outside remE)
    -- In Hplus, deg a = (# incident edges among {none, some none}) + (# incident edges outside remE)
    have hrem_deg : (remE.filter (fun e => Qplus.tail e = a.1)).card +
        (remE.filter (fun e => Qplus.head e = a.1)).card =
        (if a = v₀H then 1 else 0) + (if a = uH then 1 else 0) +
        (if a = xH then 1 else 0) + (if a = yH then 1 else 0) := by
      have ha_nz : a.1 ≠ z := a.2.1
      have ha_nw : a.1 ≠ w := a.2.2
      have hcnt : ∀ e : E,
          (if Qplus.tail e = a.1 then 1 else 0) + (if Qplus.head e = a.1 then 1 else 0) =
          (if Qplus.tail e = a.1 ∨ Qplus.head e = a.1 then 1 else 0) := fun e => by
        by_cases ht : Qplus.tail e = a.1 <;> by_cases hh : Qplus.head e = a.1
        · exact absurd (ht.trans hh.symm) (hsimp.1 e)
        · simp [ht, hh]
        · simp [ht, hh]
        · simp [ht, hh]
      have h1 : (Qplus.tail e_v0z = a.1 ∨ Qplus.head e_v0z = a.1) ↔ a = v₀H := by
        rw [Subtype.ext_iff]; dsimp only [v₀H]
        rcases he_v0z_ends with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
        · exact ⟨fun hor => (hor.resolve_right (Ne.symm ha_nz)).symm, fun h => Or.inl h.symm⟩
        · exact ⟨fun hor => (hor.resolve_left (Ne.symm ha_nz)).symm, fun h => Or.inr h.symm⟩
      have h2 : (Qplus.tail e_zu = a.1 ∨ Qplus.head e_zu = a.1) ↔ a = uH := by
        rw [Subtype.ext_iff]; dsimp only [uH]
        rcases hu_spec.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
        · exact ⟨fun hor => (hor.resolve_left (Ne.symm ha_nz)).symm, fun h => Or.inr h.symm⟩
        · exact ⟨fun hor => (hor.resolve_right (Ne.symm ha_nz)).symm, fun h => Or.inl h.symm⟩
      have h3' : ¬ (Qplus.tail e_zw = a.1 ∨ Qplus.head e_zw = a.1) := by
        rcases hw_spec.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
        · rintro (h | h); exact ha_nz h.symm; exact ha_nw h.symm
        · rintro (h | h); exact ha_nw h.symm; exact ha_nz h.symm
      have h4 : (Qplus.tail e_wx = a.1 ∨ Qplus.head e_wx = a.1) ↔ a = xH := by
        rw [Subtype.ext_iff]; dsimp only [xH]
        rcases hx_spec.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
        · exact ⟨fun hor => (hor.resolve_left (Ne.symm ha_nw)).symm, fun h => Or.inr h.symm⟩
        · exact ⟨fun hor => (hor.resolve_right (Ne.symm ha_nw)).symm, fun h => Or.inl h.symm⟩
      have h5 : (Qplus.tail e_wy = a.1 ∨ Qplus.head e_wy = a.1) ↔ a = yH := by
        rw [Subtype.ext_iff]; dsimp only [yH]
        rcases hy_spec.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
        · exact ⟨fun hor => (hor.resolve_left (Ne.symm ha_nw)).symm, fun h => Or.inr h.symm⟩
        · exact ⟨fun hor => (hor.resolve_right (Ne.symm ha_nw)).symm, fun h => Or.inl h.symm⟩
      have hcard_split : ∀ (p : E → Prop) [DecidablePred p],
          (remE.filter p).card =
          (if p e_v0z then 1 else 0) + (if p e_zu then 1 else 0) +
          (if p e_zw then 1 else 0) + (if p e_wx then 1 else 0) + (if p e_wy then 1 else 0) := by
        intro p _
        rw [Finset.card_filter]
        have hm1 : e_v0z ∉ ({e_zu, e_zw, e_wx, e_wy} : Finset E) := by simp [he_zu_ne_v0z.symm, he_zw_ne_v0z.symm, he_v0z_ne_wx, he_v0z_ne_wy]
        have hm2 : e_zu ∉ ({e_zw, e_wx, e_wy} : Finset E) := by simp [he_zu_ne_zw, he_zu_ne_wx, he_zu_ne_wy]
        have hm3 : e_zw ∉ ({e_wx, e_wy} : Finset E) := by simp [he_wx_ne_zw.symm, he_wy_ne_zw.symm]
        dsimp only [remE]
        rw [Finset.sum_insert hm1, Finset.sum_insert hm2, Finset.sum_insert hm3, Finset.sum_pair he_wx_ne_wy]
        omega
      rw [hcard_split, hcard_split]
      have hc1 := hcnt e_v0z; have hc2 := hcnt e_zu; have hc3 := hcnt e_zw; have hc4 := hcnt e_wx; have hc5 := hcnt e_wy
      rw [if_congr h1 rfl rfl] at hc1
      rw [if_congr h2 rfl rfl] at hc2
      rw [if_neg h3'] at hc3
      rw [if_congr h4 rfl rfl] at hc4
      rw [if_congr h5 rfl rfl] at hc5
      omega
    -- Compare Hplus.deg a with Qplus.deg a.1 using keepE = univ \ remE!
    have hdeg_split_Q : Qplus.deg a.1 =
        ((remE.filter (fun e => Qplus.tail e = a.1)).card + (remE.filter (fun e => Qplus.head e = a.1)).card) +
        (((Finset.univ \ remE).filter (fun e => Qplus.tail e = a.1)).card +
         ((Finset.univ \ remE).filter (fun e => Qplus.head e = a.1)).card) := by
      unfold Multigraph.deg
      have hun : (Finset.univ : Finset E) = remE ∪ (Finset.univ \ remE) := by ext e; by_cases h : e ∈ remE <;> simp [h]
      have hdisj : Disjoint remE (Finset.univ \ remE) := Finset.disjoint_sdiff
      conv_lhs => rw [hun, Finset.filter_union, Finset.filter_union,
        Finset.card_union_of_disjoint (Disjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _) hdisj),
        Finset.card_union_of_disjoint (Disjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _) hdisj)]
      omega
    have hdeg_split_H : Hplus.deg a =
        ((if a = v₀H then 1 else 0) + (if a = uH then 1 else 0) +
         (if a = xH then 1 else 0) + (if a = yH then 1 else 0)) +
        (((Finset.univ \ remE).filter (fun e => Qplus.tail e = a.1)).card +
         ((Finset.univ \ remE).filter (fun e => Qplus.head e = a.1)).card) := by
      unfold Multigraph.deg
      have ht : (Finset.univ.filter (fun e : EH => Hplus.tail e = a)).card =
          (if a = v₀H then 1 else 0) + (if a = xH then 1 else 0) +
          ((Finset.univ \ remE).filter (fun e => Qplus.tail e = a.1)).card := by
        rw [Finset.card_filter, Fintype.sum_option, Fintype.sum_option]
        dsimp only [Hplus]
        have h1 : (if v₀H = a then 1 else 0) = (if a = v₀H then 1 else 0) := by simp [eq_comm]
        have h2 : (if xH = a then 1 else 0) = (if a = xH then 1 else 0) := by simp [eq_comm]
        have h3s : ∑ e' : {e : E // e ∉ remE}, (if (⟨Qplus.tail e'.1, (hkeep_ends e').1⟩ : VH) = a then 1 else 0) =
            ((Finset.univ \ remE).filter (fun e => Qplus.tail e = a.1)).card := by
          rw [Finset.card_filter]
          refine Finset.sum_bij (fun e' _ => e'.1) (fun e' _ => Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, e'.2⟩)
            (fun _ _ _ _ h => Subtype.ext h) (fun e he => ⟨⟨e, (Finset.mem_sdiff.mp he).2⟩, Finset.mem_univ _, rfl⟩)
            (fun e' _ => by simp [Subtype.ext_iff])
        rw [h1, h2, h3s]; omega
      have hh : (Finset.univ.filter (fun e : EH => Hplus.head e = a)).card =
          (if a = uH then 1 else 0) + (if a = yH then 1 else 0) +
          ((Finset.univ \ remE).filter (fun e => Qplus.head e = a.1)).card := by
        rw [Finset.card_filter, Fintype.sum_option, Fintype.sum_option]
        dsimp only [Hplus]
        have h1 : (if uH = a then 1 else 0) = (if a = uH then 1 else 0) := by simp [eq_comm]
        have h2 : (if yH = a then 1 else 0) = (if a = yH then 1 else 0) := by simp [eq_comm]
        have h3s : ∑ e' : {e : E // e ∉ remE}, (if (⟨Qplus.head e'.1, (hkeep_ends e').2⟩ : VH) = a then 1 else 0) =
            ((Finset.univ \ remE).filter (fun e => Qplus.head e = a.1)).card := by
          rw [Finset.card_filter]
          refine Finset.sum_bij (fun e' _ => e'.1) (fun e' _ => Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, e'.2⟩)
            (fun _ _ _ _ h => Subtype.ext h) (fun e he => ⟨⟨e, (Finset.mem_sdiff.mp he).2⟩, Finset.mem_univ _, rfl⟩)
            (fun e' _ => by simp [Subtype.ext_iff])
        rw [h1, h2, h3s]; omega
      rw [ht, hh]; omega
    have hq3 := hcub a.1
    omega
  -- Hplus is 3-edge-connected (exact 16-case truth-table cut check!)
  have hH_3ec : Hplus.IsEdgeConnected 3 := by
    intro S hSne hScne
    let SV : Finset V := S.image Subtype.val
    have hSV_card : SV.card = S.card := Finset.card_image_of_injective S Subtype.val_injective
    have hz_not_SV : z ∉ SV := fun h => by obtain ⟨a, _, ha⟩ := Finset.mem_image.mp h; exact a.2.1 ha
    have hw_not_SV : w ∉ SV := fun h => by obtain ⟨a, _, ha⟩ := Finset.mem_image.mp h; exact a.2.2 ha
    have hSV_iff : ∀ a : VH, a.1 ∈ SV ↔ a ∈ S := fun a => by
      simp [SV, Subtype.val_injective.eq_iff]
    -- Count crossing edges in Hplus = (crossing among {none, some none}) + (crossing among univ \ remE)
    let crossKeep := (Finset.univ \ remE).filter (fun e =>
      (Qplus.tail e ∈ SV ∧ Qplus.head e ∉ SV) ∨ (Qplus.tail e ∉ SV ∧ Qplus.head e ∈ SV))
    have hHcut : (Hplus.cutEdges S).card =
        (if (v₀ ∈ SV ∧ u ∉ SV) ∨ (v₀ ∉ SV ∧ u ∈ SV) then 1 else 0) +
        (if (x ∈ SV ∧ y ∉ SV) ∨ (x ∉ SV ∧ y ∈ SV) then 1 else 0) + crossKeep.card := by
      unfold Multigraph.cutEdges
      rw [Finset.card_filter, Fintype.sum_option, Fintype.sum_option]
      dsimp only [Hplus]
      have h1 : ((v₀H ∈ S ∧ uH ∉ S) ∨ (v₀H ∉ S ∧ uH ∈ S)) ↔ ((v₀ ∈ SV ∧ u ∉ SV) ∨ (v₀ ∉ SV ∧ u ∈ SV)) := by
        rw [← hSV_iff v₀H, ← hSV_iff uH]
      have h2 : ((xH ∈ S ∧ yH ∉ S) ∨ (xH ∉ S ∧ yH ∈ S)) ↔ ((x ∈ SV ∧ y ∉ SV) ∨ (x ∉ SV ∧ y ∈ SV)) := by
        rw [← hSV_iff xH, ← hSV_iff yH]
      have h3s : ∑ e' : {e : E // e ∉ remE},
          (if (⟨Qplus.tail e'.1, (hkeep_ends e').1⟩ ∈ S ∧ ⟨Qplus.head e'.1, (hkeep_ends e').2⟩ ∉ S) ∨
              (⟨Qplus.tail e'.1, (hkeep_ends e').1⟩ ∉ S ∧ ⟨Qplus.head e'.1, (hkeep_ends e').2⟩ ∈ S) then 1 else 0) =
          crossKeep.card := by
        rw [Finset.card_filter]
        refine Finset.sum_bij (fun e' _ => e'.1) (fun e' _ => Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, e'.2⟩)
          (fun _ _ _ _ h => Subtype.ext h) (fun e he => ⟨⟨e, (Finset.mem_sdiff.mp he).2⟩, Finset.mem_univ _, rfl⟩)
          (fun e' _ => by
            have ht := hSV_iff ⟨Qplus.tail e'.1, (hkeep_ends e').1⟩
            have hh := hSV_iff ⟨Qplus.head e'.1, (hkeep_ends e').2⟩
            simp only [ht, hh])
      simp only [h1, h2, h3s]; omega
    -- Helper: for any T ⊆ V agreeing with SV outside {z, w}, count (Qplus.cutEdges T).card!
    have hQcut : ∀ (T : Finset V), (∀ a : V, a ≠ z → a ≠ w → (a ∈ T ↔ a ∈ SV)) →
        (Qplus.cutEdges T).card =
        (if (v₀ ∈ T ∧ z ∉ T) ∨ (v₀ ∉ T ∧ z ∈ T) then 1 else 0) +
        (if (z ∈ T ∧ u ∉ T) ∨ (z ∉ T ∧ u ∈ T) then 1 else 0) +
        (if (z ∈ T ∧ w ∉ T) ∨ (z ∉ T ∧ w ∈ T) then 1 else 0) +
        (if (w ∈ T ∧ x ∉ T) ∨ (w ∉ T ∧ x ∈ T) then 1 else 0) +
        (if (w ∈ T ∧ y ∉ T) ∨ (w ∉ T ∧ y ∈ T) then 1 else 0) + crossKeep.card := by
      intro T hT
      unfold Multigraph.cutEdges
      have hun : (Finset.univ : Finset E) = remE ∪ (Finset.univ \ remE) := by ext e; by_cases h : e ∈ remE <;> simp [h]
      have hdisj : Disjoint remE (Finset.univ \ remE) := Finset.disjoint_sdiff
      rw [hun, Finset.filter_union,
          Finset.card_union_of_disjoint (Disjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _) hdisj)]
      have hkeep_eq : ((Finset.univ \ remE).filter (fun e =>
          (Qplus.tail e ∈ T ∧ Qplus.head e ∉ T) ∨ (Qplus.tail e ∉ T ∧ Qplus.head e ∈ T))) = crossKeep := by
        ext e; simp only [crossKeep, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
        constructor <;> rintro ⟨he, h⟩ <;> refine ⟨he, ?_⟩
        · have he' := hkeep_ends ⟨e, he⟩
          rwa [hT _ he'.1.1 he'.1.2, hT _ he'.2.1 he'.2.2] at h
        · have he' := hkeep_ends ⟨e, he⟩
          rwa [hT _ he'.1.1 he'.1.2, hT _ he'.2.1 he'.2.2]
      rw [hkeep_eq, Finset.card_filter]
      have hm1 : e_v0z ∉ ({e_zu, e_zw, e_wx, e_wy} : Finset E) := by simp [he_zu_ne_v0z.symm, he_zw_ne_v0z.symm, he_v0z_ne_wx, he_v0z_ne_wy]
      have hm2 : e_zu ∉ ({e_zw, e_wx, e_wy} : Finset E) := by simp [he_zu_ne_zw, he_zu_ne_wx, he_zu_ne_wy]
      have hm3 : e_zw ∉ ({e_wx, e_wy} : Finset E) := by simp [he_wx_ne_zw.symm, he_wy_ne_zw.symm]
      dsimp only [remE]
      rw [Finset.sum_insert hm1, Finset.sum_insert hm2, Finset.sum_insert hm3, Finset.sum_pair he_wx_ne_wy]
      have hc : ∀ (e : E) (a b : V), ((Qplus.tail e = a ∧ Qplus.head e = b) ∨ (Qplus.tail e = b ∧ Qplus.head e = a)) →
          ∀ [Decidable ((Qplus.tail e ∈ T ∧ Qplus.head e ∉ T) ∨ (Qplus.tail e ∉ T ∧ Qplus.head e ∈ T))]
            [Decidable ((a ∈ T ∧ b ∉ T) ∨ (a ∉ T ∧ b ∈ T))],
          (if (Qplus.tail e ∈ T ∧ Qplus.head e ∉ T) ∨ (Qplus.tail e ∉ T ∧ Qplus.head e ∈ T) then (1 : ℕ) else 0) =
          (if (a ∈ T ∧ b ∉ T) ∨ (a ∉ T ∧ b ∈ T) then 1 else 0) := by
        intro e a b h _ _
        by_cases hL : (Qplus.tail e ∈ T ∧ Qplus.head e ∉ T) ∨ (Qplus.tail e ∉ T ∧ Qplus.head e ∈ T) <;>
        by_cases hR : (a ∈ T ∧ b ∉ T) ∨ (a ∉ T ∧ b ∈ T)
        · rw [if_pos hL, if_pos hR]
        · exfalso; apply hR
          rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rwa [h1, h2] at hL
          · rw [h1, h2] at hL; rcases hL with ⟨p1, p2⟩ | ⟨p1, p2⟩; exact Or.inr ⟨p2, p1⟩; exact Or.inl ⟨p2, p1⟩
        · exfalso; apply hL
          rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rw [h1, h2]; exact hR
          · rw [h1, h2]; rcases hR with ⟨p1, p2⟩ | ⟨p1, p2⟩; exact Or.inr ⟨p2, p1⟩; exact Or.inl ⟨p2, p1⟩
        · rw [if_neg hL, if_neg hR]
      rw [hc e_v0z v₀ z he_v0z_ends, hc e_zu z u hu_spec.2, hc e_zw z w hw_spec.2,
          hc e_wx w x hx_spec.2, hc e_wy w y hy_spec.2]
      omega
    -- Now split into 4 clean cases!
    by_cases hC1 : (v₀ ∈ SV ∧ u ∈ SV) ∧ (x ∉ SV ∧ y ∉ SV)
    · -- Case 1: T = insert z SV (uses hno3 since {v₀, u} ⊆ T and {x, y} ⊆ univ \ T!)
      let T := insert z SV
      have hT : ∀ a, a ≠ z → a ≠ w → (a ∈ T ↔ a ∈ SV) := fun a h1 _ => by simp [T, h1]
      have hT2 : 2 ≤ T.card := by
        have hsub : ({v₀, u} : Finset V) ⊆ T := by intro a ha; simp at ha; rcases ha with rfl | rfl <;> simp [T, hC1.1.1, hC1.1.2]
        rw [← Finset.card_pair hu_ne_v0.symm]; exact Finset.card_le_card hsub
      have hTc2 : 2 ≤ (Finset.univ \ T).card := by
        have hsub : ({x, y} : Finset V) ⊆ Finset.univ \ T := by
          intro a ha; simp at ha; rcases ha with rfl | rfl <;> simp [T, hx_ne_z, hy_ne_z, hC1.2.1, hC1.2.2]
        rw [← Finset.card_pair hx_ne_y]; exact Finset.card_le_card hsub
      have hcut4 := hno3 T hT2 hTc2; rw [hQcut T hT] at hcut4
      have hvT : v₀ ∈ T := Finset.mem_insert_of_mem hC1.1.1
      have huT : u ∈ T := Finset.mem_insert_of_mem hC1.1.2
      have hzT : z ∈ T := Finset.mem_insert_self _ _
      have hwT : w ∉ T := by simp [T, hw_ne_z, hw_not_SV]
      have hxT : x ∉ T := by simp [T, hx_ne_z, hC1.2.1]
      have hyT : y ∉ T := by simp [T, hy_ne_z, hC1.2.2]
      simp only [hvT, huT, hzT, hwT, hxT, hyT, hC1.1.1, hC1.1.2, hC1.2.1, hC1.2.2,
        not_true_eq_false, not_false_eq_true, and_self, and_false, false_and, or_self, or_false, false_or, ↓reduceIte] at hcut4 hHcut
      omega
    · by_cases hC2 : (v₀ ∉ SV ∧ u ∉ SV) ∧ (x ∈ SV ∧ y ∈ SV)
      · -- Case 2: T = insert w SV (uses hno3 since {x, y} ⊆ T and {v₀, u} ⊆ univ \ T!)
        let T := insert w SV
        have hT : ∀ a, a ≠ z → a ≠ w → (a ∈ T ↔ a ∈ SV) := fun a _ h2 => by simp [T, h2]
        have hT2 : 2 ≤ T.card := by
          have hsub : ({x, y} : Finset V) ⊆ T := by intro a ha; simp at ha; rcases ha with rfl | rfl <;> simp [T, hC2.2.1, hC2.2.2]
          rw [← Finset.card_pair hx_ne_y]; exact Finset.card_le_card hsub
        have hTc2 : 2 ≤ (Finset.univ \ T).card := by
          have hsub : ({v₀, u} : Finset V) ⊆ Finset.univ \ T := by
            intro a ha; simp at ha; rcases ha with rfl | rfl <;> simp [T, hw_ne_v0.symm, hu_ne_w, hC2.1.1, hC2.1.2]
          rw [← Finset.card_pair hu_ne_v0.symm]; exact Finset.card_le_card hsub
        have hcut4 := hno3 T hT2 hTc2; rw [hQcut T hT] at hcut4
        have hvT : v₀ ∉ T := by simp [T, hw_ne_v0.symm, hC2.1.1]
        have huT : u ∉ T := by simp [T, hu_ne_w, hC2.1.2]
        have hzT : z ∉ T := by simp [T, hw_ne_z.symm, hz_not_SV]
        have hwT : w ∈ T := Finset.mem_insert_self _ _
        have hxT : x ∈ T := Finset.mem_insert_of_mem hC2.2.1
        have hyT : y ∈ T := Finset.mem_insert_of_mem hC2.2.2
        simp only [hvT, huT, hzT, hwT, hxT, hyT, hC2.1.1, hC2.1.2, hC2.2.1, hC2.2.2,
          not_true_eq_false, not_false_eq_true, and_self, and_false, false_and, or_self, or_false, false_or, ↓reduceIte] at hcut4 hHcut
        omega
      · by_cases hC3 : (v₀ ∈ SV ∧ u ∈ SV) ∨ (x ∈ SV ∧ y ∈ SV)
        · -- Case 3: T = insert z (insert w SV) (uses h3; exact cut match!)
          let T := insert z (insert w SV)
          have hT : ∀ a, a ≠ z → a ≠ w → (a ∈ T ↔ a ∈ SV) := fun a h1 h2 => by simp [T, h1, h2]
          have hTne : T.Nonempty := ⟨z, Finset.mem_insert_self _ _⟩
          have hTcne : (Finset.univ \ T).Nonempty := by
            obtain ⟨a, ha⟩ := hScne
            have ha' : a ∉ S := (Finset.mem_sdiff.mp ha).2
            exact ⟨a.1, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by simp [T, a.2.1, a.2.2, hSV_iff, ha']⟩⟩
          have hcut3 := h3 T hTne hTcne; rw [hQcut T hT] at hcut3
          have hzT : z ∈ T := Finset.mem_insert_self _ _
          have hwT : w ∈ T := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
          have hvT : v₀ ∈ T ↔ v₀ ∈ SV := hT v₀ hz_ne_v0.symm hw_ne_v0.symm
          have huT : u ∈ T ↔ u ∈ SV := hT u hu_ne_z hu_ne_w
          have hxT : x ∈ T ↔ x ∈ SV := hT x hx_ne_z hx_ne_w
          have hyT : y ∈ T ↔ y ∈ SV := hT y hy_ne_z hy_ne_w
          simp only [hzT, hwT, hvT, huT, hxT, hyT, not_true_eq_false, and_false, false_and, or_false, false_or, true_and, and_true, ↓reduceIte] at hcut3
          -- Compare (if v₀ ∉ SV) + (if u ∉ SV) + (if x ∉ SV) + (if y ∉ SV) with (if v₀ ≠ u in SV) + (if x ≠ y in SV)!
          by_cases hv : v₀ ∈ SV <;> by_cases hu' : u ∈ SV <;> by_cases hx' : x ∈ SV <;> by_cases hy' : y ∈ SV <;>
            simp only [hv, hu', hx', hy', not_true_eq_false, not_false_eq_true, and_self, and_false, false_and, or_self, or_false, false_or, ↓reduceIte] at hC1 hC2 hC3 hcut3 hHcut <;>
            omega
        · -- Case 4: T = SV (uses h3; exact cut match!)
          have hT : ∀ a, a ≠ z → a ≠ w → (a ∈ SV ↔ a ∈ SV) := fun _ _ _ => Iff.rfl
          have hTne : SV.Nonempty := by obtain ⟨a, ha⟩ := hSne; exact ⟨a.1, (hSV_iff a).mpr ha⟩
          have hTcne : (Finset.univ \ SV).Nonempty := ⟨z, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hz_not_SV⟩⟩
          have hcut3 := h3 SV hTne hTcne; rw [hQcut SV hT] at hcut3
          simp only [hz_not_SV, hw_not_SV, not_false_eq_true, and_false, false_and, or_false, false_or, true_and, and_true, ↓reduceIte] at hcut3
          by_cases hv : v₀ ∈ SV <;> by_cases hu' : u ∈ SV <;> by_cases hx' : x ∈ SV <;> by_cases hy' : y ∈ SV <;>
            simp only [hv, hu', hx', hy', not_true_eq_false, not_false_eq_true, and_self, and_false, false_and, or_self, or_false, false_or, ↓reduceIte] at hC3 hcut3 hHcut <;>
            omega
  -- Apply IH to Hplus!
  obtain ⟨wcH⟩ := ih VH EH Hplus v₀H (by omega) hH_cub hH_3ec (by omega)
  -- Step 3: Lift wcH on H = Hplus.deleteVertex v₀H to Q = Qplus.deleteVertex v₀!
    -- Step 3: Lift wcH on H = Hplus.deleteVertex v₀H to Q = Qplus.deleteVertex v₀!
  let Q := Qplus.deleteVertex v₀
  let H := Hplus.deleteVertex v₀H
  let zQ : {a : V // a ≠ v₀} := ⟨z, hz_ne_v0⟩
  let wQ : {a : V // a ≠ v₀} := ⟨w, hw_ne_v0⟩
  let uQ : {a : V // a ≠ v₀} := ⟨u, hu_ne_v0⟩
  let xQ : {a : V // a ≠ v₀} := ⟨x, hx_ne_v0⟩
  let yQ : {a : V // a ≠ v₀} := ⟨y, hy_ne_v0⟩
  have hQ_ends_ne_v0 : ∀ (e : E) (a b : V), a ≠ v₀ → b ≠ v₀ →
      ((Qplus.tail e = a ∧ Qplus.head e = b) ∨ (Qplus.tail e = b ∧ Qplus.head e = a)) →
      Qplus.tail e ≠ v₀ ∧ Qplus.head e ≠ v₀ := fun e a b ha hb h => by
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
    · exact ⟨ha, hb⟩
    · exact ⟨hb, ha⟩
  let e_zuQ : {e : E // Qplus.tail e ≠ v₀ ∧ Qplus.head e ≠ v₀} :=
    ⟨e_zu, hQ_ends_ne_v0 e_zu z u hz_ne_v0 hu_ne_v0 hu_spec.2⟩
  let e_zwQ : {e : E // Qplus.tail e ≠ v₀ ∧ Qplus.head e ≠ v₀} :=
    ⟨e_zw, hQ_ends_ne_v0 e_zw z w hz_ne_v0 hw_ne_v0 hw_spec.2⟩
  let e_wxQ : {e : E // Qplus.tail e ≠ v₀ ∧ Qplus.head e ≠ v₀} :=
    ⟨e_wx, hQ_ends_ne_v0 e_wx w x hw_ne_v0 hx_ne_v0 hx_spec.2⟩
  let e_wyQ : {e : E // Qplus.tail e ≠ v₀ ∧ Qplus.head e ≠ v₀} :=
    ⟨e_wy, hQ_ends_ne_v0 e_wy w y hw_ne_v0 hy_ne_v0 hy_spec.2⟩
  let e_xyH : {e : EH // Hplus.tail e ≠ v₀H ∧ Hplus.head e ≠ v₀H} :=
    ⟨some none, fun h => hx_ne_v0 (congrArg Subtype.val h), fun h => hy_ne_v0 (congrArg Subtype.val h)⟩
  let uH' : {a : VH // a ≠ v₀H} := ⟨uH, fun h => hu_ne_v0 (congrArg Subtype.val h)⟩
  let xH' : {a : VH // a ≠ v₀H} := ⟨xH, fun h => hx_ne_v0 (congrArg Subtype.val h)⟩
  let yH' : {a : VH // a ≠ v₀H} := ⟨yH, fun h => hy_ne_v0 (congrArg Subtype.val h)⟩
  -- Vertex embedding V(H) ↪ V(Q) (misses exactly {zQ, wQ})
  let toVQ (a : {a : VH // a ≠ v₀H}) : {a : V // a ≠ v₀} := ⟨a.1.1, fun h => a.2 (Subtype.ext h)⟩
  have htoVQ_inj : Function.Injective toVQ := fun a b h => by
    rw [Subtype.ext_iff] at h; exact Subtype.ext (Subtype.ext h)
  have htoVQ_ne_z : ∀ a, toVQ a ≠ zQ := fun a h => a.1.2.1 (congrArg Subtype.val h)
  have htoVQ_ne_w : ∀ a, toVQ a ≠ wQ := fun a h => a.1.2.2 (congrArg Subtype.val h)
  have hVQ_cases : ∀ q : {a : V // a ≠ v₀}, q = zQ ∨ q = wQ ∨ ∃ a, toVQ a = q := by
    intro q
    by_cases hz : q = zQ; · exact Or.inl hz
    by_cases hw : q = wQ; · exact Or.inr (Or.inl hw)
    right; right
    have h1 : q.1 ≠ z := fun h => hz (Subtype.ext h)
    have h2 : q.1 ≠ w := fun h => hw (Subtype.ext h)
    exact ⟨⟨⟨q.1, h1, h2⟩, fun h => q.2 (congrArg Subtype.val h)⟩, rfl⟩
  -- Edge embedding from E(Q) \ {e_zuQ, e_zwQ, e_wxQ, e_wyQ} into E(H) \ {e_xyH}
  have hnot_rem_of_Q : ∀ e : {e : E // Qplus.tail e ≠ v₀ ∧ Qplus.head e ≠ v₀},
      e ≠ e_zuQ → e ≠ e_zwQ → e ≠ e_wxQ → e ≠ e_wyQ → e.1 ∉ remE := by
    intro e h1 h2 h3 h4 hm
    simp only [remE, Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl
    · rcases he_v0z_ends with ⟨ht, _⟩ | ⟨_, hh⟩
      · exact e.2.1 ht
      · exact e.2.2 hh
    · exact h1 (Subtype.ext rfl)
    · exact h2 (Subtype.ext rfl)
    · exact h3 (Subtype.ext rfl)
    · exact h4 (Subtype.ext rfl)
  let toEH (e : {e : E // Qplus.tail e ≠ v₀ ∧ Qplus.head e ≠ v₀}) (h : e.1 ∉ remE) :
      {e : EH // Hplus.tail e ≠ v₀H ∧ Hplus.head e ≠ v₀H} :=
    ⟨some (some ⟨e.1, h⟩),
     fun ht => e.2.1 (congrArg Subtype.val ht),
     fun hh => e.2.2 (congrArg Subtype.val hh)⟩
  have hQ_z_inc : ∀ e : {e : E // Qplus.tail e ≠ v₀ ∧ Qplus.head e ≠ v₀},
      (Q.tail e = zQ ∨ Q.head e = zQ) → e = e_zuQ ∨ e = e_zwQ := by
    intro e hinc
    have hinc' : Qplus.tail e.1 = z ∨ Qplus.head e.1 = z := by
      rcases hinc with h | h; exact Or.inl (congrArg Subtype.val h); exact Or.inr (congrArg Subtype.val h)
    have hne_v0z : e.1 ≠ e_v0z := fun h => by
      rcases he_v0z_ends with ⟨ht, _⟩ | ⟨_, hh⟩
      · exact e.2.1 (h.symm ▸ ht)
      · exact e.2.2 (h.symm ▸ hh)
    have hm : e.1 ∈ (Finset.univ.filter (fun e : E => Qplus.tail e = z ∨ Qplus.head e = z)).erase e_v0z :=
      Finset.mem_erase.mpr ⟨hne_v0z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hinc'⟩⟩
    rw [hz_eq2, Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  have hQ_w_inc : ∀ e : {e : E // Qplus.tail e ≠ v₀ ∧ Qplus.head e ≠ v₀},
      (Q.tail e = wQ ∨ Q.head e = wQ) → e = e_zwQ ∨ e = e_wxQ ∨ e = e_wyQ := by
    intro e hinc
    have hinc' : Qplus.tail e.1 = w ∨ Qplus.head e.1 = w := by
      rcases hinc with h | h; exact Or.inl (congrArg Subtype.val h); exact Or.inr (congrArg Subtype.val h)
    by_cases hzw : e.1 = e_zw
    · exact Or.inl (Subtype.ext hzw)
    · have hm : e.1 ∈ (Finset.univ.filter (fun e : E => Qplus.tail e = w ∨ Qplus.head e = w)).erase e_zw :=
        Finset.mem_erase.mpr ⟨hzw, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hinc'⟩⟩
      rw [hw_eq2, Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with h | h
      · exact Or.inr (Or.inl (Subtype.ext h))
      · exact Or.inr (Or.inr (Subtype.ext h))
  -- Common helper: every old edge in H (i.e. some (some e')) lifts to E(Q) with e' ∉ remE
  have hEH_cases : ∀ eH : {e : EH // Hplus.tail e ≠ v₀H ∧ Hplus.head e ≠ v₀H},
      eH = e_xyH ∨ ∃ (eQ : {e : E // Qplus.tail e ≠ v₀ ∧ Qplus.head e ≠ v₀}) (h : eQ.1 ∉ remE), toEH eQ h = eH := by
    intro eH
    cases he : eH.1 with
    | none =>
      exfalso; exact eH.2.1 (by rw [he])
    | some o =>
      cases o with
      | none => exact Or.inl (Subtype.ext he)
      | some e' =>
        right
        have hnt0 : Qplus.tail e'.1 ≠ v₀ := fun h => eH.2.1 (by rw [he]; exact Subtype.ext h)
        have hnh0 : Qplus.head e'.1 ≠ v₀ := fun h => eH.2.2 (by rw [he]; exact Subtype.ext h)
        exact ⟨⟨e'.1, hnt0, hnh0⟩, e'.2, Subtype.ext (by rw [he])⟩
  have hVH_card_del : Fintype.card {a : VH // a ≠ v₀H} + 2 = Fintype.card {a : V // a ≠ v₀} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl,
        show Fintype.card {a : VH // a = v₀H} = 1 from Fintype.card_unique,
        show Fintype.card {a : V // a = v₀} = 1 from Fintype.card_unique, hVH_card]
    omega
  -- Split on whether e_xyH ∈ wcH.blue!
  by_cases hxy_bl : e_xyH ∈ wcH.blue
  · -- CASE 2b: e_xyH is BLUE in H!
    let THm := Multigraph.Subgraph.ofEdges H Finset.univ (wcH.blue.erase e_xyH)
      (fun _ => Finset.mem_univ _) (fun _ => Finset.mem_univ _)
    -- Every vertex of H connects in THm to xH' or yH'!
    have hreach_xy : ∀ a : {a : VH // a ≠ v₀H},
        Relation.ReflTransGen THm.Adj a xH' ∨ Relation.ReflTransGen THm.Adj a yH' := by
      intro a
      have hwalk := wcH.blue_tree.2.1.2 xH' (Finset.mem_univ _) a (Finset.mem_univ _)
      have hsym : ∀ p q, Relation.ReflTransGen THm.Adj p q → Relation.ReflTransGen THm.Adj q p := fun p q h => by
        induction h with
        | refl => exact .refl
        | tail _ hs ih =>
          rcases hs with ⟨e, he, h1 | h1⟩
          · exact Relation.ReflTransGen.head ⟨e, he, Or.inr h1⟩ ih
          · exact Relation.ReflTransGen.head ⟨e, he, Or.inl h1⟩ ih
      suffices h : Relation.ReflTransGen THm.Adj xH' a ∨ Relation.ReflTransGen THm.Adj yH' a by
        rcases h with h1 | h1; exact Or.inl (hsym _ _ h1); exact Or.inr (hsym _ _ h1)
      induction hwalk with
      | refl => exact Or.inl .refl
      | @tail p q _ hs ih =>
        rcases hs with ⟨e, heB, hinc⟩
        by_cases he_xy : e = e_xyH
        · subst he_xy
          rcases hinc with ⟨_, h2⟩ | ⟨h1, _⟩
          · right; rw [← h2]; exact .refl
          · left; rw [← h1]; exact .refl
        · have heM : e ∈ wcH.blue.erase e_xyH := Finset.mem_erase.mpr ⟨he_xy, heB⟩
          rcases ih with h1 | h1
          · exact Or.inl (h1.tail ⟨e, heM, hinc⟩)
          · exact Or.inr (h1.tail ⟨e, heM, hinc⟩)
    -- Symmetric helper for Case 2b: given (xNear, xFar, eNear, eFar) where uH' reaches xNear in THm!
    have hcase2b :
        ∀ (xNearH xFarH : {a : VH // a ≠ v₀H})
          (eNearQ eFarQ : {e : E // Qplus.tail e ≠ v₀ ∧ Qplus.head e ≠ v₀}),
          ((xNearH = xH' ∧ xFarH = yH' ∧ eNearQ = e_wxQ ∧ eFarQ = e_wyQ) ∨
           (xNearH = yH' ∧ xFarH = xH' ∧ eNearQ = e_wyQ ∧ eFarQ = e_wxQ)) →
          Relation.ReflTransGen THm.Adj uH' xNearH →
          Nonempty (WellColouring Q) := by
      intro xNearH xFarH eNearQ eFarQ hchoice hu_near
      have heNear_ends : (Q.tail eNearQ = wQ ∧ Q.head eNearQ = toVQ xNearH) ∨
          (Q.tail eNearQ = toVQ xNearH ∧ Q.head eNearQ = wQ) := by
        rcases hchoice with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · rcases hx_spec.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inl ⟨Subtype.ext h1, Subtype.ext h2⟩
          · exact Or.inr ⟨Subtype.ext h1, Subtype.ext h2⟩
        · rcases hy_spec.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inl ⟨Subtype.ext h1, Subtype.ext h2⟩
          · exact Or.inr ⟨Subtype.ext h1, Subtype.ext h2⟩
      have heFar_ends : (Q.tail eFarQ = wQ ∧ Q.head eFarQ = toVQ xFarH) ∨
          (Q.tail eFarQ = toVQ xFarH ∧ Q.head eFarQ = wQ) := by
        rcases hchoice with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
        · rcases hy_spec.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inl ⟨Subtype.ext h1, Subtype.ext h2⟩
          · exact Or.inr ⟨Subtype.ext h1, Subtype.ext h2⟩
        · rcases hx_spec.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inl ⟨Subtype.ext h1, Subtype.ext h2⟩
          · exact Or.inr ⟨Subtype.ext h1, Subtype.ext h2⟩
      have he_zu_ends : (Q.tail e_zuQ = zQ ∧ Q.head e_zuQ = toVQ uH') ∨
          (Q.tail e_zuQ = toVQ uH' ∧ Q.head e_zuQ = zQ) := by
        rcases hu_spec.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨Subtype.ext h1, Subtype.ext h2⟩
        · exact Or.inr ⟨Subtype.ext h1, Subtype.ext h2⟩
      have he_zw_ends : (Q.tail e_zwQ = zQ ∧ Q.head e_zwQ = wQ) ∨
          (Q.tail e_zwQ = wQ ∧ Q.head e_zwQ = zQ) := by
        rcases hw_spec.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨Subtype.ext h1, Subtype.ext h2⟩
        · exact Or.inr ⟨Subtype.ext h1, Subtype.ext h2⟩
      have heNear_ne_Far : eNearQ ≠ eFarQ := by
        rcases hchoice with ⟨_, _, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩
        · exact fun h => he_wx_ne_wy (congrArg Subtype.val h)
        · exact fun h => he_wx_ne_wy (congrArg Subtype.val h).symm
      have heFar_ne_zu : eFarQ ≠ e_zuQ := by
        rcases hchoice with ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩
        · exact fun h => he_zu_ne_wy (congrArg Subtype.val h).symm
        · exact fun h => he_zu_ne_wx (congrArg Subtype.val h).symm
      have heFar_ne_zw : eFarQ ≠ e_zwQ := by
        rcases hchoice with ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩
        · exact fun h => he_wy_ne_zw (congrArg Subtype.val h)
        · exact fun h => he_wx_ne_zw (congrArg Subtype.val h)
      have heNear_ne_zu : eNearQ ≠ e_zuQ := by
        rcases hchoice with ⟨_, _, rfl, _⟩ | ⟨_, _, rfl, _⟩
        · exact fun h => he_zu_ne_wx (congrArg Subtype.val h).symm
        · exact fun h => he_zu_ne_wy (congrArg Subtype.val h).symm
      have heNear_ne_zw : eNearQ ≠ e_zwQ := by
        rcases hchoice with ⟨_, _, rfl, _⟩ | ⟨_, _, rfl, _⟩
        · exact fun h => he_wx_ne_zw (congrArg Subtype.val h)
        · exact fun h => he_wy_ne_zw (congrArg Subtype.val h)
      have he_zu_ne_zwQ : e_zuQ ≠ e_zwQ := fun h => he_zu_ne_zw (congrArg Subtype.val h)
      have heNear_in_rem : eNearQ.1 ∈ remE := by
        rcases hchoice with ⟨_, _, rfl, _⟩ | ⟨_, _, rfl, _⟩ <;> simp [remE, e_wxQ, e_wyQ]
      have heFar_in_rem : eFarQ.1 ∈ remE := by
        rcases hchoice with ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;> simp [remE, e_wxQ, e_wyQ]
      -- Define blue ⊆ E(Q): {e_zuQ, e_zwQ, eFarQ} ∪ {e ∉ remE | toEH e ∈ wcH.blue.erase e_xyH}
      let blue : Finset {e : E // Qplus.tail e ≠ v₀ ∧ Qplus.head e ≠ v₀} :=
        Finset.univ.filter fun e =>
          e = e_zuQ ∨ e = e_zwQ ∨ e = eFarQ ∨
          ∃ h : e.1 ∉ remE, toEH e h ∈ wcH.blue.erase e_xyH
      have hzu_bl : e_zuQ ∈ blue := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl rfl⟩
      have hzw_bl : e_zwQ ∈ blue := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr (Or.inl rfl)⟩
      have hFar_bl : eFarQ ∈ blue := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr (Or.inr (Or.inl rfl))⟩
      have hNear_red : eNearQ ∉ blue := by
        intro hm
        rcases (Finset.mem_filter.mp hm).2 with h | h | h | ⟨h, _⟩
        · exact heNear_ne_zu h
        · exact heNear_ne_zw h
        · exact heNear_ne_Far h
        · exact h heNear_in_rem
      -- Bijection between wcH.blue and blue \ {e_zuQ, e_zwQ} (sending e_xyH ↦ eFarQ)!
      have hblue_card : blue.card + 1 = Fintype.card {a : V // a ≠ v₀} := by
        have hbij_card : (blue.erase e_zuQ |>.erase e_zwQ).card = wcH.blue.card := by
          refine Finset.card_bij
            (fun e he => if h : e.1 ∉ remE then toEH e h else e_xyH)
            (fun e he => by
              have hne_zw := Finset.ne_of_mem_erase he
              have he1 := Finset.mem_of_mem_erase he
              have hne_zu := Finset.ne_of_mem_erase he1
              have hbl := (Finset.mem_filter.mp (Finset.mem_of_mem_erase he1)).2
              by_cases h : e.1 ∉ remE
              · rw [dif_pos h]
                rcases hbl with h1 | h1 | h1 | ⟨_, hmem⟩
                · exact absurd h1 hne_zu
                · exact absurd h1 hne_zw
                · exact absurd (by rw [h1]; exact heFar_in_rem) h
                · exact Finset.mem_of_mem_erase hmem
              · rw [dif_neg h]; exact hxy_bl)
            (fun e1 he1 e2 he2 heq => by
              have hne_zw1 := Finset.ne_of_mem_erase he1
              have hne_zu1 := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase he1)
              have hne_zw2 := Finset.ne_of_mem_erase he2
              have hne_zu2 := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase he2)
              have hbl1 := (Finset.mem_filter.mp (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase he1))).2
              have hbl2 := (Finset.mem_filter.mp (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase he2))).2
              by_cases h1 : e1.1 ∉ remE <;> by_cases h2 : e2.1 ∉ remE
              · rw [dif_pos h1, dif_pos h2] at heq
                have h_tmp := Option.some.inj (Option.some.inj (congrArg Subtype.val heq))
                rw [Subtype.ext_iff] at h_tmp; exact Subtype.ext h_tmp
              · rw [dif_pos h1, dif_neg h2] at heq
                exfalso; have hv := congrArg Subtype.val heq; dsimp only [toEH, e_xyH] at hv; cases hv
              · rw [dif_neg h1, dif_pos h2] at heq
                exfalso; have hv := congrArg Subtype.val heq; dsimp only [toEH, e_xyH] at hv; cases hv
              · have hf1 : e1 = eFarQ := by
                  rcases hbl1 with h | h | h | ⟨h', _⟩
                  · exact absurd h hne_zu1
                  · exact absurd h hne_zw1
                  · exact h
                  · exact absurd h' h1
                have hf2 : e2 = eFarQ := by
                  rcases hbl2 with h | h | h | ⟨h', _⟩
                  · exact absurd h hne_zu2
                  · exact absurd h hne_zw2
                  · exact h
                  · exact absurd h' h2
                exact hf1.trans hf2.symm)
            (fun eH heH => by
              rcases hEH_cases eH with rfl | ⟨eQ, hnotrem, rfl⟩
              · refine ⟨eFarQ, Finset.mem_erase.mpr ⟨heFar_ne_zw, Finset.mem_erase.mpr ⟨heFar_ne_zu, hFar_bl⟩⟩, ?_⟩
                rw [dif_neg (not_not.mpr heFar_in_rem)]
              · have hne_zu : eQ ≠ e_zuQ := fun h => hnotrem (by rw [h]; simp [remE, e_zuQ])
                have hne_zw : eQ ≠ e_zwQ := fun h => hnotrem (by rw [h]; simp [remE, e_zwQ])
                have hne_xy : toEH eQ hnotrem ≠ e_xyH := fun h => by have hv := congrArg Subtype.val h; dsimp only [toEH, e_xyH] at hv; cases hv
                have heQ_bl : eQ ∈ blue := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr (Or.inr (Or.inr ⟨hnotrem, Finset.mem_erase.mpr ⟨hne_xy, heH⟩⟩))⟩
                refine ⟨eQ, Finset.mem_erase.mpr ⟨hne_zw, Finset.mem_erase.mpr ⟨hne_zu, heQ_bl⟩⟩, ?_⟩
                rw [dif_pos hnotrem])
        have hzw_in : e_zwQ ∈ blue.erase e_zuQ := Finset.mem_erase.mpr ⟨he_zu_ne_zwQ.symm, hzw_bl⟩
        rw [Finset.card_erase_of_mem hzw_in, Finset.card_erase_of_mem hzu_bl] at hbij_card
        have hB_H := spanningTree_edges_card wcH.blue_tree
        have hge2 : 2 ≤ blue.card := by
          have hsub : ({e_zuQ, e_zwQ} : Finset _) ⊆ blue := by intro e he; simp at he; rcases he with rfl | rfl; exact hzu_bl; exact hzw_bl
          rw [← Finset.card_pair he_zu_ne_zwQ]; exact Finset.card_le_card hsub
        change wcH.blue.card + 1 = Fintype.card {a : VH // a ≠ v₀H} at hB_H
        omega
      -- Spanning tree: T = ofEdges Q univ blue is connected!
      let T := Multigraph.Subgraph.ofEdges Q Finset.univ blue (fun _ => Finset.mem_univ _) (fun _ => Finset.mem_univ _)
      have hlift_THm : ∀ a b : {a : VH // a ≠ v₀H}, Relation.ReflTransGen THm.Adj a b →
          Relation.ReflTransGen T.Adj (toVQ a) (toVQ b) := by
        intro a b hab
        induction hab with
        | refl => exact .refl
        | tail _ hs ih =>
          rcases hs with ⟨eH, heH, hinc⟩
          have hne_xy : eH ≠ e_xyH := Finset.ne_of_mem_erase heH
          rcases hEH_cases eH with rfl | ⟨eQ, hnotrem, rfl⟩
          · exact absurd rfl hne_xy
          · have heQ_bl : eQ ∈ blue := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr (Or.inr (Or.inr ⟨hnotrem, heH⟩))⟩
            refine ih.tail ⟨eQ, heQ_bl, ?_⟩
            rcases hinc with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact Or.inl ⟨Subtype.ext (congrArg (fun x => x.1.1) h1), Subtype.ext (congrArg (fun x => x.1.1) h2)⟩
            · exact Or.inr ⟨Subtype.ext (congrArg (fun x => x.1.1) h1), Subtype.ext (congrArg (fun x => x.1.1) h2)⟩
      have hsym_T : ∀ a b, Relation.ReflTransGen T.Adj a b → Relation.ReflTransGen T.Adj b a := fun a b h => by
        induction h with
        | refl => exact .refl
        | tail _ hs ih =>
          rcases hs with ⟨e, he, h1 | h1⟩
          · exact Relation.ReflTransGen.head ⟨e, he, Or.inr h1⟩ ih
          · exact Relation.ReflTransGen.head ⟨e, he, Or.inl h1⟩ ih
      have hreach_wQ : ∀ q : {a : V // a ≠ v₀}, Relation.ReflTransGen T.Adj q wQ := by
        have hz_w : Relation.ReflTransGen T.Adj zQ wQ := Relation.ReflTransGen.single ⟨e_zwQ, hzw_bl, he_zw_ends⟩
        have hu_z : Relation.ReflTransGen T.Adj (toVQ uH') zQ :=
          Relation.ReflTransGen.single ⟨e_zuQ, hzu_bl, by rcases he_zu_ends with h | h; exact Or.inr h; exact Or.inl h⟩
        have hxNear_w : Relation.ReflTransGen T.Adj (toVQ xNearH) wQ :=
          (hsym_T _ _ (hlift_THm _ _ hu_near)).trans (hu_z.trans hz_w)
        have hxFar_w : Relation.ReflTransGen T.Adj (toVQ xFarH) wQ :=
          Relation.ReflTransGen.single ⟨eFarQ, hFar_bl, by rcases heFar_ends with h | h; exact Or.inr h; exact Or.inl h⟩
        intro q
        rcases hVQ_cases q with rfl | rfl | ⟨a, rfl⟩
        · exact hz_w
        · exact .refl
        · have hor : Relation.ReflTransGen THm.Adj a xNearH ∨ Relation.ReflTransGen THm.Adj a xFarH := by
            rcases hchoice with ⟨rfl, rfl, _, _⟩ | ⟨rfl, rfl, _, _⟩
            · exact hreach_xy a
            · exact (hreach_xy a).symm
          rcases hor with h | h
          · exact (hlift_THm _ _ h).trans hxNear_w
          · exact (hlift_THm _ _ h).trans hxFar_w
      have hT_conn : T.Connected := ⟨⟨wQ, Finset.mem_univ _⟩, fun a _ b _ => (hreach_wQ a).trans (hsym_T _ _ (hreach_wQ b))⟩
      have hT_tree : T.IsSpanningTree :=
        ⟨rfl, hT_conn, connected_edges_eq_verts_sub_one_isForest T hT_conn (by change blue.card + 1 = (Finset.univ : Finset _).card; rw [Finset.card_univ]; exact hblue_card)⟩
      -- Red quotient: wQ merges into xNearH (via eNearQ), zQ is singleton, all other red edges match H!
      have hred_iff : ∀ a b : {a : VH // a ≠ v₀H},
          Relation.ReflTransGen (redAdj H wcH.blue) a b ↔
          Relation.ReflTransGen (redAdj Q blue) (toVQ a) (toVQ b) := by
        intro a b
        constructor
        · intro hab
          induction hab with
          | refl => exact .refl
          | tail _ hs ih =>
            rcases hs with ⟨eH, heH_R, hinc⟩
            have hne_xy : eH ≠ e_xyH := fun h => heH_R (h ▸ hxy_bl)
            rcases hEH_cases eH with rfl | ⟨eQ, hnotrem, rfl⟩
            · exact absurd rfl hne_xy
            · have heQ_R : eQ ∉ blue := by
                intro hm; rcases (Finset.mem_filter.mp hm).2 with h | h | h | ⟨_, hmem⟩
                · exact hnotrem (by rw [h]; simp [remE, e_zuQ, e_zwQ])
                · exact hnotrem (by rw [h]; simp [remE, e_zuQ, e_zwQ])
                · exact hnotrem (by rw [h]; exact heFar_in_rem)
                · exact heH_R (Finset.mem_of_mem_erase hmem)
              refine ih.tail ⟨eQ, heQ_R, ?_⟩
              rcases hinc with ⟨h1, h2⟩ | ⟨h1, h2⟩
              · exact Or.inl ⟨Subtype.ext (congrArg (fun x => x.1.1) h1), Subtype.ext (congrArg (fun x => x.1.1) h2)⟩
              · exact Or.inr ⟨Subtype.ext (congrArg (fun x => x.1.1) h1), Subtype.ext (congrArg (fun x => x.1.1) h2)⟩
        · intro hab
          -- Project every vertex of Q to H (sending wQ ↦ xNearH; zQ never visited since all its Q-edges are blue!)
          let projH (q : {a : V // a ≠ v₀}) : {a : VH // a ≠ v₀H} :=
            if hz : q = zQ then xNearH
            else if hw : q = wQ then xNearH
            else ⟨⟨q.1, fun h => hz (Subtype.ext h), fun h => hw (Subtype.ext h)⟩, fun h => q.2 (congrArg Subtype.val h)⟩
          have hproj_toVQ : ∀ a, projH (toVQ a) = a := fun a => by
            dsimp only [projH]; rw [dif_neg (htoVQ_ne_z a), dif_neg (htoVQ_ne_w a)]
          have hgo : ∀ p q, Relation.ReflTransGen (redAdj Q blue) p q →
              p ≠ zQ → Relation.ReflTransGen (redAdj H wcH.blue) (projH p) (projH q) ∧ q ≠ zQ := by
            intro p q hpq hp_nz
            induction hpq with
            | refl => exact ⟨.refl, hp_nz⟩
            | @tail r s _ hs ih =>
              obtain ⟨ihr, hr_nz⟩ := ih
              rcases hs with ⟨eQ, heQ_R, hinc⟩
              have hne_zu : eQ ≠ e_zuQ := fun h => heQ_R (h ▸ hzu_bl)
              have hne_zw : eQ ≠ e_zwQ := fun h => heQ_R (h ▸ hzw_bl)
              have hne_Far : eQ ≠ eFarQ := fun h => heQ_R (h ▸ hFar_bl)
              have hs_nz : s ≠ zQ := fun hs_eq => by
                have hinc_z : Q.tail eQ = zQ ∨ Q.head eQ = zQ := by
                  rcases hinc with ⟨_, h2⟩ | ⟨h1, _⟩; exact Or.inr (h2.trans hs_eq); exact Or.inl (h1.trans hs_eq)
                rcases hQ_z_inc eQ hinc_z with h | h; exact hne_zu h; exact hne_zw h
              refine ⟨?_, hs_nz⟩
              by_cases hNear : eQ = eNearQ
              · subst hNear
                -- Both endpoints of eNearQ project to xNearH!
                have hpr : projH r = xNearH := by
                  rcases hinc with ⟨h1, _⟩ | ⟨_, h2⟩
                  · rcases heNear_ends with ⟨ht, _⟩ | ⟨ht, _⟩
                    · rw [← h1, ht]; simp [projH, hw_ne_z]
                    · rw [← h1, ht, hproj_toVQ]
                  · rcases heNear_ends with ⟨_, hh⟩ | ⟨_, hh⟩
                    · rw [← h2, hh, hproj_toVQ]
                    · rw [← h2, hh]; simp [projH, hw_ne_z]
                have hps : projH s = xNearH := by
                  rcases hinc with ⟨_, h2⟩ | ⟨h1, _⟩
                  · rcases heNear_ends with ⟨_, hh⟩ | ⟨_, hh⟩
                    · rw [← h2, hh, hproj_toVQ]
                    · rw [← h2, hh]; simp [projH, hw_ne_z]
                  · rcases heNear_ends with ⟨ht, _⟩ | ⟨ht, _⟩
                    · rw [← h1, ht]; simp [projH, hw_ne_z]
                    · rw [← h1, ht, hproj_toVQ]
                rw [hps, ← hpr]; exact ihr
              · have hnotrem : eQ.1 ∉ remE := by
                  rcases hchoice with ⟨_, _, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩
                  · exact hnot_rem_of_Q eQ hne_zu hne_zw hNear hne_Far
                  · exact hnot_rem_of_Q eQ hne_zu hne_zw hne_Far hNear
                have heH_R : toEH eQ hnotrem ∉ wcH.blue := fun hm => by
                  have hne_xy : toEH eQ hnotrem ≠ e_xyH := fun h => by have hv := congrArg Subtype.val h; dsimp only [toEH, e_xyH] at hv; cases hv
                  exact heQ_R (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr (Or.inr (Or.inr ⟨hnotrem, Finset.mem_erase.mpr ⟨hne_xy, hm⟩⟩))⟩)
                have hnot_w : r ≠ wQ ∧ s ≠ wQ := by
                  constructor <;> intro hw_eq
                  · have hinc_w : Q.tail eQ = wQ ∨ Q.head eQ = wQ := by
                      rcases hinc with ⟨h1, _⟩ | ⟨_, h2⟩; exact Or.inl (h1.trans hw_eq); exact Or.inr (h2.trans hw_eq)
                    rcases hQ_w_inc eQ hinc_w with h | h | h
                    · exact hne_zw h
                    · rcases hchoice with ⟨_, _, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩; exact hNear h; exact hne_Far h
                    · rcases hchoice with ⟨_, _, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩; exact hne_Far h; exact hNear h
                  · have hinc_w : Q.tail eQ = wQ ∨ Q.head eQ = wQ := by
                      rcases hinc with ⟨_, h2⟩ | ⟨h1, _⟩; exact Or.inr (h2.trans hw_eq); exact Or.inl (h1.trans hw_eq)
                    rcases hQ_w_inc eQ hinc_w with h | h | h
                    · exact hne_zw h
                    · rcases hchoice with ⟨_, _, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩; exact hNear h; exact hne_Far h
                    · rcases hchoice with ⟨_, _, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩; exact hne_Far h; exact hNear h
                refine ihr.tail ⟨toEH eQ hnotrem, heH_R, ?_⟩
                rcases hinc with ⟨h1, h2⟩ | ⟨h1, h2⟩
                · left; constructor <;> (refine Subtype.ext (Subtype.ext ?_); dsimp only [H, Multigraph.deleteVertex, toEH, Hplus, projH])
                  · rw [dif_neg hr_nz, dif_neg hnot_w.1]; exact congrArg Subtype.val h1
                  · rw [dif_neg hs_nz, dif_neg hnot_w.2]; exact congrArg Subtype.val h2
                · right; constructor <;> (refine Subtype.ext (Subtype.ext ?_); dsimp only [H, Multigraph.deleteVertex, toEH, Hplus, projH])
                  · rw [dif_neg hs_nz, dif_neg hnot_w.2]; exact congrArg Subtype.val h1
                  · rw [dif_neg hr_nz, dif_neg hnot_w.1]; exact congrArg Subtype.val h2
          simpa [hproj_toVQ] using (hgo (toVQ a) (toVQ b) hab (htoVQ_ne_z a)).1
      -- Build Q / red 2-construction: map wcH.twoConstr onto W_old = univ \ {⟦zQ⟧}, then join with {⟦zQ⟧} via {e_zuQ, e_zwQ}!
      let qz : Quotient (redSetoid Q blue) := Quotient.mk _ zQ
      let embQ : Quotient (redSetoid H wcH.blue) ↪ Quotient (redSetoid Q blue) :=
        { toFun := Quotient.lift (fun a => Quotient.mk (redSetoid Q blue) (toVQ a))
            (fun _ _ h => Quotient.sound ((hred_iff _ _).mp h))
          inj' := fun q1 q2 heq => by
            obtain ⟨a, rfl⟩ := Quotient.exists_rep q1
            obtain ⟨b, rfl⟩ := Quotient.exists_rep q2
            exact Quotient.sound ((hred_iff a b).mpr (Quotient.exact heq)) }
      have hqz_not_img : ∀ qH, embQ qH ≠ qz := by
        intro qH heq
        obtain ⟨a, rfl⟩ := Quotient.exists_rep qH
        have hrel : Relation.ReflTransGen (redAdj Q blue) zQ (toVQ a) := (redSetoid Q blue).symm (Quotient.exact heq)
        have hstay : ∀ q, Relation.ReflTransGen (redAdj Q blue) zQ q → q = zQ := fun q h => by
          induction h with
          | refl => rfl
          | tail _ hs ih =>
            subst ih; rcases hs with ⟨eQ, heQ_R, ⟨h1, _⟩ | ⟨_, h2⟩⟩
            · rcases hQ_z_inc eQ (Or.inl h1) with rfl | rfl; exact absurd hzu_bl heQ_R; exact absurd hzw_bl heQ_R
            · rcases hQ_z_inc eQ (Or.inr h2) with rfl | rfl; exact absurd hzu_bl heQ_R; exact absurd hzw_bl heQ_R
        exact htoVQ_ne_z a (hstay _ hrel)
      have hwQ_red : Quotient.mk (redSetoid Q blue) wQ = embQ (Quotient.mk _ xNearH) :=
        Quotient.sound (Relation.ReflTransGen.single ⟨eNearQ, hNear_red, heNear_ends⟩)
      let embF : {e // e ∈ wcH.blue} ↪ {e // e ∈ blue} :=
        { toFun := fun eH =>
            if hxy : eH.1 = e_xyH then ⟨eFarQ, hFar_bl⟩
            else
              let h := hEH_cases eH.1
              have hex : ∃ (eQ : {e : E // Qplus.tail e ≠ v₀ ∧ Qplus.head e ≠ v₀}) (hn : eQ.1 ∉ remE), toEH eQ hn = eH.1 :=
                h.resolve_left hxy
              ⟨hex.choose, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
                Or.inr (Or.inr (Or.inr ⟨hex.choose_spec.choose, Finset.mem_erase.mpr ⟨by rw [hex.choose_spec.choose_spec]; exact hxy, by rw [hex.choose_spec.choose_spec]; exact eH.2⟩⟩))⟩⟩
          inj' := fun e1 e2 heq => by
            dsimp only at heq
            by_cases h1 : e1.1 = e_xyH <;> by_cases h2 : e2.1 = e_xyH
            · exact Subtype.ext (h1.trans h2.symm)
            · exfalso
              rw [dif_pos h1, dif_neg h2] at heq
              have hval := congrArg (fun x => x.1.1) heq
              exact ((hEH_cases e2.1).resolve_left h2).choose_spec.choose (hval ▸ heFar_in_rem)
            · exfalso
              rw [dif_neg h1, dif_pos h2] at heq
              have hval := congrArg (fun x => x.1.1) heq
              exact ((hEH_cases e1.1).resolve_left h1).choose_spec.choose (hval.symm ▸ heFar_in_rem)
            · rw [dif_neg h1, dif_neg h2] at heq
              have hval : ((hEH_cases e1.1).resolve_left h1).choose = ((hEH_cases e2.1).resolve_left h2).choose :=
                congrArg Subtype.val heq
              refine Subtype.ext ?_
              rw [← ((hEH_cases e1.1).resolve_left h1).choose_spec.choose_spec,
                  ← ((hEH_cases e2.1).resolve_left h2).choose_spec.choose_spec]
              refine Subtype.ext ?_; dsimp only [toEH]; rw [Subtype.ext_iff] at hval; congr 2; exact Subtype.ext hval }
      -- Lift wcH.twoConstr along (embQ, embF)
      have htc_old : TwoConstruction (redQuotient Q blue) (Finset.univ.map embQ) (Finset.univ.map embF) := by
        have hgo : ∀ {Wa : Finset (Quotient (redSetoid H wcH.blue))} {Fa : Finset {e // e ∈ wcH.blue}},
            TwoConstruction (redQuotient H wcH.blue) Wa Fa →
            TwoConstruction (redQuotient Q blue) (Wa.map embQ) (Fa.map embF) := by
          intro Wa Fa tc
          induction tc with
          | single w => simpa [Finset.map_singleton, Finset.map_empty] using TwoConstruction.single (M := redQuotient Q blue) (embQ w)
          | @join Wa Wb Fa Fb _ _ e f hdisjW hdisjF he_ne_f he1 he2 hf1 hf2 he_cr hf_cr ihl ihr =>
            rw [Finset.map_union, Finset.map_insert, Finset.map_insert, Finset.map_union]
            have hend : ∀ g : {e // e ∈ wcH.blue},
                ((redQuotient Q blue).tail (embF g) = embQ ((redQuotient H wcH.blue).tail g) ∧
                 (redQuotient Q blue).head (embF g) = embQ ((redQuotient H wcH.blue).head g)) ∨
                ((redQuotient Q blue).tail (embF g) = embQ ((redQuotient H wcH.blue).head g) ∧
                 (redQuotient Q blue).head (embF g) = embQ ((redQuotient H wcH.blue).tail g)) := by
              intro g
              by_cases hxy : g.1 = e_xyH
              · have ht_H : Quotient.mk (redSetoid H wcH.blue) (H.tail g.1) = Quotient.mk _ xH' := by
                  rw [hxy]; rfl
                have hh_H : Quotient.mk (redSetoid H wcH.blue) (H.head g.1) = Quotient.mk _ yH' := by
                  rw [hxy]; rfl
                have hfg : (embF g).1 = eFarQ := by simp only [embF, Function.Embedding.coeFn_mk]; rw [dif_pos hxy]
                dsimp only [redQuotient]; rw [hfg, ht_H, hh_H]
                rcases hchoice with ⟨rfl, rfl, _, _⟩ | ⟨rfl, rfl, _, _⟩
                · rcases heFar_ends with ⟨h1, h2⟩ | ⟨h1, h2⟩
                  · left; rw [h1, h2, hwQ_red]; exact ⟨rfl, rfl⟩
                  · right; rw [h1, h2, hwQ_red]; exact ⟨rfl, rfl⟩
                · rcases heFar_ends with ⟨h1, h2⟩ | ⟨h1, h2⟩
                  · right; rw [h1, h2, hwQ_red]; exact ⟨rfl, rfl⟩
                  · left; rw [h1, h2, hwQ_red]; exact ⟨rfl, rfl⟩
              · left
                have hfg : (embF g).1 = ((hEH_cases g.1).resolve_left hxy).choose := by
                  simp only [embF, Function.Embedding.coeFn_mk]; rw [dif_neg hxy]
                have hsp := ((hEH_cases g.1).resolve_left hxy).choose_spec.choose_spec
                dsimp only [redQuotient]; rw [hfg]
                constructor
                · dsimp only [embQ]; apply congrArg (Quotient.mk _); refine Subtype.ext ?_
                  exact congrArg (fun x => x.1.1) (congrArg H.tail hsp)
                · dsimp only [embQ]; apply congrArg (Quotient.mk _); refine Subtype.ext ?_
                  exact congrArg (fun x => x.1.1) (congrArg H.head hsp)
            refine TwoConstruction.join ihl ihr (embF e) (embF f)
              (disjoint_map_of_disjoint _ hdisjW) (disjoint_map_of_disjoint _ hdisjF)
              (fun h => he_ne_f (embF.injective h))
              (by simp [he1]) (by simp [he2]) (by simp [hf1]) (by simp [hf2]) ?_ ?_
            · rcases hend e with ⟨ht, hh⟩ | ⟨ht, hh⟩ <;> rcases he_cr with ⟨h1, h2⟩ | ⟨h1, h2⟩
              · left; exact ⟨ht ▸ Finset.mem_map_of_mem _ h1, hh ▸ Finset.mem_map_of_mem _ h2⟩
              · right; exact ⟨ht ▸ Finset.mem_map_of_mem _ h1, hh ▸ Finset.mem_map_of_mem _ h2⟩
              · right; exact ⟨ht ▸ Finset.mem_map_of_mem _ h2, hh ▸ Finset.mem_map_of_mem _ h1⟩
              · left; exact ⟨ht ▸ Finset.mem_map_of_mem _ h2, hh ▸ Finset.mem_map_of_mem _ h1⟩
            · rcases hend f with ⟨ht, hh⟩ | ⟨ht, hh⟩ <;> rcases hf_cr with ⟨h1, h2⟩ | ⟨h1, h2⟩
              · left; exact ⟨ht ▸ Finset.mem_map_of_mem _ h1, hh ▸ Finset.mem_map_of_mem _ h2⟩
              · right; exact ⟨ht ▸ Finset.mem_map_of_mem _ h1, hh ▸ Finset.mem_map_of_mem _ h2⟩
              · right; exact ⟨ht ▸ Finset.mem_map_of_mem _ h2, hh ▸ Finset.mem_map_of_mem _ h1⟩
              · left; exact ⟨ht ▸ Finset.mem_map_of_mem _ h2, hh ▸ Finset.mem_map_of_mem _ h1⟩
        exact hgo wcH.twoConstr
      -- Join htc_old with .single qz using {e_zuQ, e_zwQ}!
      have hW_univ : Finset.univ.map embQ ∪ {qz} = Finset.univ := by
        ext q; simp only [Finset.mem_union, Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_singleton, iff_true]
        obtain ⟨v, rfl⟩ := Quotient.exists_rep q
        rcases hVQ_cases v with rfl | rfl | ⟨a, rfl⟩
        · exact Or.inr rfl
        · exact Or.inl ⟨Quotient.mk _ xNearH, hwQ_red.symm⟩
        · exact Or.inl ⟨Quotient.mk _ a, rfl⟩
      have hF_univ : insert ⟨e_zuQ, hzu_bl⟩ (insert ⟨e_zwQ, hzw_bl⟩ (Finset.univ.map embF ∪ ∅)) = Finset.univ := by
        ext ⟨e, he⟩
        simp only [Finset.union_empty, Finset.mem_insert, Finset.mem_map, Finset.mem_univ, true_and, iff_true]
        rcases (Finset.mem_filter.mp he).2 with rfl | rfl | rfl | ⟨hnotrem, hmem⟩
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · right; right; refine ⟨⟨e_xyH, hxy_bl⟩, Subtype.ext ?_⟩; simp only [embF, Function.Embedding.coeFn_mk, ↓reduceDIte]
        · right; right
          have hne_xy : toEH e hnotrem ≠ e_xyH := Finset.ne_of_mem_erase hmem
          refine ⟨⟨toEH e hnotrem, Finset.mem_of_mem_erase hmem⟩, Subtype.ext ?_⟩
          simp only [embF, Function.Embedding.coeFn_mk]; rw [dif_neg hne_xy]
          have hsp := ((hEH_cases (toEH e hnotrem)).resolve_left hne_xy).choose_spec.choose_spec
          exact Subtype.ext (by have h_tmp := Option.some.inj (Option.some.inj (congrArg Subtype.val hsp)); rw [Subtype.ext_iff] at h_tmp; exact h_tmp)
      have hdisjW : Disjoint (Finset.univ.map embQ) {qz} := by
        rw [Finset.disjoint_singleton_right]; intro hm
        obtain ⟨qH, _, hq⟩ := Finset.mem_map.mp hm; exact hqz_not_img qH hq
      have hnot_in_F : ∀ (e0 : {e // e ∈ blue}), e0.1 = e_zuQ ∨ e0.1 = e_zwQ → e0 ∉ Finset.univ.map embF := by
        intro e0 hor hm
        obtain ⟨g, _, hg⟩ := Finset.mem_map.mp hm
        by_cases hxy : g.1 = e_xyH
        · have hf : (embF g).1 = eFarQ := by simp only [embF, Function.Embedding.coeFn_mk]; rw [dif_pos hxy]
          have heq : e0.1 = eFarQ := (congrArg Subtype.val hg).symm.trans hf
          rcases hor with h | h
          · exact heFar_ne_zu (heq.symm.trans h)
          · exact heFar_ne_zw (heq.symm.trans h)
        · have hf : (embF g).1.1 ∉ remE := by
            have := ((hEH_cases g.1).resolve_left hxy).choose_spec.choose
            simp only [embF, Function.Embedding.coeFn_mk]; rw [dif_neg hxy]; exact this
          have heq := congrArg (fun x => x.1.1) hg
          rw [heq] at hf
          rcases hor with h | h <;> rw [h] at hf <;> exact hf (by simp [remE, e_zuQ, e_zwQ, e_wxQ, e_wyQ])
      refine ⟨{ blue := blue, blue_tree := hT_tree, twoConstr := ?_ }⟩
      rw [← hW_univ, ← hF_univ]
      exact TwoConstruction.join htc_old (TwoConstruction.single qz)
        ⟨e_zuQ, hzu_bl⟩ ⟨e_zwQ, hzw_bl⟩ hdisjW (Finset.disjoint_empty_right _)
        (fun h => he_zu_ne_zwQ (congrArg Subtype.val h))
        (hnot_in_F _ (Or.inl rfl)) (Finset.notMem_empty _)
        (hnot_in_F _ (Or.inr rfl)) (Finset.notMem_empty _)
        (by dsimp only [redQuotient]; rcases he_zu_ends with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · right; rw [h1, h2]; exact ⟨Finset.mem_singleton_self _, Finset.mem_map_of_mem _ (Finset.mem_univ (Quotient.mk _ uH'))⟩
            · left; rw [h1, h2]; exact ⟨Finset.mem_map_of_mem _ (Finset.mem_univ (Quotient.mk _ uH')), Finset.mem_singleton_self _⟩)
        (by dsimp only [redQuotient]; rcases he_zw_ends with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · right; rw [h1, h2, hwQ_red]; exact ⟨Finset.mem_singleton_self _, Finset.mem_map_of_mem _ (Finset.mem_univ (Quotient.mk _ xNearH))⟩
            · left; rw [h1, h2, hwQ_red]; exact ⟨Finset.mem_map_of_mem _ (Finset.mem_univ (Quotient.mk _ xNearH)), Finset.mem_singleton_self _⟩)
    rcases hreach_xy uH' with hux | huy
    · exact hcase2b xH' yH' e_wxQ e_wyQ (Or.inl ⟨rfl, rfl, rfl, rfl⟩) hux
    · exact hcase2b yH' xH' e_wyQ e_wxQ (Or.inr ⟨rfl, rfl, rfl, rfl⟩) huy
  · -- CASE 2a: e_xyH is RED in H!
    have he_zu_ends : (Q.tail e_zuQ = zQ ∧ Q.head e_zuQ = toVQ uH') ∨
        (Q.tail e_zuQ = toVQ uH' ∧ Q.head e_zuQ = zQ) := by
      rcases hu_spec.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨Subtype.ext h1, Subtype.ext h2⟩
      · exact Or.inr ⟨Subtype.ext h1, Subtype.ext h2⟩
    have he_zw_ends : (Q.tail e_zwQ = zQ ∧ Q.head e_zwQ = wQ) ∨
        (Q.tail e_zwQ = wQ ∧ Q.head e_zwQ = zQ) := by
      rcases hw_spec.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨Subtype.ext h1, Subtype.ext h2⟩
      · exact Or.inr ⟨Subtype.ext h1, Subtype.ext h2⟩
    have he_wx_ends : (Q.tail e_wxQ = wQ ∧ Q.head e_wxQ = toVQ xH') ∨
        (Q.tail e_wxQ = toVQ xH' ∧ Q.head e_wxQ = wQ) := by
      rcases hx_spec.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨Subtype.ext h1, Subtype.ext h2⟩
      · exact Or.inr ⟨Subtype.ext h1, Subtype.ext h2⟩
    have he_wy_ends : (Q.tail e_wyQ = wQ ∧ Q.head e_wyQ = toVQ yH') ∨
        (Q.tail e_wyQ = toVQ yH' ∧ Q.head e_wyQ = wQ) := by
      rcases hy_spec.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨Subtype.ext h1, Subtype.ext h2⟩
      · exact Or.inr ⟨Subtype.ext h1, Subtype.ext h2⟩
    have he_zu_ne_zwQ : e_zuQ ≠ e_zwQ := fun h => he_zu_ne_zw (congrArg Subtype.val h)
    let blue : Finset {e : E // Qplus.tail e ≠ v₀ ∧ Qplus.head e ≠ v₀} :=
      Finset.univ.filter fun e =>
        e = e_zuQ ∨ e = e_zwQ ∨ ∃ h : e.1 ∉ remE, toEH e h ∈ wcH.blue
    have hzu_bl : e_zuQ ∈ blue := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl rfl⟩
    have hzw_bl : e_zwQ ∈ blue := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr (Or.inl rfl)⟩
    have hwx_red : e_wxQ ∉ blue := by
      intro hm; rcases (Finset.mem_filter.mp hm).2 with h | h | ⟨h, _⟩
      · exact he_zu_ne_wx (congrArg Subtype.val h).symm
      · exact he_wx_ne_zw (congrArg Subtype.val h)
      · exact h (by simp [remE, e_zuQ, e_zwQ, e_wxQ, e_wyQ])
    have hwy_red : e_wyQ ∉ blue := by
      intro hm; rcases (Finset.mem_filter.mp hm).2 with h | h | ⟨h, _⟩
      · exact he_zu_ne_wy (congrArg Subtype.val h).symm
      · exact he_wy_ne_zw (congrArg Subtype.val h)
      · exact h (by simp [remE, e_zuQ, e_zwQ, e_wxQ, e_wyQ])
    -- Card blue = |V(Q)| - 1
    have hblue_card : blue.card + 1 = Fintype.card {a : V // a ≠ v₀} := by
      have hbij_card : (blue.erase e_zuQ |>.erase e_zwQ).card = wcH.blue.card := by
        refine Finset.card_bij
          (fun e he =>
            have hne_zw := Finset.ne_of_mem_erase he
            have hne_zu := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase he)
            have hbl := (Finset.mem_filter.mp (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase he))).2
            have hn : e.1 ∉ remE := (hbl.resolve_left hne_zu).resolve_left hne_zw |>.choose
            toEH e hn)
          (fun e he => by
            have hne_zw := Finset.ne_of_mem_erase he
            have hne_zu := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase he)
            have hbl := (Finset.mem_filter.mp (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase he))).2
            exact ((hbl.resolve_left hne_zu).resolve_left hne_zw).choose_spec)
          (fun _ _ _ _ heq => Subtype.ext (by have h_tmp := Option.some.inj (Option.some.inj (congrArg Subtype.val heq)); rw [Subtype.ext_iff] at h_tmp; exact h_tmp))
          (fun eH heH => by
            rcases hEH_cases eH with rfl | ⟨eQ, hnotrem, rfl⟩
            · exact absurd heH hxy_bl
            · have hne_zu : eQ ≠ e_zuQ := fun h => hnotrem (by rw [h]; simp [remE, e_zuQ, e_zwQ, e_wxQ, e_wyQ])
              have hne_zw : eQ ≠ e_zwQ := fun h => hnotrem (by rw [h]; simp [remE, e_zuQ, e_zwQ, e_wxQ, e_wyQ])
              have heQ_bl : eQ ∈ blue := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr (Or.inr ⟨hnotrem, heH⟩)⟩
              exact ⟨eQ, Finset.mem_erase.mpr ⟨hne_zw, Finset.mem_erase.mpr ⟨hne_zu, heQ_bl⟩⟩, rfl⟩)
      have hzw_in : e_zwQ ∈ blue.erase e_zuQ := Finset.mem_erase.mpr ⟨he_zu_ne_zwQ.symm, hzw_bl⟩
      rw [Finset.card_erase_of_mem hzw_in, Finset.card_erase_of_mem hzu_bl] at hbij_card
      have hB_H := spanningTree_edges_card wcH.blue_tree
      have hge2 : 2 ≤ blue.card := by
        have hsub : ({e_zuQ, e_zwQ} : Finset _) ⊆ blue := by intro e he; simp at he; rcases he with rfl | rfl; exact hzu_bl; exact hzw_bl
        rw [← Finset.card_pair he_zu_ne_zwQ]; exact Finset.card_le_card hsub
      change wcH.blue.card + 1 = Fintype.card {a : VH // a ≠ v₀H} at hB_H
      omega
    -- Connected
    let T := Multigraph.Subgraph.ofEdges Q Finset.univ blue (fun _ => Finset.mem_univ _) (fun _ => Finset.mem_univ _)
    let TH := Multigraph.Subgraph.ofEdges H Finset.univ wcH.blue (fun _ => Finset.mem_univ _) (fun _ => Finset.mem_univ _)
    have hlift_TH : ∀ a b : {a : VH // a ≠ v₀H}, Relation.ReflTransGen TH.Adj a b →
        Relation.ReflTransGen T.Adj (toVQ a) (toVQ b) := by
      intro a b hab
      induction hab with
      | refl => exact .refl
      | tail _ hs ih =>
        rcases hs with ⟨eH, heH, hinc⟩
        rcases hEH_cases eH with rfl | ⟨eQ, hnotrem, rfl⟩
        · exact absurd heH hxy_bl
        · have heQ_bl : eQ ∈ blue := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr (Or.inr ⟨hnotrem, heH⟩)⟩
          refine ih.tail ⟨eQ, heQ_bl, ?_⟩
          rcases hinc with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inl ⟨Subtype.ext (congrArg (fun x => x.1.1) h1), Subtype.ext (congrArg (fun x => x.1.1) h2)⟩
          · exact Or.inr ⟨Subtype.ext (congrArg (fun x => x.1.1) h1), Subtype.ext (congrArg (fun x => x.1.1) h2)⟩
    have hsym_T : ∀ a b, Relation.ReflTransGen T.Adj a b → Relation.ReflTransGen T.Adj b a := fun a b h => by
      induction h with
      | refl => exact .refl
      | tail _ hs ih =>
        rcases hs with ⟨e, he, h1 | h1⟩
        · exact Relation.ReflTransGen.head ⟨e, he, Or.inr h1⟩ ih
        · exact Relation.ReflTransGen.head ⟨e, he, Or.inl h1⟩ ih
    have hreach_zQ : ∀ q : {a : V // a ≠ v₀}, Relation.ReflTransGen T.Adj q zQ := by
      have hu_z : Relation.ReflTransGen T.Adj (toVQ uH') zQ :=
        Relation.ReflTransGen.single ⟨e_zuQ, hzu_bl, by rcases he_zu_ends with h | h; exact Or.inr h; exact Or.inl h⟩
      have hw_z : Relation.ReflTransGen T.Adj wQ zQ :=
        Relation.ReflTransGen.single ⟨e_zwQ, hzw_bl, by rcases he_zw_ends with h | h; exact Or.inr h; exact Or.inl h⟩
      intro q
      rcases hVQ_cases q with rfl | rfl | ⟨a, rfl⟩
      · exact .refl
      · exact hw_z
      · exact (hlift_TH a uH' (wcH.blue_tree.2.1.2 a (Finset.mem_univ _) uH' (Finset.mem_univ _))).trans hu_z
    have hT_conn : T.Connected := ⟨⟨zQ, Finset.mem_univ _⟩, fun a _ b _ => (hreach_zQ a).trans (hsym_T _ _ (hreach_zQ b))⟩
    have hT_tree : T.IsSpanningTree :=
      ⟨rfl, hT_conn, connected_edges_eq_verts_sub_one_isForest T hT_conn (by change blue.card + 1 = (Finset.univ : Finset _).card; rw [Finset.card_univ]; exact hblue_card)⟩
    -- Red quotient: wQ merges into R(x) = R(y), zQ is singleton!
    have hred_iff : ∀ a b : {a : VH // a ≠ v₀H},
        Relation.ReflTransGen (redAdj H wcH.blue) a b ↔
        Relation.ReflTransGen (redAdj Q blue) (toVQ a) (toVQ b) := by
      intro a b
      constructor
      · intro hab
        induction hab with
        | refl => exact .refl
        | tail _ hs ih =>
          rcases hs with ⟨eH, heH_R, hinc⟩
          rcases hEH_cases eH with rfl | ⟨eQ, hnotrem, rfl⟩
          · -- e_xyH step: replace by 2-step red walk xQ —(e_wxQ)— wQ —(e_wyQ)— yQ!
            have hxw : Relation.ReflTransGen (redAdj Q blue) (toVQ xH') wQ :=
              Relation.ReflTransGen.single ⟨e_wxQ, hwx_red, by rcases he_wx_ends with h | h; exact Or.inr h; exact Or.inl h⟩
            have hwy : Relation.ReflTransGen (redAdj Q blue) wQ (toVQ yH') :=
              Relation.ReflTransGen.single ⟨e_wyQ, hwy_red, he_wy_ends⟩
            rcases hinc with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · have h1' : toVQ _ = toVQ xH' := congrArg toVQ h1.symm
              have h2' : toVQ _ = toVQ yH' := congrArg toVQ h2.symm
              rw [h2']; exact (h1' ▸ ih).trans (hxw.trans hwy)
            · have h1' : toVQ _ = toVQ xH' := congrArg toVQ h1.symm
              have h2' : toVQ _ = toVQ yH' := congrArg toVQ h2.symm
              rw [h1']; exact (h2' ▸ ih).trans ((redSetoid Q blue).symm (hxw.trans hwy))
          · have heQ_R : eQ ∉ blue := by
              intro hm; rcases (Finset.mem_filter.mp hm).2 with h | h | ⟨_, hmem⟩
              · exact hnotrem (by rw [h]; simp [remE, e_zuQ, e_zwQ])
              · exact hnotrem (by rw [h]; simp [remE, e_zuQ, e_zwQ])
              · exact heH_R hmem
            refine ih.tail ⟨eQ, heQ_R, ?_⟩
            rcases hinc with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · exact Or.inl ⟨Subtype.ext (congrArg (fun x => x.1.1) h1), Subtype.ext (congrArg (fun x => x.1.1) h2)⟩
            · exact Or.inr ⟨Subtype.ext (congrArg (fun x => x.1.1) h1), Subtype.ext (congrArg (fun x => x.1.1) h2)⟩
      · intro hab
        let projH (q : {a : V // a ≠ v₀}) : {a : VH // a ≠ v₀H} :=
          if hz : q = zQ then xH'
          else if hw : q = wQ then xH'
          else ⟨⟨q.1, fun h => hz (Subtype.ext h), fun h => hw (Subtype.ext h)⟩, fun h => q.2 (congrArg Subtype.val h)⟩
        have hproj_toVQ : ∀ a, projH (toVQ a) = a := fun a => by
          dsimp only [projH]; rw [dif_neg (htoVQ_ne_z a), dif_neg (htoVQ_ne_w a)]
        have hxy_red_H : Relation.ReflTransGen (redAdj H wcH.blue) xH' yH' :=
          Relation.ReflTransGen.single ⟨e_xyH, hxy_bl, Or.inl ⟨rfl, rfl⟩⟩
        have hgo : ∀ p q, Relation.ReflTransGen (redAdj Q blue) p q →
            p ≠ zQ → Relation.ReflTransGen (redAdj H wcH.blue) (projH p) (projH q) ∧ q ≠ zQ := by
          intro p q hpq hp_nz
          induction hpq with
          | refl => exact ⟨.refl, hp_nz⟩
          | @tail r s _ hs ih =>
            obtain ⟨ihr, hr_nz⟩ := ih
            rcases hs with ⟨eQ, heQ_R, hinc⟩
            have hne_zu : eQ ≠ e_zuQ := fun h => heQ_R (h ▸ hzu_bl)
            have hne_zw : eQ ≠ e_zwQ := fun h => heQ_R (h ▸ hzw_bl)
            have hs_nz : s ≠ zQ := fun hs_eq => by
              have hinc_z : Q.tail eQ = zQ ∨ Q.head eQ = zQ := by
                rcases hinc with ⟨_, h2⟩ | ⟨h1, _⟩; exact Or.inr (h2.trans hs_eq); exact Or.inl (h1.trans hs_eq)
              rcases hQ_z_inc eQ hinc_z with h | h; exact hne_zu h; exact hne_zw h
            refine ⟨?_, hs_nz⟩
            by_cases hwx : eQ = e_wxQ
            · subst hwx
              have hpr : projH r = xH' := by
                rcases hinc with ⟨h1, _⟩ | ⟨_, h2⟩
                · rcases he_wx_ends with ⟨ht, _⟩ | ⟨ht, _⟩
                  · rw [← h1, ht]; simp [projH, hw_ne_z]
                  · rw [← h1, ht, hproj_toVQ]
                · rcases he_wx_ends with ⟨_, hh⟩ | ⟨_, hh⟩
                  · rw [← h2, hh, hproj_toVQ]
                  · rw [← h2, hh]; simp [projH, hw_ne_z]
              have hps : projH s = xH' := by
                rcases hinc with ⟨_, h2⟩ | ⟨h1, _⟩
                · rcases he_wx_ends with ⟨_, hh⟩ | ⟨_, hh⟩
                  · rw [← h2, hh, hproj_toVQ]
                  · rw [← h2, hh]; simp [projH, hw_ne_z]
                · rcases he_wx_ends with ⟨ht, _⟩ | ⟨ht, _⟩
                  · rw [← h1, ht]; simp [projH, hw_ne_z]
                  · rw [← h1, ht, hproj_toVQ]
              rw [hps, ← hpr]; exact ihr
            · by_cases hwy : eQ = e_wyQ
              · subst hwy
                -- One end projects to xH' (wQ), the other to yH' (yQ), connected by e_xyH!
                rcases hinc with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases he_wy_ends with ⟨ht, hh⟩ | ⟨ht, hh⟩
                · have hpr : projH r = xH' := by rw [← h1, ht]; simp [projH, hw_ne_z]
                  have hps : projH s = yH' := by rw [← h2, hh, hproj_toVQ]
                  rw [hps]; exact (hpr ▸ ihr).trans hxy_red_H
                · have hpr : projH r = yH' := by rw [← h1, ht, hproj_toVQ]
                  have hps : projH s = xH' := by rw [← h2, hh]; simp [projH, hw_ne_z]
                  rw [hps]; exact (hpr ▸ ihr).trans ((redSetoid H wcH.blue).symm hxy_red_H)
                · have hpr : projH r = yH' := by rw [← h2, hh, hproj_toVQ]
                  have hps : projH s = xH' := by rw [← h1, ht]; simp [projH, hw_ne_z]
                  rw [hps]; exact (hpr ▸ ihr).trans ((redSetoid H wcH.blue).symm hxy_red_H)
                · have hpr : projH r = xH' := by rw [← h2, hh]; simp [projH, hw_ne_z]
                  have hps : projH s = yH' := by rw [← h1, ht, hproj_toVQ]
                  rw [hps]; exact (hpr ▸ ihr).trans hxy_red_H
              · have hnotrem : eQ.1 ∉ remE := hnot_rem_of_Q eQ hne_zu hne_zw hwx hwy
                have heH_R : toEH eQ hnotrem ∉ wcH.blue := fun hm =>
                  heQ_R (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr (Or.inr ⟨hnotrem, hm⟩)⟩)
                have hnot_w : r ≠ wQ ∧ s ≠ wQ := by
                  constructor <;> intro hw_eq
                  · have hinc_w : Q.tail eQ = wQ ∨ Q.head eQ = wQ := by
                      rcases hinc with ⟨h1, _⟩ | ⟨_, h2⟩; exact Or.inl (h1.trans hw_eq); exact Or.inr (h2.trans hw_eq)
                    rcases hQ_w_inc eQ hinc_w with h | h | h; exact hne_zw h; exact hwx h; exact hwy h
                  · have hinc_w : Q.tail eQ = wQ ∨ Q.head eQ = wQ := by
                      rcases hinc with ⟨_, h2⟩ | ⟨h1, _⟩; exact Or.inr (h2.trans hw_eq); exact Or.inl (h1.trans hw_eq)
                    rcases hQ_w_inc eQ hinc_w with h | h | h; exact hne_zw h; exact hwx h; exact hwy h
                refine ihr.tail ⟨toEH eQ hnotrem, heH_R, ?_⟩
                rcases hinc with ⟨h1, h2⟩ | ⟨h1, h2⟩
                · left; constructor <;> (refine Subtype.ext (Subtype.ext ?_); dsimp only [H, Multigraph.deleteVertex, toEH, Hplus, projH])
                  · rw [dif_neg hr_nz, dif_neg hnot_w.1]; exact congrArg Subtype.val h1
                  · rw [dif_neg hs_nz, dif_neg hnot_w.2]; exact congrArg Subtype.val h2
                · right; constructor <;> (refine Subtype.ext (Subtype.ext ?_); dsimp only [H, Multigraph.deleteVertex, toEH, Hplus, projH])
                  · rw [dif_neg hs_nz, dif_neg hnot_w.2]; exact congrArg Subtype.val h1
                  · rw [dif_neg hr_nz, dif_neg hnot_w.1]; exact congrArg Subtype.val h2
        simpa [hproj_toVQ] using (hgo (toVQ a) (toVQ b) hab (htoVQ_ne_z a)).1
    let qz : Quotient (redSetoid Q blue) := Quotient.mk _ zQ
    let embQ : Quotient (redSetoid H wcH.blue) ↪ Quotient (redSetoid Q blue) :=
      { toFun := Quotient.lift (fun a => Quotient.mk (redSetoid Q blue) (toVQ a))
          (fun _ _ h => Quotient.sound ((hred_iff _ _).mp h))
        inj' := fun q1 q2 heq => by
          obtain ⟨a, rfl⟩ := Quotient.exists_rep q1
          obtain ⟨b, rfl⟩ := Quotient.exists_rep q2
          exact Quotient.sound ((hred_iff a b).mpr (Quotient.exact heq)) }
    have hqz_not_img : ∀ qH, embQ qH ≠ qz := by
      intro qH heq
      obtain ⟨a, rfl⟩ := Quotient.exists_rep qH
      have hrel : Relation.ReflTransGen (redAdj Q blue) zQ (toVQ a) := (redSetoid Q blue).symm (Quotient.exact heq)
      have hstay : ∀ q, Relation.ReflTransGen (redAdj Q blue) zQ q → q = zQ := fun q h => by
        induction h with
        | refl => rfl
        | tail _ hs ih =>
          subst ih; rcases hs with ⟨eQ, heQ_R, ⟨h1, _⟩ | ⟨_, h2⟩⟩
          · rcases hQ_z_inc eQ (Or.inl h1) with rfl | rfl; exact absurd hzu_bl heQ_R; exact absurd hzw_bl heQ_R
          · rcases hQ_z_inc eQ (Or.inr h2) with rfl | rfl; exact absurd hzu_bl heQ_R; exact absurd hzw_bl heQ_R
      exact htoVQ_ne_z a (hstay _ hrel)
    have hwQ_red : Quotient.mk (redSetoid Q blue) wQ = embQ (Quotient.mk _ xH') :=
      Quotient.sound (Relation.ReflTransGen.single ⟨e_wxQ, hwx_red, he_wx_ends⟩)
    let embF : {e // e ∈ wcH.blue} ↪ {e // e ∈ blue} :=
      { toFun := fun eH =>
          have hne : eH.1 ≠ e_xyH := fun h => hxy_bl (h ▸ eH.2)
          have hex := (hEH_cases eH.1).resolve_left hne
          ⟨hex.choose, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            Or.inr (Or.inr ⟨hex.choose_spec.choose, by rw [hex.choose_spec.choose_spec]; exact eH.2⟩)⟩⟩
        inj' := fun e1 e2 heq => by
          have hne1 : e1.1 ≠ e_xyH := fun h => hxy_bl (h ▸ e1.2)
          have hne2 : e2.1 ≠ e_xyH := fun h => hxy_bl (h ▸ e2.2)
          have hval : ((hEH_cases e1.1).resolve_left hne1).choose = ((hEH_cases e2.1).resolve_left hne2).choose :=
            congrArg Subtype.val heq
          refine Subtype.ext ?_
          rw [← ((hEH_cases e1.1).resolve_left hne1).choose_spec.choose_spec,
              ← ((hEH_cases e2.1).resolve_left hne2).choose_spec.choose_spec]
          refine Subtype.ext ?_; dsimp only [toEH]; rw [Subtype.ext_iff] at hval; congr 2; exact Subtype.ext hval }
    have htc_old : TwoConstruction (redQuotient Q blue) (Finset.univ.map embQ) (Finset.univ.map embF) := by
      have hgo : ∀ {Wa : Finset (Quotient (redSetoid H wcH.blue))} {Fa : Finset {e // e ∈ wcH.blue}},
          TwoConstruction (redQuotient H wcH.blue) Wa Fa →
          TwoConstruction (redQuotient Q blue) (Wa.map embQ) (Fa.map embF) := by
        intro Wa Fa tc
        induction tc with
        | single w => simpa [Finset.map_singleton, Finset.map_empty] using TwoConstruction.single (M := redQuotient Q blue) (embQ w)
        | @join Wa Wb Fa Fb _ _ e f hdisjW hdisjF he_ne_f he1 he2 hf1 hf2 he_cr hf_cr ihl ihr =>
          rw [Finset.map_union, Finset.map_insert, Finset.map_insert, Finset.map_union]
          have hend : ∀ g : {e // e ∈ wcH.blue},
              (redQuotient Q blue).tail (embF g) = embQ ((redQuotient H wcH.blue).tail g) ∧
              (redQuotient Q blue).head (embF g) = embQ ((redQuotient H wcH.blue).head g) := fun g => by
            have hne : g.1 ≠ e_xyH := fun h => hxy_bl (h ▸ g.2)
            have hsp := ((hEH_cases g.1).resolve_left hne).choose_spec.choose_spec
            dsimp only [redQuotient, embF, Function.Embedding.coeFn_mk]
            constructor
            · dsimp only [embQ]; apply congrArg (Quotient.mk _); refine Subtype.ext ?_
              exact congrArg (fun x => x.1.1) (congrArg H.tail hsp)
            · dsimp only [embQ]; apply congrArg (Quotient.mk _); refine Subtype.ext ?_
              exact congrArg (fun x => x.1.1) (congrArg H.head hsp)
          refine TwoConstruction.join ihl ihr (embF e) (embF f)
            (disjoint_map_of_disjoint _ hdisjW) (disjoint_map_of_disjoint _ hdisjF)
            (fun h => he_ne_f (embF.injective h))
            (by simp [he1]) (by simp [he2]) (by simp [hf1]) (by simp [hf2]) ?_ ?_
          · rcases he_cr with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · left; rw [(hend e).1, (hend e).2]; exact ⟨Finset.mem_map_of_mem _ h1, Finset.mem_map_of_mem _ h2⟩
            · right; rw [(hend e).1, (hend e).2]; exact ⟨Finset.mem_map_of_mem _ h1, Finset.mem_map_of_mem _ h2⟩
          · rcases hf_cr with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · left; rw [(hend f).1, (hend f).2]; exact ⟨Finset.mem_map_of_mem _ h1, Finset.mem_map_of_mem _ h2⟩
            · right; rw [(hend f).1, (hend f).2]; exact ⟨Finset.mem_map_of_mem _ h1, Finset.mem_map_of_mem _ h2⟩
      exact hgo wcH.twoConstr
    have hW_univ : Finset.univ.map embQ ∪ {qz} = Finset.univ := by
      ext q; simp only [Finset.mem_union, Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_singleton, iff_true]
      obtain ⟨v, rfl⟩ := Quotient.exists_rep q
      rcases hVQ_cases v with rfl | rfl | ⟨a, rfl⟩
      · exact Or.inr rfl
      · exact Or.inl ⟨Quotient.mk _ xH', hwQ_red.symm⟩
      · exact Or.inl ⟨Quotient.mk _ a, rfl⟩
    have hF_univ : insert ⟨e_zuQ, hzu_bl⟩ (insert ⟨e_zwQ, hzw_bl⟩ (Finset.univ.map embF ∪ ∅)) = Finset.univ := by
      ext ⟨e, he⟩
      simp only [Finset.union_empty, Finset.mem_insert, Finset.mem_map, Finset.mem_univ, true_and, iff_true]
      rcases (Finset.mem_filter.mp he).2 with rfl | rfl | ⟨hnotrem, hmem⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · right; right
        have hne : toEH e hnotrem ≠ e_xyH := fun h => hxy_bl (h ▸ hmem)
        refine ⟨⟨toEH e hnotrem, hmem⟩, Subtype.ext ?_⟩
        simp only [embF, Function.Embedding.coeFn_mk]
        have hsp := ((hEH_cases (toEH e hnotrem)).resolve_left hne).choose_spec.choose_spec
        exact Subtype.ext (by have h_tmp := Option.some.inj (Option.some.inj (congrArg Subtype.val hsp)); rw [Subtype.ext_iff] at h_tmp; exact h_tmp)
    have hdisjW : Disjoint (Finset.univ.map embQ) {qz} := by
      rw [Finset.disjoint_singleton_right]; intro hm
      obtain ⟨qH, _, hq⟩ := Finset.mem_map.mp hm; exact hqz_not_img qH hq
    have hnot_in_F : ∀ (e0 : {e // e ∈ blue}), e0.1 = e_zuQ ∨ e0.1 = e_zwQ → e0 ∉ Finset.univ.map embF := by
      intro e0 hor hm
      obtain ⟨g, _, hg⟩ := Finset.mem_map.mp hm
      have hne : g.1 ≠ e_xyH := fun h => hxy_bl (h ▸ g.2)
      have hf := ((hEH_cases g.1).resolve_left hne).choose_spec.choose
      have heq : (((hEH_cases g.1).resolve_left hne).choose).1 = e0.1.1 := congrArg (fun x => x.1.1) hg
      rw [heq] at hf
      rcases hor with h | h <;> rw [h] at hf <;> exact hf (by simp [remE, e_zuQ, e_zwQ, e_wxQ, e_wyQ])
    refine ⟨{ blue := blue, blue_tree := hT_tree, twoConstr := ?_ }⟩
    rw [← hW_univ, ← hF_univ]
    exact TwoConstruction.join htc_old (TwoConstruction.single qz)
      ⟨e_zuQ, hzu_bl⟩ ⟨e_zwQ, hzw_bl⟩ hdisjW (Finset.disjoint_empty_right _)
      (fun h => he_zu_ne_zwQ (congrArg Subtype.val h))
      (hnot_in_F _ (Or.inl rfl)) (Finset.notMem_empty _)
      (hnot_in_F _ (Or.inr rfl)) (Finset.notMem_empty _)
      (by dsimp only [redQuotient]; rcases he_zu_ends with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · right; rw [h1, h2]; exact ⟨Finset.mem_singleton_self _, Finset.mem_map_of_mem _ (Finset.mem_univ (Quotient.mk _ uH'))⟩
          · left; rw [h1, h2]; exact ⟨Finset.mem_map_of_mem _ (Finset.mem_univ (Quotient.mk _ uH')), Finset.mem_singleton_self _⟩)
      (by dsimp only [redQuotient]; rcases he_zw_ends with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · right; rw [h1, h2, hwQ_red]; exact ⟨Finset.mem_singleton_self _, Finset.mem_map_of_mem _ (Finset.mem_univ (Quotient.mk _ xH'))⟩
          · left; rw [h1, h2, hwQ_red]; exact ⟨Finset.mem_map_of_mem _ (Finset.mem_univ (Quotient.mk _ xH')), Finset.mem_singleton_self _⟩)

/-! ### Part 7: Main Theorem (`JLPTWellColouring`) -/

/-- **Jaeger, Linial, Payan, and Tarsi (1992), Lemma 3.3 via Lemma 3.2:**
Every truncated cubic `3`-edge-connected graph admits a well colouring. -/
theorem jlpt_wellColouring_proved : JLPTWellColouring := by
  have hmain : ∀ n : ℕ,
      ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
        (Qplus : Multigraph V E) (v₀ : V),
        Fintype.card V = n → Qplus.IsCubic → Qplus.IsEdgeConnected 3 → 4 ≤ n →
        Nonempty (WellColouring (Qplus.deleteVertex v₀)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro V E _ _ _ _ Qplus v₀ hcard hcub h3 h4
      by_cases h4eq : n = 4
      · exact wellColouring_base_four Qplus v₀ hcub h3 (hcard.trans h4eq)
      · have h2E := cubic_two_mul_edges Qplus hcub
        have h6 : 6 ≤ Fintype.card V := by omega
        by_cases hcut : ∃ S : Finset V, 2 ≤ S.card ∧ 2 ≤ (Finset.univ \ S).card ∧ (Qplus.cutEdges S).card ≤ 3
        · rcases hcut with ⟨S, hS2, hSc2, hScut⟩
          by_cases hvS : v₀ ∈ S
          · have hP1 := contractSide_props Qplus hcub h3 S hS2 hSc2 hScut
            have hcutB : (Qplus.cutEdges (Finset.univ \ S)).card ≤ 3 := by
              have heq : Qplus.cutEdges (Finset.univ \ S) = Qplus.cutEdges S := by
                ext e; simp only [Multigraph.cutEdges, Finset.mem_filter, Finset.mem_univ, Finset.mem_sdiff, true_and]; tauto
              rw [heq]; exact hScut
            have hB_compl : Finset.univ \ (Finset.univ \ S) = S := by ext v; simp
            have hP2 := contractSide_props Qplus hcub h3 (Finset.univ \ S) hSc2 (by rw [hB_compl]; exact hS2) hcutB
            obtain ⟨wc₁⟩ := ih _ (hcard ▸ hP1.2.2.2) _ _ (contractSide Qplus S) (some ⟨v₀, hvS⟩) rfl hP1.1 hP1.2.1 hP1.2.2.1
            obtain ⟨wc₂⟩ := ih _ (hcard ▸ hP2.2.2.2) _ _ (contractSide Qplus (Finset.univ \ S)) none rfl hP2.1 hP2.2.1 hP2.2.2.1
            exact wellColouring_sticking Qplus v₀ hcub h3 (by omega) S hvS hS2 hSc2 hScut wc₁ wc₂
          · let A := Finset.univ \ S
            have hvA : v₀ ∈ A := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hvS⟩
            have hA_compl : Finset.univ \ A = S := by ext v; simp [A]
            have hcutA : (Qplus.cutEdges A).card ≤ 3 := by
              have heq : Qplus.cutEdges A = Qplus.cutEdges S := by
                ext e; simp only [A, Multigraph.cutEdges, Finset.mem_filter, Finset.mem_univ, Finset.mem_sdiff, true_and]; tauto
              rw [heq]; exact hScut
            have hP1 := contractSide_props Qplus hcub h3 A hSc2 (by rw [hA_compl]; exact hS2) hcutA
            have hP2 := contractSide_props Qplus hcub h3 (Finset.univ \ A) (by rw [hA_compl]; exact hS2)
              (by rw [hA_compl]; exact hSc2) (by rw [hA_compl]; exact hScut)
            obtain ⟨wc₁⟩ := ih _ (hcard ▸ hP1.2.2.2) _ _ (contractSide Qplus A) (some ⟨v₀, hvA⟩) rfl hP1.1 hP1.2.1 hP1.2.2.1
            obtain ⟨wc₂⟩ := ih _ (hcard ▸ hP2.2.2.2) _ _ (contractSide Qplus (Finset.univ \ A)) none rfl hP2.1 hP2.2.1 hP2.2.2.1
            exact wellColouring_sticking Qplus v₀ hcub h3 (by omega) A hvA hSc2 (by rw [hA_compl]; exact hS2) hcutA wc₁ wc₂
        · push Not at hcut
          have hno3 : ∀ S : Finset V, 2 ≤ S.card → 2 ≤ (Finset.univ \ S).card → 4 ≤ (Qplus.cutEdges S).card :=
            fun S h1 h2 => hcut S h1 h2
          exact wellColouring_growing Qplus v₀ hcub h3 h6 hno3
            (fun V' E' _ _ _ _ Hplus v' hlt hHc hH3 hH4 => ih _ (hcard ▸ hlt) V' E' Hplus v' rfl hHc hH3 hH4)
  intro V E _ _ _ _ Q hTC
  rcases hTC with ⟨V', E', _, _, _, _, Qplus, v₀, hcub, h3, h4, ⟨iso⟩⟩
  obtain ⟨wc⟩ := hmain (Fintype.card V') V' E' Qplus v₀ rfl hcub h3 h4
  exact ⟨wellColouring_of_iso iso wc⟩

end Flow.Proofs
