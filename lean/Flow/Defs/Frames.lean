-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Flow.Defs.StepSystem
import Mathlib.Basic.Real.Basic

/-!
# Good subgraphs, truncated cubic expansions, 2-constructions, well colourings, frames, and official cycles

This module provides the definitions for Section 3 of the paper:
- Definition 3.1: Good subgraphs (`(CYC)` and `(SUB)`)
- Definition 3.3: Truncated cubic `3`-edge-connected graphs
- Definition 3.5: Threads and auxiliary graph `Q = ⊔ Q_b` with flow projection `π`
- Definition 3.7: `2`-constructions and well colourings
- Definition 3.10: Frames, protected/free threads, `H_P`, `T^e`, `T^g`, and official cycles
- Definition 3.12: List assignments `Λ`, `P(Λ)`, `H`-good flows, and `Λ_f`
-/

namespace Flow

/-- A simple directed path of length `1 ≤ len ≤ 3` inside a subgraph `H` from `src` to `dst`,
given by its vertex list (length `len + 1`, nodup) and edge list (length `len`),
together with orientation signs along the path. -/
structure ThreadPath {V E : Type} (G : Multigraph V E) (H : G.Subgraph) (src dst : V) where
  verts : List V
  edges : List E
  len_pos : 1 ≤ edges.length
  len_le : edges.length ≤ 3
  verts_len : verts.length = edges.length + 1
  verts_nodup : verts.Nodup
  verts_sub : ∀ v ∈ verts, v ∈ H.verts
  edges_sub : ∀ e ∈ edges, e ∈ H.edges
  head_eq : verts.head? = some src
  last_eq : verts.getLast? = some dst
  step_connect : ∀ (i : ℕ) (hi : i < edges.length),
    let u := verts[i]'(by omega)
    let w := verts[i + 1]'(by omega)
    let e := edges[i]'hi
    (G.tail e = u ∧ G.head e = w) ∨ (G.tail e = w ∧ G.head e = u)

/-- A subdivision witness showing `H` is obtained from a loopless `3`-edge-connected
multigraph `H₀` on at least `2` vertices by replacing each edge `t : E₀` with a thread
of length `1 ≤ ℓ(t) ≤ 3`, pairwise internally vertex-disjoint and edge-disjoint. -/
structure SubdivisionData {V E : Type} [DecidableEq V] [DecidableEq E]
    (G : Multigraph V E) (H : G.Subgraph) where
  V₀ : Type
  E₀ : Type
  [fintypeV₀ : Fintype V₀]
  [fintypeE₀ : Fintype E₀]
  [decEqV₀ : DecidableEq V₀]
  [decEqE₀ : DecidableEq E₀]
  H₀ : Multigraph V₀ E₀
  loopless : H₀.IsLoopless
  edgeConn3 : H₀.IsEdgeConnected 3
  card_ge_two : 2 ≤ Fintype.card V₀
  embedV : V₀ ↪ V
  embedV_mem : ∀ v₀ : V₀, embedV v₀ ∈ H.verts
  thread : ∀ t : E₀, ThreadPath G H (embedV (H₀.tail t)) (embedV (H₀.head t))
  /-- All edges of `H` are partitioned by the threads. -/
  edges_disjoint : ∀ t₁ t₂ : E₀, t₁ ≠ t₂ → ∀ e, e ∈ (thread t₁).edges → e ∉ (thread t₂).edges
  edges_cover : ∀ e ∈ H.edges, ∃ t : E₀, e ∈ (thread t).edges
  /-- Interior vertices of threads are disjoint from branch vertices and from each other,
  and together with branch vertices cover `H.verts`. -/
  interior_disjoint_branch : ∀ t : E₀, ∀ v ∈ (thread t).verts,
    v ≠ embedV (H₀.tail t) → v ≠ embedV (H₀.head t) → ∀ v₀ : V₀, v ≠ embedV v₀
  interior_disjoint : ∀ t₁ t₂ : E₀, t₁ ≠ t₂ → ∀ v,
    (v ∈ (thread t₁).verts ∧ v ≠ embedV (H₀.tail t₁) ∧ v ≠ embedV (H₀.head t₁)) →
    ¬ (v ∈ (thread t₂).verts ∧ v ≠ embedV (H₀.tail t₂) ∧ v ≠ embedV (H₀.head t₂))
  verts_cover : ∀ v ∈ H.verts, (∃ v₀ : V₀, embedV v₀ = v) ∨ ∃ t : E₀, v ∈ (thread t).verts

attribute [instance] SubdivisionData.fintypeV₀ SubdivisionData.fintypeE₀
  SubdivisionData.decEqV₀ SubdivisionData.decEqE₀

/-- Definition 3.1 (Good subgraph): either `(CYC)` a cycle of at most `5` edges and at least
`2` vertices, or `(SUB)` a subdivision of a loopless `3`-edge-connected multigraph on at least
`2` vertices with threads of length at most `3`. -/
def IsGoodCyc {V E : Type} [DecidableEq V] (G : Multigraph V E) (H : G.Subgraph) : Prop :=
  H.IsCycle ∧ H.edges.card ≤ 5 ∧ 2 ≤ H.verts.card

def IsGoodSub {V E : Type} [DecidableEq V] [DecidableEq E]
    (G : Multigraph V E) (H : G.Subgraph) : Prop :=
  Nonempty (SubdivisionData G H)

def IsGoodSubgraph {V E : Type} [DecidableEq V] [DecidableEq E]
    (G : Multigraph V E) (H : G.Subgraph) : Prop :=
  IsGoodCyc G H ∨ IsGoodSub G H

/-- Definition 3.3 (Truncated cubic `3`-edge-connected graph):
`Q ≅ Q⁺ - v`, where `Q⁺` is a cubic `3`-edge-connected graph on at least `4` vertices
and `v ∈ V(Q⁺)`. -/
def Multigraph.IsTruncatedCubic3EC {V E : Type} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (Q : Multigraph V E) : Prop :=
  ∃ (V' E' : Type) (_ : Fintype V') (_ : Fintype E') (_ : DecidableEq V') (_ : DecidableEq E')
    (Qplus : Multigraph V' E') (v : V'),
    Qplus.IsCubic ∧ Qplus.IsEdgeConnected 3 ∧ 4 ≤ Fintype.card V' ∧
    Nonempty (Multigraph.Iso Q (Qplus.deleteVertex v))

/-- A cycle expansion of a loopless `3`-edge-connected cut-vertex-free multigraph `K`
into a truncated cubic `3`-edge-connected graph `Q_K` whose non-`K` edges form pairwise
disjoint cycles that contract back to `K` (Lemma 3.4(b)). -/
structure TruncatedCubicExpansion {VK EK : Type} [Fintype VK] [Fintype EK]
    [DecidableEq VK] [DecidableEq EK] (K : Multigraph VK EK) where
  VQ : Type
  EQ : Type
  [fintypeVQ : Fintype VQ]
  [fintypeEQ : Fintype EQ]
  [decEqVQ : DecidableEq VQ]
  [decEqEQ : DecidableEq EQ]
  Q : Multigraph VQ EQ
  isTC3EC : Q.IsTruncatedCubic3EC
  origEdge : EK ↪ EQ
  contractV : VQ → VK
  contractV_surj : Function.Surjective contractV
  orig_tail : ∀ e : EK, contractV (Q.tail (origEdge e)) = K.tail e
  orig_head : ∀ e : EK, contractV (Q.head (origEdge e)) = K.head e
  /-- Every expansion edge stays inside one fiber `contractV⁻¹(x)`. -/
  exp_fiber : ∀ e : EQ, (∀ k : EK, origEdge k ≠ e) → contractV (Q.tail e) = contractV (Q.head e)
  /-- Each fiber `contractV⁻¹(x)` is either a single vertex with no expansion edges
  or a cycle of expansion edges; hence expansion edges form pairwise disjoint cycles. -/
  fiber_cycle_or_singleton : ∀ x : VK,
    let U := Finset.univ.filter (fun u : VQ => contractV u = x)
    let F := Finset.univ.filter (fun e : EQ =>
      (∀ k : EK, origEdge k ≠ e) ∧ contractV (Q.tail e) = x)
    (U.card = 1 ∧ F = ∅) ∨
    ∃ C : Q.Subgraph, C.verts = U ∧ C.edges = F ∧ C.IsCycle

attribute [instance] TruncatedCubicExpansion.fintypeVQ TruncatedCubicExpansion.fintypeEQ
  TruncatedCubicExpansion.decEqVQ TruncatedCubicExpansion.decEqEQ

/-- Definition 3.7: A `2`-construction of a multigraph `M` on vertex set `W` and edge set `F`
fixes a recursive decomposition into stages by `2`-joins. -/
inductive TwoConstruction {W F : Type} [DecidableEq W] [DecidableEq F]
    (M : Multigraph W F) : Finset W → Finset F → Type where
  | single (w : W) : TwoConstruction M {w} ∅
  | join {W₁ W₂ : Finset W} {F₁ F₂ : Finset F}
      (left : TwoConstruction M W₁ F₁)
      (right : TwoConstruction M W₂ F₂)
      (e f : F)
      (hdisjW : Disjoint W₁ W₂)
      (hdisjF : Disjoint F₁ F₂)
      (he_ne_f : e ≠ f)
      (he_not₁ : e ∉ F₁) (he_not₂ : e ∉ F₂)
      (hf_not₁ : f ∉ F₁) (hf_not₂ : f ∉ F₂)
      (he_cross : (M.tail e ∈ W₁ ∧ M.head e ∈ W₂) ∨ (M.tail e ∈ W₂ ∧ M.head e ∈ W₁))
      (hf_cross : (M.tail f ∈ W₁ ∧ M.head f ∈ W₂) ∨ (M.tail f ∈ W₂ ∧ M.head f ∈ W₁)) :
      TwoConstruction M (W₁ ∪ W₂) (insert e (insert f (F₁ ∪ F₂)))

namespace TwoConstruction

/-- All stages `(W_U, F_U)` appearing in a `2`-construction. -/
def stages {W F : Type} [DecidableEq W] [DecidableEq F] {M : Multigraph W F} :
    ∀ {W₀ : Finset W} {F₀ : Finset F}, TwoConstruction M W₀ F₀ → List (Finset W × Finset F)
  | _, _, .single w => [({w}, ∅)]
  | _, _, .join (W₁ := W₁) (W₂ := W₂) (F₁ := F₁) (F₂ := F₂) left right e f _ _ _ _ _ _ _ _ _ =>
      (W₁ ∪ W₂, insert e (insert f (F₁ ∪ F₂))) :: (left.stages ++ right.stages)

/-- All nodes `(W₁, W₂, e, f)` (operands and joining pair) appearing in a `2`-construction. -/
def nodes {W F : Type} [DecidableEq W] [DecidableEq F] {M : Multigraph W F} :
    ∀ {W₀ : Finset W} {F₀ : Finset F},
      TwoConstruction M W₀ F₀ → List (Finset W × Finset W × F × F)
  | _, _, .single _ => []
  | _, _, .join (W₁ := W₁) (W₂ := W₂) left right e f _ _ _ _ _ _ _ _ _ =>
      (W₁, W₂, e, f) :: (left.nodes ++ right.nodes)

end TwoConstruction

/-- Red-edge adjacency in `Q` with respect to a blue edge set `blue`. -/
def redAdj {V E : Type} [DecidableEq E] (Q : Multigraph V E) (blue : Finset E) (u v : V) : Prop :=
  ∃ e : E, e ∉ blue ∧ ((Q.tail e = u ∧ Q.head e = v) ∨ (Q.tail e = v ∧ Q.head e = u))

/-- Equivalence relation of belonging to the same red connected component in `Q`. -/
def redSetoid {V E : Type} [DecidableEq E] (Q : Multigraph V E) (blue : Finset E) : Setoid V where
  r u v := Relation.ReflTransGen (redAdj Q blue) u v
  iseqv :=
    { refl := fun _ => Relation.ReflTransGen.refl
      symm := fun h => by
        induction h with
        | refl => exact Relation.ReflTransGen.refl
        | tail _ hstep ih =>
          rcases hstep with ⟨e, he, h | h⟩
          · exact Relation.ReflTransGen.head ⟨e, he, Or.inr h⟩ ih
          · exact Relation.ReflTransGen.head ⟨e, he, Or.inl h⟩ ih
      trans := fun h₁ h₂ => Relation.ReflTransGen.trans h₁ h₂ }

/-- Quotient `Q / red`: vertices are red components, edges are all blue edges of `Q`. -/
def redQuotient {V E : Type} [DecidableEq E] (Q : Multigraph V E) (blue : Finset E) :
    Multigraph (Quotient (redSetoid Q blue)) {e : E // e ∈ blue} where
  tail e := Quotient.mk (redSetoid Q blue) (Q.tail e.1)
  head e := Quotient.mk (redSetoid Q blue) (Q.head e.1)

/-- Lift a vertex subset `U` of `Q / red` back to the union `V_U ⊆ V(Q)` of its red components. -/
def stageVerts {V E : Type} [Fintype V] [DecidableEq E]
    (Q : Multigraph V E) (blue : Finset E)
    [DecidableEq (Quotient (redSetoid Q blue))]
    (U : Finset (Quotient (redSetoid Q blue))) : Finset V :=
  Finset.univ.filter (fun v => Quotient.mk (redSetoid Q blue) v ∈ U)

/-- Definition 3.7 (Well colouring): partition of `E(Q)` into blue and red edges such that
(i) blue edges form a spanning tree of `Q`, and (ii) `Q / red` is `2`-constructible. -/
structure WellColouring {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (Q : Multigraph V E) where
  blue : Finset E
  blue_tree : (Multigraph.Subgraph.ofEdges Q Finset.univ blue
    (fun _ => Finset.mem_univ _) (fun _ => Finset.mem_univ _)).IsSpanningTree
  [decEqQuot : DecidableEq (Quotient (redSetoid Q blue))]
  [fintypeQuot : Fintype (Quotient (redSetoid Q blue))]
  twoConstr : TwoConstruction (redQuotient Q blue) Finset.univ Finset.univ

attribute [instance] WellColouring.decEqQuot WellColouring.fintypeQuot

/-- Definition 3.5 (Auxiliary graph `Q = ⊔ Q_b` for a `(SUB)` subdivision `H` with
underlying `3`-edge-connected `H₀`, aligned with thread directions). -/
structure AuxGraphData {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : Multigraph V E) (H : G.Subgraph) (sub : SubdivisionData G H) where
  numBlocks : ℕ
  VQ : Type
  EQ : Type
  [fintypeVQ : Fintype VQ]
  [fintypeEQ : Fintype EQ]
  [decEqVQ : DecidableEq VQ]
  [decEqEQ : DecidableEq EQ]
  Q : Multigraph VQ EQ
  /-- Which block component `Q_b` each vertex of `Q` lies in. -/
  comp : VQ → Fin numBlocks
  edge_same_comp : ∀ e : EQ, comp (Q.tail e) = comp (Q.head e)
  /-- Each component `Q_b` is a truncated cubic `3`-edge-connected graph. -/
  comp_tc3ec : ∀ b : Fin numBlocks,
    (Multigraph.Subgraph.induced Q (Finset.univ.filter (fun v => comp v = b))).toMultigraph.IsTruncatedCubic3EC
  /-- Original edges `E(H₀)` embedded into `E(Q)`. -/
  origEdge : sub.E₀ ↪ EQ
  /-- Contraction of expansion components back to `V(H₀)`. -/
  contractV : VQ → sub.V₀
  orig_tail : ∀ t : sub.E₀, contractV (Q.tail (origEdge t)) = sub.H₀.tail t
  orig_head : ∀ t : sub.E₀, contractV (Q.head (origEdge t)) = sub.H₀.head t
  exp_same_contractV : ∀ e : EQ, (∀ t : sub.E₀, origEdge t ≠ e) →
    contractV (Q.tail e) = contractV (Q.head e)
  /-- Inside each component `Q_b`, every fiber `contractV⁻¹(x) ∩ V(Q_b)` is connected by
  expansion edges (either a singleton or a cycle of expansion edges). -/
  fiber_connected : ∀ b : Fin numBlocks, ∀ u v : VQ,
    comp u = b → comp v = b → contractV u = contractV v →
    Relation.ReflTransGen
      (fun x y => ∃ e : EQ, (∀ t : sub.E₀, origEdge t ≠ e) ∧
        ((Q.tail e = x ∧ Q.head e = y) ∨ (Q.tail e = y ∧ Q.head e = x))) u v
  /-- Each block `K_b` of `H₀` corresponds to the image of `Q_b` under `contractV`,
  and every original edge lies in a unique block component. -/
  block_subgraph : Fin numBlocks → sub.H₀.Subgraph
  is_block : ∀ b : Fin numBlocks, sub.H₀.IsBlock (block_subgraph b)
  orig_in_block : ∀ t : sub.E₀, ∀ b : Fin numBlocks,
    t ∈ (block_subgraph b).edges ↔ comp (Q.tail (origEdge t)) = b
  /-- Alignment of `G` with the thread directions on `E(H)` (Definition 3.5). -/
  thread_aligned : ∀ (t : sub.E₀) (i : ℕ) (hi : i < (sub.thread t).edges.length),
    G.tail ((sub.thread t).edges[i]'hi) = (sub.thread t).verts[i]'(by
      have := (sub.thread t).verts_len; omega) ∧
    G.head ((sub.thread t).edges[i]'hi) = (sub.thread t).verts[i + 1]'(by
      have := (sub.thread t).verts_len; omega)

attribute [instance] AuxGraphData.fintypeVQ AuxGraphData.fintypeEQ
  AuxGraphData.decEqVQ AuxGraphData.decEqEQ

/-- Flow projection `π(Y) : E(H) → A` (extended by `0` outside `E(H)`):
on every edge `e` of thread `P_t`, `π(Y)(e) = Y(origEdge t)`. -/
noncomputable def AuxGraphData.pi {V E A : Type} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] [AddCommGroup A]
    {G : Multigraph V E} {H : G.Subgraph} {sub : SubdivisionData G H}
    (aux : AuxGraphData G H sub) (Y : aux.EQ → A) (e : E) : A :=
  by
    classical
    exact if h : ∃ t : sub.E₀, e ∈ (sub.thread t).edges then Y (aux.origEdge h.choose) else 0

/-- A frame of `H` (Section 3, following Lemma 3.9): fixes a well colouring and `2`-construction
on every component `Q_b` of `Q`, together with a topological numbering `1, ..., s` of all
nodes across all components, with pairs `N_i = {e_i, f_i}` and stage vertex sets `V_{U_i}`. -/
structure Frame {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : Multigraph V E) (H : G.Subgraph) (sub : SubdivisionData G H)
    (aux : AuxGraphData G H sub) where
  blue : Finset aux.EQ
  /-- On each component `Q_b`, the blue edges form a spanning tree and `Q_b / red` is `2`-constructible. -/
  comp_wc : ∀ b : Fin aux.numBlocks,
    let Qb := (Multigraph.Subgraph.induced aux.Q (Finset.univ.filter (fun v => aux.comp v = b))).toMultigraph
    ∃ wc : WellColouring Qb, ∀ e, e ∈ wc.blue ↔ e.1 ∈ blue
  /-- Number of nodes across all components. -/
  numNodes : ℕ
  eNode : Fin numNodes → aux.EQ
  fNode : Fin numNodes → aux.EQ
  stageV : Fin numNodes → Finset aux.VQ
  op1V : Fin numNodes → Finset aux.VQ
  op2V : Fin numNodes → Finset aux.VQ
  nodeComp : Fin numNodes → Fin aux.numBlocks
  e_ne_f : ∀ i, eNode i ≠ fNode i
  e_blue : ∀ i, eNode i ∈ blue
  f_blue : ∀ i, fNode i ∈ blue
  /-- Every blue edge belongs to a unique node pair `{e_i, f_i}`. -/
  blue_unique : ∀ t ∈ blue, ∃! i : Fin numNodes, t = eNode i ∨ t = fNode i
  /-- Stage decomposition at node `i` (matching Lemma 3.9(d)). -/
  stage_in_comp : ∀ i, ∀ v ∈ stageV i, aux.comp v = nodeComp i
  stage_union : ∀ i, stageV i = op1V i ∪ op2V i
  stage_disj : ∀ i, Disjoint (op1V i) (op2V i)
  op1_nonempty : ∀ i, (op1V i).Nonempty
  op2_nonempty : ∀ i, (op2V i).Nonempty
  e_cross : ∀ i, (aux.Q.tail (eNode i) ∈ op1V i ∧ aux.Q.head (eNode i) ∈ op2V i) ∨
                 (aux.Q.tail (eNode i) ∈ op2V i ∧ aux.Q.head (eNode i) ∈ op1V i)
  f_cross : ∀ i, (aux.Q.tail (fNode i) ∈ op1V i ∧ aux.Q.head (fNode i) ∈ op2V i) ∨
                 (aux.Q.tail (fNode i) ∈ op2V i ∧ aux.Q.head (fNode i) ∈ op1V i)
  /-- Red edges stay inside operands; blue edges inside `stageV i` belong to nodes `≤ i`
  (topological order), and the only edges of `Q[stageV i]` crossing `op1V i` and `op2V i`
  are `eNode i` and `fNode i`. -/
  red_no_cross : ∀ i, ∀ e : aux.EQ, e ∉ blue →
    (aux.Q.tail e ∈ op1V i → aux.Q.head e ∉ op2V i) ∧
    (aux.Q.tail e ∈ op2V i → aux.Q.head e ∉ op1V i)
  stage_blue_topo : ∀ i, ∀ e ∈ blue,
    aux.Q.tail e ∈ stageV i → aux.Q.head e ∈ stageV i →
    ∃ j : Fin numNodes, j ≤ i ∧ (e = eNode j ∨ e = fNode j)
  stage_crossing_only : ∀ i, ∀ e : aux.EQ,
    ((aux.Q.tail e ∈ op1V i ∧ aux.Q.head e ∈ op2V i) ∨
     (aux.Q.tail e ∈ op2V i ∧ aux.Q.head e ∈ op1V i)) →
    e = eNode i ∨ e = fNode i
  /-- Stage graphs `Q[stageV i]`, `Q[op1V i]`, `Q[op2V i]` are connected, and their red
  edges form forests; every blue edge with both ends in `op1V i` or `op2V i` belongs to a node `< i`. -/
  op1_blue_strict : ∀ i, ∀ e ∈ blue,
    aux.Q.tail e ∈ op1V i → aux.Q.head e ∈ op1V i →
    ∃ j : Fin numNodes, j < i ∧ (e = eNode j ∨ e = fNode j)
  op2_blue_strict : ∀ i, ∀ e ∈ blue,
    aux.Q.tail e ∈ op2V i → aux.Q.head e ∈ op2V i →
    ∃ j : Fin numNodes, j < i ∧ (e = eNode j ∨ e = fNode j)
  red_forest : (Multigraph.Subgraph.ofEdges aux.Q Finset.univ (Finset.univ \ blue)
    (fun _ => Finset.mem_univ _) (fun _ => Finset.mem_univ _)).IsForest
  /-- Every choice `g_i ∈ {e_i, f_i}` plus all red edges spans every stage and every operand,
  guaranteed by recursive stage-nesting and red-closure of operands and components. -/
  op1_connected : ∀ i, (Multigraph.Subgraph.induced aux.Q (op1V i)).Connected
  op2_connected : ∀ i, (Multigraph.Subgraph.induced aux.Q (op2V i)).Connected
  op1_is_stage_or_red : ∀ i,
    (∃ j : Fin numNodes, j < i ∧ op1V i = stageV j) ∨
    (∀ u ∈ op1V i, ∀ v ∈ op1V i, Relation.ReflTransGen (redAdj aux.Q blue) u v)
  op2_is_stage_or_red : ∀ i,
    (∃ j : Fin numNodes, j < i ∧ op2V i = stageV j) ∨
    (∀ u ∈ op2V i, ∀ v ∈ op2V i, Relation.ReflTransGen (redAdj aux.Q blue) u v)
  comp_is_stage_or_red : ∀ b : Fin aux.numBlocks,
    (∃ i : Fin numNodes, stageV i = Finset.univ.filter (fun v => aux.comp v = b)) ∨
    (∀ u v, aux.comp u = b → aux.comp v = b → Relation.ReflTransGen (redAdj aux.Q blue) u v)
  op1_red_closed : ∀ i, ∀ e : aux.EQ, e ∉ blue →
    (aux.Q.tail e ∈ op1V i ↔ aux.Q.head e ∈ op1V i)
  op2_red_closed : ∀ i, ∀ e : aux.EQ, e ∉ blue →
    (aux.Q.tail e ∈ op2V i ↔ aux.Q.head e ∈ op2V i)

namespace Frame

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  {G : Multigraph V E} {H : G.Subgraph} {sub : SubdivisionData G H}
  {aux : AuxGraphData G H sub}

/-- Definition 3.10: An original edge `t : sub.E₀` is protected if `origEdge t ∈ blue`. -/
def IsProtected (fr : Frame G H sub aux) (t : sub.E₀) : Prop :=
  aux.origEdge t ∈ fr.blue

/-- Definition 3.10: An original edge `t : sub.E₀` is free if `origEdge t ∉ blue`. -/
def IsFree (fr : Frame G H sub aux) (t : sub.E₀) : Prop :=
  aux.origEdge t ∉ fr.blue

/-- Definition 3.10: `H_P`, the union of all protected threads in `H`. -/
def HProtected (fr : Frame G H sub aux) : G.Subgraph where
  verts := H.verts.filter (fun v => ∃ t : sub.E₀, aux.origEdge t ∈ fr.blue ∧ v ∈ (sub.thread t).verts)
  edges := H.edges.filter (fun e => ∃ t : sub.E₀, aux.origEdge t ∈ fr.blue ∧ e ∈ (sub.thread t).edges)
  tail_mem {e} he := by
    rw [Finset.mem_filter] at he ⊢
    rcases he with ⟨heH, t, htblue, het⟩
    refine ⟨H.tail_mem heH, t, htblue, ?_⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem het
    have halign := aux.thread_aligned t i hi
    rw [halign.1]
    exact List.getElem_mem _
  head_mem {e} he := by
    rw [Finset.mem_filter] at he ⊢
    rcases he with ⟨heH, t, htblue, het⟩
    refine ⟨H.head_mem heH, t, htblue, ?_⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem het
    have halign := aux.thread_aligned t i hi
    rw [halign.2]
    exact List.getElem_mem _

/-- Subgraph `T^g` of `Q` formed by all red edges together with `g 1, ..., g s`. -/
def Tg (fr : Frame G H sub aux) (g : Fin fr.numNodes → aux.EQ) : aux.Q.Subgraph where
  verts := Finset.univ
  edges := (Finset.univ \ fr.blue) ∪ Finset.univ.image g
  tail_mem _ := Finset.mem_univ _
  head_mem _ := Finset.mem_univ _

/-- Definition 3.10: `T^e`, the subgraph of `Q` formed by all red edges and `e_1, ..., e_s`. -/
def Te (fr : Frame G H sub aux) : aux.Q.Subgraph :=
  fr.Tg fr.eNode

/-- Definition 3.10: `C` is the `i`-th official cycle `C_i` if it is the fundamental cycle
of `f_i` in `T^e`, directed forward along `f_i`. -/
def IsOfficialCycle (fr : Frame G H sub aux) (i : Fin fr.numNodes) (C : aux.Q.DirectedCycle) : Prop :=
  aux.Q.IsFundamentalCycle fr.Te (fr.fNode i) C

end Frame

/-- Definition 3.12: A list assignment `Λ` assigns to each blue edge `t` of `Q` a subset
`Λ(t) ⊆ A`, with `Λ(t) = ∅` on every expansion edge. -/
structure ListAssignment {V E A : Type} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] [AddCommGroup A] [DecidableEq A]
    {G : Multigraph V E} {H : G.Subgraph} {sub : SubdivisionData G H}
    {aux : AuxGraphData G H sub} (fr : Frame G H sub aux) where
  list : aux.EQ → Finset A
  empty_on_exp : ∀ e : aux.EQ, (∀ t : sub.E₀, aux.origEdge t ≠ e) → list e = ∅

/-- `P(Λ)`: the set of `A`-flows `Y` of `Q` satisfying `Y(t) ∉ Λ(t)` for all blue edges `t`. -/
def PLam {V E A : Type} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] [AddCommGroup A] [DecidableEq A]
    {G : Multigraph V E} {H : G.Subgraph} {sub : SubdivisionData G H}
    {aux : AuxGraphData G H sub} {fr : Frame G H sub aux}
    (Lam : ListAssignment (A := A) fr) : Set (aux.EQ → A) :=
  {Y | aux.Q.IsFlow Y ∧ ∀ t ∈ fr.blue, Y t ∉ Lam.list t}

/-- Definition 3.12 (`H`-good flow in case `(CYC)`): `f` is nowhere zero and its
`A`-coordinate `u = quoFlow B f` is non-zero on every edge of `H`. -/
def IsHGoodCyc {V E Γ : Type} [Fintype E] [DecidableEq V] [AddCommGroup Γ]
    (G : Multigraph V E) (B : AddSubgroup Γ) (H : G.Subgraph) (f : G.NZFlow Γ) : Prop :=
  ∀ e ∈ H.edges, quoFlow B f.val e ≠ 0

/-- Definition 3.12 (`H`-good flow in case `(SUB)`): `f` is nowhere zero and its
`A`-coordinate is non-zero on every edge of every protected thread. -/
def IsHGoodSub {V E Γ : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    [AddCommGroup Γ] {G : Multigraph V E} {H : G.Subgraph} {sub : SubdivisionData G H}
    {aux : AuxGraphData G H sub} (fr : Frame G H sub aux) (B : AddSubgroup Γ)
    (f : G.NZFlow Γ) : Prop :=
  ∀ t : sub.E₀, fr.IsProtected t → ∀ e ∈ (sub.thread t).edges, quoFlow B f.val e ≠ 0

/-- Definition 3.12: `Λ_f(t) = { -u(e) : e ∈ E(P_t) }` on original blue edges, `∅` elsewhere. -/
noncomputable def LamOfFlow {V E Γ : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    [AddCommGroup Γ] (B : AddSubgroup Γ) [DecidableEq (Γ ⧸ B)]
    {G : Multigraph V E} {H : G.Subgraph} {sub : SubdivisionData G H}
    {aux : AuxGraphData G H sub} (fr : Frame G H sub aux)
    (f : G.NZFlow Γ) : ListAssignment (A := Γ ⧸ B) fr where
  list e := by
    classical
    exact if h : e ∈ fr.blue ∧ ∃ t : sub.E₀, aux.origEdge t = e then
      ((sub.thread h.2.choose).edges.toFinset).image (fun e' => -quoFlow B f.val e')
    else ∅
  empty_on_exp e hexp := by
    classical
    simp [hexp]

end Flow
