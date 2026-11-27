module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Logic.Relation

@[expose] public section
set_option backward.proofsInPublic true

/-!
# Core definitions for finite multigraphs, flows, and reconfiguration graphs

This module defines finite oriented multigraphs (allowing loops and parallel edges),
subgraphs, cycles and directed cycles with signed indicators, bridgelessness,
edge-connectivity, blocks, contractions, abelian-group flows, integer `k`-flows,
and the reconfiguration graphs `F(G, Γ)`, `M_k(G)`, and `I_k(G)`.
-/

namespace Flow

/-- A finite oriented multigraph on vertex type `V` and edge type `E`.
Parallel edges and loops (`tail e = head e`) are permitted. -/
structure Multigraph (V E : Type) where
  tail : E → V
  head : E → V

namespace Multigraph

variable {V E : Type}

/-- An edge is a loop if its tail and head coincide. -/
def IsLoop (G : Multigraph V E) (e : E) : Prop :=
  G.tail e = G.head e

/-- A multigraph is loopless if no edge is a loop. -/
def IsLoopless (G : Multigraph V E) : Prop :=
  ∀ e : E, G.tail e ≠ G.head e

/-- Two edges are parallel if they share the same unordered pair of endpoints. -/
def SameEnds (G : Multigraph V E) (e₁ e₂ : E) : Prop :=
  (G.tail e₁ = G.tail e₂ ∧ G.head e₁ = G.head e₂) ∨
  (G.tail e₁ = G.head e₂ ∧ G.head e₁ = G.tail e₂)

/-- A multigraph is simple if it is loopless and has no distinct parallel edges. -/
def IsSimple (G : Multigraph V E) : Prop :=
  G.IsLoopless ∧ ∀ e₁ e₂ : E, G.SameEnds e₁ e₂ → e₁ = e₂

/-- Undirected adjacency of two vertices in `G`. -/
def Adj (G : Multigraph V E) (u v : V) : Prop :=
  ∃ e : E, (G.tail e = u ∧ G.head e = v) ∨ (G.tail e = v ∧ G.head e = u)

/-- A multigraph is connected if every pair of vertices is joined by a walk. -/
def Connected (G : Multigraph V E) : Prop :=
  ∀ u v : V, Relation.ReflTransGen G.Adj u v

/-- Reorient the edges selected by `flip`. -/
def reorient (G : Multigraph V E) (flip : E → Bool) : Multigraph V E where
  tail e := if flip e then G.head e else G.tail e
  head e := if flip e then G.tail e else G.head e

/-- Transform an edge-valued function under edge reorientation. -/
def reorientVal {Γ : Type} [AddCommGroup Γ] (flip : E → Bool) (x : E → Γ) (e : E) : Γ :=
  if flip e then -x e else x e

/-- Degree of a vertex in `G`; each loop contributes `2`. -/
def deg [Fintype E] [DecidableEq V] (G : Multigraph V E) (v : V) : ℕ :=
  (Finset.univ.filter (fun e => G.tail e = v)).card +
  (Finset.univ.filter (fun e => G.head e = v)).card

/-- A multigraph is cubic if every vertex has degree `3`. -/
def IsCubic [Fintype E] [DecidableEq V] (G : Multigraph V E) : Prop :=
  ∀ v : V, G.deg v = 3

/-- Edges crossing the bipartition `(S, V \ S)`. Loops never cross a cut. -/
def cutEdges [Fintype E] [DecidableEq V] (G : Multigraph V E) (S : Finset V) : Finset E :=
  Finset.univ.filter (fun e =>
    (G.tail e ∈ S ∧ G.head e ∉ S) ∨ (G.tail e ∉ S ∧ G.head e ∈ S))

/-- A multigraph is `j`-edge-connected if every bipartition of `V` into two
non-empty parts has at least `j` crossing edges. -/
def IsEdgeConnected [Fintype V] [Fintype E] [DecidableEq V] (G : Multigraph V E) (j : ℕ) : Prop :=
  ∀ S : Finset V, S.Nonempty → (Finset.univ \ S).Nonempty → j ≤ (G.cutEdges S).card

/-- Delete a vertex `v` and all incident edges from `G`. -/
def deleteVertex (G : Multigraph V E) (v : V) :
    Multigraph {u : V // u ≠ v} {e : E // G.tail e ≠ v ∧ G.head e ≠ v} where
  tail e := ⟨G.tail e.1, e.2.1⟩
  head e := ⟨G.head e.1, e.2.2⟩

/-- Delete all loops from `G`. -/
def deleteLoops (G : Multigraph V E) : Multigraph V {e : E // G.tail e ≠ G.head e} where
  tail e := G.tail e.1
  head e := G.head e.1

/-- An isomorphism of multigraphs (allowing edge orientations to be reversed). -/
structure Iso {V₁ E₁ V₂ E₂ : Type} (G₁ : Multigraph V₁ E₁) (G₂ : Multigraph V₂ E₂) where
  toVert : V₁ ≃ V₂
  toEdge : E₁ ≃ E₂
  dir : E₁ → Bool
  tail_eq : ∀ e, G₂.tail (toEdge e) =
    if dir e then toVert (G₁.head e) else toVert (G₁.tail e)
  head_eq : ∀ e, G₂.head (toEdge e) =
    if dir e then toVert (G₁.tail e) else toVert (G₁.head e)

/-- A subgraph of `G`, specified by finite vertex and edge sets closed under endpoints. -/
@[ext]
structure Subgraph (G : Multigraph V E) where
  verts : Finset V
  edges : Finset E
  tail_mem : ∀ {e}, e ∈ edges → G.tail e ∈ verts
  head_mem : ∀ {e}, e ∈ edges → G.head e ∈ verts

namespace Subgraph

/-- Ordering on subgraphs by inclusion of vertex and edge sets. -/
instance (G : Multigraph V E) : LE (Subgraph G) where
  le H₁ H₂ := H₁.verts ⊆ H₂.verts ∧ H₁.edges ⊆ H₂.edges

/-- The whole graph as a subgraph of itself. -/
def top [Fintype V] [Fintype E] (G : Multigraph V E) : Subgraph G where
  verts := Finset.univ
  edges := Finset.univ
  tail_mem _ := Finset.mem_univ _
  head_mem _ := Finset.mem_univ _

/-- Convert a subgraph to a standalone multigraph on its vertex and edge subtypes. -/
def toMultigraph {G : Multigraph V E} (H : Subgraph G) :
    Multigraph {v : V // v ∈ H.verts} {e : E // e ∈ H.edges} where
  tail e := ⟨G.tail e.1, H.tail_mem e.2⟩
  head e := ⟨G.head e.1, H.head_mem e.2⟩

/-- Degree of a vertex `v` in a subgraph `H` (loops contribute `2`). -/
def deg [DecidableEq V] {G : Multigraph V E} (H : Subgraph G) (v : V) : ℕ :=
  (H.edges.filter (fun e => G.tail e = v)).card +
  (H.edges.filter (fun e => G.head e = v)).card

/-- Adjacency inside a subgraph `H`. -/
def Adj {G : Multigraph V E} (H : Subgraph G) (u v : V) : Prop :=
  ∃ e ∈ H.edges, (G.tail e = u ∧ G.head e = v) ∨ (G.tail e = v ∧ G.head e = u)

/-- A subgraph is connected if its vertex set is non-empty and any two vertices are joined
by a walk in `H`. -/
def Connected {G : Multigraph V E} (H : Subgraph G) : Prop :=
  H.verts.Nonempty ∧ ∀ u ∈ H.verts, ∀ v ∈ H.verts, Relation.ReflTransGen H.Adj u v

/-- A cycle is a connected `2`-regular subgraph (a loop has length `1`; two parallel
edges form a cycle of length `2`). -/
def IsCycle [DecidableEq V] {G : Multigraph V E} (H : Subgraph G) : Prop :=
  H.Connected ∧ ∀ v ∈ H.verts, H.deg v = 2

/-- A subgraph is acyclic (a forest) if it contains no cycle subgraph. -/
def IsForest [DecidableEq V] {G : Multigraph V E} (H : Subgraph G) : Prop :=
  ∀ C : Subgraph G, C ≤ H → ¬ C.IsCycle

/-- A spanning forest of `G` has all vertices of `G`, is acyclic, and preserves
connectedness within each component of `G`. -/
def IsSpanningForest [Fintype V] [DecidableEq V] {G : Multigraph V E} (T : Subgraph G) : Prop :=
  T.verts = Finset.univ ∧ T.IsForest ∧
  ∀ u v : V, Relation.ReflTransGen G.Adj u v → Relation.ReflTransGen T.Adj u v

/-- A spanning tree of `G` is a connected acyclic subgraph on all vertices of `G`. -/
def IsSpanningTree [Fintype V] [DecidableEq V] {G : Multigraph V E} (T : Subgraph G) : Prop :=
  T.verts = Finset.univ ∧ T.Connected ∧ T.IsForest

/-- Delete vertex `v` and its incident edges from a subgraph `H`. -/
def deleteVertex [DecidableEq V] [DecidableEq E] {G : Multigraph V E}
    (H : Subgraph G) (v : V) : Subgraph G where
  verts := H.verts.erase v
  edges := H.edges.filter (fun e => G.tail e ≠ v ∧ G.head e ≠ v)
  tail_mem {e} he := by
    rw [Finset.mem_filter] at he
    exact Finset.mem_erase.mpr ⟨he.2.1, H.tail_mem he.1⟩
  head_mem {e} he := by
    rw [Finset.mem_filter] at he
    exact Finset.mem_erase.mpr ⟨he.2.2, H.head_mem he.1⟩

/-- `v` is a cut vertex of `H` if `v ∈ H.verts` and `H - v` is disconnected
(has at least two vertices not joined by a walk in `H - v`). -/
def IsCutVertex [DecidableEq V] [DecidableEq E] {G : Multigraph V E}
    (H : Subgraph G) (v : V) : Prop :=
  v ∈ H.verts ∧ ∃ u w, u ∈ (H.deleteVertex v).verts ∧ w ∈ (H.deleteVertex v).verts ∧
    ¬ Relation.ReflTransGen (H.deleteVertex v).Adj u w

/-- A subgraph has no cut vertex. -/
def HasNoCutVertex [DecidableEq V] [DecidableEq E] {G : Multigraph V E}
    (H : Subgraph G) : Prop :=
  ∀ v ∈ H.verts, ¬ H.IsCutVertex v

/-- The induced subgraph of `G` on a vertex subset `U`. -/
def induced [Fintype E] [DecidableEq V] (G : Multigraph V E) (U : Finset V) : Subgraph G where
  verts := U
  edges := Finset.univ.filter (fun e => G.tail e ∈ U ∧ G.head e ∈ U)
  tail_mem he := (Finset.mem_filter.mp he).2.1
  head_mem he := (Finset.mem_filter.mp he).2.2

/-- Subgraph on `U` retaining edges from `F` whose endpoints lie in `U`. -/
def ofEdges (G : Multigraph V E) (U : Finset V) (F : Finset E)
    (ht : ∀ {e}, e ∈ F → G.tail e ∈ U) (hh : ∀ {e}, e ∈ F → G.head e ∈ U) : Subgraph G where
  verts := U
  edges := F
  tail_mem := ht
  head_mem := hh

end Subgraph

/-- A block of `G` is a maximal connected subgraph without a cut vertex. -/
def IsBlock [DecidableEq V] [DecidableEq E] (G : Multigraph V E) (K : Subgraph G) : Prop :=
  K.Connected ∧ K.HasNoCutVertex ∧
  ∀ K' : Subgraph G, K ≤ K' → K'.Connected → K'.HasNoCutVertex → K' = K

/-- An edge `e` is a bridge if it lies on no cycle of `G`. -/
def IsBridge [DecidableEq V] (G : Multigraph V E) (e : E) : Prop :=
  ¬ ∃ C : Subgraph G, C.IsCycle ∧ e ∈ C.edges

/-- A multigraph is bridgeless if it has no bridges (an edgeless graph is bridgeless). -/
def IsBridgeless [DecidableEq V] (G : Multigraph V E) : Prop :=
  ∀ e : E, ¬ G.IsBridge e

/-- Contraction `G / H` obtained by identifying `H.verts` to a single vertex (`none`)
and deleting all edges of `H` (keeping all other edges, possibly creating loops or
parallel edges). -/
def contractSubgraph [DecidableEq V] [DecidableEq E] (G : Multigraph V E) (H : Subgraph G) :
    Multigraph (Option {v : V // v ∉ H.verts}) {e : E // e ∉ H.edges} where
  tail e := if h : G.tail e.1 ∈ H.verts then none else some ⟨G.tail e.1, h⟩
  head e := if h : G.head e.1 ∈ H.verts then none else some ⟨G.head e.1, h⟩

/-- Identify a partition of `V` given by `q : V → W` and delete edges whose endpoints
map to the same class. -/
def contractBy {W : Type} [DecidableEq W] (G : Multigraph V E) (q : V → W) :
    Multigraph W {e : E // q (G.tail e) ≠ q (G.head e)} where
  tail e := q (G.tail e.1)
  head e := q (G.head e.1)

/-- Contract a single non-loop edge `e₀` by identifying its endpoints and deleting `e₀`. -/
def contractEdge [DecidableEq V] [DecidableEq E] (G : Multigraph V E) (e₀ : E)
    (hne : G.tail e₀ ≠ G.head e₀) :
    Multigraph {v : V // v ≠ G.head e₀} {e : E // e ≠ e₀} where
  tail e := if h : G.tail e.1 = G.head e₀ then ⟨G.tail e₀, hne⟩ else ⟨G.tail e.1, h⟩
  head e := if h : G.head e.1 = G.head e₀ then ⟨G.tail e₀, hne⟩ else ⟨G.head e.1, h⟩

/-! ### Boundaries, flows, directed cycles, and reconfiguration graphs -/

/-- Boundary `(∂ x)(v) = ∑_{head e = v} x e - ∑_{tail e = v} x e`. Loops cancel. -/
def boundary {Γ : Type} [AddCommGroup Γ] [Fintype E] [DecidableEq V]
    (G : Multigraph V E) (x : E → Γ) (v : V) : Γ :=
  (∑ e ∈ Finset.univ.filter (fun e => G.head e = v), x e) -
  (∑ e ∈ Finset.univ.filter (fun e => G.tail e = v), x e)

/-- `x : E → Γ` is a `Γ`-flow if its boundary vanishes at every vertex. -/
def IsFlow {Γ : Type} [AddCommGroup Γ] [Fintype E] [DecidableEq V]
    (G : Multigraph V E) (x : E → Γ) : Prop :=
  ∀ v : V, G.boundary x v = 0

/-- An edge map is nowhere zero if it vanishes on no edge. -/
def IsNowhereZero {Γ : Type} [Zero Γ] (x : E → Γ) : Prop :=
  ∀ e : E, x e ≠ 0

/-- Support of an edge map `x : E → Γ`. -/
def supp {Γ : Type} [Zero Γ] [Fintype E] [DecidableEq Γ] (x : E → Γ) : Finset E :=
  Finset.univ.filter (fun e => x e ≠ 0)

/-- A directed cycle `C` in `G` consists of a cycle subgraph `sub` together with its signed
indicator `sign : E → {-1, 0, 1}` satisfying `∂ sign = 0`. -/
@[ext]
structure DirectedCycle [Fintype E] [DecidableEq V] (G : Multigraph V E) where
  sub : Subgraph G
  isCycle : sub.IsCycle
  sign : E → ℤ
  sign_mem : ∀ {e}, e ∈ sub.edges → sign e = 1 ∨ sign e = -1
  sign_zero : ∀ {e}, e ∉ sub.edges → sign e = 0
  isFlow : G.IsFlow sign

/-- Reversing a directed cycle negates its signed indicator. -/
def DirectedCycle.reverse [Fintype E] [DecidableEq V] {G : Multigraph V E}
    (C : G.DirectedCycle) : G.DirectedCycle where
  sub := C.sub
  isCycle := C.isCycle
  sign e := -C.sign e
  sign_mem {e} he := by
    rcases C.sign_mem he with h | h <;> simp [h]
  sign_zero {e} he := by
    simp [C.sign_zero he]
  isFlow v := by
    have h := C.isFlow v
    unfold boundary at h ⊢
    simp only [Finset.sum_neg_distrib, sub_eq_zero] at h ⊢
    rw [h]

/-- `C` is the fundamental cycle of `e` in a subgraph (spanning forest) `T`, directed
forward along `e`: its edges lie in `{e} ∪ E(T)` and `χ_C(e) = 1`. -/
def IsFundamentalCycle [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : Multigraph V E) (T : Subgraph G) (e : E) (C : G.DirectedCycle) : Prop :=
  C.sub.edges ⊆ insert e T.edges ∧ C.sign e = 1

/-- A nowhere-zero `Γ`-flow of `G`. -/
@[ext]
structure NZFlow [Fintype E] [DecidableEq V] (G : Multigraph V E) (Γ : Type) [AddCommGroup Γ] where
  val : E → Γ
  isFlow : G.IsFlow val
  nonzero : IsNowhereZero val

/-- Adjacency (move) in `F(G, Γ)`: `g - f = λ • χ_C` for a directed cycle `C` and `λ ≠ 0`. -/
def FlowMove [Fintype E] [DecidableEq V] {Γ : Type} [AddCommGroup Γ]
    (G : Multigraph V E) (f g : G.NZFlow Γ) : Prop :=
  ∃ (C : G.DirectedCycle) (lam : Γ), lam ≠ 0 ∧ ∀ e, g.val e = f.val e + C.sign e • lam

/-- Connectivity of the flow reconfiguration graph `F(G, Γ)` (empty graph is connected). -/
def FlowGraphConnected [Fintype E] [DecidableEq V] (G : Multigraph V E) (Γ : Type)
    [AddCommGroup Γ] : Prop :=
  ∀ f g : G.NZFlow Γ, Relation.ReflTransGen G.FlowMove f g

/-- Connectivity of the modular flow reconfiguration graph `M_k(G) = F(G, ℤ_k)`. -/
def ModularFlowConnected [Fintype E] [DecidableEq V] (G : Multigraph V E) (k : ℕ) : Prop :=
  G.FlowGraphConnected (ZMod k)

/-- An integer `k`-flow: a nowhere-zero `ℤ`-flow with `1 ≤ |F(e)| ≤ k - 1` on every edge. -/
@[ext]
structure IntKFlow [Fintype E] [DecidableEq V] (G : Multigraph V E) (k : ℕ) where
  val : E → ℤ
  isFlow : G.IsFlow val
  nonzero : ∀ e, val e ≠ 0
  bound : ∀ e, |val e| ≤ (k : ℤ) - 1

/-- Adjacency (move) in `I_k(G)`: `F' - F = λ · χ_C` for a directed cycle `C` and `λ ∈ ℤ \ {0}`. -/
def IntKFlowMove [Fintype E] [DecidableEq V] {k : ℕ}
    (G : Multigraph V E) (F F' : G.IntKFlow k) : Prop :=
  ∃ (C : G.DirectedCycle) (lam : ℤ), lam ≠ 0 ∧ ∀ e, F'.val e = F.val e + C.sign e * lam

/-- Connectivity of the integer flow reconfiguration graph `I_k(G)`. -/
def IntFlowConnected [Fintype E] [DecidableEq V] (G : Multigraph V E) (k : ℕ) : Prop :=
  ∀ F F' : G.IntKFlow k, Relation.ReflTransGen G.IntKFlowMove F F'

/-- `F ∈ V(I_k(G))` is an integer lift of a nowhere-zero `ℤ_k`-flow `f` if `F ≡ f (mod k)`. -/
def IsIntLift [Fintype E] [DecidableEq V] {k : ℕ}
    (G : Multigraph V E) (f : G.NZFlow (ZMod k)) (F : G.IntKFlow k) : Prop :=
  ∀ e, (F.val e : ZMod k) = f.val e

/-- Definition 2.5 (Liftable step): for `k ≥ 3`, `z ∈ ℤ_k \ {0}` is liftable if for every
finite loopless multigraph `G` and every move `f → f + z χ_C` of `M_k(G)`, all integer
lifts of `f` and all integer lifts of `f + z χ_C` lie in the same component of `I_k(G)`. -/
def IsLiftable (k : ℕ) (z : ZMod k) : Prop :=
  z ≠ 0 ∧
  ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : Multigraph V E), G.IsLoopless →
    ∀ (f f' : G.NZFlow (ZMod k)) (C : G.DirectedCycle),
      (∀ e, f'.val e = f.val e + C.sign e • z) →
      ∀ (F F' : G.IntKFlow k), G.IsIntLift f F → G.IsIntLift f' F' →
        Relation.ReflTransGen G.IntKFlowMove F F'

end Multigraph
end Flow
