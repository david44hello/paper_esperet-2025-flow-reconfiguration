-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Logic.Relation
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.Data.Nat.Prime.Defs

@[expose] public section
set_option backward.proofsInPublic true

/-!
# Flow reconfiguration: Theorems 1.1, 1.2, and 1.3
Standalone Mathlib-only statements of Theorems 1.1(a), 1.1(b), 1.1 (`k = 40`), 1.2,
1.2 (orders `40`, `44`, `48`, `50`), and 1.3 for finite bridgeless multigraphs.
-/

namespace Flow

/-- A finite oriented multigraph on vertex type `V` and edge type `E`.
Parallel edges and loops (`tail e = head e`) are permitted. -/
structure Multigraph (V E : Type) where
  tail : E → V
  head : E → V

namespace Multigraph

variable {V E : Type}

/-- A multigraph is loopless if no edge is a loop. -/
def IsLoopless (G : Multigraph V E) : Prop :=
  ∀ e : E, G.tail e ≠ G.head e

/-- Edges crossing the bipartition `(S, V \ S)`. Loops never cross a cut. -/
def cutEdges [Fintype E] [DecidableEq V] (G : Multigraph V E) (S : Finset V) : Finset E :=
  Finset.univ.filter (fun e =>
    (G.tail e ∈ S ∧ G.head e ∉ S) ∨ (G.tail e ∉ S ∧ G.head e ∈ S))

/-- A multigraph is `j`-edge-connected if every bipartition of `V` into two
non-empty parts has at least `j` crossing edges. -/
def IsEdgeConnected [Fintype V] [Fintype E] [DecidableEq V] (G : Multigraph V E) (j : ℕ) : Prop :=
  ∀ S : Finset V, S.Nonempty → (Finset.univ \ S).Nonempty → j ≤ (G.cutEdges S).card

/-- A subgraph of `G`, specified by finite vertex and edge sets closed under endpoints. -/
structure Subgraph (G : Multigraph V E) where
  verts : Finset V
  edges : Finset E
  tail_mem : ∀ {e}, e ∈ edges → G.tail e ∈ verts
  head_mem : ∀ {e}, e ∈ edges → G.head e ∈ verts

namespace Subgraph

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

end Subgraph

/-- An edge `e` is a bridge if it lies on no cycle of `G`. -/
def IsBridge [DecidableEq V] (G : Multigraph V E) (e : E) : Prop :=
  ¬ ∃ C : Subgraph G, C.IsCycle ∧ e ∈ C.edges

/-- A multigraph is bridgeless if it has no bridges (an edgeless graph is bridgeless). -/
def IsBridgeless [DecidableEq V] (G : Multigraph V E) : Prop :=
  ∀ e : E, ¬ G.IsBridge e

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

/-- A directed cycle `C` in `G` consists of a cycle subgraph `sub` together with its signed
indicator `sign : E → {-1, 0, 1}` satisfying `∂ sign = 0`. -/
structure DirectedCycle [Fintype E] [DecidableEq V] (G : Multigraph V E) where
  sub : Subgraph G
  isCycle : sub.IsCycle
  sign : E → ℤ
  sign_mem : ∀ {e}, e ∈ sub.edges → sign e = 1 ∨ sign e = -1
  sign_zero : ∀ {e}, e ∉ sub.edges → sign e = 0
  isFlow : G.IsFlow sign

/-- A nowhere-zero `Γ`-flow of `G`. -/
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

end Multigraph

/-- A symmetric step system in an abelian group `Γ`: a subset `Σ ⊆ Γ \ {0}` closed
under negation. -/
structure StepSystem (Γ : Type) [AddCommGroup Γ] where
  carrier : Set Γ
  zero_not_mem : (0 : Γ) ∉ carrier
  neg_mem : ∀ {x : Γ}, x ∈ carrier → -x ∈ carrier

namespace StepSystem

variable {Γ : Type} [AddCommGroup Γ]

/-- The subgroup step set `Σ_B = Σ ∩ B` viewed as a subset of `B`. -/
def sigB (B : AddSubgroup Γ) (Sig : StepSystem Γ) : Set B :=
  {b : B | (b : Γ) ∈ Sig.carrier}

/-- The projected quotient step set `Σ_A = {q(λ) : λ ∈ Σ} \ {0}` in `Γ / B`. -/
def sigA (B : AddSubgroup Γ) (Sig : StepSystem Γ) : Set (Γ ⧸ B) :=
  {a : Γ ⧸ B | a ≠ 0 ∧ ∃ lam ∈ Sig.carrier, QuotientAddGroup.mk lam = a}

end StepSystem

/-- Reachability inside a set `S ⊆ α` using additive steps from `Step ⊆ α`. -/
def WalkIn {α : Type} [Add α] (S Step : Set α) (x y : α) : Prop :=
  x ∈ S ∧ y ∈ S ∧
  Relation.ReflTransGen (fun u v => u ∈ S ∧ v ∈ S ∧ ∃ s ∈ Step, v = u + s) x y

/-- Condition `(R1)`: after deleting at most `6` elements of `A = Γ / B`, any two
remaining elements are joined by a walk with steps in `Σ_A`. -/
def CondR1 {Γ : Type} [AddCommGroup Γ] (B : AddSubgroup Γ) (Sig : StepSystem Γ) : Prop :=
  ∀ X : Finset (Γ ⧸ B), X.card ≤ 6 →
    ∀ x y : Γ ⧸ B, x ∉ X → y ∉ X → WalkIn {a | a ∉ X} (Sig.sigA B) x y

/-- Condition `(R2)`: after deleting at most `2` elements of `B`, any two remaining
elements are joined by a walk with steps in `Σ_B`. -/
def CondR2 {Γ : Type} [AddCommGroup Γ] (B : AddSubgroup Γ) (Sig : StepSystem Γ) : Prop :=
  ∀ X : Finset B, X.card ≤ 2 →
    ∀ x y : B, x ∉ X → y ∉ X → WalkIn {b | b ∉ X} (Sig.sigB B) x y

/-- Condition `(R3)`: any two non-zero elements of `Γ` are joined by a walk in
`Γ \ {0}` with steps in `Σ`. -/
def CondR3 {Γ : Type} [AddCommGroup Γ] (Sig : StepSystem Γ) : Prop :=
  ∀ x y : Γ, x ≠ 0 → y ≠ 0 → WalkIn {g | g ≠ 0} Sig.carrier x y

/-- A `Σ`-move between nowhere-zero `Γ`-flows: difference is `λ • χ_C` with `λ ∈ Σ`. -/
def Multigraph.SigmaMove {V E Γ : Type} [Fintype E] [DecidableEq V] [DecidableEq E]
    [AddCommGroup Γ] (G : Multigraph V E) (Sig : Set Γ) (f g : G.NZFlow Γ) : Prop :=
  ∃ (C : G.DirectedCycle) (lam : Γ), lam ∈ Sig ∧ ∀ e, g.val e = f.val e + C.sign e • lam

/-- Two nowhere-zero `Γ`-flows are `Σ`-joined if a finite sequence of `Σ`-moves connects them. -/
def Multigraph.SigmaJoined {V E Γ : Type} [Fintype E] [DecidableEq V] [DecidableEq E]
    [AddCommGroup Γ] (G : Multigraph V E) (Sig : Set Γ) (f g : G.NZFlow Γ) : Prop :=
  Relation.ReflTransGen (G.SigmaMove Sig) f g

/-- The `A`-coordinate (quotient modulo `B`) of an edge map `f : E → Γ`. -/
def quoFlow {E Γ : Type} [AddCommGroup Γ] (B : AddSubgroup Γ) (f : E → Γ) (e : E) : Γ ⧸ B :=
  QuotientAddGroup.mk (f e)

/-- Condition `(AV)`: on every loopless `3`-edge-connected multigraph `G` with `n ≥ 2`
vertices and `m` edges, every nowhere-zero `Γ`-flow is `Σ`-joined to a nowhere-zero
`Γ`-flow whose `A`-coordinate has at most `m / 9` zeros (equivalently `9 * zeros ≤ m`). -/
def CondAV {Γ : Type} [AddCommGroup Γ] (B : AddSubgroup Γ) [DecidableEq (Γ ⧸ B)]
    (Sig : StepSystem Γ) : Prop :=
  ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : Multigraph V E),
    G.IsLoopless → G.IsEdgeConnected 3 → 2 ≤ Fintype.card V →
    ∀ f : G.NZFlow Γ,
      ∃ f' : G.NZFlow Γ, G.SigmaJoined Sig.carrier f f' ∧
        9 * (Finset.univ.filter (fun e => quoFlow B f'.val e = 0)).card ≤ Fintype.card E

/-- A finite abelian group `Γ` is cyclic of prime-power order if `Γ ≃+ ZMod (p^r)`
for some prime `p` and `r ≥ 1`. -/
def IsCyclicPrimePower (Γ : Type) [AddCommGroup Γ] : Prop :=
  ∃ (p r : ℕ), Nat.Prime p ∧ 1 ≤ r ∧ Nonempty (Γ ≃+ ZMod (p ^ r))

namespace Paper

/-- **Theorem 1.3 (Master theorem for step systems).**
Let `Γ` be a finite abelian group with a subgroup `B` and quotient `A = Γ / B`
satisfying `|A| ≥ 10` and `|B| ≥ 4`, and let `Σ` be a step system satisfying
`(R1)`, `(R2)`, `(R3)`, and `(AV)`. Then on every finite bridgeless multigraph `G`
(loops allowed), every nowhere-zero `Γ`-flow is `Σ`-joined to every `Γ`-flow whose
`A`-coordinate is nowhere zero; in particular, any two nowhere-zero `Γ`-flows are
`Σ`-joined and `F(G, Γ)` is connected. -/
theorem thm_1_3
    {Γ : Type} [AddCommGroup Γ] [Fintype Γ] [DecidableEq Γ]
    (B : AddSubgroup Γ) [Fintype (Γ ⧸ B)] [Fintype B] [DecidableEq (Γ ⧸ B)] [DecidableEq B]
    (hA : 10 ≤ Fintype.card (Γ ⧸ B)) (hB : 4 ≤ Fintype.card B)
    (Sig : StepSystem Γ)
    (hR1 : CondR1 B Sig) (hR2 : CondR2 B Sig) (hR3 : CondR3 Sig) (hAV : CondAV B Sig)
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : Multigraph V E) (hbr : G.IsBridgeless) :
    (∀ (f h : G.NZFlow Γ), (∀ e, quoFlow B h.val e ≠ 0) → G.SigmaJoined Sig.carrier f h) ∧
    (∀ (f g : G.NZFlow Γ), G.SigmaJoined Sig.carrier f g) ∧
    G.FlowGraphConnected Γ := by sorry

/-- **Theorem 1.1(a) (Integer and modular flows — modular part).**
For every positive multiple `k` of `40`, `48`, or `66`, `M_k(G)` is connected for
every finite bridgeless multigraph `G` (loops allowed). -/
theorem thm_1_1_a
    {k : ℕ} (hk_pos : 0 < k) (hk_div : 40 ∣ k ∨ 48 ∣ k ∨ 66 ∣ k)
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : Multigraph V E) (hbr : G.IsBridgeless) :
    G.ModularFlowConnected k := by sorry

/-- **Theorem 1.1(b) (Integer and modular flows — integer part).**
For every positive multiple `k` of `40`, `48`, or `66`, `I_k(G)` is connected for
every finite bridgeless loopless multigraph `G`. -/
theorem thm_1_1_b
    {k : ℕ} (hk_pos : 0 < k) (hk_div : 40 ∣ k ∨ 48 ∣ k ∨ 66 ∣ k)
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : Multigraph V E) (hbr : G.IsBridgeless) (hll : G.IsLoopless) :
    G.IntFlowConnected k := by sorry

/-- **Theorem 1.1 (k = 40 specialization, answering Problem 1.2 for uniform `k ≥ 5`).** -/
theorem thm_1_1_k40 :
    ∃ k : ℕ, 5 ≤ k ∧ k = 40 ∧
      ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
        (G : Multigraph V E), G.IsBridgeless → G.IsLoopless → G.IntFlowConnected k := by sorry

/-- **Theorem 1.2 (Abelian group flows).**
Let `Γ` be a finite abelian group that is not cyclic of prime-power order, and suppose
`|Γ|` has a divisor `d` with `4 ≤ d ≤ |Γ| / 10`. Then `F(G, Γ)` is connected for every
finite bridgeless multigraph `G` (loops allowed). -/
theorem thm_1_2
    {Γ : Type} [AddCommGroup Γ] [Fintype Γ] [DecidableEq Γ]
    (hnotcp : ¬ IsCyclicPrimePower Γ)
    (hdiv : ∃ d : ℕ, d ∣ Fintype.card Γ ∧ 4 ≤ d ∧ 10 * d ≤ Fintype.card Γ)
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : Multigraph V E) (hbr : G.IsBridgeless) :
    G.FlowGraphConnected Γ := by sorry

/-- **Theorem 1.2 (orders 40, 44, 48, 50 specialization).**
In particular, `F(G, Γ)` is connected for every abelian group `Γ` of order
`40`, `44`, `48`, or `50`. -/
theorem thm_1_2_orders_40_44_48_50
    {Γ : Type} [AddCommGroup Γ] [Fintype Γ] [DecidableEq Γ]
    (hord : Fintype.card Γ = 40 ∨ Fintype.card Γ = 44 ∨ Fintype.card Γ = 48 ∨ Fintype.card Γ = 50)
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : Multigraph V E) (hbr : G.IsBridgeless) :
    G.FlowGraphConnected Γ := by sorry

end Paper
end Flow
