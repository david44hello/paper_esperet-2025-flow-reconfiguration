-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Flow.Defs.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Data.Nat.Prime.Defs

/-!
# Step systems, quotient conditions `(R1)`–`(R3)` and `(AV)`, and group predicates

This module defines symmetric step systems `Σ ⊆ Γ \ {0}`, their induced sets
`Σ_B` and `Σ_A`, `Σ`-moves and `Σ`-joinability, the four master-theorem conditions
`(R1)`, `(R2)`, `(R3)`, `(AV)`, and the cyclic prime-power exclusion predicate.
-/

namespace Flow

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

/-- A `Σ`-move restricted to cycles lying inside a subgraph `H` of `G`. -/
def Multigraph.SigmaMoveIn {V E Γ : Type} [Fintype E] [DecidableEq V] [DecidableEq E]
    [AddCommGroup Γ] (G : Multigraph V E) (H : G.Subgraph) (Sig : Set Γ)
    (f g : G.NZFlow Γ) : Prop :=
  ∃ (C : G.DirectedCycle) (lam : Γ),
    C.sub ≤ H ∧ lam ∈ Sig ∧ ∀ e, g.val e = f.val e + C.sign e • lam

/-- Two nowhere-zero `Γ`-flows are `Σ`-joined by moves on cycles inside `H`. -/
def Multigraph.SigmaJoinedIn {V E Γ : Type} [Fintype E] [DecidableEq V] [DecidableEq E]
    [AddCommGroup Γ] (G : Multigraph V E) (H : G.Subgraph) (Sig : Set Γ)
    (f g : G.NZFlow Γ) : Prop :=
  Relation.ReflTransGen (G.SigmaMoveIn H Sig) f g

/-- The `A`-coordinate (quotient modulo `B`) of an edge map `f : E → Γ`. -/
def quoFlow {E Γ : Type} [AddCommGroup Γ] (B : AddSubgroup Γ) (f : E → Γ) (e : E) : Γ ⧸ B :=
  QuotientAddGroup.mk (f e)

/-- A `Γ`-flow `h` is a target flow (relative to `B`) if its `A`-coordinate `quoFlow B h`
is nowhere zero. -/
def IsTargetFlow {V E Γ : Type} [Fintype E] [DecidableEq V] [AddCommGroup Γ]
    (G : Multigraph V E) (B : AddSubgroup Γ) (h : E → Γ) : Prop :=
  G.IsFlow h ∧ ∀ e, quoFlow B h e ≠ 0

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

end Flow
