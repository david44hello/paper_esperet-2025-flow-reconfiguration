module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Flow.Defs.Frames

@[expose] public section
set_option backward.proofsInPublic true

/-!
# Statements of the two background theorems from the literature

The paper cites two published theorems from the literature:
1. Seymour (1981) / Tutte (1954) `6`-flow theorem (Theorem 1.4).
2. Jaeger, Linial, Payan, and Tarsi (1992) well-colouring lemma (Theorem 3.8).

Both are formulated here as `Prop` predicates and proved unconditionally from Lean's
three standard axioms in `Flow/Proofs/JLPTWellColouring.lean`,
`Flow/Proofs/TutteFlowPoly.lean`, and `Flow/Proofs/SeymourFromJLPT.lean`.
-/

namespace Flow

/-- **Theorem 1.4 (Seymour 1981; Tutte 1954) — Refereed literature input.**

Source: P. D. Seymour, *Nowhere-zero 6-flows*, J. Combin. Theory Ser. B 30 (1981),
result (3.3), p. 133 (integer circulation with nonzero values of absolute value at most 5);
combined with W. T. Tutte, *A contribution to the theory of chromatic polynomials*,
Canad. J. Math. 6 (1954), 80–91 (reducing modulo `k = |A| ≥ 6` and using Tutte's
same-order group-flow result gives the derived group-order formulation below).

Statement: Every finite bridgeless multigraph (loops allowed) has a nowhere-zero flow
with values in any finite abelian group of order at least `6`. -/
def SeymourSixFlow : Prop :=
  ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : Multigraph V E) (A : Type) [AddCommGroup A] [Fintype A] [DecidableEq A],
    G.IsBridgeless → 6 ≤ Fintype.card A → Nonempty (G.NZFlow A)

/-- **Theorem 3.8 (Jaeger, Linial, Payan, and Tarsi 1992) — Refereed literature input.**

Source: F. Jaeger, N. Linial, C. Payan, and M. Tarsi, *Group connectivity of graphs —
a nonhomogeneous analogue of nowhere-zero flow properties*, J. Combin. Theory Ser. B 56
(1992), 165–182, Lemma 3.3 (p. 177) via Lemma 3.2 (p. 175).

Statement: Every truncated cubic `3`-edge-connected graph admits a well colouring. -/
def JLPTWellColouring : Prop :=
  ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (Q : Multigraph V E), Q.IsTruncatedCubic3EC → Nonempty (WellColouring Q)

end Flow
