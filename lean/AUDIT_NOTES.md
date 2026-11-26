# Audit notes

This document records the scope, proof architecture, and verification status of the Lean 4 formalization of the short flow reconfiguration paper.

## Axioms and background theorems (zero custom axioms, zero external hypotheses)

Every one of the 65 checked declarations in `Flow/Paper/Statements.lean` (covering all 61 rows of `CLAIM_MAP.tsv`) is proved unconditionally from Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`). Neither custom `axiom`s nor unproved literature hypotheses remain:

1. **`Flow.JLPTWellColouring`** (Theorem 3.8, `Flow.Paper.thm_3_8`):
   - Proved unconditionally in `Flow/Proofs/JLPTWellColouring.lean` following Jaeger, Linial, Payan, and Tarsi (1992), Lemma 3.3 via Lemma 3.2 (induction via sticking at non-trivial 3-edge-cuts and growing on internally 4-edge-connected cubic graphs).

2. **`Flow.SeymourSixFlow`** (Theorem 1.4, `Flow.Paper.thm_1_4`):
   - Proved unconditionally in `Flow/Proofs/TutteFlowPoly.lean` and `Flow/Proofs/SeymourFromJLPT.lean`: Tutte's (1954) deletion–contraction invariance of `|NZFlow G A|` plus Corollary 2.3 reduces the theorem to `ZMod 6`; bottom-up `ZMod 3`-connectivity of `2`-constructible graphs combined with `ZMod 2` fundamental cycles of red edges in the blue spanning tree yields a nowhere-zero `ZMod 6`-flow on every well-coloured graph; reduction of general bridgeless multigraphs (loops, disconnected components, 2-edge-cuts, cut vertices) to loopless 3-edge-connected cut-vertex-free blocks invokes Lemma 3.4(b) and `JLPTWellColouring`.

## Proof modules

- `Flow/Proofs/Elementary.lean`: elementary facts `(E1)`–`(E5)`, small groups `|Γ| ≤ 2`, cycle scalar flows, reorientation flow invariance, loop-cycle non-vacuity witness.
- `Flow/Proofs/SmallClaims.lean`: trivial `I_2(G)` connectivity and move-iff-cycle-support characterization.
- `Flow/Proofs/Coverage.lean`: `ℤ_3` three-parallel-edge counterexample, reorientation move invariance, natural density 1 of Theorem 1.2 orders.
- `Flow/Proofs/Witnesses.lean`: non-vacuity witnesses for `K_4 - v` and the 2-vertex 3-parallel-edge subdivision / auxiliary graph / frame.
- `Flow/Proofs/Basic.lean`, `Flow/Proofs/Liftable.lean`: Section 2 (Lemmas 2.1–2.7, Corollaries 2.3 and 2.8).
- `Flow/Proofs/Extraction.lean`, `Flow/Proofs/Blocks.lean`, `Flow/Proofs/FlowsQ.lean`, `Flow/Proofs/Frames.lean`: Section 3 (Lemmas 3.2, 3.4, 3.6, 3.9, 3.11, Definition 3.12, frame existence).
- `Flow/Proofs/MasterHelpers.lean`, `Flow/Proofs/LiftMove.lean`, `Flow/Proofs/PathAndSub.lean`, `Flow/Proofs/Master.lean`: Section 4 (Lemmas 4.1–4.8 and Theorem 1.3).
- `Flow/Proofs/Averaging.lean`, `Flow/Proofs/Moduli.lean`, `Flow/Proofs/MainInt.lean`: Sections 5–6 (Lemma 5.1, Remark 5.2, Lemmas 6.1–6.2, Table 2, Remark 6.3, Theorems 1.1 and 1.2).
- `Flow/Proofs/JLPTWellColouring.lean`, `Flow/Proofs/TutteFlowPoly.lean`, `Flow/Proofs/SeymourFromJLPT.lean`: unconditional proofs of Theorems 3.8 and 1.4.

## Route differences

- Theorem 1.4 (`SeymourSixFlow`) is proved via `JLPTWellColouring` (`TwoConstruction` `ZMod 3`-connectivity + `ZMod 2` fundamental cycles) and Tutte's deletion–contraction flow polynomial invariance, rather than via Seymour's (1981) original 2-base proof; the stated theorem in `Flow/Defs/Literature.lean` is identical.

Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see [LICENSE](../LICENSE).
