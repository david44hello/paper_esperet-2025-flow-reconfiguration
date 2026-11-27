# Guide to the Lean 4 formalization

This guide summarizes the Lean 4 formalization of the paper's results, its definitions, its proof architecture, and its verification record.

## 1. Definitions and trust surface

All definitions appearing in the theorem statements live in `Flow/Defs/` (zero custom axioms):

- `Flow/Defs/Basic.lean`: finite oriented multigraphs (`Multigraph V E`, allowing parallel edges and loops), half-edge degrees (each loop contributes 2), subgraphs, cycles (connected 2-regular subgraphs) and directed cycles with signed indicators `sign : E → ℤ` satisfying `∂ sign = 0`, bridgelessness (edgeless graphs are bridgeless), `j`-edge-connectivity, blocks, subgraph/edge contractions, abelian-group flows, nowhere-zero flows, reconfiguration graphs `F(G, Γ)`, `M_k(G)`, and `I_k(G)`, integer lifts, and liftable steps (Definition 2.5).
- `Flow/Defs/StepSystem.lean`: symmetric step systems `Σ ⊆ Γ \ {0}`, induced step sets `Σ_B` and `Σ_A`, walks in subsets, `Σ`-moves, conditions `(R1)`, `(R2)`, `(R3)`, `(AV)`, target flows, and the cyclic prime-power predicate `IsCyclicPrimePower`.
- `Flow/Defs/Frames.lean`: threads, `(CYC)` and `(SUB)` good subgraphs (Definition 3.1), truncated cubic 3-edge-connected graphs (Definition 3.3), cycle expansions (Lemma 3.4(b)), `2`-constructions and well colourings (Definition 3.7, retaining all blue edges in `Q / red`), auxiliary graphs `Q = ⊔ Q_b` and flow projection `π` (Definition 3.5), frames, protected/free threads, `H_P`, `T^e`, `T^g`, official cycles (Definition 3.10), and list assignments `Λ`, `P(Λ)`, `H`-good flows, and `Λ_f` (Definition 3.12).
- `Flow/Defs/Literature.lean`: the statements of the two published background theorems (`Flow.SeymourSixFlow` and `Flow.JLPTWellColouring`), both proved unconditionally inside `Flow/Proofs/`.

## 2. Axioms and proved background theorems

No custom `axiom` declarations exist anywhere in the repository, and no `sorry`s exist anywhere in the proof library (`Flow.lean`, `Flow/**/*.lean`, and `RegistrySolution.lean`); the two independent comparator challenge files (`comparator/Flow/Paper/Challenge.lean` and `lean/RegistryChallenge.lean`) intentionally contain `sorry` placeholders for the compared statements. Every checked declaration in `Flow/Paper/Statements.lean` depends strictly on Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`), with zero remaining external hypotheses. Both published results cited in the paper are formally proved from scratch:

1. **`Flow.Paper.thm_3_8 : Flow.JLPTWellColouring`** (`Flow/Proofs/JLPTWellColouring.lean`):
   - Proves Lemma 3.3 via Lemma 3.2 of Jaeger, Linial, Payan, and Tarsi (1992): every truncated cubic 3-edge-connected graph admits a well colouring, via strong induction using sticking at non-trivial 3-edge-cuts and growing on internally 4-edge-connected cubic graphs.

2. **`Flow.Paper.thm_1_4 : Flow.SeymourSixFlow`** (`Flow/Proofs/TutteFlowPoly.lean`, `Flow/Proofs/SeymourFromJLPT.lean`):
   - Proves the Seymour (1981) / Tutte (1954) 6-flow theorem for every finite bridgeless multigraph and every finite abelian group of order at least 6: `TwoConstruction` gives `ZMod 3`-connectivity on blue edges, fundamental cycles in the blue spanning tree give a `ZMod 2`-flow non-zero on red edges, combining to a nowhere-zero `ZMod 6`-flow on truncated cubic expansions; reduction to loopless 3-edge-connected cut-vertex-free blocks (Lemma 3.4(b)), integer lifting (Corollary 2.3), and Tutte's deletion–contraction flow polynomial invariance (`tutte_nzflow_card_eq`) extend existence to every finite abelian group of order at least 6.

## 3. Main statements

All paper claims are stated in `Flow/Paper/Statements.lean` and indexed in `CLAIM_MAP.tsv` and `AUDIT.md`:

- **Theorem 1.1** (`Flow.Paper.thm_1_1_a`, `thm_1_1_b`, `thm_1_1_k40`): positive multiples of 40, 48, or 66 make `M_k(G)` connected (loops allowed) and `I_k(G)` connected (loopless); in particular `k = 40` answers Problem 1.2 positively.
- **Theorem 1.2** (`Flow.Paper.thm_1_2`, `thm_1_2_orders_40_44_48_50`): every finite abelian group `Γ` that is not cyclic of prime-power order and admits a divisor `4 ≤ d ≤ |Γ|/10` makes `F(G, Γ)` connected (loops allowed), including all abelian groups of order 40, 44, 48, and 50.
- **Theorem 1.3** (`Flow.Paper.thm_1_3`): master theorem for step systems under `|A| ≥ 10`, `|B| ≥ 4`, `(R1)`, `(R2)`, `(R3)`, and `(AV)`.
- **Theorem 1.4 & Theorem 3.8** (`Flow.Paper.thm_1_4`, `Flow.Paper.thm_3_8`): both background theorems proved unconditionally.

## 4. Verification record

All checks below ran on the exact Lean sources (`Flow.lean`, `Flow/**/*.lean`, `RegistryChallenge.lean`, `RegistrySolution.lean`, `lakefile.toml`, `lean-toolchain`, `lake-manifest.json`, Lean `v4.35.0`, Mathlib `v4.35.0`) and comparator inputs (`comparator/Flow/Paper/Challenge.lean`, `comparator/comparator.json`, `lean/comparator.json`):

- **Clean build from empty:** All 26 `Flow` modules (`Flow`, `Flow.Defs.*`, `Flow.Proofs.*`, `Flow.Paper.Statements`) plus `RegistryChallenge` and `RegistrySolution` built cleanly from an empty build directory (`764 s`).
- **Audit and axiom check (`./scripts/check.sh` / `python3 scripts/audit.py`):** Checked all 66 public declarations in `Flow/Paper/Statements.lean` (covering all 61 rows of `CLAIM_MAP.tsv`). Every declaration depends strictly on Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`), with zero custom axioms, zero `sorry`s in the proof library, and zero external literature hypotheses. An independent `#print axioms` probe confirmed `66 = 66 standard-only + 0 cited` (`0` errors).
- **Per-module kernel replay and whole-library export (`scripts/kernel_replay.sh`):**
  - Per-module `leanchecker` replay on all 25 declaration-bearing `Flow` modules: **PASS** (`316 s`, peak RSS `3.3 GB`); `leanchecker RegistrySolution`: **PASS**.
  - Whole-library `leanexport`: `1,063` safe public `Flow` constants plus transitive core and Mathlib dependencies (`37,214` declaration records; `0` missing; `4` compiler-generated `._unsafe_rec` helpers skipped and replayed in per-module `leanchecker`; export SHA-256 `c9b4e77231cdfb314466ee5a647f4404f9e4809320e81ef0387d6cb5414d74c0`; declared axioms strictly `propext`, `Quot.sound`, `Classical.choice`).
  - Independent export checkers (from an empty environment, `0` failures, `0` skips): `leanchecker --from-export` (**PASS**, `117 s`), `leanchecker-paranoid --from-export` (**PASS**, `116 s`), `lean4lean --import` (**PASS**, `37,211` declarations, `103 s`), `nanoda` (**PASS**, `39,115` declarations, `184 s`), `con-leche --verified` (**PASS**, `37,214` declarations, `265 s`), and `con-ron --verified` (**PASS**, `37,214` declarations, `95 s`).
- **Statement comparison (`lake comparator`):**
  - **Full 66-claim paper challenge** (`comparator/comparator.json`): minimal-mode challenge `comparator/Flow/Paper/Challenge.lean` imports strictly `Flow.Defs.Literature` and `Mathlib.Algebra.Field.ZMod` (zero `Flow.Proofs.*` imports) and matches all 66 theorem signatures verbatim against `Flow/Paper/Statements.lean` with every proof body replaced by `sorry`. Standard mode (`873 s`) and paranoid mode (`--paranoid`, `1,347 s`, all six kernels: `leanchecker`, `leanchecker-paranoid`, `lean4lean` `36,895` declarations, `nanoda`, `con-leche --verified` `36,898` declarations, `con-ron --verified` `36,898` declarations) both accepted (`Your solution is okay!`).
  - **Standalone 6-target registry challenge** (`lean/comparator.json`, `enable_nanoda: true`): `lean/RegistryChallenge.lean` (290 lines, 6 allowlisted Mathlib imports, 6 `sorry` placeholders covering Theorems 1.1–1.3) compared against `lean/RegistrySolution.lean`. Standard mode (`906 s`) and paranoid mode (`--paranoid`, `1,242 s`, all six kernels including `lean4lean` `32,703` declarations and `con-leche`/`con-ron` `32,706` declarations) both accepted (`Your solution is okay!`), and a one-character definition-change negative control (`IsEdgeConnected` `≤` → `<`) was refused (`exit 1`).

Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see [LICENSE](../LICENSE).
