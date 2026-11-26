# Flow reconfiguration: formalization in Lean 4

The paper's link is on the [front page of this repository](https://github.com/david44hello/paper_esperet-2025-flow-reconfiguration).

This directory contains a complete, self-contained Lean 4 formalization of the paper — Theorem 1.1 (integer and modular flow reconfiguration for positive multiples of 40, 48, and 66), Theorem 1.2 (abelian group flow reconfiguration for non-cyclic-prime-power finite abelian groups admitting a divisor $4 \le d \le |\Gamma|/10$), and Theorem 1.3 (the master theorem for step systems) — together with all supporting lemmas, remarks, and the two cited background results (Theorem 1.4, Seymour–Tutte 6-flow theorem; Theorem 3.8, Jaeger–Linial–Payan–Tarsi well-colouring lemma). Every checked declaration is proved unconditionally from Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`), with zero custom axioms and zero external hypotheses.

See [WHAT_TO_READ.md](WHAT_TO_READ.md) for the statement guide, proof architecture, and verification record.

## How to verify

Install [elan](https://github.com/leanprover/elan) (the toolchain is pinned in `lean-toolchain`), then from this directory run:

```bash
./scripts/check.sh
```

A successful run ends with:

```text
Checked 66 Lean declarations against the three permitted standard axioms.
```

Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see [LICENSE](../LICENSE).
