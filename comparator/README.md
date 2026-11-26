# Comparing the Lean statements

The challenge states Theorems 1.1–1.4, Theorem 3.8, and every supporting lemma, corollary, remark, and witness in `Flow/Paper/Statements.lean` (65 declarations in total). Each challenge theorem has an open proof (`sorry`), and the challenge module imports strictly `Flow.Defs.Literature` and `Mathlib.Algebra.Field.ZMod` (no proof modules). The solution in the Lean directory supplies unconditional proofs depending strictly on Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

To run the comparison on Linux with Git, elan, and bubblewrap, start at the root of the checked-out repository:

```sh
set -eu
comparison_dir=$(mktemp -d)
git archive HEAD:lean | tar -xf - -C "$comparison_dir"
cp comparator/Flow/Paper/Challenge.lean "$comparison_dir/Flow/Paper/Challenge.lean"
cp comparator/comparator.json "$comparison_dir/comparator.json"
cd "$comparison_dir"
lake exe cache get
lake --no-cache comparator --config=comparator.json --paranoid
```

Lake compares all 65 declarations and checks the solution across all bundled kernels. A successful run ends with `Your solution is okay!`.

Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see [LICENSE](../LICENSE).
