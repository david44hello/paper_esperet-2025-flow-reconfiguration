# Paper claim audit

Every declaration below is proved unconditionally from Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`), with zero custom axioms and zero external hypotheses.

| Place | Source anchor | Lines | Claim | Status | Lean declarations |
|---|---|---|---|---|---|
| Theorem 1.1(a) — modular flows | thm:main-int | 122–125 | For every positive multiple k of 40, 48, or 66, M_k(G) is connected for every finite bridgeless multigraph G (loops allowed). | PROVED | `Flow.Paper.thm_1_1_a` |
| Theorem 1.1(b) — integer flows | thm:main-int | 122–126 | For every positive multiple k of 40, 48, or 66, I_k(G) is connected for every finite bridgeless loopless multigraph G. | PROVED | `Flow.Paper.thm_1_1_b` |
| Theorem 1.1 — k = 40 answers Problem 1.2 | thm:main-int | 128 | k = 40 satisfies k >= 5 and makes I_40(G) connected for every finite bridgeless loopless multigraph G. | PROVED | `Flow.Paper.thm_1_1_k40` |
| Theorem 1.2 — abelian group flows | thm:main-grp | 131–133 | For every finite abelian group Gamma not cyclic of prime-power order with a divisor 4 <= d <= |Gamma|/10, F(G, Gamma) is connected for every finite bridgeless multigraph G. | PROVED | `Flow.Paper.thm_1_2` |
| Theorem 1.2 — orders 40, 44, 48, 50 | thm:main-grp | 132–133 | F(G, Gamma) is connected for every finite abelian group of order 40, 44, 48, or 50. | PROVED | `Flow.Paper.thm_1_2_orders_40_44_48_50` |
| Theorem 1.3 — master theorem for step systems | thm:master | 143–145 | Under |A| >= 10, |B| >= 4, (R1), (R2), (R3), and (AV), every nowhere-zero Gamma-flow is Sigma-joined to every target flow, any two nowhere-zero flows are Sigma-joined, and F(G, Gamma) is connected. | PROVED | `Flow.Paper.thm_1_3` |
| Theorem 1.4 — Seymour-Tutte 6-flow theorem | thm:seymour | 169–171 | Every finite bridgeless multigraph (loops allowed) admits a nowhere-zero flow in every finite abelian group of order at least 6. | PROVED | `Flow.Paper.thm_1_4` |
| Section 1 — trivial small groups | sec:intro | 92 | F(G, Gamma) is connected whenever |Gamma| <= 2. | PROVED | `Flow.Paper.sec1_trivial_small_group` |
| Section 1 — trivial integer 2-flows | sec:intro | 92 | I_2(G) is connected for every finite multigraph G. | PROVED | `Flow.Paper.sec1_trivial_int_k2` |
| Section 1 — Z_3 counterexample | sec:intro | 92 | Z_3 fails on three parallel edges between two vertices. | PROVED | `Flow.Paper.sec1_Z3_three_parallel_disconnected` |
| Figure 1 caption — density 1 of covered orders | fig:before-after | fig1 151 | The set of orders covered by Theorem 1.2 has natural density 1. | PROVED | `Flow.Paper.fig1_density_one` |
| Section 2 — cycle scalar flow | sec:lifting | 185 | lambda * chi_C is a Gamma-flow for every directed cycle C and lambda in Gamma. | PROVED | `Flow.Paper.sec2_cycle_smul_isFlow` |
| Section 2 — reorientation preserves flows | sec:lifting | 185 | Reversing reference edge orientations and negating flow values preserves flows. | PROVED | `Flow.Paper.sec2_reorient_preserves_flow` |
| Section 2 — reorientation preserves moves | sec:lifting | 185 | Reversing reference edge orientations preserves flow adjacency. | PROVED | `Flow.Paper.sec2_reorient_preserves_flowMove` |
| Section 2 — move iff cycle support | sec:lifting | 187 | Two nowhere-zero flows differ by a nonzero cycle multiple iff the support of their difference is a cycle. | PROVED | `Flow.Paper.sec2_move_iff_supp_cycle` |
| Lemma 2.1(a) — fundamental cycle decomposition | lem:cycledec | 193–196 | Every A-flow has a unique fundamental-cycle representation with respect to any spanning forest and is a sum of cycle flows. | PROVED | `Flow.Paper.lem_2_1_a` |
| Lemma 2.1(b) — signed cycle decomposition | lem:cycledec | 197–198 | Every integer flow decomposes into sign-consistent directed cycles with multiplicity |h(e)|, edge-disjoint for {-1,0,1}-flows. | PROVED | `Flow.Paper.lem_2_1_b` |
| Lemma 2.2 — rounding | lem:rounding | 207–209 | Every [0,1]-valued edge map with integer boundary rounds to a {0,1}-valued map with the same boundary preserving {0,1} edges. | PROVED | `Flow.Paper.lem_2_2` |
| Corollary 2.3 — integer lifts | cor:lifting | 215–217 | Every Z_k-flow lifts to an integer flow with |F(e)| <= k - 1 and identical zero set. | PROVED | `Flow.Paper.cor_2_3` |
| Lemma 2.4 — connected fibres | lem:fibres | 223–225 | Integer lifts of a nowhere-zero Z_k-flow induce a connected subgraph of I_k(G). | PROVED | `Flow.Paper.lem_2_4` |
| Lemma 2.6 — step of size 1 | lem:step1 | 238–240 | For every integer lift F of f, F + chi_C is an integer lift of f + chi_C. | PROVED | `Flow.Paper.lem_2_6` |
| Lemma 2.7 — divisor move | lem:divmove | 246–248 | For any proper divisor 1 <= q < k, a path in I_k(G) connects a lift of f to a lift of f + q chi_C. | PROVED | `Flow.Paper.lem_2_7` |
| Corollary 2.8(a) — proper divisors are liftable | cor:liftable | 269–272 | Every +-q for a proper divisor 1 <= q < k is liftable. | PROVED | `Flow.Paper.cor_2_8_a` |
| Corollary 2.8(b) — liftable step systems lift connectivity | cor:liftable | 273–274 | If a liftable step system connects M_k(G) on a loopless multigraph G, then I_k(G) is connected. | PROVED | `Flow.Paper.cor_2_8_b` |
| Lemma 3.2 — extraction | lem:extraction | 299–301 | Every loopless multigraph with n >= 3 vertices and more than (4/3)n - 2 edges contains a good subgraph. | PROVED | `Flow.Paper.lem_3_2` |
| Lemma 3.4(a) — block 3-edge-connectivity | lem:reduction | 329–331 | Every block of a loopless 3-edge-connected multigraph on >= 2 vertices is loopless, 3-edge-connected, has >= 2 vertices, and has no cut vertex. | PROVED | `Flow.Paper.lem_3_4_a` |
| Lemma 3.4(b) — truncated cubic expansion | lem:reduction | 332–333 | Every loopless 3-edge-connected cut-vertex-free multigraph on >= 2 vertices admits a truncated cubic 3-edge-connected cycle expansion. | PROVED | `Flow.Paper.lem_3_4_b` |
| Definition 3.5 — auxiliary graph existence | def:threads | 348–350 | After reorienting H along thread directions, every (SUB) subdivision admits an auxiliary graph Q = disjoint union Q_b. | PROVED | `Flow.Paper.aux_graph_exists` |
| Lemma 3.6(a) — thread constancy and bijection | lem:flows | 356–359 | Cycles and A-flows of H are constant on threads and A-flows of H biject explicitly with A-flows of H_0. | PROVED | `Flow.Paper.lem_3_6_a` |
| Lemma 3.6(b) — block flow restriction | lem:flows | 360 | Restriction of an A-flow of H_0 to any block K_b is an A-flow of K_b. | PROVED | `Flow.Paper.lem_3_6_b` |
| Lemma 3.6(c) — projection pi surjectivity | lem:flows | 361 | pi maps A-flows of Q onto A-flows of H. | PROVED | `Flow.Paper.lem_3_6_c` |
| Lemma 3.6(d) — projected cycle decomposition | lem:flows | 362 | For every directed cycle C of Q, pi(x chi_C) is x times a sum of pairwise edge-disjoint directed cycles of H. | PROVED | `Flow.Paper.lem_3_6_d` |
| Theorem 3.8 — JLPT well colouring | thm:jlpt | 384–386 | Every truncated cubic 3-edge-connected graph admits a well colouring. | PROVED | `Flow.Paper.thm_3_8` |
| Lemma 3.9(a) — well-colouring counts and red forest | lem:counts-stages | 392–395 | Q_b is simple and connected with 3(n-1)/2 edges, red edges form a forest, and no blue edge stays in one red component. | PROVED | `Flow.Paper.lem_3_9` |
| Lemma 3.9(b)–(d) — stages and stage graphs | lem:counts-stages | 396–399 | Stages are disjoint or nested, induced in Q/red, Q_U is connected with exact edge and operand decompositions. | PROVED | `Flow.Paper.lem_3_9_bcd` |
| Section 3 — frame existence | sec:frames | 408 | Given JLPT well colouring, every auxiliary graph Q admits a topologically ordered frame. | PROVED | `Flow.Paper.frame_exists` |
| Lemma 3.11 — official cycles (O1)–(O6) | lem:official | 416–425 | Properties (O1)–(O6) for T^g, official cycles C_i, H_P, and free-edge cycles D_eps. | PROVED | `Flow.Paper.lem_3_11` |
| Section 3 — Definition 3.12 properties | def:lists | 451 | For an H-good flow f, |Lambda_f(t)| <= 3, 0 in P(Lambda_f), and Y in P(Lambda_f) iff u + pi(Y) is non-zero on protected threads. | PROVED | `Flow.Paper.def_3_12_properties` |
| Section 4 — elementary facts (E1)–(E5) | sec:master | 460–466 | Five elementary flow facts (E1)–(E5) on quotients, cycle sums, lifts, and contractions. | PROVED | `Flow.Paper.sec4_E1`, `Flow.Paper.sec4_E2`, `Flow.Paper.sec4_E3`, `Flow.Paper.sec4_E4`, `Flow.Paper.sec4_E5` |
| Lemma 4.1 — sparse zeros yield good subgraph | lem:AVgood | 468–470 | Under (AV), on a loopless 3-edge-connected multigraph with n >= 2, every flow is Sigma-joined to one whose A-support contains a good subgraph. | PROVED | `Flow.Paper.lem_4_1` |
| Lemma 4.2(a) — reverse choice | lem:reverse | 480–483 | If |Lambda(e_i)| + |Lambda(f_i)| < |A| at every node, some official-cycle combination lands in P(Lambda). | PROVED | `Flow.Paper.lem_4_2_a` |
| Lemma 4.2(b) — reverse choice with red edges | lem:reverse | 484–489 | Every red edge lies on an official cycle, and reverse choice avoids Phi on E' under the degree bound. | PROVED | `Flow.Paper.lem_4_2_b` |
| Lemma 4.3 — walk lemma | lem:walk | 498–500 | Under |A| >= 10 and (R1), any two flows in P(Lambda) are connected by official-cycle Sigma_A steps inside P(Lambda). | PROVED | `Flow.Paper.lem_4_3` |
| Lemma 4.4 — preparation in B | lem:prepB | 533–535 | Under |B| >= 4 and (R2), B-moves inside H avoid T_eps on free threads in E^circ while preserving u and outside edges. | PROVED | `Flow.Paper.lem_4_4` |
| Lemma 4.5 — one step inside H | lem:stepH | 543–545 | Under |B| >= 4 and (R2), a valid official-cycle step sigma chi_C in A lifts to Sigma-moves inside H. | PROVED | `Flow.Paper.lem_4_5` |
| Lemma 4.6 — changing A-coordinate inside H | lem:L1 | 555–557 | Under |A| >= 10, |B| >= 4, (R1), (R2), any Y in P(Lambda_f) is realized by Sigma-moves inside H. | PROVED | `Flow.Paper.lem_4_6` |
| Lemma 4.7 — the path | lem:P | 565–567 | Any distinct p, p' in V(H) are joined by a path J in H using at most 3 edges on the threads of each pair N_i. | PROVED | `Flow.Paper.lem_4_7` |
| Lemma 4.8 — lifting a contracted move (CYC) | lem:L2 | 581–583 | A contracted Sigma-move on G/H lifts to Sigma-moves on G preserving H-goodness in case (CYC). | PROVED | `Flow.Paper.lem_4_8_cyc` |
| Lemma 4.8 — lifting a contracted move (SUB) | lem:L2 | 581–583 | A contracted Sigma-move on G/H lifts to Sigma-moves on G preserving H-goodness relative to a fixed frame in case (SUB). | PROVED | `Flow.Paper.lem_4_8_sub` |
| Section 4 — integer consequence | sec:master | 635 | Combining Theorem 1.3 and Corollary 2.8(b) yields connectivity of M_{ab}(G) and I_{ab}(G). | PROVED | `Flow.Paper.sec4_integer_consequence` |
| Lemma 5.1 — averaging in a product | lem:AVG | 642–648 | Product averaging gives a Sigma-joined flow with at most m/9 zeros in its A-coordinate and establishes (AV). | PROVED | `Flow.Paper.lem_5_1` |
| Remark 5.2 — index bound | rem:internal | 687–689 | For a >= 9 and b >= 1, 9 * (b - 1) < a * b - 1. | PROVED | `Flow.Paper.rem_5_2_index_bound` |
| Remark 5.2 — internal direct sums | rem:internal | 687–689 | Internal direct sum with generating sets in Sigma and |A| >= 9 implies (AV). | PROVED | `Flow.Paper.rem_5_2_internal_direct_sum` |
| Section 5 — orders 40 to 50 | sec:averaging | 694 | Among 40 <= n <= 50, a divisor 4 <= d <= n/10 exists iff n in {40, 44, 48, 50}, none of which is a prime power. | PROVED | `Flow.Paper.sec5_orders_40_to_50` |
| Lemma 6.1 — at most two non-steps in Z_a | lem:twononsteps | 703–705 | For a >= 10 and symmetric D of size >= a - 3, deleting <= 6 elements leaves Z_a connected by D-steps. | PROVED | `Flow.Paper.lem_6_1` |
| Lemma 6.2 — Z_b minus two elements | lem:Zb | 711–713 | For b >= 4 and proper divisor 1 < d < b, deleting <= 2 elements leaves Z_b connected by {+-1, +-d}. | PROVED | `Flow.Paper.lem_6_2` |
| Table 2 — base proper divisors of 40, 48, 66 | tab:moduli | 735–740 | Base proper divisors of 40, 48, 66 cover all non-zero residues mod 10, 12, 11 except +-3, +-5, +-4. | PROVED | `Flow.Paper.sec6_table2_moduli` |
| Remark 6.3 — sharpness at 40, k = 44, prime powers | rem:sharpness | 755–757 | 44 = 11 * 4 uniquely, proper divisors of 44 project to {+-1, +-2, +-4} mod 11 failing (R1), and Z_{p^r} has no non-trivial product split. | PROVED | `Flow.Paper.rem_6_3_sharpness` |
| Non-vacuity — loop cycle | Lean-only | Lean-only | A single loop on Unit is a cycle and bridgeless. | PROVED | `Flow.Paper.nonvacuous_loop_cycle` |
| Non-vacuity — truncated cubic and well colouring | Lean-only | Lean-only | K_4 - v is truncated cubic 3-edge-connected and admits a well colouring. | PROVED | `Flow.Paper.nonvacuous_tc3ec_and_well_colouring` |
| Non-vacuity — subdivision, aux graph, frame | Lean-only | Lean-only | The 2-vertex 3-parallel-edge multigraph admits SubdivisionData, AuxGraphData, and Frame. | PROVED | `Flow.Paper.nonvacuous_subdivision_aux_frame` |
