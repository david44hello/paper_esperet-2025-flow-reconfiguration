module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Flow.Defs.Literature
public import Flow.Proofs.Elementary
public import Flow.Proofs.Basic
public import Flow.Proofs.Liftable
public import Flow.Proofs.Extraction
public import Flow.Proofs.Blocks
public import Flow.Proofs.FlowsQ
public import Flow.Proofs.Frames
public import Flow.Proofs.SmallClaims
public import Flow.Proofs.Witnesses
public import Flow.Proofs.Coverage
public import Flow.Proofs.Moduli
public import Flow.Proofs.Averaging
public import Flow.Proofs.MainInt
public import Flow.Proofs.MasterHelpers
public import Flow.Proofs.LiftMove
public import Flow.Proofs.PathAndSub
public import Flow.Proofs.Master
public import Flow.Proofs.JLPTWellColouring
public import Flow.Proofs.SeymourFromJLPT

@[expose] public section
set_option backward.proofsInPublic true

/-!
# Paper statements — single source of truth for all claims in the paper

Every numbered theorem, lemma, corollary, and mathematical remark, together with
named proof steps and running-text mathematical claims, is stated here against
the definitions in `Flow.Defs.*`.
-/

namespace Flow.Paper

open Flow

private lemma hasCycleDecomp_proved : Flow.Proofs.HasCycleDecomp := by
  intro V E A _ _ _ _ _ G h hh
  obtain ⟨T₀, hT₀⟩ := Flow.Proofs.exists_spanningForest G
  exact (Flow.Proofs.lem_2_1_a G T₀ hT₀).2.2 h hh

private lemma jlpt_proved : JLPTWellColouring :=
  Flow.Proofs.jlpt_wellColouring_proved

private lemma seymour_proved : SeymourSixFlow :=
  Flow.Proofs.seymour_of_jlpt jlpt_proved

private lemma sec3Bundle_proved : Flow.Proofs.Sec3Bundle jlpt_proved where
  aux_exists := fun sub => Flow.Proofs.aux_graph_exists sub
  frame_exists := fun sub aux => Flow.Proofs.frame_exists jlpt_proved sub aux
  lem_3_6_a_cyc := fun sub aux O t => (Flow.Proofs.lem_3_6_a (A := ℤ) sub aux).1 O t
  lem_3_6_c_surj := fun sub aux h hh => (Flow.Proofs.lem_3_6_c sub aux).2 h hh
  lem_3_6_d := fun sub aux C => Flow.Proofs.lem_3_6_d sub aux C
  lem_3_11 := fun fr =>
    let h := Flow.Proofs.lem_3_11 fr
    ⟨fun g hg => ⟨(h.1 g hg).2.1, fun i => ⟨((h.1 g hg).2.2 i).2.1, ((h.1 g hg).2.2 i).2.2⟩⟩,
     h.2.1,
     fun C hC =>
       let h' := h.2.2.1 C hC
       ⟨fun i => ⟨(h'.1 i).2.1, (h'.1 i).2.2⟩, h'.2.1, h'.2.2.1, h'.2.2.2⟩,
     h.2.2.2⟩
  def_3_12 := fun B _ _ _ _ _ fr f hgood => Flow.Proofs.def_3_12_properties B fr f hgood

/-! ## Section 1: Main results and literature input -/

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
    G.FlowGraphConnected Γ :=
  Flow.Proofs.thm_1_3_of seymour_proved jlpt_proved sec3Bundle_proved B hA hB Sig hR1 hR2 hR3 hAV G hbr

/-- **Theorem 1.1(a) (Integer and modular flows — modular part).**
For every positive multiple `k` of `40`, `48`, or `66`, `M_k(G)` is connected for
every finite bridgeless multigraph `G` (loops allowed). -/
theorem thm_1_1_a
    {k : ℕ} (hk_pos : 0 < k) (hk_div : 40 ∣ k ∨ 48 ∣ k ∨ 66 ∣ k)
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : Multigraph V E) (hbr : G.IsBridgeless) :
    G.ModularFlowConnected k := by
  have : NeZero k := ⟨Nat.ne_of_gt hk_pos⟩
  exact (Flow.Proofs.thm_1_1_of hasCycleDecomp_proved hk_pos hk_div G hbr
    (fun B _ _ _ _ hA hB Sig hR1 hR2 hR3 hAV =>
      let h := thm_1_3 B hA hB Sig hR1 hR2 hR3 hAV G hbr
      ⟨h.2.1, h.2.2⟩)
    (fun _ hk h1 h2 h3 => Flow.Proofs.cor_2_8_a hk h1 h2 h3)
    (fun Sig hll hk hlift hjoin => Flow.Proofs.cor_2_8_b G hll hk Sig hlift hjoin)).1

/-- **Theorem 1.1(b) (Integer and modular flows — integer part).**
For every positive multiple `k` of `40`, `48`, or `66`, `I_k(G)` is connected for
every finite bridgeless loopless multigraph `G`. -/
theorem thm_1_1_b
    {k : ℕ} (hk_pos : 0 < k) (hk_div : 40 ∣ k ∨ 48 ∣ k ∨ 66 ∣ k)
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : Multigraph V E) (hbr : G.IsBridgeless) (hll : G.IsLoopless) :
    G.IntFlowConnected k := by
  have : NeZero k := ⟨Nat.ne_of_gt hk_pos⟩
  exact (Flow.Proofs.thm_1_1_of hasCycleDecomp_proved hk_pos hk_div G hbr
    (fun B _ _ _ _ hA hB Sig hR1 hR2 hR3 hAV =>
      let h := thm_1_3 B hA hB Sig hR1 hR2 hR3 hAV G hbr
      ⟨h.2.1, h.2.2⟩)
    (fun _ hk h1 h2 h3 => Flow.Proofs.cor_2_8_a hk h1 h2 h3)
    (fun Sig hll' hk hlift hjoin => Flow.Proofs.cor_2_8_b G hll' hk Sig hlift hjoin)).2 hll

/-- **Theorem 1.1 (k = 40 specialization, answering Problem 1.2 for uniform `k ≥ 5`).** -/
theorem thm_1_1_k40 :
    ∃ k : ℕ, 5 ≤ k ∧ k = 40 ∧
      ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
        (G : Multigraph V E), G.IsBridgeless → G.IsLoopless → G.IntFlowConnected k :=
  ⟨40, by decide, rfl, fun _ _ _ _ _ _ G hbr hll =>
    thm_1_1_b (by decide) (Or.inl dvd_rfl) G hbr hll⟩

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
    G.FlowGraphConnected Γ :=
  Flow.Proofs.thm_1_2_of hasCycleDecomp_proved hnotcp hdiv G hbr
    (fun B _ _ _ _ hA hB Sig hR1 hR2 hR3 hAV =>
      (thm_1_3 B hA hB Sig hR1 hR2 hR3 hAV G hbr).2.2)

/-- **Theorem 1.2 (orders 40, 44, 48, 50 specialization).**
In particular, `F(G, Γ)` is connected for every abelian group `Γ` of order
`40`, `44`, `48`, or `50`. -/
theorem thm_1_2_orders_40_44_48_50
    {Γ : Type} [AddCommGroup Γ] [Fintype Γ] [DecidableEq Γ]
    (hord : Fintype.card Γ = 40 ∨ Fintype.card Γ = 44 ∨ Fintype.card Γ = 48 ∨ Fintype.card Γ = 50)
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : Multigraph V E) (hbr : G.IsBridgeless) :
    G.FlowGraphConnected Γ := by
  have h50 := Flow.Proofs.sec5_orders_40_to_50_proved (Fintype.card Γ)
    (by rcases hord with h | h | h | h <;> omega)
    (by rcases hord with h | h | h | h <;> omega)
  have hnotcp : ¬ IsCyclicPrimePower Γ := by
    rintro ⟨p, r, hp, hr, ⟨e⟩⟩
    haveI : NeZero (p ^ r) := ⟨pow_ne_zero r hp.ne_zero⟩
    have hcard : Fintype.card Γ = p ^ r := by
      rw [Fintype.card_congr e.toEquiv, ZMod.card]
    exact h50.2 hord ⟨p, r, hp, hr, hcard⟩
  exact thm_1_2 hnotcp (h50.1.mpr hord) G hbr

/-- **Theorem 1.4 (Seymour 1981; Tutte 1954).**
Proved unconditionally from Lean's standard axioms via Tutte's flow polynomial invariance
and the JLPT well-colouring lemma. -/
theorem thm_1_4 : SeymourSixFlow :=
  seymour_proved

/-- **Section 1 in-text coverage (trivial cases `|Γ| ≤ 2` and `k = 2`).** -/
theorem sec1_trivial_small_group
    {Γ : Type} [AddCommGroup Γ] [Fintype Γ]
    (hcard : Fintype.card Γ ≤ 2)
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : Multigraph V E) :
    G.FlowGraphConnected Γ :=
  Flow.Proofs.sec1_trivial_small_group_proved hcard G

theorem sec1_trivial_int_k2
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : Multigraph V E) :
    G.IntFlowConnected 2 :=
  Flow.Proofs.sec1_trivial_int_k2_proved G

/-- **Section 1 in-text coverage:** `ℤ_3` fails on three parallel edges between two vertices. -/
theorem sec1_Z3_three_parallel_disconnected :
    let G : Multigraph (Fin 2) (Fin 3) := ⟨fun _ => 0, fun _ => 1⟩
    G.IsBridgeless ∧ G.IsLoopless ∧ ¬ G.FlowGraphConnected (ZMod 3) :=
  Flow.Proofs.sec1_Z3_three_parallel_disconnected_proved

/-- **Figure 1 caption coverage:** the set of orders `n` covered by Theorem 1.2
(not a prime power and admitting a divisor `4 ≤ d ≤ n / 10`) has natural density `1`. -/
theorem fig1_density_one :
    let covered : ℕ → Prop := fun n =>
      (¬ ∃ p r, Nat.Prime p ∧ 1 ≤ r ∧ n = p ^ r) ∧
      (∃ d : ℕ, d ∣ n ∧ 4 ≤ d ∧ 10 * d ≤ n)
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 N ∧ (∀ n ∈ S, covered n) ∧
        (1 - ε) * (N : ℝ) ≤ (S.card : ℝ) :=
  Flow.Proofs.fig1_density_one_proved

/-! ## Section 2: Conventions and liftable divisor steps -/

/-- **Section 2 in-text coverage:** `λ • χ_C` is a `Γ`-flow for every directed cycle `C`
and `λ ∈ Γ`, edge reorientation preserves flows and adjacency, and a move is equivalent to
the support of `g - f` being a cycle. -/
theorem sec2_cycle_smul_isFlow
    {V E Γ : Type} [Fintype E] [DecidableEq V] [AddCommGroup Γ]
    (G : Multigraph V E) (C : G.DirectedCycle) (lam : Γ) :
    G.IsFlow (fun e => C.sign e • lam) :=
  Flow.Proofs.sec2_cycle_smul_isFlow_proved G C lam

theorem sec2_reorient_preserves_flow
    {V E Γ : Type} [Fintype E] [DecidableEq V] [AddCommGroup Γ]
    (G : Multigraph V E) (flip : E → Bool) (x : E → Γ) :
    (G.reorient flip).IsFlow (Multigraph.reorientVal flip x) ↔ G.IsFlow x :=
  Flow.Proofs.sec2_reorient_preserves_flow_proved G flip x

theorem sec2_reorient_preserves_flowMove
    {V E Γ : Type} [Fintype E] [DecidableEq V] [AddCommGroup Γ]
    (G : Multigraph V E) (flip : E → Bool) (f g : G.NZFlow Γ)
    (f' g' : (G.reorient flip).NZFlow Γ)
    (hf' : ∀ e, f'.val e = Multigraph.reorientVal flip f.val e)
    (hg' : ∀ e, g'.val e = Multigraph.reorientVal flip g.val e) :
    (G.reorient flip).FlowMove f' g' ↔ G.FlowMove f g := by
  classical
  exact Flow.Proofs.sec2_reorient_preserves_flowMove_proved G flip f g f' g' hf' hg'

theorem sec2_move_iff_supp_cycle
    {V E Γ : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    [AddCommGroup Γ] [DecidableEq Γ]
    (G : Multigraph V E) (f g : G.NZFlow Γ) :
    G.FlowMove f g ↔
      ∃ C : G.Subgraph, C.IsCycle ∧ C.edges = Multigraph.supp (fun e => g.val e - f.val e) :=
  Flow.Proofs.sec2_move_iff_supp_cycle_proved G f g

/-- **Lemma 2.1(a) (Cycle decomposition — fundamental cycles).**
For any abelian group `A` (finite or infinite) and spanning forest `T₀` of `G`,
each `e ∉ E(T₀)` has a unique fundamental cycle `C_e` directed forward along `e`,
every `A`-flow `h` has the unique representation `h = ∑_{e ∉ E(T₀)} h(e) • χ_{C_e}`,
and in particular every `A`-flow is a sum of cycle flows. -/
theorem lem_2_1_a
    {V E A : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    [AddCommGroup A]
    (G : Multigraph V E) (T₀ : G.Subgraph) (hT : T₀.IsSpanningForest) :
    (∀ e : E, e ∉ T₀.edges → ∃! C : G.DirectedCycle, G.IsFundamentalCycle T₀ e C) ∧
    (∀ (fund : ∀ e : E, e ∉ T₀.edges → G.DirectedCycle),
      (∀ e (he : e ∉ T₀.edges), G.IsFundamentalCycle T₀ e (fund e he)) →
      ∀ (h : E → A), G.IsFlow h →
        (∀ e', h e' = ∑ e ∈ (Finset.univ \ T₀.edges).attach,
          (fund e.1 (Finset.mem_sdiff.mp e.2).2).sign e' • h e.1) ∧
        (∀ (c : E → A),
          (∀ e', h e' = ∑ e ∈ (Finset.univ \ T₀.edges).attach,
            (fund e.1 (Finset.mem_sdiff.mp e.2).2).sign e' • c e.1) →
          ∀ e, e ∉ T₀.edges → c e = h e)) ∧
    (∀ (h : E → A), G.IsFlow h →
      ∃ (l : List (A × G.DirectedCycle)),
        ∀ e, h e = (l.map (fun p => p.2.sign e • p.1)).sum) :=
  Flow.Proofs.lem_2_1_a G T₀ hT

/-- **Lemma 2.1(b) (Signed cycle decomposition).**
Every integer flow `h` of `G` is a sum `h = χ_{O₁} + ... + χ_{O_j}` of directed cycles
such that `χ_{O_i}(e) * h(e) > 0` for every `i` and every `e ∈ E(O_i)`. Consequently,
every edge `e` lies on `|h(e)|` of the cycles, all cycles lie in `supp(h)`, and if
`h(e) ∈ {-1, 0, 1}` for all `e` then the cycles are pairwise edge-disjoint. -/
theorem lem_2_1_b
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : Multigraph V E) (h : E → ℤ) (hh : G.IsFlow h) :
    ∃ (cycles : List G.DirectedCycle),
      (∀ e, h e = (cycles.map (fun C => C.sign e)).sum) ∧
      (∀ C ∈ cycles, ∀ e ∈ C.sub.edges, 0 < C.sign e * h e) ∧
      (∀ e, ((cycles.filter (fun C => e ∈ C.sub.edges)).length : ℤ) = |h e|) ∧
      (∀ C ∈ cycles, ∀ e ∈ C.sub.edges, h e ≠ 0) ∧
      ((∀ e, h e = -1 ∨ h e = 0 ∨ h e = 1) →
        ∀ i j (hi : i < cycles.length) (hj : j < cycles.length), i ≠ j →
          Disjoint (cycles[i]'hi).sub.edges (cycles[j]'hj).sub.edges) :=
  Flow.Proofs.lem_2_1_b G h hh

/-- **Lemma 2.2 (Rounding).**
Let `x : E(G) → [0, 1]` have integer boundary at every vertex. Then there exists
`z : E(G) → {0, 1}` with `∂ z = ∂ x` and `z(e) = x(e)` whenever `x(e) ∈ {0, 1}`. -/
theorem lem_2_2
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : Multigraph V E) (x : E → ℝ)
    (hx_range : ∀ e, 0 ≤ x e ∧ x e ≤ 1)
    (hx_int : ∀ v, ∃ n : ℤ, G.boundary x v = (n : ℝ)) :
    ∃ z : E → ℤ,
      (∀ e, z e = 0 ∨ z e = 1) ∧
      (∀ v, (G.boundary (Γ := ℤ) z v : ℝ) = G.boundary x v) ∧
      (∀ e, x e = 0 → z e = 0) ∧
      (∀ e, x e = 1 → z e = 1) :=
  Flow.Proofs.lem_2_2 G x hx_range hx_int

/-- **Corollary 2.3 (Integer lifts).**
Let `k ≥ 2` and let `f` be a `ℤ_k`-flow of `G` (zeros allowed). Then there exists an
integer flow `F` of `G` with `F ≡ f (mod k)`, `|F(e)| ≤ k - 1`, and `F(e) = 0 ↔ f(e) = 0`.
In particular, every nowhere-zero `ℤ_k`-flow has an integer lift. -/
theorem cor_2_3
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : Multigraph V E) {k : ℕ} (hk : 2 ≤ k)
    (f : E → ZMod k) (hf : G.IsFlow f) :
    ∃ F : E → ℤ,
      G.IsFlow F ∧
      (∀ e, (F e : ZMod k) = f e) ∧
      (∀ e, |F e| ≤ (k : ℤ) - 1) ∧
      (∀ e, F e = 0 ↔ f e = 0) :=
  Flow.Proofs.cor_2_3 G hk f hf

/-- **Lemma 2.4 (Connected fibres).**
Let `k ≥ 2` and let `f` be a nowhere-zero `ℤ_k`-flow of `G`. Then any two integer lifts
of `f` are joined by a path in `I_k(G)` through integer lifts of `f`. -/
theorem lem_2_4
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : Multigraph V E) {k : ℕ} (hk : 2 ≤ k)
    (f : G.NZFlow (ZMod k)) (F F' : G.IntKFlow k)
    (hF : G.IsIntLift f F) (hF' : G.IsIntLift f F') :
    Relation.ReflTransGen
      (fun A B => G.IsIntLift f A ∧ G.IsIntLift f B ∧ G.IntKFlowMove A B) F F' :=
  Flow.Proofs.lem_2_4 G hk f F F' hF hF'

/-- **Lemma 2.6 (Step of size 1).**
Let `k ≥ 2`, `C` a directed cycle of `G`, and `f, f + χ_C` nowhere-zero `ℤ_k`-flows.
Then for every integer lift `F` of `f`, `F + χ_C` is an integer lift of `f + χ_C`. -/
theorem lem_2_6
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : Multigraph V E) {k : ℕ} (hk : 2 ≤ k)
    (C : G.DirectedCycle) (f f' : G.NZFlow (ZMod k))
    (hstep : ∀ e, f'.val e = f.val e + (C.sign e : ZMod k))
    (F : G.IntKFlow k) (hF : G.IsIntLift f F) :
    ∃ F' : G.IntKFlow k,
      (∀ e, F'.val e = F.val e + C.sign e) ∧ G.IsIntLift f' F' :=
  Flow.Proofs.lem_2_6 G hk C f f' hstep F hF

/-- **Lemma 2.7 (Divisor move).**
Let `k ≥ 3` and `q` a proper divisor of `k` (`1 ≤ q < k`). Let `C` be a directed cycle
and `f, f + q χ_C` nowhere-zero `ℤ_k`-flows. Then there is a path in `I_k(G)` from an
integer lift of `f` to an integer lift of `f + q χ_C`. -/
theorem lem_2_7
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : Multigraph V E) {k q : ℕ} (hk : 3 ≤ k)
    (hq_pos : 1 ≤ q) (hq_lt : q < k) (hq_div : q ∣ k)
    (C : G.DirectedCycle) (f f' : G.NZFlow (ZMod k))
    (hstep : ∀ e, f'.val e = f.val e + C.sign e • (q : ZMod k)) :
    ∃ (F F' : G.IntKFlow k),
      G.IsIntLift f F ∧ G.IsIntLift f' F' ∧ Relation.ReflTransGen G.IntKFlowMove F F' :=
  Flow.Proofs.lem_2_7 G hk hq_pos hq_lt hq_div C f f' hstep

/-- **Corollary 2.8(a) (Liftable divisor steps).**
For `k ≥ 3` and every proper divisor `q` of `k` (`1 ≤ q < k`), both `q` and `-q` are
liftable in `ℤ_k`. -/
theorem cor_2_8_a
    {k q : ℕ} (hk : 3 ≤ k) (hq_pos : 1 ≤ q) (hq_lt : q < k) (hq_div : q ∣ k) :
    Multigraph.IsLiftable k (q : ZMod k) ∧ Multigraph.IsLiftable k (-(q : ZMod k)) :=
  Flow.Proofs.cor_2_8_a hk hq_pos hq_lt hq_div

/-- **Corollary 2.8(b) (Liftable step systems connect `I_k(G)`).**
If `Σ ⊆ ℤ_k \ {0}` is a step system of liftable elements and any two nowhere-zero
`ℤ_k`-flows of a finite loopless multigraph `G` are `Σ`-joined, then `I_k(G)` is connected. -/
theorem cor_2_8_b
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : Multigraph V E) (hll : G.IsLoopless)
    {k : ℕ} (hk : 3 ≤ k) (Sig : StepSystem (ZMod k))
    (hlift : ∀ z ∈ Sig.carrier, Multigraph.IsLiftable k z)
    (hjoin : ∀ f g : G.NZFlow (ZMod k), G.SigmaJoined Sig.carrier f g) :
    G.IntFlowConnected k :=
  Flow.Proofs.cor_2_8_b G hll hk Sig hlift hjoin

/-! ## Section 3: Good subgraphs, truncated cubic frames, and official cycles -/

/-- **Lemma 3.2 (Extraction).**
Every loopless multigraph `G` with `n ≥ 3` vertices and `m > (4/3) n - 2` edges
(equivalently `3 * m + 6 > 4 * n`) contains a good subgraph. -/
theorem lem_3_2
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : Multigraph V E) (hll : G.IsLoopless)
    (hn : 3 ≤ Fintype.card V) (hm : 4 * Fintype.card V < 3 * Fintype.card E + 6) :
    ∃ H : G.Subgraph, IsGoodSubgraph G H :=
  Flow.Proofs.lem_3_2 G hll hn hm

/-- **Lemma 3.4(a) (Blocks of a loopless 3-edge-connected multigraph).**
Every block `K` of a loopless `3`-edge-connected multigraph `H₀` on at least `2` vertices
is loopless, `3`-edge-connected, has at least `2` vertices, and has no cut vertex. -/
theorem lem_3_4_a
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (H₀ : Multigraph V E) (hll : H₀.IsLoopless) (h3 : H₀.IsEdgeConnected 3)
    (hn : 2 ≤ Fintype.card V) (K : H₀.Subgraph) (hK : H₀.IsBlock K) :
    K.toMultigraph.IsLoopless ∧
    K.toMultigraph.IsEdgeConnected 3 ∧
    2 ≤ K.verts.card ∧
    K.HasNoCutVertex :=
  Flow.Proofs.lem_3_4_a H₀ hll h3 hn K hK

/-- **Lemma 3.4(b) (Truncated cubic expansion of a block).**
Every loopless `3`-edge-connected multigraph `K` on at least `2` vertices without a cut
vertex admits a truncated cubic `3`-edge-connected expansion `Q_K` whose extra edges
form pairwise disjoint cycles contracting back to `K`. -/
theorem lem_3_4_b
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (K : Multigraph V E) (hll : K.IsLoopless) (h3 : K.IsEdgeConnected 3)
    (hn : 2 ≤ Fintype.card V) (hnc : (Multigraph.Subgraph.top K).HasNoCutVertex) :
    Nonempty (TruncatedCubicExpansion K) :=
  Flow.Proofs.lem_3_4_b K hll h3 hn hnc

/-- **Definition 3.5 / Lemma 3.4 existence:**
For every `(SUB)` subdivision `H` of `G`, there is a reorientation `flip` (supported on
`H.edges`) after which `H` admits an auxiliary graph `AuxGraphData`. -/
theorem aux_graph_exists
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : Multigraph V E} {H : G.Subgraph} (sub : SubdivisionData G H) :
    ∃ (flip : E → Bool), (∀ e, e ∉ H.edges → flip e = false) ∧
      ∃ (H' : (G.reorient flip).Subgraph) (sub' : SubdivisionData (G.reorient flip) H'),
        H'.verts = H.verts ∧ H'.edges = H.edges ∧
        Nonempty (AuxGraphData (G.reorient flip) H' sub') :=
  Flow.Proofs.aux_graph_exists sub

/-- **Lemma 3.6 (Flows of `H`, `H₀`, and `Q`).**
Covers all four parts (a)–(d) for any abelian group `A` (finite or infinite). -/
theorem lem_3_6_a
    {V E A : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    [AddCommGroup A]
    {G : Multigraph V E} {H : G.Subgraph} (sub : SubdivisionData G H)
    (aux : AuxGraphData G H sub) :
    (∀ (O : H.toMultigraph.DirectedCycle) (t : sub.E₀),
      ∃ s : ℤ, (s = 1 ∨ s = 0 ∨ s = -1) ∧
        ∀ e (he : e ∈ (sub.thread t).edges), O.sign ⟨e, (sub.thread t).edges_sub e he⟩ = s) ∧
    (∀ (h : {e // e ∈ H.edges} → A), H.toMultigraph.IsFlow h →
      ∀ t : sub.E₀, ∀ e₁ e₂ (h₁ : e₁ ∈ (sub.thread t).edges) (h₂ : e₂ ∈ (sub.thread t).edges),
        h ⟨e₁, (sub.thread t).edges_sub e₁ h₁⟩ = h ⟨e₂, (sub.thread t).edges_sub e₂ h₂⟩) ∧
    (∃ e : {h : {e // e ∈ H.edges} → A // H.toMultigraph.IsFlow h} ≃
           {h₀ : sub.E₀ → A // sub.H₀.IsFlow h₀},
      ∀ (h : {h : {e // e ∈ H.edges} → A // H.toMultigraph.IsFlow h}) (t : sub.E₀)
        (edge : E) (hedge : edge ∈ (sub.thread t).edges),
        h.1 ⟨edge, (sub.thread t).edges_sub edge hedge⟩ = (e h).1 t) :=
  Flow.Proofs.lem_3_6_a sub aux

theorem lem_3_6_b
    {V E A : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    [AddCommGroup A]
    {G : Multigraph V E} {H : G.Subgraph} (sub : SubdivisionData G H)
    (aux : AuxGraphData G H sub)
    (h₀ : sub.E₀ → A) (hh₀ : sub.H₀.IsFlow h₀) (b : Fin aux.numBlocks) :
    (aux.block_subgraph b).toMultigraph.IsFlow (fun e => h₀ e.1) :=
  Flow.Proofs.lem_3_6_b sub aux h₀ hh₀ b

theorem lem_3_6_c
    {V E A : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    [AddCommGroup A]
    {G : Multigraph V E} {H : G.Subgraph} (sub : SubdivisionData G H)
    (aux : AuxGraphData G H sub) :
    (∀ Y : aux.EQ → A, aux.Q.IsFlow Y →
      sub.H₀.IsFlow (fun t => Y (aux.origEdge t)) ∧
      H.toMultigraph.IsFlow (fun e => aux.pi Y e.1)) ∧
    (∀ h : {e // e ∈ H.edges} → A, H.toMultigraph.IsFlow h →
      ∃ Y : aux.EQ → A, aux.Q.IsFlow Y ∧ ∀ e : {e // e ∈ H.edges}, aux.pi Y e.1 = h e) :=
  Flow.Proofs.lem_3_6_c sub aux

theorem lem_3_6_d
    {V E A : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    [AddCommGroup A]
    {G : Multigraph V E} {H : G.Subgraph} (sub : SubdivisionData G H)
    (aux : AuxGraphData G H sub)
    (C : aux.Q.DirectedCycle) :
    ∃ (cycles : List G.DirectedCycle),
      (∀ O ∈ cycles, O.sub ≤ H) ∧
      (∀ i j (hi : i < cycles.length) (hj : j < cycles.length), i ≠ j →
        Disjoint (cycles[i]'hi).sub.edges (cycles[j]'hj).sub.edges) ∧
      (∀ (x : A) (e : E),
        aux.pi (fun eq => C.sign eq • x) e =
          (cycles.map (fun O => O.sign e • x)).sum) :=
  Flow.Proofs.lem_3_6_d sub aux C

/-- **Theorem 3.8 (Jaeger, Linial, Payan, and Tarsi 1992).**
Proved unconditionally from Lean's standard axioms via sticking and growing on `TC_3`. -/
theorem thm_3_8 : JLPTWellColouring :=
  jlpt_proved

/-- **Lemma 3.9(a) (Counts and red forest).**
`Q` is simple and connected with `2 * |E| = 3 * (n - 1)`, red edges form a forest, and no
blue edge has both ends in one red component. -/
theorem lem_3_9
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (Q : Multigraph V E) (hTC : Q.IsTruncatedCubic3EC)
    (wc : WellColouring Q) :
    Q.IsSimple ∧
    Q.Connected ∧
    2 * Fintype.card E = 3 * (Fintype.card V - 1) ∧
    (Multigraph.Subgraph.ofEdges Q Finset.univ (Finset.univ \ wc.blue)
      (fun _ => Finset.mem_univ _) (fun _ => Finset.mem_univ _)).IsForest ∧
    (∀ e ∈ wc.blue,
      Quotient.mk (redSetoid Q wc.blue) (Q.tail e) ≠
      Quotient.mk (redSetoid Q wc.blue) (Q.head e)) :=
  Flow.Proofs.lem_3_9 Q hTC wc

/-- **Lemma 3.9(b)–(d) (Stages and stage graphs of a `2`-construction).**
(b) Any two stages of `Q / red` are disjoint or nested; every blue edge belongs to a
    unique node; each stage `U` is an induced subgraph of `Q / red` whose edges are the
    edges of the nodes contained in `U`.
(c) Each stage graph `Q_U = Q[V_U]` is connected, and `E(Q_U)` consists of the red edges
    inside `V_U` together with the edges of all nodes contained in `U`.
(d) For every node joining operands `U', U''` by `{e, f}`, `V_U = V_{U'} ⊔ V_{U''}`, each
    of `e, f` crosses between `V_{U'}` and `V_{U''}`, and
    `E(Q_U) = E(Q_{U'}) ∪ E(Q_{U''}) ∪ {e, f}`. -/
theorem lem_3_9_bcd
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (Q : Multigraph V E) (hTC : Q.IsTruncatedCubic3EC)
    (wc : WellColouring Q) :
    let M := redQuotient Q wc.blue
    let stg := wc.twoConstr.stages
    let nds := wc.twoConstr.nodes
    -- (b1) Any two stages are disjoint or nested
    (∀ s₁ ∈ stg, ∀ s₂ ∈ stg, Disjoint s₁.1 s₂.1 ∨ s₁.1 ⊆ s₂.1 ∨ s₂.1 ⊆ s₁.1) ∧
    -- (b2) Every blue edge belongs to a unique node
    (∀ e : {e : E // e ∈ wc.blue},
      ∃! idx : Fin nds.length,
        let nd := nds[idx.1]'idx.2
        e = nd.2.2.1 ∨ e = nd.2.2.2) ∧
    -- (b3) Each stage (W_U, F_U) is induced in Q / red and F_U = edges of nodes inside W_U
    (∀ s ∈ stg, ∀ e : {e : E // e ∈ wc.blue},
      (M.tail e ∈ s.1 ∧ M.head e ∈ s.1) ↔ e ∈ s.2) ∧
    (∀ s ∈ stg, ∀ e : {e : E // e ∈ wc.blue},
      e ∈ s.2 ↔ ∃ nd ∈ nds, (nd.1 ∪ nd.2.1) ⊆ s.1 ∧ (e = nd.2.2.1 ∨ e = nd.2.2.2)) ∧
    -- (c) Q_U = Q[V_U] is connected and its edges are red edges inside V_U plus blue edges in F_U
    (∀ s ∈ stg,
      let VU := stageVerts Q wc.blue s.1
      let QU := Multigraph.Subgraph.induced Q VU
      QU.Connected ∧
      ∀ e : E, e ∈ QU.edges ↔
        ((e ∉ wc.blue ∧ Q.tail e ∈ VU ∧ Q.head e ∈ VU) ∨
         ∃ he : e ∈ wc.blue, (⟨e, he⟩ : {e : E // e ∈ wc.blue}) ∈ s.2)) ∧
    -- (d) Operand partition, crossing edges, and edge union at every node
    (∀ nd ∈ nds,
      let VU' := stageVerts Q wc.blue nd.1
      let VU'' := stageVerts Q wc.blue nd.2.1
      let VU := stageVerts Q wc.blue (nd.1 ∪ nd.2.1)
      VU = VU' ∪ VU'' ∧ Disjoint VU' VU'' ∧
      ((Q.tail nd.2.2.1.1 ∈ VU' ∧ Q.head nd.2.2.1.1 ∈ VU'') ∨
       (Q.tail nd.2.2.1.1 ∈ VU'' ∧ Q.head nd.2.2.1.1 ∈ VU')) ∧
      ((Q.tail nd.2.2.2.1 ∈ VU' ∧ Q.head nd.2.2.2.1 ∈ VU'') ∨
       (Q.tail nd.2.2.2.1 ∈ VU'' ∧ Q.head nd.2.2.2.1 ∈ VU')) ∧
      (Multigraph.Subgraph.induced Q VU).edges =
        (Multigraph.Subgraph.induced Q VU').edges ∪
        (Multigraph.Subgraph.induced Q VU'').edges ∪ {nd.2.2.1.1, nd.2.2.2.1}) :=
  Flow.Proofs.lem_3_9_bcd Q hTC wc

/-- **Frame existence (Section 3, following Lemma 3.9):**
Every `(SUB)` subdivision `H` admits an auxiliary graph `Q` and a frame `Frame G H sub aux`. -/
theorem frame_exists
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : Multigraph V E} {H : G.Subgraph} (sub : SubdivisionData G H)
    (aux : AuxGraphData G H sub) :
    Nonempty (Frame G H sub aux) :=
  Flow.Proofs.frame_exists jlpt_proved sub aux

/-- **Lemma 3.11 (Official cycles and free-edge cycles, (O1)–(O6)).** -/
theorem lem_3_11
    {V E A : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    [AddCommGroup A]
    {G : Multigraph V E} {H : G.Subgraph} {sub : SubdivisionData G H}
    {aux : AuxGraphData G H sub} (fr : Frame G H sub aux) :
    -- (O1) For every choice g_i ∈ {e_i, f_i}, T^g is a spanning forest of Q and a spanning tree
    -- of every component Q_b, every stage Q_{U_i}, and every operand Q_{U'_i}, Q_{U''_i}.
    (∀ g : Fin fr.numNodes → aux.EQ, (∀ i, g i = fr.eNode i ∨ g i = fr.fNode i) →
      (fr.Tg g).IsSpanningForest ∧
      (∀ b : Fin aux.numBlocks,
        let Vb := Finset.univ.filter (fun v => aux.comp v = b)
        (Multigraph.Subgraph.ofEdges aux.Q Vb
          ((fr.Tg g).edges.filter (fun e => aux.Q.tail e ∈ Vb ∧ aux.Q.head e ∈ Vb))
          (fun he => (Finset.mem_filter.mp he).2.1)
          (fun he => (Finset.mem_filter.mp he).2.2)).Connected) ∧
      (∀ i : Fin fr.numNodes,
        (Multigraph.Subgraph.ofEdges aux.Q (fr.stageV i)
          ((fr.Tg g).edges.filter (fun e => aux.Q.tail e ∈ fr.stageV i ∧ aux.Q.head e ∈ fr.stageV i))
          (fun he => (Finset.mem_filter.mp he).2.1)
          (fun he => (Finset.mem_filter.mp he).2.2)).Connected ∧
        (Multigraph.Subgraph.ofEdges aux.Q (fr.op1V i)
          ((fr.Tg g).edges.filter (fun e => aux.Q.tail e ∈ fr.op1V i ∧ aux.Q.head e ∈ fr.op1V i))
          (fun he => (Finset.mem_filter.mp he).2.1)
          (fun he => (Finset.mem_filter.mp he).2.2)).Connected ∧
        (Multigraph.Subgraph.ofEdges aux.Q (fr.op2V i)
          ((fr.Tg g).edges.filter (fun e => aux.Q.tail e ∈ fr.op2V i ∧ aux.Q.head e ∈ fr.op2V i))
          (fun he => (Finset.mem_filter.mp he).2.1)
          (fun he => (Finset.mem_filter.mp he).2.2)).Connected)) ∧
    -- Existence/uniqueness + (O2), (O3), (O4), (O5) for official cycles C_i
    (∀ i : Fin fr.numNodes, ∃! C : aux.Q.DirectedCycle, fr.IsOfficialCycle i C) ∧
    (∀ (C : Fin fr.numNodes → aux.Q.DirectedCycle),
      (∀ i, fr.IsOfficialCycle i (C i)) →
      -- (O2) C_i lies in Q_{U_i} and contains both e_i and f_i
      (∀ i, (C i).sub.verts ⊆ fr.stageV i ∧
            fr.eNode i ∈ (C i).sub.edges ∧ fr.fNode i ∈ (C i).sub.edges) ∧
      -- (O3) l < i → C_l contains neither e_i nor f_i
      (∀ l i : Fin fr.numNodes, l < i →
            fr.eNode i ∉ (C l).sub.edges ∧ fr.fNode i ∉ (C l).sub.edges) ∧
      -- (O4) l > i → C_l does not contain f_i
      (∀ l i : Fin fr.numNodes, i < l → fr.fNode i ∉ (C l).sub.edges) ∧
      -- (O5) unique linear combination for every A-flow Y of Q
      (∀ Y : aux.EQ → A, aux.Q.IsFlow Y →
        ∃! x : Fin fr.numNodes → A,
          ∀ eq, Y eq = ∑ i : Fin fr.numNodes, (C i).sign eq • x i)) ∧
    -- (O6) H_P is connected, covers V(H) outside free interiors, and every free edge lies on D_ε
    (fr.HProtected.Connected ∧
      (∀ v ∈ H.verts, (∀ t : sub.E₀, fr.IsFree t →
        ¬ (v ∈ (sub.thread t).verts ∧ v ≠ sub.embedV (sub.H₀.tail t) ∧ v ≠ sub.embedV (sub.H₀.head t))) →
        v ∈ fr.HProtected.verts) ∧
      (∀ eps : sub.E₀, fr.IsFree eps →
        ∃ D : G.DirectedCycle,
          D.sub ≤ H ∧
          (∀ e ∈ (sub.thread eps).edges, e ∈ D.sub.edges ∧ D.sign e = 1) ∧
          (∀ t : sub.E₀, fr.IsFree t → t ≠ eps →
            ∀ e ∈ (sub.thread t).edges, e ∉ D.sub.edges))) :=
  Flow.Proofs.lem_3_11 fr

/-- **Section 3 in-text remark after Definition 3.12:**
For an `H`-good flow `f`, `|Λ_f(t)| ≤ 3`, `0 ∈ P(Λ_f)`, and `Y ∈ P(Λ_f)` holds iff
`u + π(Y)` is non-zero on every edge of every protected thread. -/
theorem def_3_12_properties
    {V E Γ : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    [AddCommGroup Γ] (B : AddSubgroup Γ) [DecidableEq (Γ ⧸ B)]
    {G : Multigraph V E} {H : G.Subgraph} {sub : SubdivisionData G H}
    {aux : AuxGraphData G H sub} (fr : Frame G H sub aux)
    (f : G.NZFlow Γ) (hgood : IsHGoodSub fr B f) :
    (∀ t : aux.EQ, ((LamOfFlow B fr f).list t).card ≤ 3) ∧
    (0 : aux.EQ → Γ ⧸ B) ∈ PLam (LamOfFlow B fr f) ∧
    (∀ Y : aux.EQ → Γ ⧸ B, aux.Q.IsFlow Y →
      (Y ∈ PLam (LamOfFlow B fr f) ↔
        ∀ t : sub.E₀, fr.IsProtected t → ∀ e ∈ (sub.thread t).edges,
          quoFlow B f.val e + aux.pi Y e ≠ 0)) :=
  Flow.Proofs.def_3_12_properties B fr f hgood

/-! ## Section 4: Master theorem lemmas -/

/-- **Section 4 elementary facts `(E1)`–`(E5)`.** -/
theorem sec4_E1
    {V E Γ : Type} [Fintype E] [DecidableEq V] [AddCommGroup Γ]
    (B : AddSubgroup Γ) (f : E → Γ) (e : E) :
    f e ≠ 0 ↔ (quoFlow B f e ≠ 0 ∨ (quoFlow B f e = 0 ∧ f e ∈ B ∧ f e ≠ 0)) :=
  Flow.Proofs.sec4_E1_proved (V := V) B f e

theorem sec4_E2
    {V E Γ : Type} [Fintype E] [DecidableEq V] [AddCommGroup Γ]
    (G : Multigraph V E) (B : AddSubgroup Γ) (f : E → Γ) (C : G.DirectedCycle)
    (y : Γ) (hy : y ∈ B) (e : E) :
    quoFlow B (fun e' => f e' + C.sign e' • y) e = quoFlow B f e :=
  Flow.Proofs.sec4_E2_proved G B f C y hy e

theorem sec4_E3
    {V E Γ : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] [AddCommGroup Γ]
    (G : Multigraph V E) (h : E → Γ) (hh : G.IsFlow h) :
    ∃ (l : List (Γ × G.DirectedCycle)),
      ∀ e, h e = (l.map (fun p => p.2.sign e • p.1)).sum :=
  hasCycleDecomp_proved V E Γ G h hh

theorem sec4_E4
    {V E Γ : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] [AddCommGroup Γ]
    (G : Multigraph V E) (B : AddSubgroup Γ) (v : E → Γ ⧸ B) (hv : G.IsFlow v) :
    ∃ f : E → Γ, G.IsFlow f ∧ ∀ e, quoFlow B f e = v e :=
  Flow.Proofs.sec4_E4_of_E3 G B v hv (hasCycleDecomp_proved V E (Γ ⧸ B) G v hv)

theorem sec4_E5
    {V E W Γ : Type} [Fintype E] [DecidableEq V] [DecidableEq W] [AddCommGroup Γ]
    (G : Multigraph V E) (q : V → W) (f : E → Γ) (hf : G.IsFlow f) :
    (G.contractBy q).IsFlow (fun e => f e.1) :=
  Flow.Proofs.sec4_E5_proved G q f hf

/-- **(E5) (subset deletion form, matching the printed sentence):**
Identifying vertex classes of `G` via `q : V → W` and deleting any set `S` of edges
with both ends in one class (retaining every edge outside `S`, including retained
intra-class edges as loops) sends every `Γ`-flow of `G`, by restriction, to a `Γ`-flow
of the contracted multigraph. -/
theorem sec4_E5_subset
    {V E W Γ : Type} [Fintype E] [DecidableEq V] [DecidableEq W] [DecidableEq E] [AddCommGroup Γ]
    (G : Multigraph V E) (q : V → W) (S : Finset E)
    (hS : ∀ e ∈ S, q (G.tail e) = q (G.head e))
    (f : E → Γ) (hf : G.IsFlow f) :
    Multigraph.IsFlow
      ({ tail := fun e => q (G.tail e.1), head := fun e => q (G.head e.1) } :
        Multigraph W {e : E // e ∉ S})
      (fun e => f e.1) :=
  Flow.Proofs.sec4_E5_subset_proved G q S hS f hf

/-- **Lemma 4.1 (Sparse zeros yield a good subgraph).** -/
theorem lem_4_1
    {Γ : Type} [AddCommGroup Γ] [Fintype Γ] [DecidableEq Γ]
    (B : AddSubgroup Γ) [DecidableEq (Γ ⧸ B)]
    (Sig : StepSystem Γ) (hAV : CondAV B Sig)
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : Multigraph V E) (hll : G.IsLoopless) (h3 : G.IsEdgeConnected 3)
    (hn : 2 ≤ Fintype.card V) (f : G.NZFlow Γ) :
    ∃ (f' : G.NZFlow Γ) (H : G.Subgraph),
      G.SigmaJoined Sig.carrier f f' ∧
      IsGoodSubgraph G H ∧
      ∀ e ∈ H.edges, quoFlow B f'.val e ≠ 0 :=
  Flow.Proofs.lem_4_1_proved B Sig hAV G hll h3 hn f

/-- **Lemma 4.2(a) (Reverse choice).** -/
theorem lem_4_2_a
    {V E A : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    [AddCommGroup A] [Fintype A] [DecidableEq A]
    {G : Multigraph V E} {H : G.Subgraph} {sub : SubdivisionData G H}
    {aux : AuxGraphData G H sub} (fr : Frame G H sub aux)
    (C : Fin fr.numNodes → aux.Q.DirectedCycle)
    (hC : ∀ i, fr.IsOfficialCycle i (C i))
    (Lam : ListAssignment (A := A) fr)
    (hcard : ∀ i : Fin fr.numNodes,
      (Lam.list (fr.eNode i)).card + (Lam.list (fr.fNode i)).card < Fintype.card A)
    (Y₀ : aux.EQ → A) (hY₀ : aux.Q.IsFlow Y₀) :
    ∃ x : Fin fr.numNodes → A,
      (fun eq => Y₀ eq + ∑ i : Fin fr.numNodes, (C i).sign eq • x i) ∈ PLam Lam := by
  have h311 := (Flow.Proofs.lem_3_11 (A := A) fr).2.2.1 C hC
  exact Flow.Proofs.lem_4_2_a_of fr C (fun i => ⟨(h311.1 i).2.1, (h311.1 i).2.2⟩) h311.2.1 Lam hcard Y₀ hY₀

/-- **Lemma 4.2(b) (Reverse choice with red edges).**
Every red edge `ε` lies on at least one official cycle; letting `i(ε)` be the least such
index, if the sum of forbidden sizes at each node `i` is `< |A|`, then there exists
`Y ∈ P(Λ)` avoiding `Φ(ε)` for every `ε ∈ E'`. -/
theorem lem_4_2_b
    {V E A : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    [AddCommGroup A] [Fintype A] [DecidableEq A]
    {G : Multigraph V E} {H : G.Subgraph} {sub : SubdivisionData G H}
    {aux : AuxGraphData G H sub} (fr : Frame G H sub aux)
    (C : Fin fr.numNodes → aux.Q.DirectedCycle)
    (hC : ∀ i, fr.IsOfficialCycle i (C i)) :
    (∀ eps : aux.EQ, eps ∉ fr.blue → ∃ i : Fin fr.numNodes, eps ∈ (C i).sub.edges) ∧
    (∀ (Lam : ListAssignment (A := A) fr) (E' : Finset aux.EQ)
      (hE' : ∀ eps ∈ E', eps ∉ fr.blue)
      (Phi : aux.EQ → Finset A)
      (leastIdx : aux.EQ → Fin fr.numNodes)
      (hleast : ∀ eps ∈ E',
        eps ∈ (C (leastIdx eps)).sub.edges ∧
        ∀ j : Fin fr.numNodes, eps ∈ (C j).sub.edges → leastIdx eps ≤ j),
      (∀ i : Fin fr.numNodes,
        (Lam.list (fr.eNode i)).card + (Lam.list (fr.fNode i)).card +
        ∑ eps ∈ E'.filter (fun eps => leastIdx eps = i), (Phi eps).card < Fintype.card A) →
      ∃ Y ∈ PLam Lam, ∀ eps ∈ E', Y eps ∉ Phi eps) := by
  have h311Z := (Flow.Proofs.lem_3_11 (A := ℤ) fr).2.2.1 C hC
  exact Flow.Proofs.lem_4_2_b_of fr C (fun i => ⟨(h311Z.1 i).2.1, (h311Z.1 i).2.2⟩) h311Z.2.1 h311Z.2.2.2

/-- **Lemma 4.3 (Walk lemma).** -/
theorem lem_4_3
    {V E Γ : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    [AddCommGroup Γ] [Fintype Γ] [DecidableEq Γ]
    (B : AddSubgroup Γ) [Fintype (Γ ⧸ B)] [DecidableEq (Γ ⧸ B)]
    (hA : 10 ≤ Fintype.card (Γ ⧸ B))
    (Sig : StepSystem Γ) (hR1 : CondR1 B Sig)
    {G : Multigraph V E} {H : G.Subgraph} {sub : SubdivisionData G H}
    {aux : AuxGraphData G H sub} (fr : Frame G H sub aux)
    (C : Fin fr.numNodes → aux.Q.DirectedCycle)
    (hC : ∀ i, fr.IsOfficialCycle i (C i))
    (Lam : ListAssignment (A := Γ ⧸ B) fr)
    (hLam : ∀ t ∈ fr.blue, (Lam.list t).card ≤ 3)
    (Y Y' : aux.EQ → Γ ⧸ B) (hY : Y ∈ PLam Lam) (hY' : Y' ∈ PLam Lam) :
    Relation.ReflTransGen
      (fun Z Z' => Z ∈ PLam Lam ∧ Z' ∈ PLam Lam ∧
        ∃ (σ : Γ ⧸ B) (l : Fin fr.numNodes), σ ∈ Sig.sigA B ∧
          ∀ eq, Z' eq = Z eq + (C l).sign eq • σ) Y Y' := by
  have h311 := (Flow.Proofs.lem_3_11 (A := Γ ⧸ B) fr).2.2.1 C hC
  exact Flow.Proofs.lem_4_3_of B hA Sig hR1 fr C
    (fun i => ⟨(h311.1 i).2.1, (h311.1 i).2.2⟩) h311.2.1 h311.2.2.1 h311.2.2.2 Lam hLam Y Y' hY hY'

/-- **Lemma 4.4 (Preparation in `B`).** -/
theorem lem_4_4
    {V E Γ : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    [AddCommGroup Γ] [Fintype Γ] [DecidableEq Γ]
    (B : AddSubgroup Γ) [Fintype B] [DecidableEq B] [DecidableEq (Γ ⧸ B)]
    (hB : 4 ≤ Fintype.card B) (Sig : StepSystem Γ) (hR2 : CondR2 B Sig)
    {G : Multigraph V E} {H : G.Subgraph} {sub : SubdivisionData G H}
    {aux : AuxGraphData G H sub} (fr : Frame G H sub aux)
    (f : G.NZFlow Γ) (hgood : IsHGoodSub fr B f)
    (Ecirc : Finset sub.E₀) (hEcirc : ∀ eps ∈ Ecirc, fr.IsFree eps)
    (T : sub.E₀ → Finset B)
    (hT_sup : ∀ eps ∈ Ecirc, ∀ e ∈ (sub.thread eps).edges,
      quoFlow B f.val e = 0 →
      ∀ (hb : -f.val e ∈ B), (⟨-f.val e, hb⟩ : B) ∈ T eps)
    (hT_card : ∀ eps ∈ Ecirc, (T eps).card ≤ (sub.thread eps).edges.length) :
    ∃ fcirc : G.NZFlow Γ,
      G.SigmaJoinedIn H {lam | lam ∈ Sig.carrier ∧ lam ∈ B} f fcirc ∧
      IsHGoodSub fr B fcirc ∧
      (∀ e, quoFlow B fcirc.val e = quoFlow B f.val e) ∧
      (∀ e, e ∉ H.edges → fcirc.val e = f.val e) ∧
      (∀ t : sub.E₀, fr.IsFree t → t ∉ Ecirc → ∀ e ∈ (sub.thread t).edges, fcirc.val e = f.val e) ∧
      (∀ eps ∈ Ecirc, ∃ y : B, y ∉ T eps ∧
        ∀ e ∈ (sub.thread eps).edges, fcirc.val e = f.val e + (y : Γ)) :=
  Flow.Proofs.lem_4_4_of B hB Sig hR2 fr (Flow.Proofs.lem_3_11 (A := ℤ) fr).2.2.2.2.2
    f hgood Ecirc hEcirc T hT_sup hT_card

/-- **Lemma 4.5 (One step inside `H`).** -/
theorem lem_4_5
    {V E Γ : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    [AddCommGroup Γ] [Fintype Γ] [DecidableEq Γ]
    (B : AddSubgroup Γ) [Fintype B] [DecidableEq B] [DecidableEq (Γ ⧸ B)]
    (hB : 4 ≤ Fintype.card B) (Sig : StepSystem Γ) (hR2 : CondR2 B Sig)
    {G : Multigraph V E} {H : G.Subgraph} {sub : SubdivisionData G H}
    {aux : AuxGraphData G H sub} (fr : Frame G H sub aux)
    (f : G.NZFlow Γ) (hgood : IsHGoodSub fr B f)
    (C : aux.Q.DirectedCycle) (σ : Γ ⧸ B) (hσ : σ ∈ Sig.sigA B)
    (hu' : ∀ t : sub.E₀, fr.IsProtected t → ∀ e ∈ (sub.thread t).edges,
      quoFlow B f.val e + aux.pi (fun eq => C.sign eq • σ) e ≠ 0) :
    ∃ f' : G.NZFlow Γ,
      G.SigmaJoinedIn H Sig.carrier f f' ∧
      IsHGoodSub fr B f' ∧
      (∀ e, quoFlow B f'.val e = quoFlow B f.val e + aux.pi (fun eq => C.sign eq • σ) e) ∧
      (∀ e, e ∉ H.edges → f'.val e = f.val e) :=
  Flow.Proofs.lem_4_5_of B hB Sig hR2 fr
    (Flow.Proofs.lem_3_6_a (A := ℤ) sub aux).1
    (Flow.Proofs.lem_3_6_d sub aux)
    (Flow.Proofs.lem_3_11 (A := ℤ) fr).2.2.2.2.2
    f hgood C σ hσ hu'

/-- **Lemma 4.6 (Changing the `A`-coordinate inside `H`).** -/
theorem lem_4_6
    {V E Γ : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    [AddCommGroup Γ] [Fintype Γ] [DecidableEq Γ]
    (B : AddSubgroup Γ) [Fintype (Γ ⧸ B)] [Fintype B] [DecidableEq (Γ ⧸ B)] [DecidableEq B]
    (hA : 10 ≤ Fintype.card (Γ ⧸ B)) (hB : 4 ≤ Fintype.card B)
    (Sig : StepSystem Γ) (hR1 : CondR1 B Sig) (hR2 : CondR2 B Sig)
    {G : Multigraph V E} {H : G.Subgraph} {sub : SubdivisionData G H}
    {aux : AuxGraphData G H sub} (fr : Frame G H sub aux)
    (f : G.NZFlow Γ) (hgood : IsHGoodSub fr B f)
    (Y : aux.EQ → Γ ⧸ B) (hY : Y ∈ PLam (LamOfFlow B fr f)) :
    ∃ f' : G.NZFlow Γ,
      G.SigmaJoinedIn H Sig.carrier f f' ∧
      IsHGoodSub fr B f' ∧
      (∀ e, quoFlow B f'.val e = quoFlow B f.val e + aux.pi Y e) ∧
      (∀ e, e ∉ H.edges → f'.val e = f.val e) := by
  have h311 := Flow.Proofs.lem_3_11 (A := Γ ⧸ B) fr
  let C : Fin fr.numNodes → aux.Q.DirectedCycle := fun i => (h311.2.1 i).choose
  have hC : ∀ i, fr.IsOfficialCycle i (C i) := fun i => (h311.2.1 i).choose_spec.1
  have hO := h311.2.2.1 C hC
  exact Flow.Proofs.lem_4_6_of B hA hB Sig hR1 hR2 fr C
    (fun i => ⟨(hO.1 i).2.1, (hO.1 i).2.2⟩) hO.2.1 hO.2.2.1 hO.2.2.2
    (Flow.Proofs.lem_3_6_a (A := ℤ) sub aux).1
    (Flow.Proofs.lem_3_6_d sub aux)
    h311.2.2.2.2.2 f hgood (Flow.Proofs.def_3_12_properties B fr f hgood) Y hY

/-- **Lemma 4.7 (The path).**
For any distinct vertices `p, p' ∈ V(H)`, there is a simple path `J` in `H` from `p` to
`p'` using at most `3` edges in total on the threads of each pair `N_i = {e_i, f_i}`. -/
theorem lem_4_7
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : Multigraph V E} {H : G.Subgraph} {sub : SubdivisionData G H}
    {aux : AuxGraphData G H sub} (fr : Frame G H sub aux)
    (p p' : V) (hp : p ∈ H.verts) (hp' : p' ∈ H.verts) (hne : p ≠ p') :
    ∃ (verts : List V) (edges : List E) (hlen : verts.length = edges.length + 1),
      verts.Nodup ∧
      (∀ v ∈ verts, v ∈ H.verts) ∧
      (∀ e ∈ edges, e ∈ H.edges) ∧
      verts.head? = some p ∧
      verts.getLast? = some p' ∧
      (∀ (k : ℕ) (hk : k < edges.length),
        let u := verts[k]'(by omega)
        let w := verts[k + 1]'(by omega)
        let e := edges[k]'hk
        (G.tail e = u ∧ G.head e = w) ∨ (G.tail e = w ∧ G.head e = u)) ∧
      (∀ i : Fin fr.numNodes,
        (edges.toFinset.filter (fun e =>
          (∃ t : sub.E₀, aux.origEdge t = fr.eNode i ∧ e ∈ (sub.thread t).edges) ∨
          (∃ t : sub.E₀, aux.origEdge t = fr.fNode i ∧ e ∈ (sub.thread t).edges))).card ≤ 3) := by
  have h311 := (Flow.Proofs.lem_3_11 (A := ℤ) fr).1
  exact Flow.Proofs.lem_4_7_of fr
    (fun g hg => ⟨(h311 g hg).2.1, fun i => ⟨((h311 g hg).2.2 i).2.1, ((h311 g hg).2.2 i).2.2⟩⟩)
    p p' hp hp' hne

/-- **Lemma 4.8 (Lifting a contracted move — case `(CYC)`).** -/
theorem lem_4_8_cyc
    {Γ : Type} [AddCommGroup Γ] [Fintype Γ] [DecidableEq Γ]
    (B : AddSubgroup Γ) [Fintype (Γ ⧸ B)] [Fintype B] [DecidableEq (Γ ⧸ B)] [DecidableEq B]
    (hA : 10 ≤ Fintype.card (Γ ⧸ B)) (hB : 4 ≤ Fintype.card B)
    (Sig : StepSystem Γ) (hR1 : CondR1 B Sig) (hR2 : CondR2 B Sig)
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : Multigraph V E) (hbr : G.IsBridgeless)
    (H : G.Subgraph) (hcyc : IsGoodCyc G H)
    (f : G.NZFlow Γ) (hHgood : IsHGoodCyc G B H f)
    (gstar : (G.contractSubgraph H).NZFlow Γ)
    (hmove : ∃ (Cstar : (G.contractSubgraph H).DirectedCycle) (lam : Γ),
      lam ∈ Sig.carrier ∧ ∀ e, gstar.val e = f.val e.1 + Cstar.sign e • lam) :
    ∃ g : G.NZFlow Γ,
      G.SigmaJoined Sig.carrier f g ∧
      (∀ e : {e : E // e ∉ H.edges}, g.val e.1 = gstar.val e) ∧
      IsHGoodCyc G B H g :=
  Flow.Proofs.lem_4_8_cyc_proved B hA hB Sig hR1 hR2 G hbr H hcyc f hHgood gstar hmove

/-- **Lemma 4.8 (Lifting a contracted move — case `(SUB)`, relative to a fixed frame `fr`).** -/
theorem lem_4_8_sub
    {Γ : Type} [AddCommGroup Γ] [Fintype Γ] [DecidableEq Γ]
    (B : AddSubgroup Γ) [Fintype (Γ ⧸ B)] [Fintype B] [DecidableEq (Γ ⧸ B)] [DecidableEq B]
    (hA : 10 ≤ Fintype.card (Γ ⧸ B)) (hB : 4 ≤ Fintype.card B)
    (Sig : StepSystem Γ) (hR1 : CondR1 B Sig) (hR2 : CondR2 B Sig)
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : Multigraph V E) (hbr : G.IsBridgeless)
    (H : G.Subgraph) (sub : SubdivisionData G H)
    (aux : AuxGraphData G H sub) (fr : Frame G H sub aux)
    (f : G.NZFlow Γ) (hHgood : IsHGoodSub fr B f)
    (gstar : (G.contractSubgraph H).NZFlow Γ)
    (hmove : ∃ (Cstar : (G.contractSubgraph H).DirectedCycle) (lam : Γ),
      lam ∈ Sig.carrier ∧ ∀ e, gstar.val e = f.val e.1 + Cstar.sign e • lam) :
    ∃ g : G.NZFlow Γ,
      G.SigmaJoined Sig.carrier f g ∧
      (∀ e : {e : E // e ∉ H.edges}, g.val e.1 = gstar.val e) ∧
      IsHGoodSub fr B g := by
  have h311A := Flow.Proofs.lem_3_11 (A := Γ ⧸ B) fr
  have h311Z := Flow.Proofs.lem_3_11 (A := ℤ) fr
  let C : Fin fr.numNodes → aux.Q.DirectedCycle := fun i => (h311A.2.1 i).choose
  have hC : ∀ i, fr.IsOfficialCycle i (C i) := fun i => (h311A.2.1 i).choose_spec.1
  have hOA := h311A.2.2.1 C hC
  have hOZ := h311Z.2.2.1 C hC
  exact Flow.Proofs.lem_4_8_sub_of B hA hB Sig hR1 hR2 G hbr H sub aux fr C
    (fun g hg => ⟨(h311A.1 g hg).2.1, fun i => ⟨((h311A.1 g hg).2.2 i).2.1, ((h311A.1 g hg).2.2 i).2.2⟩⟩)
    (fun i => ⟨(hOA.1 i).2.1, (hOA.1 i).2.2⟩) hOA.2.1 hOA.2.2.1 hOA.2.2.2 hOZ.2.2.2
    ⟨h311A.2.2.2.1, h311A.2.2.2.2.1⟩ h311A.2.2.2.2.2
    (Flow.Proofs.lem_3_6_a (A := ℤ) sub aux).1
    (Flow.Proofs.lem_3_6_d sub aux)
    (fun f₀ hf₀ => Flow.Proofs.def_3_12_properties B fr f₀ hf₀)
    f hHgood gstar hmove

/-- **Section 4 closing remark (integer consequence of Theorem 1.3 + Corollary 2.8(b)).** -/
theorem sec4_integer_consequence
    {a b : ℕ} (ha : 10 ≤ a) (hb : 4 ≤ b)
    (B : AddSubgroup (ZMod (a * b)))
    [Fintype (ZMod (a * b) ⧸ B)] [Fintype B]
    [DecidableEq (ZMod (a * b) ⧸ B)] [DecidableEq B]
    (hcardA : Fintype.card (ZMod (a * b) ⧸ B) = a)
    (hcardB : Fintype.card B = b)
    (Sig : StepSystem (ZMod (a * b)))
    (hlift : ∀ z ∈ Sig.carrier, Multigraph.IsLiftable (a * b) z)
    (hR1 : CondR1 B Sig) (hR2 : CondR2 B Sig) (hR3 : CondR3 Sig) (hAV : CondAV B Sig)
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : Multigraph V E) (hbr : G.IsBridgeless) :
    G.ModularFlowConnected (a * b) ∧ (G.IsLoopless → G.IntFlowConnected (a * b)) := by
  have : NeZero (a * b) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  exact Flow.Proofs.sec4_integer_consequence_of ha hb Sig G
    (let h := thm_1_3 B (hcardA.symm ▸ ha) (hcardB.symm ▸ hb) Sig hR1 hR2 hR3 hAV G hbr
     ⟨h.2.1, h.2.2⟩)
    (fun hll hk hjoin => Flow.Proofs.cor_2_8_b G hll hk Sig hlift hjoin)

/-! ## Section 5: Product averaging and the abelian group theorem -/

/-- **Lemma 5.1 (Averaging in a product).**
Let `Γ = Γ₁ × Γ₂` be a finite abelian group with both factors non-trivial, `B ≤ Γ` a
subgroup with `9 * (|B| - 1) < |Γ| - 1` (in particular whenever `|Γ / B| ≥ 9`), and `Σ`
a step system containing generating sets of `Γ₁ × {0}` and `{0} × Γ₂`. Then on every
multigraph `G` with `m` edges, every nowhere-zero `Γ`-flow is `Σ`-joined to a nowhere-zero
`Γ`-flow whose `A`-coordinate has at most `m / 9` zeros; in particular `(AV)` holds. -/
theorem lem_5_1
    {Γ₁ Γ₂ : Type} [AddCommGroup Γ₁] [AddCommGroup Γ₂]
    [Fintype Γ₁] [Fintype Γ₂] [DecidableEq Γ₁] [DecidableEq Γ₂]
    (h₁ : 2 ≤ Fintype.card Γ₁) (h₂ : 2 ≤ Fintype.card Γ₂)
    (B : AddSubgroup (Γ₁ × Γ₂)) [Fintype B] [DecidableEq B] [DecidableEq ((Γ₁ × Γ₂) ⧸ B)]
    (hbound : 9 * (Fintype.card B - 1) < Fintype.card (Γ₁ × Γ₂) - 1)
    (Sig : StepSystem (Γ₁ × Γ₂))
    (hgen₁ : ∀ x : Γ₁, (x, (0 : Γ₂)) ∈ AddSubgroup.closure (Sig.carrier ∩ {p | p.2 = 0}))
    (hgen₂ : ∀ y : Γ₂, ((0 : Γ₁), y) ∈ AddSubgroup.closure (Sig.carrier ∩ {p | p.1 = 0})) :
    (∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : Multigraph V E) (f : G.NZFlow (Γ₁ × Γ₂)),
      ∃ f' : G.NZFlow (Γ₁ × Γ₂), G.SigmaJoined Sig.carrier f f' ∧
        9 * (Finset.univ.filter (fun e => quoFlow B f'.val e = 0)).card ≤ Fintype.card E) ∧
    CondAV B Sig :=
  Flow.Proofs.lem_5_1_of hasCycleDecomp_proved h₁ h₂ B hbound Sig hgen₁ hgen₂

/-- **Remark 5.2 (Internal direct sums and the index bound).** -/
theorem rem_5_2_index_bound
    {a b : ℕ} (ha : 9 ≤ a) (hb : 1 ≤ b) :
    9 * (b - 1) < a * b - 1 :=
  Flow.Proofs.rem_5_2_index_bound_proved ha hb

theorem rem_5_2_internal_direct_sum
    {Γ : Type} [AddCommGroup Γ] [Fintype Γ] [DecidableEq Γ]
    (Γ₁ Γ₂ : AddSubgroup Γ) [Fintype Γ₁] [Fintype Γ₂]
    (h₁ : 2 ≤ Fintype.card Γ₁) (h₂ : 2 ≤ Fintype.card Γ₂)
    (hdisj : Γ₁ ⊓ Γ₂ = ⊥) (hspan : Γ₁ ⊔ Γ₂ = ⊤)
    (B : AddSubgroup Γ) [Fintype B] [Fintype (Γ ⧸ B)] [DecidableEq B] [DecidableEq (Γ ⧸ B)]
    (hA : 9 ≤ Fintype.card (Γ ⧸ B))
    (Sig : StepSystem Γ)
    (hgen₁ : Γ₁ ≤ AddSubgroup.closure (Sig.carrier ∩ (Γ₁ : Set Γ)))
    (hgen₂ : Γ₂ ≤ AddSubgroup.closure (Sig.carrier ∩ (Γ₂ : Set Γ))) :
    CondAV B Sig :=
  Flow.Proofs.rem_5_2_internal_direct_sum_of hasCycleDecomp_proved Γ₁ Γ₂ h₁ h₂ hdisj hspan B hA Sig hgen₁ hgen₂

/-- **Section 5 in-text coverage (`40 ≤ n ≤ 50` divisor characterization).** -/
theorem sec5_orders_40_to_50 :
    ∀ n : ℕ, 40 ≤ n → n ≤ 50 →
      ((∃ d : ℕ, d ∣ n ∧ 4 ≤ d ∧ 10 * d ≤ n) ↔
        (n = 40 ∨ n = 44 ∨ n = 48 ∨ n = 50)) ∧
      ((n = 40 ∨ n = 44 ∨ n = 48 ∨ n = 50) →
        ¬ ∃ p r : ℕ, Nat.Prime p ∧ 1 ≤ r ∧ n = p ^ r) :=
  Flow.Proofs.sec5_orders_40_to_50_proved

/-! ## Section 6: The moduli 40, 48, and 66 and their multiples -/

/-- **Lemma 6.1 (At most two non-steps in `ℤ_a`).** -/
theorem lem_6_1
    {a : ℕ} (ha : 10 ≤ a)
    (D : Finset (ZMod a))
    (hzero : (0 : ZMod a) ∉ D)
    (hsym : ∀ x ∈ D, -x ∈ D)
    (hcard : a - 3 ≤ D.card)
    (X : Finset (ZMod a)) (hX : X.card ≤ 6)
    (x y : ZMod a) (hx : x ∉ X) (hy : y ∉ X) :
    WalkIn {u : ZMod a | u ∉ X} (D : Set (ZMod a)) x y :=
  Flow.Proofs.lem_6_1_proved ha D hzero hsym hcard X hX x y hx hy

/-- **Lemma 6.2 (`ℤ_b` minus two elements).** -/
theorem lem_6_2
    {b d : ℕ} (hb : 4 ≤ b) (hd_gt : 1 < d) (hd_lt : d < b) (hd_div : d ∣ b)
    (X : Finset (ZMod b)) (hX : X.card ≤ 2)
    (x y : ZMod b) (hx : x ∉ X) (hy : y ∉ X) :
    WalkIn {u : ZMod b | u ∉ X} ({(1 : ZMod b), -1, (d : ZMod b), -(d : ZMod b)}) x y :=
  Flow.Proofs.lem_6_2_proved hb hd_gt hd_lt hd_div X hX x y hx hy

/-- **Table 2 coverage:** base proper divisors of `40, 48, 66` and their omitted non-zero
residues modulo `10, 12, 11`. -/
theorem sec6_table2_moduli :
    (∀ z : ZMod 10, z ≠ 0 → z ≠ 3 → z ≠ -3 →
      ∃ q : ℕ, 1 ≤ q ∧ q < 40 ∧ q ∣ 40 ∧ (z = (q : ZMod 10) ∨ z = -(q : ZMod 10))) ∧
    (∀ z : ZMod 12, z ≠ 0 → z ≠ 5 → z ≠ -5 →
      ∃ q : ℕ, 1 ≤ q ∧ q < 48 ∧ q ∣ 48 ∧ (z = (q : ZMod 12) ∨ z = -(q : ZMod 12))) ∧
    (∀ z : ZMod 11, z ≠ 0 → z ≠ 4 → z ≠ -4 →
      ∃ q : ℕ, 1 ≤ q ∧ q < 66 ∧ q ∣ 66 ∧ (z = (q : ZMod 11) ∨ z = -(q : ZMod 11))) :=
  Flow.Proofs.sec6_table2_moduli_proved

/-- **Remark 6.3 (Sharpness of 40, obstruction at `k = 44`, and indecomposability of `ℤ_{p^r}`).** -/
theorem rem_6_3_sharpness :
    (∀ a b : ℕ, a * b = 44 → 10 ≤ a → 4 ≤ b → a = 11 ∧ b = 4) ∧
    (∀ q : ℕ, 1 ≤ q → q < 44 → q ∣ 44 →
      (q : ZMod 11) = 0 ∨ (q : ZMod 11) ∈ ({(1 : ZMod 11), -1, 2, -2, 4, -4} : Finset (ZMod 11))) ∧
    (∃ X : Finset (ZMod 11), X.card ≤ 6 ∧
      ¬ ∀ x y : ZMod 11, x ∉ X → y ∉ X →
        WalkIn {u : ZMod 11 | u ∉ X}
          ({(1 : ZMod 11), -1, 2, -2, 4, -4}) x y) ∧
    (∀ (p r : ℕ), Nat.Prime p → 1 ≤ r →
      ¬ ∃ (Γ₁ Γ₂ : Type) (_ : AddCommGroup Γ₁) (_ : AddCommGroup Γ₂)
          (_ : Fintype Γ₁) (_ : Fintype Γ₂),
          2 ≤ Fintype.card Γ₁ ∧ 2 ≤ Fintype.card Γ₂ ∧
          Nonempty (ZMod (p ^ r) ≃+ Γ₁ × Γ₂)) :=
  Flow.Proofs.rem_6_3_sharpness_proved

/-! ## Non-vacuity witnesses for key structures -/

/-- Witness: a single loop on `Unit` is a cycle and bridgeless. -/
theorem nonvacuous_loop_cycle :
    let G : Multigraph Unit Unit := ⟨fun _ => (), fun _ => ()⟩
    (Multigraph.Subgraph.top G).IsCycle ∧ G.IsBridgeless :=
  Flow.Proofs.nonvacuous_loop_cycle_proved

/-- Witness: `K_4 - v` (the triangle `K_3`) is truncated cubic `3`-edge-connected and admits a well colouring. -/
theorem nonvacuous_tc3ec_and_well_colouring :
    ∃ (V E : Type) (_ : Fintype V) (_ : Fintype E) (_ : DecidableEq V) (_ : DecidableEq E)
      (Q : Multigraph V E), Q.IsTruncatedCubic3EC ∧ Nonempty (WellColouring Q) :=
  Flow.Proofs.nonvacuous_tc3ec_and_well_colouring_proved

/-- Witness: the `2`-vertex, `3`-parallel-edge multigraph admits a `(SUB)` `SubdivisionData`,
an `AuxGraphData`, and a `Frame` (matching Figures 3–4). -/
theorem nonvacuous_subdivision_aux_frame :
    let G : Multigraph (Fin 2) (Fin 3) := ⟨fun _ => 0, fun _ => 1⟩
    ∃ (sub : SubdivisionData G (Multigraph.Subgraph.top G))
      (aux : AuxGraphData G (Multigraph.Subgraph.top G) sub),
      Nonempty (Frame G (Multigraph.Subgraph.top G) sub aux) :=
  Flow.Proofs.nonvacuous_subdivision_aux_frame_proved

end Flow.Paper
