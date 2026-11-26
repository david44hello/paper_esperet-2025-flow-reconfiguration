-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Flow.Defs.Literature
import Flow.Proofs.Elementary
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.QuotientGroup.Finite
import Mathlib.GroupTheory.PGroup
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Section 5: Product averaging (Lemma 5.1), Remark 5.2, and Theorem 1.2
-/

namespace Flow.Proofs

open Flow
open scoped DirectSum

/-! ### Cycle-flow decomposition interface -/

/-- The cycle-flow decomposition property (Lemma 2.1(a) / (E3)): every `A`-flow on a
finite multigraph is a finite sum of cycle flows. -/
def HasCycleDecomp : Prop :=
  ∀ (V E A : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] [AddCommGroup A]
    (G : Multigraph V E) (h : E → A), G.IsFlow h →
    ∃ l : List (A × G.DirectedCycle), ∀ e, h e = (l.map (fun p => p.2.sign e • p.1)).sum

/-! ### Lifting cycles from an edge-subset subgraph -/

private def restrictEdges {V E : Type} (G : Multigraph V E) (P : E → Prop) :
    Multigraph V {e : E // P e} where
  tail e := G.tail e.1
  head e := G.head e.1

private lemma restrictEdges_isFlow {V E A : Type} [Fintype E] [DecidableEq V] [AddCommGroup A]
    (G : Multigraph V E) (P : E → Prop) [DecidablePred P] (x : E → A)
    (hx : G.IsFlow x) (hsupp : ∀ e, ¬ P e → x e = 0) :
    (restrictEdges G P).IsFlow (fun e => x e.1) := by
  classical
  intro v
  have h0 := hx v
  rw [← h0]
  unfold Multigraph.boundary restrictEdges
  have hsum : ∀ (g : E → V),
      ∑ e ∈ Finset.univ.filter (fun e : {e : E // P e} => g e.1 = v), x e.1 =
      ∑ e ∈ Finset.univ.filter (fun e : E => g e = v), x e := by
    intro g
    simp only [Finset.sum_filter]
    rw [← Fintype.sum_subtype_add_sum_subtype (p := P) (f := fun e => if g e = v then x e else 0)]
    have hzero : ∑ e : {e : E // ¬ P e}, (if g e.1 = v then x e.1 else 0) = 0 :=
      Finset.sum_eq_zero fun e _ => by simp [hsupp e.1 e.2]
    rw [hzero, add_zero]
  rw [hsum G.head, hsum G.tail]

private def liftDirectedCycle {V E : Type} [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : Multigraph V E) (P : E → Prop) [DecidablePred P]
    (C : (restrictEdges G P).DirectedCycle) : G.DirectedCycle where
  sub :=
    { verts := C.sub.verts
      edges := C.sub.edges.image Subtype.val
      tail_mem := by
        intro e he
        rcases Finset.mem_image.mp he with ⟨e', he', rfl⟩
        exact C.sub.tail_mem he'
      head_mem := by
        intro e he
        rcases Finset.mem_image.mp he with ⟨e', he', rfl⟩
        exact C.sub.head_mem he' }
  isCycle := by
    refine ⟨⟨C.isCycle.1.1, ?_⟩, ?_⟩
    · intro u hu v hv
      have hwalk := C.isCycle.1.2 u hu v hv
      clear hv
      induction hwalk with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ hstep ih =>
        rcases hstep with ⟨e', he', h⟩
        exact Relation.ReflTransGen.tail ih ⟨e'.1, Finset.mem_image_of_mem Subtype.val he', h⟩
    · intro v hv
      have hdeg := C.isCycle.2 v hv
      unfold Multigraph.Subgraph.deg at hdeg ⊢
      have hcard : ∀ (g : E → V),
          ((C.sub.edges.image Subtype.val).filter (fun e => g e = v)).card =
          (C.sub.edges.filter (fun e' : {e : E // P e} => g e'.1 = v)).card := by
        intro g
        rw [Finset.filter_image]
        exact Finset.card_image_of_injective _ Subtype.val_injective
      rw [hcard G.tail, hcard G.head]
      exact hdeg
  sign e := if h : P e then C.sign ⟨e, h⟩ else 0
  sign_mem := by
    intro e he
    rcases Finset.mem_image.mp he with ⟨e', he', rfl⟩
    simp only [e'.2, ↓reduceDIte]
    exact C.sign_mem he'
  sign_zero := by
    intro e he
    by_cases hp : P e
    · simp only [hp, ↓reduceDIte]
      apply C.sign_zero
      intro hmem
      exact he (Finset.mem_image.mpr ⟨⟨e, hp⟩, hmem, rfl⟩)
    · simp [hp]
  isFlow := by
    intro v
    have hsum : ∀ (g : E → V),
        ∑ e ∈ Finset.univ.filter (fun e : E => g e = v), (if h : P e then C.sign ⟨e, h⟩ else 0) =
        ∑ e ∈ Finset.univ.filter (fun e : {e : E // P e} => g e.1 = v), C.sign e := by
      intro g
      simp only [Finset.sum_filter]
      rw [← Fintype.sum_subtype_add_sum_subtype (p := P)
        (f := fun e => if g e = v then (if h : P e then C.sign ⟨e, h⟩ else 0) else 0)]
      have hzero : ∑ e : {e : E // ¬ P e},
          (if g e.1 = v then (if h : P e.1 then C.sign ⟨e.1, h⟩ else 0) else 0) = 0 :=
        Finset.sum_eq_zero fun e _ => by simp [e.2]
      rw [hzero, add_zero]
      refine Finset.sum_congr rfl fun e _ => ?_
      simp [e.2]
    calc (∑ e ∈ Finset.univ.filter (fun e : E => G.head e = v),
            if h : P e then C.sign ⟨e, h⟩ else 0) -
         (∑ e ∈ Finset.univ.filter (fun e : E => G.tail e = v),
            if h : P e then C.sign ⟨e, h⟩ else 0)
        = (∑ e ∈ Finset.univ.filter (fun e : {e : E // P e} => G.head e.1 = v), C.sign e) -
          (∑ e ∈ Finset.univ.filter (fun e : {e : E // P e} => G.tail e.1 = v), C.sign e) := by
          rw [hsum G.head, hsum G.tail]
      _ = (restrictEdges G P).boundary C.sign v := rfl
      _ = 0 := C.isFlow v

/-! ### Finite distributions on `G.NZFlow Γ` and fiber cardinality -/

private noncomputable instance instFintypeNZFlow {V E Γ : Type} [Fintype E] [DecidableEq V]
    [AddCommGroup Γ] [Fintype Γ] {G : Multigraph V E} : Fintype (G.NZFlow Γ) := by
  classical
  exact Fintype.ofEquiv {x : E → Γ // G.IsFlow x ∧ Multigraph.IsNowhereZero x}
    { toFun := fun x => ⟨x.1, x.2.1, x.2.2⟩
      invFun := fun f => ⟨f.val, f.isFlow, f.nonzero⟩
      left_inv := fun ⟨_, _, _⟩ => rfl
      right_inv := fun ⟨_, _, _⟩ => rfl }

private noncomputable instance instDecidableEqNZFlow {V E Γ : Type} [Fintype E] [DecidableEq V]
    [AddCommGroup Γ] {G : Multigraph V E} : DecidableEq (G.NZFlow Γ) := by
  classical exact inferInstance

private structure FlowDist {V E Γ : Type} [Fintype E] [DecidableEq V] [DecidableEq E]
    [AddCommGroup Γ] [Fintype Γ] [DecidableEq Γ]
    (G : Multigraph V E) (Sig : Set Γ) (f : G.NZFlow Γ) where
  prob : G.NZFlow Γ → ℝ
  nonneg : ∀ φ, 0 ≤ prob φ
  sum_one : ∑ φ, prob φ = 1
  supp_joined : ∀ φ, 0 < prob φ → G.SigmaJoined Sig f φ

private lemma card_fiber_surjective {K A : Type} [AddCommGroup K] [AddCommGroup A]
    [Fintype K] [Fintype A] [DecidableEq A]
    (ψ : K →+ A) (hsurj : Function.Surjective ψ) (a : A) :
    (Finset.univ.filter (fun k => ψ k = a)).card * Fintype.card A = Fintype.card K := by
  classical
  have hsame : ∀ b : A,
      (Finset.univ.filter (fun k => ψ k = b)).card =
      (Finset.univ.filter (fun k => ψ k = 0)).card := by
    intro b
    obtain ⟨k₀, hk₀⟩ := hsurj b
    refine Finset.card_bij (fun k _ => k - k₀) ?_ ?_ ?_
    · intro k hk
      rw [Finset.mem_filter] at hk ⊢
      exact ⟨Finset.mem_univ _, by rw [map_sub, hk.2, hk₀, sub_self]⟩
    · intro k₁ _ k₂ _ h; exact sub_left_inj.mp h
    · intro k hk
      rw [Finset.mem_filter] at hk
      refine ⟨k + k₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, add_sub_cancel_right k k₀⟩
      rw [map_add, hk.2, hk₀, zero_add]
  have hsum : ∑ b : A, (Finset.univ.filter (fun k => ψ k = b)).card = Fintype.card K := by
    rw [← Finset.card_biUnion]
    · congr 1; ext k; simp
    · intro b₁ _ b₂ _ hne
      exact Finset.disjoint_left.mpr fun k hk₁ hk₂ =>
        hne ((Finset.mem_filter.mp hk₁).2.symm.trans (Finset.mem_filter.mp hk₂).2)
  rw [Finset.sum_congr rfl (fun b _ => hsame b), Finset.sum_const, Finset.card_univ, smul_eq_mul,
      mul_comm] at hsum
  rw [hsame a, hsum]

private lemma sigmaJoined_symm {V E Γ : Type} [Fintype E] [DecidableEq V] [DecidableEq E]
    [AddCommGroup Γ] {G : Multigraph V E} {Sig : StepSystem Γ}
    {u v : G.NZFlow Γ} (huv : G.SigmaJoined Sig.carrier u v) :
    G.SigmaJoined Sig.carrier v u := by
  induction huv with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hmv ih =>
    rcases hmv with ⟨C, lam, hlam, heq⟩
    refine Relation.ReflTransGen.head ?_ ih
    refine ⟨C, -lam, Sig.neg_mem hlam, fun e => ?_⟩
    rw [heq e, smul_neg, add_neg_cancel_right]

/-! ### Transition matrices `Π₁`, `Π₂`, `Π = Π₁ Π₂`, and `ℓ₁`-contraction -/

private noncomputable def Pi1 {Γ₁ Γ₂ : Type} [AddCommGroup Γ₁] [AddCommGroup Γ₂]
    [Fintype Γ₁] [Fintype Γ₂] [DecidableEq Γ₁] [DecidableEq Γ₂]
    (x y : {p : Γ₁ × Γ₂ // p ≠ 0}) : ℝ :=
  if x.1.2 = 0 then (if y = x then 1 else 0)
  else (if y.1.2 = x.1.2 then (1 : ℝ) / (Fintype.card Γ₁ : ℝ) else 0)

private noncomputable def Pi2 {Γ₁ Γ₂ : Type} [AddCommGroup Γ₁] [AddCommGroup Γ₂]
    [Fintype Γ₁] [Fintype Γ₂] [DecidableEq Γ₁] [DecidableEq Γ₂]
    (x y : {p : Γ₁ × Γ₂ // p ≠ 0}) : ℝ :=
  if x.1.1 = 0 then (if y = x then 1 else 0)
  else (if y.1.1 = x.1.1 then (1 : ℝ) / (Fintype.card Γ₂ : ℝ) else 0)

private noncomputable def matMul {α : Type} [Fintype α] (P Q : α → α → ℝ) (x y : α) : ℝ :=
  ∑ z : α, P x z * Q z y

private noncomputable def vecMul {α : Type} [Fintype α] (μ : α → ℝ) (P : α → α → ℝ) (y : α) : ℝ :=
  ∑ x : α, μ x * P x y

private lemma vecMul_matMul {α : Type} [Fintype α] (μ : α → ℝ) (P Q : α → α → ℝ) (y : α) :
    vecMul (vecMul μ P) Q y = vecMul μ (matMul P Q) y := by
  unfold vecMul matMul
  simp_rw [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

private lemma Pi1_nonneg {Γ₁ Γ₂ : Type} [AddCommGroup Γ₁] [AddCommGroup Γ₂]
    [Fintype Γ₁] [Fintype Γ₂] [DecidableEq Γ₁] [DecidableEq Γ₂]
    (x y : {p : Γ₁ × Γ₂ // p ≠ 0}) : 0 ≤ Pi1 x y := by
  unfold Pi1; split_ifs <;> positivity

private lemma Pi2_nonneg {Γ₁ Γ₂ : Type} [AddCommGroup Γ₁] [AddCommGroup Γ₂]
    [Fintype Γ₁] [Fintype Γ₂] [DecidableEq Γ₁] [DecidableEq Γ₂]
    (x y : {p : Γ₁ × Γ₂ // p ≠ 0}) : 0 ≤ Pi2 x y := by
  unfold Pi2; split_ifs <;> positivity

private lemma Pi1_symm {Γ₁ Γ₂ : Type} [AddCommGroup Γ₁] [AddCommGroup Γ₂]
    [Fintype Γ₁] [Fintype Γ₂] [DecidableEq Γ₁] [DecidableEq Γ₂]
    (x y : {p : Γ₁ × Γ₂ // p ≠ 0}) : Pi1 x y = Pi1 y x := by
  unfold Pi1
  split_ifs with hx hy h1 h2 h3 h4
  all_goals first | rfl | (exfalso; simp_all)

private lemma Pi2_symm {Γ₁ Γ₂ : Type} [AddCommGroup Γ₁] [AddCommGroup Γ₂]
    [Fintype Γ₁] [Fintype Γ₂] [DecidableEq Γ₁] [DecidableEq Γ₂]
    (x y : {p : Γ₁ × Γ₂ // p ≠ 0}) : Pi2 x y = Pi2 y x := by
  unfold Pi2
  split_ifs with hx hy h1 h2 h3 h4
  all_goals first | rfl | (exfalso; simp_all)

private lemma Pi1_row_sum {Γ₁ Γ₂ : Type} [AddCommGroup Γ₁] [AddCommGroup Γ₂]
    [Fintype Γ₁] [Fintype Γ₂] [DecidableEq Γ₁] [DecidableEq Γ₂]
    (h1 : 2 ≤ Fintype.card Γ₁) (x : {p : Γ₁ × Γ₂ // p ≠ 0}) :
    ∑ y, Pi1 x y = 1 := by
  unfold Pi1
  by_cases hx : x.1.2 = 0
  · simp [hx]
  · simp only [hx, ↓reduceIte, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hcard : (Finset.univ.filter (fun y : {p : Γ₁ × Γ₂ // p ≠ 0} => y.1.2 = x.1.2)).card =
        Fintype.card Γ₁ := by
      refine Finset.card_bij (fun y _ => y.1.1) ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro y₁ hy₁ y₂ hy₂ heq
        exact Subtype.ext (Prod.ext heq
          ((Finset.mem_filter.mp hy₁).2.trans (Finset.mem_filter.mp hy₂).2.symm))
      · intro a _
        refine ⟨⟨(a, x.1.2), fun h0 => hx (congrArg Prod.snd h0)⟩, ?_, rfl⟩
        simp
    rw [hcard]
    have hne0 : (Fintype.card Γ₁ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp

private lemma Pi2_row_sum {Γ₁ Γ₂ : Type} [AddCommGroup Γ₁] [AddCommGroup Γ₂]
    [Fintype Γ₁] [Fintype Γ₂] [DecidableEq Γ₁] [DecidableEq Γ₂]
    (h2 : 2 ≤ Fintype.card Γ₂) (x : {p : Γ₁ × Γ₂ // p ≠ 0}) :
    ∑ y, Pi2 x y = 1 := by
  unfold Pi2
  by_cases hx : x.1.1 = 0
  · simp [hx]
  · simp only [hx, ↓reduceIte, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hcard : (Finset.univ.filter (fun y : {p : Γ₁ × Γ₂ // p ≠ 0} => y.1.1 = x.1.1)).card =
        Fintype.card Γ₂ := by
      refine Finset.card_bij (fun y _ => y.1.2) ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro y₁ hy₁ y₂ hy₂ heq
        exact Subtype.ext (Prod.ext
          ((Finset.mem_filter.mp hy₁).2.trans (Finset.mem_filter.mp hy₂).2.symm) heq)
      · intro b _
        refine ⟨⟨(x.1.1, b), fun h0 => hx (congrArg Prod.fst h0)⟩, ?_, rfl⟩
        simp
    rw [hcard]
    have hne0 : (Fintype.card Γ₂ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp

private lemma matMul_nonneg {α : Type} [Fintype α] {P Q : α → α → ℝ}
    (hP : ∀ x y, 0 ≤ P x y) (hQ : ∀ x y, 0 ≤ Q x y) (x y : α) :
    0 ≤ matMul P Q x y :=
  Finset.sum_nonneg fun z _ => mul_nonneg (hP x z) (hQ z y)

private lemma matMul_row_sum {α : Type} [Fintype α] {P Q : α → α → ℝ}
    (hP : ∀ x, ∑ y, P x y = 1) (hQ : ∀ x, ∑ y, Q x y = 1) (x : α) :
    ∑ y, matMul P Q x y = 1 := by
  unfold matMul
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hQ, mul_one]
  exact hP x

private lemma matMul_col_sum {α : Type} [Fintype α] {P Q : α → α → ℝ}
    (hP : ∀ y, ∑ x, P x y = 1) (hQ : ∀ y, ∑ x, Q x y = 1) (y : α) :
    ∑ x, matMul P Q x y = 1 := by
  unfold matMul
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, hP, one_mul]
  exact hQ y

private lemma Pi_cube_ge {Γ₁ Γ₂ : Type} [AddCommGroup Γ₁] [AddCommGroup Γ₂]
    [Fintype Γ₁] [Fintype Γ₂] [DecidableEq Γ₁] [DecidableEq Γ₂]
    (h1 : 2 ≤ Fintype.card Γ₁) (h2 : 2 ≤ Fintype.card Γ₂) :
    let Pi := matMul (Pi1 (Γ₁ := Γ₁) (Γ₂ := Γ₂)) (Pi2 (Γ₁ := Γ₁) (Γ₂ := Γ₂))
    let Pi3 := matMul (matMul Pi Pi) Pi
    ∀ x y : {p : Γ₁ × Γ₂ // p ≠ 0},
      1 / ((Fintype.card Γ₁ : ℝ) * (Fintype.card Γ₂ : ℝ)) ^ 3 ≤ Pi3 x y := by
  intro Pi Pi3 x y
  let g1 : ℝ := (Fintype.card Γ₁ : ℝ)
  let g2 : ℝ := (Fintype.card Γ₂ : ℝ)
  have hg1_pos : (0 : ℝ) < g1 := by positivity
  have hg2_pos : (0 : ℝ) < g2 := by positivity
  have hg1_ge1 : (1 : ℝ) ≤ (Fintype.card Γ₁ : ℝ) := by exact_mod_cast (by omega : 1 ≤ Fintype.card Γ₁)
  have hg2_ge1 : (1 : ℝ) ≤ (Fintype.card Γ₂ : ℝ) := by exact_mod_cast (by omega : 1 ≤ Fintype.card Γ₂)
  have hPi_nn : ∀ a b, 0 ≤ Pi a b := matMul_nonneg Pi1_nonneg Pi2_nonneg
  have hPi2_nn : ∀ a b, 0 ≤ matMul Pi Pi a b := matMul_nonneg hPi_nn hPi_nn
  have hPi_ge : ∀ a b z : {p : Γ₁ × Γ₂ // p ≠ 0},
      Pi1 a z * Pi2 z b ≤ Pi a b := fun a b z =>
    Finset.single_le_sum (fun w _ => mul_nonneg (Pi1_nonneg a w) (Pi2_nonneg w b)) (Finset.mem_univ z)
  have hinv1_le1 : 1 / g1 ≤ 1 := div_le_one_of_le₀ hg1_ge1 (le_of_lt hg1_pos)
  have hinv2_le1 : 1 / g2 ≤ 1 := div_le_one_of_le₀ hg2_ge1 (le_of_lt hg2_pos)
  have hbound : 1 / (g1 * g2) = (1 / g1) * (1 / g2) := by field_simp
  have h_diag : ∀ a, 1 / (g1 * g2) ≤ Pi a a := by
    intro a
    calc 1 / (g1 * g2) = (1 / g1) * (1 / g2) := hbound
      _ ≤ Pi1 a a * Pi2 a a := by
          apply mul_le_mul
          · unfold Pi1; split_ifs with h1' h2' h3'
            · exact hinv1_le1
            · exact absurd rfl h2'
            · exact le_rfl
            · exact absurd rfl h3'
          · unfold Pi2; split_ifs with h1' h2' h3'
            · exact hinv2_le1
            · exact absurd rfl h2'
            · exact le_rfl
            · exact absurd rfl h3'
          · positivity
          · exact Pi1_nonneg a a
      _ ≤ Pi a a := hPi_ge a a a
  have h_cross : ∀ a b : {p : Γ₁ × Γ₂ // p ≠ 0}, a.1.2 ≠ 0 → b.1.1 ≠ 0 →
      1 / (g1 * g2) ≤ Pi a b := by
    intro a b ha2 hb1
    let z : {p : Γ₁ × Γ₂ // p ≠ 0} := ⟨(b.1.1, a.1.2), fun h0 => hb1 (congrArg Prod.fst h0)⟩
    calc 1 / (g1 * g2) = (1 / g1) * (1 / g2) := hbound
      _ = Pi1 a z * Pi2 z b := by simp [Pi1, Pi2, z, g1, g2, ha2, hb1]
      _ ≤ Pi a b := hPi_ge a b z
  have h_from0 : ∀ (a : {p : Γ₁ × Γ₂ // p ≠ 0}) (b2 : Γ₂) (ha2 : a.1.2 = 0),
      let z : {p : Γ₁ × Γ₂ // p ≠ 0} :=
        ⟨(a.1.1, b2), fun h0 => a.2 (Prod.ext (by simpa using congrArg Prod.fst h0) ha2)⟩
      1 / (g1 * g2) ≤ Pi a z := by
    intro a b2 ha2
    have ha1 : a.1.1 ≠ 0 := fun h1' => a.2 (Prod.ext h1' ha2)
    let z : {p : Γ₁ × Γ₂ // p ≠ 0} := ⟨(a.1.1, b2), fun h0 => ha1 (congrArg Prod.fst h0)⟩
    calc 1 / (g1 * g2) = (1 / g1) * (1 / g2) := hbound
      _ ≤ 1 * (1 / g2) := mul_le_mul_of_nonneg_right hinv1_le1 (by positivity)
      _ = Pi1 a a * Pi2 a z := by simp [Pi1, Pi2, z, g2, ha2, ha1]
      _ ≤ Pi a z := hPi_ge a z a
  have h_to0 : ∀ (b : {p : Γ₁ × Γ₂ // p ≠ 0}) (a1 : Γ₁) (hb1 : b.1.1 = 0),
      let z : {p : Γ₁ × Γ₂ // p ≠ 0} :=
        ⟨(a1, b.1.2), fun h0 => b.2 (Prod.ext hb1 (by simpa using congrArg Prod.snd h0))⟩
      1 / (g1 * g2) ≤ Pi z b := by
    intro b a1 hb1
    have hb2 : b.1.2 ≠ 0 := fun h2' => b.2 (Prod.ext hb1 h2')
    let z : {p : Γ₁ × Γ₂ // p ≠ 0} := ⟨(a1, b.1.2), fun h0 => hb2 (congrArg Prod.snd h0)⟩
    calc 1 / (g1 * g2) = (1 / g1) * (1 / g2) := hbound
      _ ≤ (1 / g1) * 1 := mul_le_mul_of_nonneg_left hinv2_le1 (by positivity)
      _ = Pi1 z b * Pi2 b b := by simp [Pi1, Pi2, z, g1, hb1, hb2]
      _ ≤ Pi z b := hPi_ge z b b
  have hex1 : ∃ u : Γ₁, u ≠ 0 := by
    by_contra h; push Not at h
    have : Fintype.card Γ₁ ≤ 1 :=
      Fintype.card_le_one_iff_subsingleton.mpr ⟨fun a b => (h a).trans (h b).symm⟩
    omega
  have hex2 : ∃ v : Γ₂, v ≠ 0 := by
    by_contra h; push Not at h
    have : Fintype.card Γ₂ ≤ 1 :=
      Fintype.card_le_one_iff_subsingleton.mpr ⟨fun a b => (h a).trans (h b).symm⟩
    omega
  obtain ⟨u0, hu0⟩ := hex1
  obtain ⟨v0, hv0⟩ := hex2
  have hex_x' : ∃ x' : {p : Γ₁ × Γ₂ // p ≠ 0}, x'.1.2 ≠ 0 ∧ 1 / (g1 * g2) ≤ Pi x x' := by
    by_cases hx2 : x.1.2 = 0
    · refine ⟨⟨(x.1.1, v0), fun h => hv0 (congrArg Prod.snd h)⟩, hv0, ?_⟩
      exact h_from0 x v0 hx2
    · exact ⟨x, hx2, h_diag x⟩
  obtain ⟨x', hx'2, hxx'⟩ := hex_x'
  have hPi3_ge : ∀ w1 w2, Pi x w1 * Pi w1 w2 * Pi w2 y ≤ Pi3 x y := by
    intro w1 w2
    have h12 : Pi x w1 * Pi w1 w2 ≤ matMul Pi Pi x w2 :=
      Finset.single_le_sum (fun w _ => mul_nonneg (hPi_nn x w) (hPi_nn w w2)) (Finset.mem_univ w1)
    have h123 : matMul Pi Pi x w2 * Pi w2 y ≤ Pi3 x y :=
      Finset.single_le_sum (fun w _ => mul_nonneg (hPi2_nn x w) (hPi_nn w y)) (Finset.mem_univ w2)
    have : Pi x w1 * Pi w1 w2 * Pi w2 y ≤ matMul Pi Pi x w2 * Pi w2 y :=
      mul_le_mul_of_nonneg_right h12 (hPi_nn w2 y)
    linarith
  have hcube : 1 / (g1 * g2) ^ 3 = (1 / (g1 * g2)) * (1 / (g1 * g2)) * (1 / (g1 * g2)) := by
    field_simp
  by_cases hy1 : y.1.1 = 0
  · let x'' : {p : Γ₁ × Γ₂ // p ≠ 0} := ⟨(u0, y.1.2), fun h => hu0 (congrArg Prod.fst h)⟩
    have hx'x'' : 1 / (g1 * g2) ≤ Pi x' x'' := h_cross x' x'' hx'2 hu0
    have hx''y : 1 / (g1 * g2) ≤ Pi x'' y := h_to0 y u0 hy1
    have hmul : (1 / (g1 * g2)) * (1 / (g1 * g2)) * (1 / (g1 * g2)) ≤
        Pi x x' * Pi x' x'' * Pi x'' y := by
      have h12 : (1 / (g1 * g2)) * (1 / (g1 * g2)) ≤ Pi x x' * Pi x' x'' :=
        mul_le_mul hxx' hx'x'' (by positivity) (hPi_nn x x')
      exact mul_le_mul h12 hx''y (by positivity) (mul_nonneg (hPi_nn x x') (hPi_nn x' x''))
    linarith [hPi3_ge x' x'']
  · have hx'y : 1 / (g1 * g2) ≤ Pi x' y := h_cross x' y hx'2 hy1
    have hyy : 1 / (g1 * g2) ≤ Pi y y := h_diag y
    have hmul : (1 / (g1 * g2)) * (1 / (g1 * g2)) * (1 / (g1 * g2)) ≤
        Pi x x' * Pi x' y * Pi y y := by
      have h12 : (1 / (g1 * g2)) * (1 / (g1 * g2)) ≤ Pi x x' * Pi x' y :=
        mul_le_mul hxx' hx'y (by positivity) (hPi_nn x x')
      exact mul_le_mul h12 hyy (by positivity) (mul_nonneg (hPi_nn x x') (hPi_nn x' y))
    linarith [hPi3_ge x' y]

private lemma l1_contract {α : Type} [Fintype α] [Nonempty α]
    (M : α → α → ℝ) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hrow : ∀ x, ∑ y, M x y = 1) (hcol : ∀ y, ∑ x, M x y = 1)
    (hlow : ∀ x y, δ / (Fintype.card α : ℝ) ≤ M x y)
    (μ : α → ℝ) (hμ_sum : ∑ x, μ x = 1) :
    let η : α → ℝ := fun _ => 1 / (Fintype.card α : ℝ)
    ∑ y, |vecMul μ M y - η y| ≤ (1 - δ) * ∑ x, |μ x - η x| := by
  intro η
  let N : ℝ := (Fintype.card α : ℝ)
  have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr Fintype.card_pos
  have h1mδ : 0 < 1 - δ := by linarith
  let Mr : α → α → ℝ := fun x y => (M x y - δ / N) / (1 - δ)
  have hMr_nn : ∀ x y, 0 ≤ Mr x y := fun x y => div_nonneg (by linarith [hlow x y]) (le_of_lt h1mδ)
  have hMr_row : ∀ x, ∑ y, Mr x y = 1 := by
    intro x
    simp only [Mr, ← Finset.sum_div, Finset.sum_sub_distrib, hrow x, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    have hN_ne : N ≠ 0 := ne_of_gt hN_pos
    have h1mδ_ne : 1 - δ ≠ 0 := ne_of_gt h1mδ
    dsimp only [N]
    field_simp
  have hMr_col : ∀ y, ∑ x, Mr x y = 1 := by
    intro y
    simp only [Mr, ← Finset.sum_div, Finset.sum_sub_distrib, hcol y, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    have hN_ne : N ≠ 0 := ne_of_gt hN_pos
    have h1mδ_ne : 1 - δ ≠ 0 := ne_of_gt h1mδ
    dsimp only [N]
    field_simp
  have hid : ∀ y, vecMul μ M y - η y = (1 - δ) * ∑ x, (μ x - η x) * Mr x y := by
    intro y
    have hM_eq : ∀ x, M x y = δ / N + (1 - δ) * Mr x y := by
      intro x; simp only [Mr]; field_simp; ring
    have h1 : vecMul μ M y = δ / N + (1 - δ) * ∑ x, μ x * Mr x y := by
      unfold vecMul
      simp_rw [hM_eq, mul_add]
      rw [Finset.sum_add_distrib]
      congr 1
      · rw [← Finset.sum_mul, hμ_sum, one_mul]
      · rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => by ring
    have h2 : ∑ x, η x * Mr x y = 1 / N := by
      simp only [η, ← Finset.mul_sum, hMr_col y, mul_one]
      rfl
    have h3 : ∑ x, (μ x - η x) * Mr x y = (∑ x, μ x * Mr x y) - 1 / N := by
      simp_rw [sub_mul, Finset.sum_sub_distrib, h2]
    rw [h1, h3]
    change δ / N + (1 - δ) * (∑ x, μ x * Mr x y) - 1 / N =
      (1 - δ) * ((∑ x, μ x * Mr x y) - 1 / N)
    ring
  calc ∑ y, |vecMul μ M y - η y|
      = ∑ y, |(1 - δ) * ∑ x, (μ x - η x) * Mr x y| := Finset.sum_congr rfl (fun y _ => by rw [hid y])
    _ = ∑ y, (1 - δ) * |∑ x, (μ x - η x) * Mr x y| :=
        Finset.sum_congr rfl fun y _ => by rw [abs_mul, abs_of_pos h1mδ]
    _ = (1 - δ) * ∑ y, |∑ x, (μ x - η x) * Mr x y| := (Finset.mul_sum ..).symm
    _ ≤ (1 - δ) * ∑ y, ∑ x, |μ x - η x| * Mr x y := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt h1mδ)
        refine Finset.sum_le_sum fun y _ => ?_
        calc |∑ x, (μ x - η x) * Mr x y|
            ≤ ∑ x, |(μ x - η x) * Mr x y| := Finset.abs_sum_le_sum_abs _ _
          _ = ∑ x, |μ x - η x| * Mr x y :=
              Finset.sum_congr rfl fun x _ => by rw [abs_mul, abs_of_nonneg (hMr_nn x y)]
    _ = (1 - δ) * ∑ x, |μ x - η x| := by
        congr 1
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [← Finset.mul_sum, hMr_row x, mul_one]

/-! ### Modular Type-1 and Type-2 round operators -/

private def K1Subgroup {V E Γ₁ Γ₂ : Type} [Fintype E] [DecidableEq V]
    [AddCommGroup Γ₁] [AddCommGroup Γ₂]
    (G : Multigraph V E) (φ : G.NZFlow (Γ₁ × Γ₂)) : AddSubgroup (E → Γ₁) where
  carrier := {ξ | G.IsFlow ξ ∧ ∀ e, (φ.val e).2 = 0 → ξ e = 0}
  add_mem' {a b} ha hb :=
    ⟨fun v => by
      change G.boundary (fun e => a e + b e) v = 0
      rw [boundary_add, ha.1 v, hb.1 v, add_zero],
     fun e he => by simp [ha.2 e he, hb.2 e he]⟩
  zero_mem' := ⟨fun v => by simp [Multigraph.boundary], fun _ _ => rfl⟩
  neg_mem' {a} ha :=
    ⟨fun v => by
      change G.boundary (fun e => -a e) v = 0
      rw [boundary_neg, ha.1 v, neg_zero],
     fun e he => by simp [ha.2 e he]⟩

private def addK1 {V E Γ₁ Γ₂ : Type} [Fintype E] [DecidableEq V]
    [AddCommGroup Γ₁] [AddCommGroup Γ₂]
    {G : Multigraph V E} (φ : G.NZFlow (Γ₁ × Γ₂)) (ξ : K1Subgroup G φ) :
    G.NZFlow (Γ₁ × Γ₂) where
  val e := ((φ.val e).1 + ξ.1 e, (φ.val e).2)
  isFlow v := by
    have hφ := φ.isFlow v
    have hξ := ξ.2.1 v
    unfold Multigraph.boundary at hφ hξ ⊢
    ext
    · have h1 := congrArg Prod.fst hφ
      simp only [Prod.fst_sub, Prod.fst_sum, Prod.fst_zero] at h1 ⊢
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      calc (∑ x with G.head x = v, (φ.val x).1) + (∑ x with G.head x = v, ξ.1 x) -
           ((∑ x with G.tail x = v, (φ.val x).1) + (∑ x with G.tail x = v, ξ.1 x))
          = ((∑ x with G.head x = v, (φ.val x).1) - (∑ x with G.tail x = v, (φ.val x).1)) +
            ((∑ x with G.head x = v, ξ.1 x) - (∑ x with G.tail x = v, ξ.1 x)) := by abel
        _ = 0 + 0 := by rw [h1, hξ]
        _ = 0 := add_zero 0
    · have h2 := congrArg Prod.snd hφ
      simp only [Prod.snd_sub, Prod.snd_sum, Prod.snd_zero] at h2 ⊢
      exact h2
  nonzero e := by
    dsimp only
    by_cases h2 : (φ.val e).2 = 0
    · rw [ξ.2.2 e h2, add_zero]; exact φ.nonzero e
    · intro h0; exact h2 (congrArg Prod.snd h0)

private lemma K1_joined {V E Γ₁ Γ₂ : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    [AddCommGroup Γ₁] [AddCommGroup Γ₂]
    (hCD : HasCycleDecomp) (G : Multigraph V E) (Sig : StepSystem (Γ₁ × Γ₂))
    (hgen₁ : ∀ x : Γ₁, (x, (0 : Γ₂)) ∈ AddSubgroup.closure (Sig.carrier ∩ {p | p.2 = 0}))
    (φ : G.NZFlow (Γ₁ × Γ₂)) (ξ : K1Subgroup G φ) :
    G.SigmaJoined Sig.carrier φ (addK1 φ ξ) := by
  classical
  let P : E → Prop := fun e => (φ.val e).2 ≠ 0
  let S₁ : Set (Γ₁ × Γ₂) := Sig.carrier ∩ {p : Γ₁ × Γ₂ | p.2 = 0}
  have hcl_snd : ∀ x ∈ AddSubgroup.closure S₁, x.2 = 0 := by
    intro x hx
    induction hx using AddSubgroup.closure_induction with
    | mem s hs => exact hs.2
    | zero => rfl
    | add _ _ _ _ ha hb => simp [ha, hb]
    | neg _ _ ha => simp [ha]
  have hξ_flow : (restrictEdges G P).IsFlow (fun e => ξ.1 e.1) :=
    restrictEdges_isFlow G P ξ.1 ξ.2.1 (fun e he => ξ.2.2 e (not_not.mp he))
  obtain ⟨l, hl⟩ := hCD V {e : E // P e} Γ₁ (restrictEdges G P) (fun e => ξ.1 e.1) hξ_flow
  have hstep_cycle : ∀ (C : (restrictEdges G P).DirectedCycle) (a : Γ₁)
      (ψ : G.NZFlow (Γ₁ × Γ₂)), (∀ e, (ψ.val e).2 = (φ.val e).2) →
      ∃ ψ₁ : G.NZFlow (Γ₁ × Γ₂),
        (∀ e, ψ₁.val e = ψ.val e + (liftDirectedCycle G P C).sign e • (a, (0 : Γ₂))) ∧
        G.SigmaJoined Sig.carrier ψ ψ₁ := by
    intro C a ψ hψ2
    have hmk : ∀ x : AddSubgroup.closure S₁,
        G.IsFlow (fun e => ψ.val e + (liftDirectedCycle G P C).sign e • x.1) ∧
        Multigraph.IsNowhereZero (fun e => ψ.val e + (liftDirectedCycle G P C).sign e • x.1) := by
      intro x
      refine ⟨fun v => by
        rw [boundary_add, ψ.isFlow v, sec2_cycle_smul_isFlow_proved _ _ x.1 v, add_zero],
        fun e => ?_⟩
      by_cases he : e ∈ (liftDirectedCycle G P C).sub.edges
      · rcases Finset.mem_image.mp he with ⟨e', _, rfl⟩
        intro h0
        have h02 : (ψ.val e'.1).2 = 0 := by
          have h := congrArg Prod.snd h0
          simpa [hcl_snd x.1 x.2] using h
        exact e'.2 ((hψ2 e'.1).symm.trans h02)
      · dsimp only
        rw [(liftDirectedCycle G P C).sign_zero he, zero_zsmul, add_zero]
        exact ψ.nonzero e
    let mkF : AddSubgroup.closure S₁ → G.NZFlow (Γ₁ × Γ₂) := fun x =>
      ⟨fun e => ψ.val e + (liftDirectedCycle G P C).sign e • x.1, (hmk x).1, (hmk x).2⟩
    have h0 : mkF 0 = ψ := by ext e <;> simp [mkF]
    have hgen : ∀ b (hb : b ∈ AddSubgroup.closure S₁) (x : AddSubgroup.closure S₁),
        G.SigmaJoined Sig.carrier (mkF x) (mkF (x + ⟨b, hb⟩)) := by
      intro b hb
      induction hb using AddSubgroup.closure_induction with
      | mem s hs =>
        intro x
        exact Relation.ReflTransGen.single
          ⟨liftDirectedCycle G P C, s, hs.1, fun e => by
            simp only [mkF, AddSubgroup.coe_add, smul_add, add_assoc]⟩
      | zero =>
        intro x
        have hx0 : x + ⟨0, zero_mem _⟩ = x := by ext <;> simp
        rw [hx0]
        exact Relation.ReflTransGen.refl
      | add b₁ b₂ hb₁ hb₂ ih₁ ih₂ =>
        intro x
        have h1' := ih₁ x
        have h2' := ih₂ (x + ⟨b₁, hb₁⟩)
        have heq : x + ⟨b₁, hb₁⟩ + ⟨b₂, hb₂⟩ = x + ⟨b₁ + b₂, add_mem hb₁ hb₂⟩ := by
          ext <;> simp [add_assoc]
        rw [heq] at h2'
        exact h1'.trans h2'
      | neg b₁ hb₁ ih₁ =>
        intro x
        have h1' := ih₁ (x + ⟨-b₁, neg_mem hb₁⟩)
        have heq : x + ⟨-b₁, neg_mem hb₁⟩ + ⟨b₁, hb₁⟩ = x := by ext <;> simp
        rw [heq] at h1'
        exact sigmaJoined_symm h1'
    have hfin := hgen (a, 0) (hgen₁ a) 0
    rw [h0, zero_add] at hfin
    exact ⟨mkF ⟨(a, 0), hgen₁ a⟩, fun _ => rfl, hfin⟩
  have hwalk : ∀ (m : List (Γ₁ × (restrictEdges G P).DirectedCycle)) (ψ : G.NZFlow (Γ₁ × Γ₂)),
      (∀ e, (ψ.val e).2 = (φ.val e).2) →
      ∃ ψ' : G.NZFlow (Γ₁ × Γ₂),
        (∀ e, ψ'.val e = ψ.val e +
          ((m.map (fun p => (liftDirectedCycle G P p.2).sign e • p.1)).sum, (0 : Γ₂))) ∧
        G.SigmaJoined Sig.carrier ψ ψ' := by
    intro m
    induction m with
    | nil => intro ψ _; exact ⟨ψ, fun e => by simp, Relation.ReflTransGen.refl⟩
    | cons hd tl ih =>
      intro ψ hψ2
      obtain ⟨ψ₁, hψ₁_eq, hψ₁_join⟩ := hstep_cycle hd.2 hd.1 ψ hψ2
      have hψ₁2 : ∀ e, (ψ₁.val e).2 = (φ.val e).2 := fun e => by rw [hψ₁_eq e]; simp [hψ2 e]
      obtain ⟨ψ', hψ'_eq, hψ'_join⟩ := ih ψ₁ hψ₁2
      refine ⟨ψ', fun e => ?_, hψ₁_join.trans hψ'_join⟩
      rw [hψ'_eq e, hψ₁_eq e]
      ext
      · simp [add_assoc]
      · simp
  obtain ⟨ψ', hψ'_eq, hψ'_join⟩ := hwalk l φ (fun _ => rfl)
  have heq_fin : ψ' = addK1 φ ξ := by
    ext e
    · rw [hψ'_eq e]
      simp only [addK1, Prod.fst_add]
      congr 1
      by_cases hp : P e
      · rw [hl ⟨e, hp⟩]
        congr 1
        exact List.map_congr_left fun p _ => by simp [liftDirectedCycle, hp]
      · rw [ξ.2.2 e (not_not.mp hp)]
        have hmap0 : l.map (fun p => (liftDirectedCycle G P p.2).sign e • p.1) =
            l.map (fun _ => (0 : Γ₁)) :=
          List.map_congr_left fun p _ => by simp [liftDirectedCycle, hp]
        rw [hmap0]
        induction l with
        | nil => rfl
        | cons _ _ ih' => simp [ih']
    · rw [hψ'_eq e]; simp [addK1]
  exact heq_fin ▸ hψ'_join

private noncomputable instance instFintypeK1 {V E Γ₁ Γ₂ : Type} [Fintype E] [DecidableEq V]
    [AddCommGroup Γ₁] [AddCommGroup Γ₂] [Fintype Γ₁] {G : Multigraph V E}
    {φ : G.NZFlow (Γ₁ × Γ₂)} : Fintype (K1Subgroup G φ) := by
  classical exact Fintype.ofFinite _

private lemma K1_kernel {V E Γ₁ Γ₂ : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    [AddCommGroup Γ₁] [AddCommGroup Γ₂] [Fintype Γ₁] [Fintype Γ₂] [DecidableEq Γ₁] [DecidableEq Γ₂]
    (hCD : HasCycleDecomp) (h1 : 2 ≤ Fintype.card Γ₁)
    (G : Multigraph V E) (φ : G.NZFlow (Γ₁ × Γ₂)) (e : E) (y : {p : Γ₁ × Γ₂ // p ≠ 0}) :
    ((Finset.univ.filter (fun ξ : K1Subgroup G φ => (addK1 φ ξ).val e = y.1)).card : ℝ) /
    (Fintype.card (K1Subgroup G φ) : ℝ) = Pi1 ⟨φ.val e, φ.nonzero e⟩ y := by
  classical
  have hKpos : (0 : ℝ) < (Fintype.card (K1Subgroup G φ) : ℝ) :=
    Nat.cast_pos.mpr Fintype.card_pos
  unfold Pi1
  by_cases h2 : (φ.val e).2 = 0
  · simp only [h2, ↓reduceIte]
    have heq_all : ∀ ξ : K1Subgroup G φ, (addK1 φ ξ).val e = φ.val e := fun ξ =>
      Prod.ext (by simp [addK1, ξ.2.2 e h2]) rfl
    by_cases hy : y = ⟨φ.val e, φ.nonzero e⟩
    · subst hy
      simp only [↓reduceIte]
      have hfilt : Finset.univ.filter (fun ξ : K1Subgroup G φ => (addK1 φ ξ).val e = φ.val e) =
          Finset.univ := by ext ξ; simp [heq_all ξ]
      rw [hfilt, Finset.card_univ, div_self (ne_of_gt hKpos)]
    · simp only [hy, ↓reduceIte]
      have hne : φ.val e ≠ y.1 := fun h => hy (Subtype.ext h.symm)
      have hfilt : Finset.univ.filter (fun ξ : K1Subgroup G φ => (addK1 φ ξ).val e = y.1) = ∅ := by
        ext ξ; simp [heq_all ξ, hne]
      rw [hfilt, Finset.card_empty, Nat.cast_zero, zero_div]
  · simp only [h2, ↓reduceIte]
    by_cases hy2 : y.1.2 = (φ.val e).2
    · simp only [hy2, ↓reduceIte]
      let evalE : K1Subgroup G φ →+ Γ₁ := ⟨⟨fun ξ => ξ.1 e, rfl⟩, fun _ _ => rfl⟩
      have hsurj : Function.Surjective evalE := by
        let P : E → Prop := fun e' => (φ.val e').2 ≠ 0
        have hφ2_flow : (restrictEdges G P).IsFlow (fun e' => (φ.val e'.1).2) :=
          restrictEdges_isFlow G P (fun e' => (φ.val e').2)
            (fun v => by
              have h := congrArg Prod.snd (φ.isFlow v)
              unfold Multigraph.boundary at h ⊢
              simp only [Prod.snd_sub, Prod.snd_sum, Prod.snd_zero] at h
              exact h)
            (fun e' he' => not_not.mp he')
        obtain ⟨l, hl⟩ := hCD V {e' : E // P e'} Γ₂ (restrictEdges G P)
          (fun e' => (φ.val e'.1).2) hφ2_flow
        have hne0 := hl ⟨e, h2⟩
        have hexC : ∃ p ∈ l, p.2.sign ⟨e, h2⟩ ≠ 0 := by
          by_contra hall
          push Not at hall
          have h0 : (l.map (fun p => p.2.sign ⟨e, h2⟩ • p.1)).sum = 0 := by
            have hmap : l.map (fun p => p.2.sign ⟨e, h2⟩ • p.1) = l.map (fun _ => (0 : Γ₂)) :=
              List.map_congr_left fun p hp => by rw [hall p hp, zero_zsmul]
            rw [hmap]
            induction l with
            | nil => rfl
            | cons _ _ ih => simp [ih]
          exact h2 (hne0.trans h0)
        obtain ⟨p, _, hp_ne⟩ := hexC
        let C := liftDirectedCycle G P p.2
        have hCe : C.sign e = 1 ∨ C.sign e = -1 := by
          have hmem : ⟨e, h2⟩ ∈ p.2.sub.edges := by
            by_contra hn; exact hp_ne (p.2.sign_zero hn)
          exact C.sign_mem (Finset.mem_image_of_mem Subtype.val hmem)
        intro z
        let lam : Γ₁ := if C.sign e = 1 then z else -z
        have hξ_mem : (fun e' => C.sign e' • lam) ∈ K1Subgroup G φ := by
          refine ⟨sec2_cycle_smul_isFlow_proved G C lam, fun e' he' => ?_⟩
          have hnP : ¬ P e' := fun h => h he'
          simp [C, liftDirectedCycle, hnP]
        refine ⟨⟨fun e' => C.sign e' • lam, hξ_mem⟩, ?_⟩
        simp only [evalE, AddMonoidHom.coe_mk, ZeroHom.coe_mk, lam]
        rcases hCe with h1' | hm1'
        · simp [h1']
        · simp [hm1']
      have hfilt_eq :
          Finset.univ.filter (fun ξ : K1Subgroup G φ => (addK1 φ ξ).val e = y.1) =
          Finset.univ.filter (fun ξ : K1Subgroup G φ => evalE ξ = y.1.1 - (φ.val e).1) := by
        ext ξ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, addK1, evalE,
          AddMonoidHom.coe_mk, ZeroHom.coe_mk, Prod.ext_iff, hy2, and_true]
        constructor
        · intro h; rw [← h, add_sub_cancel_left]
        · intro h; rw [h, add_sub_cancel]
      rw [hfilt_eq]
      have hcard_f := card_fiber_surjective evalE hsurj (y.1.1 - (φ.val e).1)
      have hcard_fR :
          ((Finset.univ.filter (fun ξ : K1Subgroup G φ => evalE ξ = y.1.1 - (φ.val e).1)).card : ℝ) *
          (Fintype.card Γ₁ : ℝ) = (Fintype.card (K1Subgroup G φ) : ℝ) := by
        exact_mod_cast hcard_f
      have hg1_ne0 : (Fintype.card Γ₁ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hf_ne0 : ((Finset.univ.filter (fun ξ : K1Subgroup G φ => evalE ξ = y.1.1 - (φ.val e).1)).card : ℝ) ≠ 0 := by
        intro h0; rw [h0, zero_mul] at hcard_fR; linarith
      rw [← hcard_fR]
      field_simp
    · simp only [hy2, ↓reduceIte]
      have hfilt : Finset.univ.filter (fun ξ : K1Subgroup G φ => (addK1 φ ξ).val e = y.1) = ∅ := by
        ext ξ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        intro h; exact hy2 (congrArg Prod.snd h).symm
      rw [hfilt, Finset.card_empty, Nat.cast_zero, zero_div]

private noncomputable def margDist {V E Γ₁ Γ₂ : Type} [Fintype E] [DecidableEq V] [DecidableEq E]
    [AddCommGroup Γ₁] [AddCommGroup Γ₂] [Fintype Γ₁] [Fintype Γ₂] [DecidableEq Γ₁] [DecidableEq Γ₂]
    {G : Multigraph V E} {Sig : Set (Γ₁ × Γ₂)} {f : G.NZFlow (Γ₁ × Γ₂)}
    (D : FlowDist G Sig f) (e : E) (y : {p : Γ₁ × Γ₂ // p ≠ 0}) : ℝ :=
  ∑ φ ∈ Finset.univ.filter (fun φ : G.NZFlow (Γ₁ × Γ₂) => φ.val e = y.1), D.prob φ

private noncomputable def stepT1 {V E Γ₁ Γ₂ : Type} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] [AddCommGroup Γ₁] [AddCommGroup Γ₂]
    [Fintype Γ₁] [Fintype Γ₂] [DecidableEq Γ₁] [DecidableEq Γ₂]
    (hCD : HasCycleDecomp) (G : Multigraph V E) (Sig : StepSystem (Γ₁ × Γ₂))
    (hgen₁ : ∀ x : Γ₁, (x, (0 : Γ₂)) ∈ AddSubgroup.closure (Sig.carrier ∩ {p | p.2 = 0}))
    {f : G.NZFlow (Γ₁ × Γ₂)} (D : FlowDist G Sig.carrier f) : FlowDist G Sig.carrier f := by
  classical
  exact
    { prob := fun ψ =>
        ∑ φ : G.NZFlow (Γ₁ × Γ₂), D.prob φ *
          (((Finset.univ.filter (fun ξ : K1Subgroup G φ => addK1 φ ξ = ψ)).card : ℝ) /
           (Fintype.card (K1Subgroup G φ) : ℝ))
      nonneg := fun ψ => Finset.sum_nonneg fun φ _ => mul_nonneg (D.nonneg φ) (by positivity)
      sum_one := by
        rw [Finset.sum_comm]
        have hinner : ∀ φ : G.NZFlow (Γ₁ × Γ₂),
            ∑ ψ : G.NZFlow (Γ₁ × Γ₂), D.prob φ *
              (((Finset.univ.filter (fun ξ : K1Subgroup G φ => addK1 φ ξ = ψ)).card : ℝ) /
               (Fintype.card (K1Subgroup G φ) : ℝ)) = D.prob φ := by
          intro φ
          rw [← Finset.mul_sum, ← Finset.sum_div]
          have hsum_card : ∑ ψ : G.NZFlow (Γ₁ × Γ₂),
              (Finset.univ.filter (fun ξ : K1Subgroup G φ => addK1 φ ξ = ψ)).card =
              Fintype.card (K1Subgroup G φ) := by
            rw [← Finset.card_biUnion]
            · congr 1; ext ξ; simp
            · intro ψ₁ _ ψ₂ _ hne
              exact Finset.disjoint_left.mpr fun ξ h1' h2' =>
                hne ((Finset.mem_filter.mp h1').2.symm.trans (Finset.mem_filter.mp h2').2)
          have hsum_R : (∑ ψ : G.NZFlow (Γ₁ × Γ₂),
              ((Finset.univ.filter (fun ξ : K1Subgroup G φ => addK1 φ ξ = ψ)).card : ℝ)) =
              (Fintype.card (K1Subgroup G φ) : ℝ) := by exact_mod_cast hsum_card
          have hpos : (Fintype.card (K1Subgroup G φ) : ℝ) ≠ 0 :=
            Nat.cast_ne_zero.mpr Fintype.card_ne_zero
          rw [hsum_R, div_self hpos, mul_one]
        simp_rw [hinner]
        exact D.sum_one
      supp_joined := by
        intro ψ hpos
        by_contra hnot
        have hle0 : (∑ φ : G.NZFlow (Γ₁ × Γ₂), D.prob φ *
            (((Finset.univ.filter (fun ξ : K1Subgroup G φ => addK1 φ ξ = ψ)).card : ℝ) /
             (Fintype.card (K1Subgroup G φ) : ℝ))) = 0 := by
          refine Finset.sum_eq_zero fun φ _ => ?_
          by_cases hp : 0 < D.prob φ
          · have hfφ := D.supp_joined φ hp
            have hempty : Finset.univ.filter (fun ξ : K1Subgroup G φ => addK1 φ ξ = ψ) = ∅ := by
              ext ξ
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
              intro heq
              exact hnot (hfφ.trans (heq ▸ K1_joined hCD G Sig hgen₁ φ ξ))
            simp [hempty]
          · have h0 : D.prob φ = 0 := le_antisymm (le_of_not_gt hp) (D.nonneg φ)
            simp [h0]
        linarith }

private lemma marg_stepT1 {V E Γ₁ Γ₂ : Type} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] [AddCommGroup Γ₁] [AddCommGroup Γ₂]
    [Fintype Γ₁] [Fintype Γ₂] [DecidableEq Γ₁] [DecidableEq Γ₂]
    (hCD : HasCycleDecomp) (h1 : 2 ≤ Fintype.card Γ₁)
    (G : Multigraph V E) (Sig : StepSystem (Γ₁ × Γ₂))
    (hgen₁ : ∀ x : Γ₁, (x, (0 : Γ₂)) ∈ AddSubgroup.closure (Sig.carrier ∩ {p | p.2 = 0}))
    {f : G.NZFlow (Γ₁ × Γ₂)} (D : FlowDist G Sig.carrier f)
    (e : E) (y : {p : Γ₁ × Γ₂ // p ≠ 0}) :
    margDist (stepT1 hCD G Sig hgen₁ D) e y = vecMul (margDist D e) Pi1 y := by
  classical
  simp only [margDist, stepT1, vecMul]
  rw [Finset.sum_comm]
  have hinner : ∀ φ : G.NZFlow (Γ₁ × Γ₂),
      ∑ ψ ∈ Finset.univ.filter (fun ψ : G.NZFlow (Γ₁ × Γ₂) => ψ.val e = y.1),
        D.prob φ * (((Finset.univ.filter (fun ξ : K1Subgroup G φ => addK1 φ ξ = ψ)).card : ℝ) /
          (Fintype.card (K1Subgroup G φ) : ℝ)) =
      D.prob φ * Pi1 ⟨φ.val e, φ.nonzero e⟩ y := by
    intro φ
    rw [← Finset.mul_sum, ← Finset.sum_div, ← K1_kernel hCD h1 G φ e y]
    have hcard_eq :
        ∑ ψ ∈ Finset.univ.filter (fun ψ : G.NZFlow (Γ₁ × Γ₂) => ψ.val e = y.1),
          (Finset.univ.filter (fun ξ : K1Subgroup G φ => addK1 φ ξ = ψ)).card =
        (Finset.univ.filter (fun ξ : K1Subgroup G φ => (addK1 φ ξ).val e = y.1)).card := by
      rw [← Finset.card_biUnion]
      · congr 1; ext ξ
        simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun ⟨_, hψ, h⟩ => h ▸ hψ, fun h => ⟨addK1 φ ξ, h, rfl⟩⟩
      · intro ψ₁ _ ψ₂ _ hne
        exact Finset.disjoint_left.mpr fun ξ h1' h2' =>
          hne ((Finset.mem_filter.mp h1').2.symm.trans (Finset.mem_filter.mp h2').2)
    have hcard_R :
        (∑ ψ ∈ Finset.univ.filter (fun ψ : G.NZFlow (Γ₁ × Γ₂) => ψ.val e = y.1),
          ((Finset.univ.filter (fun ξ : K1Subgroup G φ => addK1 φ ξ = ψ)).card : ℝ)) =
        ((Finset.univ.filter (fun ξ : K1Subgroup G φ => (addK1 φ ξ).val e = y.1)).card : ℝ) := by
      exact_mod_cast hcard_eq
    rw [hcard_R]
  simp_rw [hinner]
  symm
  calc ∑ x : {p : Γ₁ × Γ₂ // p ≠ 0},
        (∑ φ ∈ Finset.univ.filter (fun φ : G.NZFlow (Γ₁ × Γ₂) => φ.val e = x.1), D.prob φ) *
          Pi1 x y
      = ∑ x : {p : Γ₁ × Γ₂ // p ≠ 0},
          ∑ φ ∈ Finset.univ.filter (fun φ : G.NZFlow (Γ₁ × Γ₂) => φ.val e = x.1),
            D.prob φ * Pi1 ⟨φ.val e, φ.nonzero e⟩ y := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun φ hφ => ?_
        have hx : (⟨φ.val e, φ.nonzero e⟩ : {p : Γ₁ × Γ₂ // p ≠ 0}) = x :=
          Subtype.ext (Finset.mem_filter.mp hφ).2
        rw [hx]
    _ = ∑ φ : G.NZFlow (Γ₁ × Γ₂), D.prob φ * Pi1 ⟨φ.val e, φ.nonzero e⟩ y := by
        rw [← Finset.sum_biUnion]
        · congr 1; ext φ
          simp only [Finset.mem_biUnion, Finset.mem_univ, Finset.mem_filter, true_and, iff_true]
          exact ⟨⟨φ.val e, φ.nonzero e⟩, rfl⟩
        · intro x₁ _ x₂ _ hne
          exact Finset.disjoint_left.mpr fun φ h1' h2' =>
            hne (Subtype.ext ((Finset.mem_filter.mp h1').2.symm.trans (Finset.mem_filter.mp h2').2))

/-- Transport `stepT1` by swapping coordinates to obtain `stepT2` cleanly without duplication! -/
private def swapNZFlow {V E Γ₁ Γ₂ : Type} [Fintype E] [DecidableEq V]
    [AddCommGroup Γ₁] [AddCommGroup Γ₂] {G : Multigraph V E} :
    G.NZFlow (Γ₁ × Γ₂) ≃ G.NZFlow (Γ₂ × Γ₁) where
  toFun φ :=
    { val := fun e => ((φ.val e).2, (φ.val e).1)
      isFlow := fun v => by
        have h := φ.isFlow v
        unfold Multigraph.boundary at h ⊢
        have h1 := congrArg Prod.fst h
        have h2 := congrArg Prod.snd h
        simp only [Prod.fst_sub, Prod.fst_sum, Prod.fst_zero, Prod.snd_sub, Prod.snd_sum,
          Prod.snd_zero] at h1 h2
        exact Prod.ext
          (by simp only [Prod.fst_sub, Prod.fst_sum, Prod.fst_zero]; exact h2)
          (by simp only [Prod.snd_sub, Prod.snd_sum, Prod.snd_zero]; exact h1)
      nonzero := fun e h0 =>
        φ.nonzero e (Prod.ext (congrArg Prod.snd h0) (congrArg Prod.fst h0)) }
  invFun φ :=
    { val := fun e => ((φ.val e).2, (φ.val e).1)
      isFlow := fun v => by
        have h := φ.isFlow v
        unfold Multigraph.boundary at h ⊢
        have h1 := congrArg Prod.fst h
        have h2 := congrArg Prod.snd h
        simp only [Prod.fst_sub, Prod.fst_sum, Prod.fst_zero, Prod.snd_sub, Prod.snd_sum,
          Prod.snd_zero] at h1 h2
        exact Prod.ext
          (by simp only [Prod.fst_sub, Prod.fst_sum, Prod.fst_zero]; exact h2)
          (by simp only [Prod.snd_sub, Prod.snd_sum, Prod.snd_zero]; exact h1)
      nonzero := fun e h0 =>
        φ.nonzero e (Prod.ext (congrArg Prod.snd h0) (congrArg Prod.fst h0)) }
  left_inv φ := by ext e <;> rfl
  right_inv φ := by ext e <;> rfl

private def swapStepSystem {Γ₁ Γ₂ : Type} [AddCommGroup Γ₁] [AddCommGroup Γ₂]
    (Sig : StepSystem (Γ₁ × Γ₂)) : StepSystem (Γ₂ × Γ₁) where
  carrier := {p : Γ₂ × Γ₁ | (p.2, p.1) ∈ Sig.carrier}
  zero_not_mem := Sig.zero_not_mem
  neg_mem {p} hp := by exact Sig.neg_mem hp

private lemma swapNZFlow_sigmaJoined {V E Γ₁ Γ₂ : Type} [Fintype E] [DecidableEq V] [DecidableEq E]
    [AddCommGroup Γ₁] [AddCommGroup Γ₂] {G : Multigraph V E} {Sig : StepSystem (Γ₁ × Γ₂)}
    {φ ψ : G.NZFlow (Γ₁ × Γ₂)} :
    G.SigmaJoined (swapStepSystem Sig).carrier (swapNZFlow φ) (swapNZFlow ψ) ↔
    G.SigmaJoined Sig.carrier φ ψ := by
  constructor
  · intro h
    have hgen : ∀ a b : G.NZFlow (Γ₂ × Γ₁),
        G.SigmaJoined (swapStepSystem Sig).carrier a b →
        G.SigmaJoined Sig.carrier (swapNZFlow.symm a) (swapNZFlow.symm b) := by
      intro a b hab
      induction hab with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ hmv ih =>
        rcases hmv with ⟨C, lam, hlam, heq⟩
        refine Relation.ReflTransGen.tail ih ⟨C, (lam.2, lam.1), hlam, fun e => ?_⟩
        have he := heq e
        exact Prod.ext (congrArg Prod.snd he) (congrArg Prod.fst he)
    simpa using hgen _ _ h
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hmv ih =>
      rcases hmv with ⟨C, lam, hlam, heq⟩
      refine Relation.ReflTransGen.tail ih ⟨C, (lam.2, lam.1), hlam, fun e => ?_⟩
      have he := heq e
      exact Prod.ext (congrArg Prod.snd he) (congrArg Prod.fst he)

private noncomputable def stepT2 {V E Γ₁ Γ₂ : Type} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] [AddCommGroup Γ₁] [AddCommGroup Γ₂]
    [Fintype Γ₁] [Fintype Γ₂] [DecidableEq Γ₁] [DecidableEq Γ₂]
    (hCD : HasCycleDecomp) (G : Multigraph V E) (Sig : StepSystem (Γ₁ × Γ₂))
    (hgen₂ : ∀ y : Γ₂, ((0 : Γ₁), y) ∈ AddSubgroup.closure (Sig.carrier ∩ {p | p.1 = 0}))
    {f : G.NZFlow (Γ₁ × Γ₂)} (D : FlowDist G Sig.carrier f) : FlowDist G Sig.carrier f := by
  classical
  have hgen₂' : ∀ y : Γ₂, (y, (0 : Γ₁)) ∈
      AddSubgroup.closure ((swapStepSystem Sig).carrier ∩ {p | p.2 = 0}) := by
    intro y
    have hy := hgen₂ y
    have hswap_map : ∀ x ∈ AddSubgroup.closure (Sig.carrier ∩ {p : Γ₁ × Γ₂ | p.1 = 0}),
        (x.2, x.1) ∈ AddSubgroup.closure ((swapStepSystem Sig).carrier ∩ {p : Γ₂ × Γ₁ | p.2 = 0}) := by
      intro x hx
      induction hx using AddSubgroup.closure_induction with
      | mem s hs => exact AddSubgroup.subset_closure ⟨hs.1, hs.2⟩
      | zero => exact zero_mem _
      | add _ _ _ _ ha hb => exact add_mem ha hb
      | neg _ _ ha => exact neg_mem ha
    exact hswap_map (0, y) hy
  let D' : FlowDist G (swapStepSystem Sig).carrier (swapNZFlow f) :=
    { prob := fun φ => D.prob (swapNZFlow.symm φ)
      nonneg := fun φ => D.nonneg _
      sum_one := by
        rw [Equiv.sum_comp swapNZFlow.symm D.prob]
        exact D.sum_one
      supp_joined := fun φ hp =>
        swapNZFlow_sigmaJoined.mpr (by simpa using D.supp_joined _ hp) }
  let D'' := stepT1 hCD G (swapStepSystem Sig) hgen₂' D'
  exact
    { prob := fun φ => D''.prob (swapNZFlow φ)
      nonneg := fun φ => D''.nonneg _
      sum_one := by
        rw [Equiv.sum_comp swapNZFlow D''.prob]
        exact D''.sum_one
      supp_joined := fun φ hp => swapNZFlow_sigmaJoined.mp (D''.supp_joined _ hp) }

private lemma marg_stepT2 {V E Γ₁ Γ₂ : Type} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] [AddCommGroup Γ₁] [AddCommGroup Γ₂]
    [Fintype Γ₁] [Fintype Γ₂] [DecidableEq Γ₁] [DecidableEq Γ₂]
    (hCD : HasCycleDecomp) (h2 : 2 ≤ Fintype.card Γ₂)
    (G : Multigraph V E) (Sig : StepSystem (Γ₁ × Γ₂))
    (hgen₂ : ∀ y : Γ₂, ((0 : Γ₁), y) ∈ AddSubgroup.closure (Sig.carrier ∩ {p | p.1 = 0}))
    {f : G.NZFlow (Γ₁ × Γ₂)} (D : FlowDist G Sig.carrier f)
    (e : E) (y : {p : Γ₁ × Γ₂ // p ≠ 0}) :
    margDist (stepT2 hCD G Sig hgen₂ D) e y = vecMul (margDist D e) Pi2 y := by
  classical
  let swapX : {p : Γ₁ × Γ₂ // p ≠ 0} ≃ {p : Γ₂ × Γ₁ // p ≠ 0} :=
    { toFun := fun x => ⟨(x.1.2, x.1.1), fun h => x.2 (Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h))⟩
      invFun := fun x => ⟨(x.1.2, x.1.1), fun h => x.2 (Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h))⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hPi_swap : ∀ x : {p : Γ₁ × Γ₂ // p ≠ 0}, Pi1 (swapX x) (swapX y) = Pi2 x y := by
    intro x
    unfold Pi1 Pi2
    change (if x.1.1 = 0 then if swapX y = swapX x then (1 : ℝ) else 0
            else if y.1.1 = x.1.1 then (1 : ℝ) / (Fintype.card Γ₂ : ℝ) else 0) = _
    simp [swapX.apply_eq_iff_eq]
  have hgen₂' : ∀ y' : Γ₂, (y', (0 : Γ₁)) ∈
      AddSubgroup.closure ((swapStepSystem Sig).carrier ∩ {p | p.2 = 0}) := by
    have hswap_map : ∀ x ∈ AddSubgroup.closure (Sig.carrier ∩ {p : Γ₁ × Γ₂ | p.1 = 0}),
        (x.2, x.1) ∈ AddSubgroup.closure ((swapStepSystem Sig).carrier ∩ {p : Γ₂ × Γ₁ | p.2 = 0}) := by
      intro x hx
      induction hx using AddSubgroup.closure_induction with
      | mem s hs => exact AddSubgroup.subset_closure ⟨hs.1, hs.2⟩
      | zero => exact zero_mem _
      | add _ _ _ _ ha hb => exact add_mem ha hb
      | neg _ _ ha => exact neg_mem ha
    intro y'
    exact hswap_map (0, y') (hgen₂ y')
  let D' : FlowDist G (swapStepSystem Sig).carrier (swapNZFlow f) :=
    { prob := fun φ => D.prob (swapNZFlow.symm φ)
      nonneg := fun φ => D.nonneg _
      sum_one := by rw [Equiv.sum_comp swapNZFlow.symm D.prob]; exact D.sum_one
      supp_joined := fun φ hp => swapNZFlow_sigmaJoined.mpr (by simpa using D.supp_joined _ hp) }
  have hmarg_lhs : margDist (stepT2 hCD G Sig hgen₂ D) e y =
      margDist (stepT1 hCD G (swapStepSystem Sig) hgen₂' D') e (swapX y) := by
    unfold margDist stepT2
    refine Finset.sum_bij (fun φ _ => swapNZFlow φ) ?_ ?_ ?_ ?_
    · intro φ hφ
      rw [Finset.mem_filter] at hφ ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      ext <;> simp [swapNZFlow, swapX, hφ.2]
    · intro _ _ _ _ h; exact swapNZFlow.injective h
    · intro ψ hψ
      rw [Finset.mem_filter] at hψ
      refine ⟨swapNZFlow.symm ψ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, swapNZFlow.apply_symm_apply ψ⟩
      ext <;> simp [swapNZFlow, swapX, hψ.2]
    · intro _ _; rfl
  have hmarg_D : ∀ x : {p : Γ₁ × Γ₂ // p ≠ 0}, margDist D' e (swapX x) = margDist D e x := by
    intro x
    unfold margDist D'
    refine Finset.sum_bij (fun φ _ => swapNZFlow.symm φ) ?_ ?_ ?_ ?_
    · intro φ hφ
      rw [Finset.mem_filter] at hφ ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      ext <;> simp [swapNZFlow, swapX, hφ.2]
    · intro _ _ _ _ h; exact swapNZFlow.symm.injective h
    · intro ψ hψ
      rw [Finset.mem_filter] at hψ
      refine ⟨swapNZFlow ψ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, swapNZFlow.symm_apply_apply ψ⟩
      ext <;> simp [swapNZFlow, swapX, hψ.2]
    · intro _ _; rfl
  rw [hmarg_lhs, marg_stepT1 hCD h2 G (swapStepSystem Sig) hgen₂' D' e (swapX y)]
  unfold vecMul
  rw [← Equiv.sum_comp swapX]
  refine Finset.sum_congr rfl fun x _ => by rw [hmarg_D x, hPi_swap x]

/-! ### Lemma 5.1 (Averaging in a product), parametrized on `HasCycleDecomp` -/

theorem lem_5_1_of
    (hCD : HasCycleDecomp)
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
    CondAV B Sig := by
  classical
  have hmain : ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (G : Multigraph V E) (f : G.NZFlow (Γ₁ × Γ₂)),
      ∃ f' : G.NZFlow (Γ₁ × Γ₂), G.SigmaJoined Sig.carrier f f' ∧
        9 * (Finset.univ.filter (fun e => quoFlow B f'.val e = 0)).card ≤ Fintype.card E := by
    intro V E _ _ _ _ G f
    by_cases hm0 : Fintype.card E = 0
    · refine ⟨f, Relation.ReflTransGen.refl, ?_⟩
      have hle : (Finset.univ.filter (fun e : E => quoFlow B f.val e = 0)).card ≤ Fintype.card E :=
        Finset.card_filter_le _ _
      omega
    let Γx := {p : Γ₁ × Γ₂ // p ≠ 0}
    have hcard_Γx : Fintype.card Γx = Fintype.card Γ₁ * Fintype.card Γ₂ - 1 := by
      have h1 : Fintype.card {p : Γ₁ × Γ₂ // p = 0} = 1 :=
        Fintype.card_eq_one_iff.mpr ⟨⟨0, rfl⟩, fun ⟨x, hx⟩ => Subtype.ext hx⟩
      have h2 := Fintype.card_subtype_compl (fun p : Γ₁ × Γ₂ => p = 0)
      rw [h1, Fintype.card_prod] at h2
      exact h2
    have hΓx_pos : 0 < Fintype.card Γx := by
      have h4 : 4 ≤ Fintype.card Γ₁ * Fintype.card Γ₂ := by nlinarith
      omega
    haveI : Nonempty Γx := Fintype.card_pos_iff.mp hΓx_pos
    have hmarg_sum : ∀ (D : FlowDist G Sig.carrier f) (e : E), ∑ y : Γx, margDist D e y = 1 := by
      intro D e
      rw [← D.sum_one]
      simp only [margDist]
      rw [← Finset.sum_biUnion]
      · congr 1; ext φ
        simp only [Finset.mem_biUnion, Finset.mem_univ, Finset.mem_filter, true_and, iff_true]
        exact ⟨⟨φ.val e, φ.nonzero e⟩, rfl⟩
      · intro y₁ _ y₂ _ hne
        exact Finset.disjoint_left.mpr fun φ h1' h2' =>
          hne (Subtype.ext ((Finset.mem_filter.mp h1').2.symm.trans (Finset.mem_filter.mp h2').2))
    have hmarg_nn : ∀ (D : FlowDist G Sig.carrier f) (e : E) (y : Γx), 0 ≤ margDist D e y :=
      fun D e y => Finset.sum_nonneg fun φ _ => D.nonneg φ
    let Pi := matMul (Pi1 (Γ₁ := Γ₁) (Γ₂ := Γ₂)) (Pi2 (Γ₁ := Γ₁) (Γ₂ := Γ₂))
    let Pi3 := matMul (matMul Pi Pi) Pi
    let Tpair : FlowDist G Sig.carrier f → FlowDist G Sig.carrier f :=
      fun D => stepT2 hCD G Sig hgen₂ (stepT1 hCD G Sig hgen₁ D)
    let Tsix : FlowDist G Sig.carrier f → FlowDist G Sig.carrier f :=
      fun D => Tpair (Tpair (Tpair D))
    have hTpair_marg : ∀ D e y, margDist (Tpair D) e y = vecMul (margDist D e) Pi y := by
      intro D e y
      have h2' := marg_stepT2 hCD h₂ G Sig hgen₂ (stepT1 hCD G Sig hgen₁ D) e y
      have h1' : margDist (stepT1 hCD G Sig hgen₁ D) e = vecMul (margDist D e) Pi1 :=
        funext fun z => marg_stepT1 hCD h₁ G Sig hgen₁ D e z
      change margDist (stepT2 hCD G Sig hgen₂ (stepT1 hCD G Sig hgen₁ D)) e y = _
      rw [h2', h1', vecMul_matMul]
    have hTsix_marg : ∀ D e y, margDist (Tsix D) e y = vecMul (margDist D e) Pi3 y := by
      intro D e y
      have hstep : ∀ D' : FlowDist G Sig.carrier f, margDist (Tpair D') e = vecMul (margDist D' e) Pi :=
        fun D' => funext fun z => hTpair_marg D' e z
      have h1' : margDist (Tsix D) e y =
          vecMul (margDist (Tpair (Tpair D)) e) Pi y := hTpair_marg _ e y
      have h2' : vecMul (vecMul (margDist D e) Pi) Pi = vecMul (margDist D e) (matMul Pi Pi) :=
        funext fun z => vecMul_matMul _ _ _ z
      rw [h1', hstep, hstep, h2', vecMul_matMul]
    have hPi_row : ∀ x, ∑ y, Pi x y = 1 := matMul_row_sum (Pi1_row_sum h₁) (Pi2_row_sum h₂)
    have hPi_col : ∀ y, ∑ x, Pi x y = 1 := by
      apply matMul_col_sum
      · intro y; simp_rw [Pi1_symm]; exact Pi1_row_sum h₁ y
      · intro y; simp_rw [Pi2_symm]; exact Pi2_row_sum h₂ y
    have hPi3_row : ∀ x, ∑ y, Pi3 x y = 1 := matMul_row_sum (matMul_row_sum hPi_row hPi_row) hPi_row
    have hPi3_col : ∀ y, ∑ x, Pi3 x y = 1 := matMul_col_sum (matMul_col_sum hPi_col hPi_col) hPi_col
    let g : ℝ := (Fintype.card Γ₁ : ℝ) * (Fintype.card Γ₂ : ℝ)
    let δ : ℝ := (Fintype.card Γx : ℝ) / g ^ 3
    have hg_ge4 : (4 : ℝ) ≤ (Fintype.card Γ₁ : ℝ) * (Fintype.card Γ₂ : ℝ) := by
      have : 4 ≤ Fintype.card Γ₁ * Fintype.card Γ₂ := by nlinarith
      exact_mod_cast this
    have hg_pos : (0 : ℝ) < g := by linarith
    have hΓx_eq_R : (Fintype.card Γx : ℝ) = g - 1 := by
      rw [hcard_Γx]
      have h1le : 1 ≤ Fintype.card Γ₁ * Fintype.card Γ₂ := by nlinarith
      rw [Nat.cast_sub h1le, Nat.cast_mul, Nat.cast_one]
    have hδ0 : 0 < δ := div_pos (Nat.cast_pos.mpr hΓx_pos) (pow_pos hg_pos 3)
    have hδ1 : δ < 1 := by
      change (Fintype.card Γx : ℝ) / g ^ 3 < 1
      rw [div_lt_one (pow_pos hg_pos 3), hΓx_eq_R]
      have hsq : g ≤ g ^ 2 := by nlinarith
      have hcu : g ^ 2 ≤ g ^ 3 := by nlinarith
      linarith
    have hlow : ∀ x y : Γx, δ / (Fintype.card Γx : ℝ) ≤ Pi3 x y := by
      intro x y
      have hne : (Fintype.card Γx : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hΓx_pos)
      have heq : δ / (Fintype.card Γx : ℝ) = 1 / g ^ 3 := by simp only [δ]; field_simp
      rw [heq]
      exact Pi_cube_ge h₁ h₂ x y
    let D0 : FlowDist G Sig.carrier f :=
      { prob := fun φ => if φ = f then 1 else 0
        nonneg := fun φ => by split_ifs <;> norm_num
        sum_one := by simp
        supp_joined := fun φ hpos => by
          by_cases h : φ = f
          · subst h; exact Relation.ReflTransGen.refl
          · simp [h] at hpos }
    let η : Γx → ℝ := fun _ => 1 / (Fintype.card Γx : ℝ)
    have hcontract_iter : ∀ (j : ℕ) (e : E),
        ∑ y : Γx, |margDist (Tsix^[j] D0) e y - η y| ≤ 2 * (1 - δ) ^ j := by
      intro j
      induction j with
      | zero =>
        intro e
        simp only [Function.iterate_zero, id_eq, pow_zero, mul_one]
        calc ∑ y : Γx, |margDist D0 e y - η y|
            ≤ ∑ y : Γx, (|margDist D0 e y| + |η y|) :=
              Finset.sum_le_sum fun y _ => abs_sub _ _
          _ = (∑ y : Γx, margDist D0 e y) + (∑ y : Γx, η y) := by
              rw [Finset.sum_add_distrib]
              congr 1
              · exact Finset.sum_congr rfl fun y _ => abs_of_nonneg (hmarg_nn D0 e y)
              · exact Finset.sum_congr rfl fun y _ => abs_of_nonneg (by positivity)
          _ = 1 + 1 := by
              rw [hmarg_sum D0 e]
              congr 1
              simp only [η, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
              have hne : (Fintype.card Γx : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hΓx_pos)
              field_simp
          _ = 2 := by norm_num
      | succ j ih =>
        intro e
        rw [Function.iterate_succ_apply']
        have heq : ∑ y : Γx, |margDist (Tsix (Tsix^[j] D0)) e y - η y| =
            ∑ y : Γx, |vecMul (margDist (Tsix^[j] D0) e) Pi3 y - η y| :=
          Finset.sum_congr rfl fun y _ => by rw [hTsix_marg]
        rw [heq]
        have hstep := l1_contract Pi3 δ hδ0 hδ1 hPi3_row hPi3_col hlow
          (margDist (Tsix^[j] D0) e) (hmarg_sum _ e)
        have h1mδ : 0 ≤ 1 - δ := by linarith
        calc ∑ y : Γx, |vecMul (margDist (Tsix^[j] D0) e) Pi3 y - η y|
            ≤ (1 - δ) * ∑ x : Γx, |margDist (Tsix^[j] D0) e x - η x| := hstep
          _ ≤ (1 - δ) * (2 * (1 - δ) ^ j) := mul_le_mul_of_nonneg_left (ih e) h1mδ
          _ = 2 * (1 - δ) ^ (j + 1) := by ring
    have hgap : (0 : ℝ) < 1 / 9 - ((Fintype.card B - 1 : ℕ) : ℝ) / (Fintype.card Γx : ℝ) := by
      have hbd : 9 * (Fintype.card B - 1) < Fintype.card Γx := by
        rw [hcard_Γx, ← Fintype.card_prod]; exact hbound
      have hbdR : (9 : ℝ) * ((Fintype.card B - 1 : ℕ) : ℝ) < (Fintype.card Γx : ℝ) := by
        exact_mod_cast hbd
      have hΓx_posR : (0 : ℝ) < (Fintype.card Γx : ℝ) := Nat.cast_pos.mpr hΓx_pos
      rw [sub_pos, div_lt_div_iff₀ hΓx_posR (by norm_num)]
      linarith
    have hex_j : ∃ j : ℕ, 2 * (1 - δ) ^ j < 1 / 9 - ((Fintype.card B - 1 : ℕ) : ℝ) / (Fintype.card Γx : ℝ) := by
      have htend := tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith : 0 ≤ 1 - δ) (by linarith : 1 - δ < 1)
      have hmul := htend.const_mul (2 : ℝ)
      rw [mul_zero, Metric.tendsto_atTop] at hmul
      obtain ⟨j, hj⟩ := hmul _ hgap
      refine ⟨j, ?_⟩
      have hdist := hj j le_rfl
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at hdist
      exact hdist
    obtain ⟨j, hj⟩ := hex_j
    let Dj := Tsix^[j] D0
    have hedge_lt : ∀ e : E,
        ∑ φ ∈ Finset.univ.filter (fun φ : G.NZFlow (Γ₁ × Γ₂) => quoFlow B φ.val e = 0), Dj.prob φ < 1 / 9 := by
      intro e
      let Bnz : Finset Γx := Finset.univ.filter (fun y : Γx => y.1 ∈ B)
      have hBnz_card : Bnz.card = Fintype.card B - 1 := by
        have h1 : Bnz.card = (Finset.univ.filter (fun b : B => b ≠ 0)).card := by
          refine Finset.card_bij (fun y hy => ⟨y.1, (Finset.mem_filter.mp hy).2⟩) ?_ ?_ ?_
          · intro y hy
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
            intro h0; exact y.2 (congrArg Subtype.val h0)
          · intro y₁ _ y₂ _ heq; exact Subtype.ext (congrArg (Subtype.val : B → Γ₁ × Γ₂) heq)
          · intro b hb
            have hne0 : (b : Γ₁ × Γ₂) ≠ 0 := fun h => (Finset.mem_filter.mp hb).2 (Subtype.ext h)
            exact ⟨⟨b.1, hne0⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, b.2⟩, rfl⟩
        rw [h1]
        have h2 : Finset.univ.filter (fun b : B => b ≠ 0) = Finset.univ.erase 0 := by ext b; simp
        rw [h2, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
      have hsum_eq :
          ∑ φ ∈ Finset.univ.filter (fun φ : G.NZFlow (Γ₁ × Γ₂) => quoFlow B φ.val e = 0), Dj.prob φ =
          ∑ y ∈ Bnz, margDist Dj e y := by
        simp only [margDist]
        rw [← Finset.sum_biUnion]
        · congr 1; ext φ
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, Bnz]
          constructor
          · intro hq
            exact ⟨⟨φ.val e, φ.nonzero e⟩, (QuotientAddGroup.eq_zero_iff (φ.val e)).mp hq, rfl⟩
          · rintro ⟨y, hyB, hyeq⟩
            unfold quoFlow
            rw [hyeq]
            exact (QuotientAddGroup.eq_zero_iff y.1).mpr hyB
        · intro y₁ _ y₂ _ hne
          exact Finset.disjoint_left.mpr fun φ h1' h2' =>
            hne (Subtype.ext ((Finset.mem_filter.mp h1').2.symm.trans (Finset.mem_filter.mp h2').2))
      rw [hsum_eq]
      calc ∑ y ∈ Bnz, margDist Dj e y
          = (∑ y ∈ Bnz, η y) + ∑ y ∈ Bnz, (margDist Dj e y - η y) := by
            rw [← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun y _ => by ring
        _ ≤ (∑ y ∈ Bnz, η y) + ∑ y ∈ Bnz, |margDist Dj e y - η y| := by
            gcongr with y _; exact le_abs_self _
        _ ≤ (∑ y ∈ Bnz, η y) + ∑ y : Γx, |margDist Dj e y - η y| := by
            have hle := Finset.sum_le_univ_sum_of_nonneg (s := Bnz)
              (f := fun y : Γx => |margDist Dj e y - η y|) (fun y => abs_nonneg _)
            linarith
        _ ≤ ((Fintype.card B - 1 : ℕ) : ℝ) / (Fintype.card Γx : ℝ) + 2 * (1 - δ) ^ j := by
            have hη : ∑ y ∈ Bnz, η y = ((Fintype.card B - 1 : ℕ) : ℝ) / (Fintype.card Γx : ℝ) := by
              simp only [η, Finset.sum_const, nsmul_eq_mul, hBnz_card, mul_one_div]
            rw [hη]
            linarith [hcontract_iter j e]
        _ < 1 / 9 := by linarith
    have hexp_lt :
        ∑ φ : G.NZFlow (Γ₁ × Γ₂),
          Dj.prob φ * ((Finset.univ.filter (fun e : E => quoFlow B φ.val e = 0)).card : ℝ) <
        (Fintype.card E : ℝ) / 9 := by
      have hswap :
          ∑ φ : G.NZFlow (Γ₁ × Γ₂),
            Dj.prob φ * ((Finset.univ.filter (fun e : E => quoFlow B φ.val e = 0)).card : ℝ) =
          ∑ e : E, ∑ φ ∈ Finset.univ.filter (fun φ : G.NZFlow (Γ₁ × Γ₂) => quoFlow B φ.val e = 0),
            Dj.prob φ := by
        have h1' : ∀ φ : G.NZFlow (Γ₁ × Γ₂),
            Dj.prob φ * ((Finset.univ.filter (fun e : E => quoFlow B φ.val e = 0)).card : ℝ) =
            ∑ e : E, if quoFlow B φ.val e = 0 then Dj.prob φ else 0 := by
          intro φ
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
        simp_rw [h1']
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun e _ => by rw [Finset.sum_filter]
      rw [hswap]
      have hneE : (Finset.univ : Finset E).Nonempty :=
        Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hm0))
      calc ∑ e : E, ∑ φ ∈ Finset.univ.filter (fun φ : G.NZFlow (Γ₁ × Γ₂) => quoFlow B φ.val e = 0),
              Dj.prob φ
          < ∑ _e : E, (1 / 9 : ℝ) := Finset.sum_lt_sum_of_nonempty hneE fun e _ => hedge_lt e
        _ = (Fintype.card E : ℝ) / 9 := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one_div]
    by_contra hall
    push Not at hall
    have hge : (Fintype.card E : ℝ) / 9 ≤
        ∑ φ : G.NZFlow (Γ₁ × Γ₂),
          Dj.prob φ * ((Finset.univ.filter (fun e : E => quoFlow B φ.val e = 0)).card : ℝ) := by
      calc (Fintype.card E : ℝ) / 9
          = (∑ φ : G.NZFlow (Γ₁ × Γ₂), Dj.prob φ) * ((Fintype.card E : ℝ) / 9) := by
            rw [Dj.sum_one, one_mul]
        _ = ∑ φ : G.NZFlow (Γ₁ × Γ₂), Dj.prob φ * ((Fintype.card E : ℝ) / 9) := Finset.sum_mul ..
        _ ≤ ∑ φ : G.NZFlow (Γ₁ × Γ₂),
              Dj.prob φ * ((Finset.univ.filter (fun e : E => quoFlow B φ.val e = 0)).card : ℝ) := by
            refine Finset.sum_le_sum fun φ _ => ?_
            by_cases hp : 0 < Dj.prob φ
            · have hlt := hall φ (Dj.supp_joined φ hp)
              have hltR : (Fintype.card E : ℝ) <
                  9 * ((Finset.univ.filter (fun e : E => quoFlow B φ.val e = 0)).card : ℝ) := by
                exact_mod_cast hlt
              exact mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hp)
            · have h0 : Dj.prob φ = 0 := le_antisymm (le_of_not_gt hp) (Dj.nonneg φ)
              simp [h0]
    linarith
  exact ⟨hmain, fun V E _ _ _ _ G _ _ _ f => hmain V E G f⟩

/-! ### Remark 5.2: Index bound and internal direct sums -/

theorem rem_5_2_index_bound_proved {a b : ℕ} (ha : 9 ≤ a) (hb : 1 ≤ b) :
    9 * (b - 1) < a * b - 1 := by
  have h1 : 9 * b ≤ a * b := Nat.mul_le_mul_right b ha
  omega

private lemma condAV_of_addEquiv
    {Γ Γ' : Type} [AddCommGroup Γ] [AddCommGroup Γ'] [Fintype Γ] [Fintype Γ']
    [DecidableEq Γ] [DecidableEq Γ']
    (e : Γ ≃+ Γ')
    (B : AddSubgroup Γ) [DecidableEq (Γ ⧸ B)] [DecidableEq (Γ' ⧸ B.map e.toAddMonoidHom)]
    (Sig : StepSystem Γ)
    (Sig' : StepSystem Γ')
    (hSig : ∀ x : Γ, e x ∈ Sig'.carrier ↔ x ∈ Sig.carrier)
    (hAV' : CondAV (B.map e.toAddMonoidHom) Sig') :
    CondAV B Sig := by
  classical
  intro V E _ _ _ _ G hll h3 hn f
  let f' : G.NZFlow Γ' :=
    { val := fun ed => e (f.val ed)
      isFlow := fun v => by
        have h := f.isFlow v
        unfold Multigraph.boundary at h ⊢
        rw [← map_sum, ← map_sum, ← map_sub, h, map_zero]
      nonzero := fun ed h0 => f.nonzero ed (e.injective (by simpa using h0)) }
  obtain ⟨g', hg'_join, hg'_zeros⟩ := hAV' V E G hll h3 hn f'
  let back : G.NZFlow Γ' → G.NZFlow Γ := fun φ =>
    { val := fun ed => e.symm (φ.val ed)
      isFlow := fun v => by
        have h := φ.isFlow v
        unfold Multigraph.boundary at h ⊢
        rw [← map_sum, ← map_sum, ← map_sub, h, map_zero]
      nonzero := fun ed h0 => φ.nonzero ed (e.symm.injective (by simpa using h0)) }
  have hback_f : back f' = f := by ext ed; simp [back, f']
  have hback_join : G.SigmaJoined Sig.carrier (back f') (back g') := by
    have hgen : ∀ a b : G.NZFlow Γ', G.SigmaJoined Sig'.carrier a b →
        G.SigmaJoined Sig.carrier (back a) (back b) := by
      intro a b hab
      induction hab with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ hmv ih =>
        rcases hmv with ⟨C, lam, hlam, heq⟩
        refine Relation.ReflTransGen.tail ih
          ⟨C, e.symm lam, (hSig (e.symm lam)).mp (by simpa using hlam), fun ed => ?_⟩
        simp only [back, heq ed, map_add, map_zsmul]
    exact hgen f' g' hg'_join
  refine ⟨back g', hback_f ▸ hback_join, ?_⟩
  have hfilt :
      Finset.univ.filter (fun ed : E => quoFlow B (back g').val ed = 0) =
      Finset.univ.filter (fun ed : E => quoFlow (B.map e.toAddMonoidHom) g'.val ed = 0) := by
    ext ed
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    unfold quoFlow
    dsimp only [back]
    rw [QuotientAddGroup.eq_zero_iff, QuotientAddGroup.eq_zero_iff]
    constructor
    · intro h; exact ⟨e.symm (g'.val ed), h, e.apply_symm_apply _⟩
    · rintro ⟨x, hxB, hxe⟩
      change e x = g'.val ed at hxe
      have : e.symm (g'.val ed) = x := by rw [← hxe, e.symm_apply_apply]
      rwa [this]
  rw [hfilt]
  exact hg'_zeros

theorem rem_5_2_internal_direct_sum_of
    (hCD : HasCycleDecomp)
    {Γ : Type} [AddCommGroup Γ] [Fintype Γ] [DecidableEq Γ]
    (Γ₁ Γ₂ : AddSubgroup Γ) [Fintype Γ₁] [Fintype Γ₂]
    (h₁ : 2 ≤ Fintype.card Γ₁) (h₂ : 2 ≤ Fintype.card Γ₂)
    (hdisj : Γ₁ ⊓ Γ₂ = ⊥) (hspan : Γ₁ ⊔ Γ₂ = ⊤)
    (B : AddSubgroup Γ) [Fintype B] [Fintype (Γ ⧸ B)] [DecidableEq B] [DecidableEq (Γ ⧸ B)]
    (hA : 9 ≤ Fintype.card (Γ ⧸ B))
    (Sig : StepSystem Γ)
    (hgen₁ : Γ₁ ≤ AddSubgroup.closure (Sig.carrier ∩ (Γ₁ : Set Γ)))
    (hgen₂ : Γ₂ ≤ AddSubgroup.closure (Sig.carrier ∩ (Γ₂ : Set Γ))) :
    CondAV B Sig := by
  classical
  let toG : Γ₁ × Γ₂ →+ Γ :=
    { toFun := fun p => (p.1 : Γ) + (p.2 : Γ)
      map_zero' := by simp
      map_add' := fun p q => by simp [add_assoc, add_left_comm] }
  have hinj : Function.Injective toG := by
    rw [injective_iff_map_eq_zero]
    intro p hp
    change (p.1 : Γ) + (p.2 : Γ) = 0 at hp
    have h12 : (p.1 : Γ) = -(p.2 : Γ) := eq_neg_of_add_eq_zero_left hp
    have hmem : (p.1 : Γ) ∈ Γ₁ ⊓ Γ₂ := ⟨p.1.2, h12 ▸ Γ₂.neg_mem p.2.2⟩
    rw [hdisj] at hmem
    have h10 : (p.1 : Γ) = 0 := hmem
    have h20 : (p.2 : Γ) = 0 := by rw [h10, zero_add] at hp; exact hp
    exact Prod.ext (Subtype.ext h10) (Subtype.ext h20)
  have hsurj : Function.Surjective toG := by
    intro g
    have hmem : g ∈ Γ₁ ⊔ Γ₂ := hspan.symm ▸ trivial
    rcases AddSubgroup.mem_sup.mp hmem with ⟨x, hx, y, hy, rfl⟩
    exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), rfl⟩
  let e : Γ ≃+ Γ₁ × Γ₂ := (AddEquiv.ofBijective toG ⟨hinj, hsurj⟩).symm
  let B' : AddSubgroup (Γ₁ × Γ₂) := B.map e.toAddMonoidHom
  let Sig' : StepSystem (Γ₁ × Γ₂) :=
    { carrier := e '' Sig.carrier
      zero_not_mem := by rintro ⟨x, hx, hx0⟩; exact Sig.zero_not_mem ((map_eq_zero_iff e e.injective).mp hx0 ▸ hx)
      neg_mem := by rintro y ⟨x, hx, rfl⟩; exact ⟨-x, Sig.neg_mem hx, map_neg e x⟩ }
  have hSig : ∀ x : Γ, e x ∈ Sig'.carrier ↔ x ∈ Sig.carrier := fun x =>
    ⟨by rintro ⟨y, hy, hyx⟩; exact e.injective hyx ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩
  have hcardB : Fintype.card B' = Fintype.card B := by
    refine Fintype.card_congr ?_
    exact
      { toFun := fun y => ⟨e.symm y.1, by rcases y.2 with ⟨x, hx, hx1⟩; simpa [← hx1] using hx⟩
        invFun := fun x => ⟨e x.1, ⟨x.1, x.2, rfl⟩⟩
        left_inv := fun y => Subtype.ext (e.apply_symm_apply y.1)
        right_inv := fun x => Subtype.ext (e.symm_apply_apply x.1) }
  have hcardG : Fintype.card (Γ₁ × Γ₂) = Fintype.card Γ := Fintype.card_congr e.symm.toEquiv
  have hlag : Fintype.card Γ = Fintype.card (Γ ⧸ B) * Fintype.card B := by
    simpa [Nat.card_eq_fintype_card] using AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup B
  have hbound : 9 * (Fintype.card B' - 1) < Fintype.card (Γ₁ × Γ₂) - 1 := by
    rw [hcardB, hcardG, hlag]
    exact rem_5_2_index_bound_proved hA Fintype.card_pos
  have he1 : ∀ x : Γ₁, e (x : Γ) = (x, 0) := by
    intro x
    apply e.symm.injective
    rw [e.symm_apply_apply]
    change (x : Γ) = (x : Γ) + (0 : Γ)
    exact (add_zero _).symm
  have he2 : ∀ y : Γ₂, e (y : Γ) = (0, y) := by
    intro y
    apply e.symm.injective
    rw [e.symm_apply_apply]
    change (y : Γ) = (0 : Γ) + (y : Γ)
    exact (zero_add _).symm
  have hgen₁' : ∀ x : Γ₁, (x, (0 : Γ₂)) ∈ AddSubgroup.closure (Sig'.carrier ∩ {p | p.2 = 0}) := by
    have hmap : ∀ g ∈ AddSubgroup.closure (Sig.carrier ∩ (Γ₁ : Set Γ)),
        e g ∈ AddSubgroup.closure (Sig'.carrier ∩ {p | p.2 = 0}) := by
      intro g hg
      induction hg using AddSubgroup.closure_induction with
      | mem s hs =>
        apply AddSubgroup.subset_closure
        refine ⟨⟨s, hs.1, rfl⟩, ?_⟩
        have := he1 ⟨s, hs.2⟩
        simp [this]
      | zero => simp
      | add _ _ _ _ ha hb => rw [map_add]; exact add_mem ha hb
      | neg _ _ ha => rw [map_neg]; exact neg_mem ha
    intro x
    rw [← he1 x]
    exact hmap x.1 (hgen₁ x.2)
  have hgen₂' : ∀ y : Γ₂, ((0 : Γ₁), y) ∈ AddSubgroup.closure (Sig'.carrier ∩ {p | p.1 = 0}) := by
    have hmap : ∀ g ∈ AddSubgroup.closure (Sig.carrier ∩ (Γ₂ : Set Γ)),
        e g ∈ AddSubgroup.closure (Sig'.carrier ∩ {p | p.1 = 0}) := by
      intro g hg
      induction hg using AddSubgroup.closure_induction with
      | mem s hs =>
        apply AddSubgroup.subset_closure
        refine ⟨⟨s, hs.1, rfl⟩, ?_⟩
        have := he2 ⟨s, hs.2⟩
        simp [this]
      | zero => simp
      | add _ _ _ _ ha hb => rw [map_add]; exact add_mem ha hb
      | neg _ _ ha => rw [map_neg]; exact neg_mem ha
    intro y
    rw [← he2 y]
    exact hmap y.1 (hgen₂ y.2)
  have hAV' : CondAV B' Sig' := (lem_5_1_of hCD h₁ h₂ B' hbound Sig' hgen₁' hgen₂').2
  exact condAV_of_addEquiv e B Sig Sig' hSig hAV'

/-! ### Finite abelian group structure helpers for Theorem 1.2 -/

theorem exists_addSubgroup_card_eq :
    ∀ (n : ℕ) (Γ : Type) [AddCommGroup Γ] [Fintype Γ],
      Fintype.card Γ = n → ∀ d : ℕ, d ∣ n → ∃ B : AddSubgroup Γ, Nat.card B = d := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro Γ _ _ hcard d hd
    classical
    by_cases hd1 : d ≤ 1
    · have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hd (hcard ▸ Fintype.card_pos)
      have hd_eq : d = 1 := by omega
      subst hd_eq
      exact ⟨⊥, by simp⟩
    · let p := d.minFac
      have hp : Nat.Prime p := Nat.minFac_prime (by omega)
      have : Fact p.Prime := ⟨hp⟩
      have hp_dvd_d : p ∣ d := Nat.minFac_dvd d
      have hp_dvd_G : p ∣ Fintype.card Γ := hcard.symm ▸ hp_dvd_d.trans hd
      obtain ⟨g, hg⟩ := exists_prime_addOrderOf_dvd_card p hp_dvd_G
      let P : AddSubgroup Γ := AddSubgroup.zmultiples g
      have hcardP : Nat.card P = p := by rw [Nat.card_zmultiples, hg]
      have hlagP : Fintype.card Γ = Nat.card (Γ ⧸ P) * Nat.card P := by
        simpa [Nat.card_eq_fintype_card] using AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup P
      have hcardQ_lt : Nat.card (Γ ⧸ P) < n := by
        rw [hcard, hcardP] at hlagP
        have hp2 : 2 ≤ p := hp.two_le
        have hqpos : 0 < Nat.card (Γ ⧸ P) := Nat.card_pos
        nlinarith
      have hd'_dvd : d / p ∣ Nat.card (Γ ⧸ P) := by
        rcases hd with ⟨q, hq⟩
        refine ⟨q, ?_⟩
        have h1 : p * (d / p * q) = p * Nat.card (Γ ⧸ P) := by
          calc p * (d / p * q) = (p * (d / p)) * q := by ring
            _ = d * q := by rw [Nat.mul_div_cancel' hp_dvd_d]
            _ = n := hq.symm
            _ = Nat.card (Γ ⧸ P) * p := by rw [← hcard, hlagP, hcardP]
            _ = p * Nat.card (Γ ⧸ P) := mul_comm _ _
        exact (Nat.mul_left_cancel hp.pos h1).symm
      obtain ⟨B', hB'⟩ := ih (Nat.card (Γ ⧸ P)) hcardQ_lt (Γ ⧸ P)
        (Nat.card_eq_fintype_card.symm) (d / p) hd'_dvd
      let B : AddSubgroup Γ := B'.comap (QuotientAddGroup.mk' P)
      have hP_le : P ≤ B := by
        intro x hx
        change QuotientAddGroup.mk' P x ∈ B'
        rw [QuotientAddGroup.mk'_apply, (QuotientAddGroup.eq_zero_iff x).mpr hx]
        exact zero_mem B'
      let ψ : B →+ B' :=
        { toFun := fun x => ⟨QuotientAddGroup.mk' P x.1, x.2⟩
          map_zero' := by ext; simp
          map_add' := fun x y => by ext; simp }
      have hψ_surj : Function.Surjective ψ := by
        rintro ⟨q, hq⟩
        obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective P q
        exact ⟨⟨x, hq⟩, rfl⟩
      have hker_card : Nat.card ψ.ker = p := by
        rw [← hcardP]
        refine Nat.card_congr ?_
        exact
          { toFun := fun x => ⟨x.1.1, by
              have hx0 : QuotientAddGroup.mk' P x.1.1 = 0 := congrArg Subtype.val x.2
              rw [QuotientAddGroup.mk'_apply] at hx0
              exact (QuotientAddGroup.eq_zero_iff x.1.1).mp hx0⟩
            invFun := fun y => ⟨⟨y.1, hP_le y.2⟩, by
              change ψ ⟨y.1, hP_le y.2⟩ = 0
              ext
              change QuotientAddGroup.mk' P y.1 = 0
              rw [QuotientAddGroup.mk'_apply]
              exact (QuotientAddGroup.eq_zero_iff y.1).mpr y.2⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
      have hcardB : Nat.card B = Nat.card B' * Nat.card ψ.ker := by
        have h1 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup ψ.ker
        have h2 : Nat.card (B ⧸ ψ.ker) = Nat.card B' :=
          Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective ψ hψ_surj).toEquiv
        rw [h2] at h1
        exact h1
      refine ⟨B, ?_⟩
      rw [hcardB, hB', hker_card, mul_comm, Nat.mul_div_cancel' hp_dvd_d]

theorem split_product_of_not_cyclic_prime_power
    {Γ : Type} [AddCommGroup Γ] [Fintype Γ]
    (hcard : 2 ≤ Fintype.card Γ) (hnotcp : ¬ IsCyclicPrimePower Γ) :
    ∃ (Γ₁ Γ₂ : Type) (_ : AddCommGroup Γ₁) (_ : AddCommGroup Γ₂)
      (_ : Fintype Γ₁) (_ : Fintype Γ₂),
      2 ≤ Fintype.card Γ₁ ∧ 2 ≤ Fintype.card Γ₂ ∧ Nonempty (Γ ≃+ Γ₁ × Γ₂) := by
  classical
  obtain ⟨ι, hι, p, hp, r, ⟨e⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite Γ
  let ι' := {i : ι // r i ≠ 0}
  have hr_pos : ∀ i : ι', 1 ≤ r i.1 := fun i => Nat.pos_of_ne_zero i.2
  have : ∀ i : ι', NeZero (p i.1 ^ r i.1) := fun i => ⟨pow_ne_zero _ (hp i.1).ne_zero⟩
  have hcard_fac : ∀ i : ι', 2 ≤ Fintype.card (ZMod (p i.1 ^ r i.1)) := by
    intro i
    rw [ZMod.card]
    have h1 : p i.1 ≤ p i.1 ^ r i.1 := by simpa using Nat.pow_le_pow_right (hp i.1).pos (hr_pos i)
    have h2 : 2 ≤ p i.1 := (hp i.1).two_le
    omega
  let e_pi : (⨁ i : ι, ZMod (p i ^ r i)) ≃+ ((i : ι') → ZMod (p i.1 ^ r i.1)) :=
    { toFun := fun f i => f i.1
      invFun := fun g => ∑ i : ι', DirectSum.of (fun j => ZMod (p j ^ r j)) i.1 (g i)
      map_add' := fun f₁ f₂ => by ext i; simp
      left_inv := fun f => by
        ext i
        change (∑ j : ι', DirectSum.of (fun k => ZMod (p k ^ r k)) j.1 (f j.1)) i = f i
        rw [DirectSum.sum_apply]
        by_cases hi : r i = 0
        · have : Subsingleton (ZMod (p i ^ r i)) := by rw [hi, pow_zero]; exact inferInstance
          exact Subsingleton.elim _ _
        · rw [Finset.sum_eq_single ⟨i, hi⟩]
          · simp
          · intro j _ hji
            have hne : j.1 ≠ i := fun h => hji (Subtype.ext h)
            exact DirectSum.of_eq_of_ne _ _ _ hne.symm
          · intro h; exact absurd (Finset.mem_univ _) h
      right_inv := fun g => by
        ext i
        change (∑ j : ι', DirectSum.of (fun k => ZMod (p k ^ r k)) j.1 (g j)) i.1 = g i
        rw [DirectSum.sum_apply, Finset.sum_eq_single i]
        · simp
        · intro j _ hji
          have hne : j.1 ≠ i.1 := fun h => hji (Subtype.ext h)
          exact DirectSum.of_eq_of_ne _ _ _ hne.symm
        · intro h; exact absurd (Finset.mem_univ _) h }
  let e' : Γ ≃+ ((i : ι') → ZMod (p i.1 ^ r i.1)) := e.trans e_pi
  have hι'_ne : Nonempty ι' := by
    by_contra hempty
    haveI : IsEmpty ι' := not_nonempty_iff.mp hempty
    have h1 : Fintype.card Γ = 1 := by
      rw [Fintype.card_congr e'.toEquiv, Fintype.card_eq_one_iff]
      exact ⟨0, fun f => by ext i; exact isEmptyElim i⟩
    omega
  obtain ⟨i₀⟩ := hι'_ne
  have hι'_ge2 : ∃ i₁ : ι', i₁ ≠ i₀ := by
    by_contra h
    push Not at h
    apply hnotcp
    refine ⟨p i₀.1, r i₀.1, hp i₀.1, hr_pos i₀, ⟨e'.trans ?_⟩⟩
    exact
      { toFun := fun f => f i₀
        invFun := fun a i => (h i).symm ▸ a
        map_add' := fun _ _ => rfl
        left_inv := fun f => by ext i; have hi := h i; subst hi; rfl
        right_inv := fun a => by simp }
  obtain ⟨i₁, hi₁⟩ := hι'_ge2
  let Γ₁ := ZMod (p i₀.1 ^ r i₀.1)
  let Γ₂ := (i : {i : ι' // i ≠ i₀}) → ZMod (p i.1.1 ^ r i.1.1)
  have hcard1 : 2 ≤ Fintype.card Γ₁ := hcard_fac i₀
  have hcard2 : 2 ≤ Fintype.card Γ₂ := by
    have h1 := hcard_fac i₁
    have hle : Fintype.card (ZMod (p i₁.1 ^ r i₁.1)) ≤ Fintype.card Γ₂ := by
      let emb : ZMod (p i₁.1 ^ r i₁.1) ↪ Γ₂ :=
        ⟨fun a j => if h : j.1 = i₁ then h ▸ a else 0, by
          intro a b hab
          have h' := congrFun hab ⟨i₁, hi₁⟩
          simpa using h'⟩
      exact Fintype.card_le_of_injective emb emb.injective
    omega
  let e_split : ((i : ι') → ZMod (p i.1 ^ r i.1)) ≃+ Γ₁ × Γ₂ :=
    { toFun := fun f => (f i₀, fun j => f j.1)
      invFun := fun pq i => if h : i = i₀ then h ▸ pq.1 else pq.2 ⟨i, h⟩
      map_add' := fun _ _ => rfl
      left_inv := fun f => by
        ext i
        by_cases h : i = i₀
        · subst h; simp
        · simp [h]
      right_inv := fun pq => by
        ext
        · simp
        · rename_i j; simp [j.2] }
  exact ⟨Γ₁, Γ₂, inferInstance, inferInstance, inferInstance, inferInstance,
    hcard1, hcard2, ⟨e'.trans e_split⟩⟩

/-! ### Theorem 1.2 (parametrized on `HasCycleDecomp` and Master Theorem) -/

theorem thm_1_2_of
    (hCD : HasCycleDecomp)
    {Γ : Type} [AddCommGroup Γ] [Fintype Γ] [DecidableEq Γ]
    (hnotcp : ¬ IsCyclicPrimePower Γ)
    (hdiv : ∃ d : ℕ, d ∣ Fintype.card Γ ∧ 4 ≤ d ∧ 10 * d ≤ Fintype.card Γ)
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : Multigraph V E) (_hbr : G.IsBridgeless)
    (hMaster :
      ∀ (B : AddSubgroup Γ) [Fintype (Γ ⧸ B)] [Fintype B] [DecidableEq (Γ ⧸ B)] [DecidableEq B],
        10 ≤ Fintype.card (Γ ⧸ B) → 4 ≤ Fintype.card B →
        ∀ (Sig : StepSystem Γ),
          CondR1 B Sig → CondR2 B Sig → CondR3 Sig → CondAV B Sig →
          G.FlowGraphConnected Γ) :
    G.FlowGraphConnected Γ := by
  classical
  obtain ⟨d, hd_dvd, hd4, hd10⟩ := hdiv
  have hcardG : 40 ≤ Fintype.card Γ := by omega
  obtain ⟨Γ₁, Γ₂, _, _, _, _, h1, h2, ⟨e⟩⟩ :=
    split_product_of_not_cyclic_prime_power (by omega) hnotcp
  obtain ⟨B, hB_card⟩ := exists_addSubgroup_card_eq (Fintype.card Γ) Γ rfl d hd_dvd
  have hB_fcard : Fintype.card B = d := by simpa [Nat.card_eq_fintype_card] using hB_card
  have hlag : Fintype.card Γ = Fintype.card (Γ ⧸ B) * Fintype.card B := by
    simpa [Nat.card_eq_fintype_card] using AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup B
  have hA_fcard : 10 ≤ Fintype.card (Γ ⧸ B) := by rw [hB_fcard] at hlag; nlinarith
  let Sig : StepSystem Γ :=
    { carrier := {x : Γ | x ≠ 0}
      zero_not_mem := fun h => h rfl
      neg_mem := fun {x} hx => neg_ne_zero.mpr hx }
  have hR1 : CondR1 B Sig := by
    intro X _ x y hx hy
    by_cases hxy : x = y
    · subst hxy; exact ⟨hx, hx, Relation.ReflTransGen.refl⟩
    · refine ⟨hx, hy, Relation.ReflTransGen.single ⟨hx, hy, y - x, ?_, by abel⟩⟩
      refine ⟨sub_ne_zero.mpr (Ne.symm hxy), ?_⟩
      obtain ⟨g, hg⟩ := QuotientAddGroup.mk'_surjective B (y - x)
      refine ⟨g, fun hg0 => sub_ne_zero.mpr (Ne.symm hxy) (by rw [← hg, hg0, map_zero]), hg⟩
  have hR2 : CondR2 B Sig := by
    intro X _ x y hx hy
    by_cases hxy : x = y
    · subst hxy; exact ⟨hx, hx, Relation.ReflTransGen.refl⟩
    · refine ⟨hx, hy, Relation.ReflTransGen.single ⟨hx, hy, y - x, ?_, by abel⟩⟩
      intro h0
      exact hxy (sub_eq_zero.mp (Subtype.ext h0)).symm
  have hR3 : CondR3 Sig := by
    intro x y hx hy
    by_cases hxy : x = y
    · subst hxy; exact ⟨hx, hx, Relation.ReflTransGen.refl⟩
    · exact ⟨hx, hy, Relation.ReflTransGen.single ⟨hx, hy, y - x, sub_ne_zero.mpr (Ne.symm hxy), by abel⟩⟩
  have hAV : CondAV B Sig := by
    let B' : AddSubgroup (Γ₁ × Γ₂) := B.map e.toAddMonoidHom
    let Sig' : StepSystem (Γ₁ × Γ₂) :=
      { carrier := {p : Γ₁ × Γ₂ | p ≠ 0}
        zero_not_mem := fun h => h rfl
        neg_mem := fun {p} hp => neg_ne_zero.mpr hp }
    have hSig : ∀ x : Γ, e x ∈ Sig'.carrier ↔ x ∈ Sig.carrier := fun x =>
      ⟨fun h h0 => h (by rw [h0, map_zero]), fun h h0 => h (e.injective (by simpa using h0))⟩
    have hcardB' : Fintype.card B' = d := by
      rw [← hB_fcard]
      refine Fintype.card_congr ?_
      exact
        { toFun := fun y => ⟨e.symm y.1, by rcases y.2 with ⟨x, hx, hx1⟩; simpa [← hx1] using hx⟩
          invFun := fun x => ⟨e x.1, ⟨x.1, x.2, rfl⟩⟩
          left_inv := fun y => Subtype.ext (e.apply_symm_apply y.1)
          right_inv := fun x => Subtype.ext (e.symm_apply_apply x.1) }
    have hcardG' : Fintype.card (Γ₁ × Γ₂) = Fintype.card Γ := Fintype.card_congr e.symm.toEquiv
    have hbd : 9 * (Fintype.card B' - 1) < Fintype.card (Γ₁ × Γ₂) - 1 := by
      rw [hcardB', hcardG', hlag, hB_fcard]
      exact rem_5_2_index_bound_proved (by omega) (by omega)
    have hgen₁ : ∀ x : Γ₁, (x, (0 : Γ₂)) ∈ AddSubgroup.closure (Sig'.carrier ∩ {p | p.2 = 0}) := by
      intro x
      by_cases hx : x = 0
      · subst hx; exact zero_mem _
      · exact AddSubgroup.subset_closure ⟨fun h => hx (congrArg Prod.fst h), rfl⟩
    have hgen₂ : ∀ y : Γ₂, ((0 : Γ₁), y) ∈ AddSubgroup.closure (Sig'.carrier ∩ {p | p.1 = 0}) := by
      intro y
      by_cases hy : y = 0
      · subst hy; exact zero_mem _
      · exact AddSubgroup.subset_closure ⟨fun h => hy (congrArg Prod.snd h), rfl⟩
    have hAV' := (lem_5_1_of hCD h1 h2 B' hbd Sig' hgen₁ hgen₂).2
    exact condAV_of_addEquiv e B Sig Sig' hSig hAV'
  exact hMaster B hA_fcard (by omega) Sig hR1 hR2 hR3 hAV

end Flow.Proofs
