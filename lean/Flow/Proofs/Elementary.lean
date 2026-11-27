module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Flow.Defs.Literature
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
# Elementary lemmas, Section 1 trivial cases, Section 2 conventions, Section 4 (E1)–(E5),
and non-vacuity witnesses
-/

namespace Flow.Proofs

open Flow

/-! ### Section 2: Cycle flows and edge reorientation -/

theorem boundary_add {V E Γ : Type} [Fintype E] [DecidableEq V] [AddCommGroup Γ]
    (G : Multigraph V E) (x y : E → Γ) (v : V) :
    G.boundary (fun e => x e + y e) v = G.boundary x v + G.boundary y v := by
  unfold Multigraph.boundary
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  abel

theorem boundary_sub {V E Γ : Type} [Fintype E] [DecidableEq V] [AddCommGroup Γ]
    (G : Multigraph V E) (x y : E → Γ) (v : V) :
    G.boundary (fun e => x e - y e) v = G.boundary x v - G.boundary y v := by
  unfold Multigraph.boundary
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  abel

theorem boundary_neg {V E Γ : Type} [Fintype E] [DecidableEq V] [AddCommGroup Γ]
    (G : Multigraph V E) (x : E → Γ) (v : V) :
    G.boundary (fun e => -x e) v = -G.boundary x v := by
  unfold Multigraph.boundary
  rw [Finset.sum_neg_distrib, Finset.sum_neg_distrib]
  abel

theorem boundary_zsmul {V E Γ : Type} [Fintype E] [DecidableEq V] [AddCommGroup Γ]
    (G : Multigraph V E) (c : E → ℤ) (lam : Γ) (v : V) :
    G.boundary (fun e => c e • lam) v = G.boundary c v • lam := by
  unfold Multigraph.boundary
  rw [sub_smul, Finset.sum_smul, Finset.sum_smul]

theorem sec2_cycle_smul_isFlow_proved
    {V E Γ : Type} [Fintype E] [DecidableEq V] [AddCommGroup Γ]
    (G : Multigraph V E) (C : G.DirectedCycle) (lam : Γ) :
    G.IsFlow (fun e => C.sign e • lam) := by
  intro v
  rw [boundary_zsmul, C.isFlow v, zero_zsmul]

theorem boundary_reorient
    {V E Γ : Type} [Fintype E] [DecidableEq V] [AddCommGroup Γ]
    (G : Multigraph V E) (flip : E → Bool) (x : E → Γ) (v : V) :
    (G.reorient flip).boundary (Multigraph.reorientVal flip x) v = G.boundary x v := by
  classical
  unfold Multigraph.boundary Multigraph.reorient Multigraph.reorientVal
  simp only [Finset.sum_filter, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  cases hfl : flip e
  · simp
  · by_cases ht : G.tail e = v <;> by_cases hh : G.head e = v <;> simp [ht, hh]

theorem sec2_reorient_preserves_flow_proved
    {V E Γ : Type} [Fintype E] [DecidableEq V] [AddCommGroup Γ]
    (G : Multigraph V E) (flip : E → Bool) (x : E → Γ) :
    (G.reorient flip).IsFlow (Multigraph.reorientVal flip x) ↔ G.IsFlow x := by
  constructor <;> intro h v
  · rw [← boundary_reorient G flip x v]; exact h v
  · rw [boundary_reorient G flip x v]; exact h v

/-! ### Section 1: Trivial small-group case -/

theorem sec1_trivial_small_group_proved
    {Γ : Type} [AddCommGroup Γ] [Fintype Γ]
    (hcard : Fintype.card Γ ≤ 2)
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : Multigraph V E) :
    G.FlowGraphConnected Γ := by
  classical
  intro f g
  have hfg : f = g := by
    ext e
    have hf : f.val e ≠ 0 := f.nonzero e
    have hg : g.val e ≠ 0 := g.nonzero e
    by_contra hne
    have h3 : ({0, f.val e, g.val e} : Finset Γ).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
      · simp [hne]
      · simp [hf.symm, hg.symm]
    have hle : ({0, f.val e, g.val e} : Finset Γ).card ≤ Fintype.card Γ :=
      Finset.card_le_univ _
    omega
  subst hfg
  exact Relation.ReflTransGen.refl

/-! ### Section 4: Elementary facts (E1)–(E5) -/

theorem sec4_E1_proved
    {V E Γ : Type} [Fintype E] [DecidableEq V] [AddCommGroup Γ]
    (B : AddSubgroup Γ) (f : E → Γ) (e : E) :
    f e ≠ 0 ↔ (quoFlow B f e ≠ 0 ∨ (quoFlow B f e = 0 ∧ f e ∈ B ∧ f e ≠ 0)) := by
  constructor
  · intro hne
    by_cases hq : quoFlow B f e = 0
    · right
      refine ⟨hq, ?_, hne⟩
      exact (QuotientAddGroup.eq_zero_iff (f e)).mp hq
    · left; exact hq
  · rintro (hq | ⟨_, _, hne⟩)
    · intro h0
      apply hq
      unfold quoFlow
      rw [h0]
      rfl
    · exact hne

theorem sec4_E2_proved
    {V E Γ : Type} [Fintype E] [DecidableEq V] [AddCommGroup Γ]
    (G : Multigraph V E) (B : AddSubgroup Γ) (f : E → Γ) (C : G.DirectedCycle)
    (y : Γ) (hy : y ∈ B) (e : E) :
    quoFlow B (fun e' => f e' + C.sign e' • y) e = quoFlow B f e := by
  unfold quoFlow
  change (QuotientAddGroup.mk' B) (f e + C.sign e • y) = (QuotientAddGroup.mk' B) (f e)
  rw [map_add, map_zsmul]
  have hy0 : (QuotientAddGroup.mk' B) y = 0 := (QuotientAddGroup.eq_zero_iff y).mpr hy
  rw [hy0, smul_zero, add_zero]

theorem sec4_E4_of_E3
    {V E Γ : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] [AddCommGroup Γ]
    (G : Multigraph V E) (B : AddSubgroup Γ) (v : E → Γ ⧸ B) (_hv : G.IsFlow v)
    (hE3 : ∃ (l : List ((Γ ⧸ B) × G.DirectedCycle)),
      ∀ e, v e = (l.map (fun p => p.2.sign e • p.1)).sum) :
    ∃ f : E → Γ, G.IsFlow f ∧ ∀ e, quoFlow B f e = v e := by
  obtain ⟨l, hl⟩ := hE3
  let f : E → Γ := fun e => (l.map (fun p => p.2.sign e • Quotient.out p.1)).sum
  refine ⟨f, ?_, ?_⟩
  · intro u
    have hsum : ∀ (m : List ((Γ ⧸ B) × G.DirectedCycle)),
        G.boundary (fun e => (m.map (fun p => p.2.sign e • Quotient.out p.1)).sum) u = 0 := by
      intro m
      induction m with
      | nil =>
        simp [Multigraph.boundary]
      | cons hd tl ih =>
        simp only [List.map_cons, List.sum_cons]
        rw [boundary_add, sec2_cycle_smul_isFlow_proved G hd.2 (Quotient.out hd.1) u, ih, add_zero]
    exact hsum l
  · intro e
    rw [hl e]
    unfold quoFlow f
    have hmap : ∀ (m : List ((Γ ⧸ B) × G.DirectedCycle)),
        (QuotientAddGroup.mk' B) ((m.map (fun p => p.2.sign e • Quotient.out p.1)).sum) =
          (m.map (fun p => p.2.sign e • p.1)).sum := by
      intro m
      induction m with
      | nil => simp
      | cons hd tl ih =>
        simp only [List.map_cons, List.sum_cons, map_add, map_zsmul]
        rw [ih]
        have hout : (QuotientAddGroup.mk' B) (Quotient.out hd.1) = hd.1 := Quotient.out_eq hd.1
        rw [hout]
    exact hmap l

theorem sec4_E5_proved
    {V E W Γ : Type} [Fintype E] [DecidableEq V] [DecidableEq W] [AddCommGroup Γ]
    (G : Multigraph V E) (q : V → W) (f : E → Γ) (hf : G.IsFlow f) :
    (G.contractBy q).IsFlow (fun e => f e.1) := by
  classical
  intro w
  let U : Finset V := Finset.univ.image G.head ∪ Finset.univ.image G.tail
  have hzero : ∑ u ∈ U.filter (fun u : V => q u = w), G.boundary f u = 0 :=
    Finset.sum_eq_zero fun u _ => hf u
  rw [← hzero]
  unfold Multigraph.boundary Multigraph.contractBy
  simp only [Finset.sum_filter]
  rw [← Finset.sum_sub_distrib]
  have hrhs :
      ∑ u ∈ U, (if q u = w then
        (∑ e : E, if G.head e = u then f e else 0) -
        (∑ e : E, if G.tail e = u then f e else 0)
      else 0) =
      ∑ e : E, ((if q (G.head e) = w then f e else 0) -
                (if q (G.tail e) = w then f e else 0)) := by
    have hsplit : ∀ (g : E → V), (∀ e : E, g e ∈ U) →
        ∑ u ∈ U, (if q u = w then ∑ e : E, if g e = u then f e else 0 else 0) =
        ∑ e : E, if q (g e) = w then f e else 0 := by
      intro g hgU
      calc
        ∑ u ∈ U, (if q u = w then ∑ e : E, if g e = u then f e else 0 else 0)
            = ∑ u ∈ U, ∑ e : E, if q u = w ∧ g e = u then f e else 0 := by
              refine Finset.sum_congr rfl fun u _ => ?_
              by_cases hqu : q u = w <;> simp [hqu]
        _ = ∑ e : E, ∑ u ∈ U, if q u = w ∧ g e = u then f e else 0 := Finset.sum_comm
        _ = ∑ e : E, if q (g e) = w then f e else 0 := by
              refine Finset.sum_congr rfl fun e _ => ?_
              rw [Finset.sum_eq_single (g e)]
              · simp
              · intro u _ hne
                simp [Ne.symm hne]
              · intro hmem; exact absurd (hgU e) hmem
    have hsub :
        ∑ u ∈ U, (if q u = w then
          (∑ e : E, if G.head e = u then f e else 0) -
          (∑ e : E, if G.tail e = u then f e else 0)
        else 0) =
        (∑ u ∈ U, if q u = w then ∑ e : E, if G.head e = u then f e else 0 else 0) -
        (∑ u ∈ U, if q u = w then ∑ e : E, if G.tail e = u then f e else 0 else 0) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun u _ => ?_
      by_cases hqu : q u = w <;> simp [hqu]
    rw [hsub,
        hsplit G.head (fun e => Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ e))),
        hsplit G.tail (fun e => Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ e))),
        ← Finset.sum_sub_distrib]
  rw [hrhs]
  rw [← Fintype.sum_subtype_add_sum_subtype (p := fun e : E => q (G.tail e) ≠ q (G.head e))]
  have hcancel :
      ∑ e : {e : E // ¬ q (G.tail e) ≠ q (G.head e)},
        ((if q (G.head e.1) = w then f e.1 else 0) -
         (if q (G.tail e.1) = w then f e.1 else 0)) = 0 := by
    refine Finset.sum_eq_zero fun e _ => ?_
    have heq : q (G.tail e.1) = q (G.head e.1) := not_not.mp e.2
    rw [heq, sub_self]
  rw [hcancel, add_zero]

theorem sec4_E5_subset_proved
    {V E W Γ : Type} [Fintype E] [DecidableEq V] [DecidableEq W] [DecidableEq E] [AddCommGroup Γ]
    (G : Multigraph V E) (q : V → W) (S : Finset E)
    (hS : ∀ e ∈ S, q (G.tail e) = q (G.head e))
    (f : E → Γ) (hf : G.IsFlow f) :
    Multigraph.IsFlow
      ({ tail := fun e => q (G.tail e.1), head := fun e => q (G.head e.1) } :
        Multigraph W {e : E // e ∉ S})
      (fun e => f e.1) := by
  intro w
  let U : Finset V := Finset.univ.image G.head ∪ Finset.univ.image G.tail
  have hzero : ∑ u ∈ U.filter (fun u : V => q u = w), G.boundary f u = 0 :=
    Finset.sum_eq_zero fun u _ => hf u
  rw [← hzero]
  unfold Multigraph.boundary
  simp only [Finset.sum_filter]
  rw [← Finset.sum_sub_distrib]
  have hrhs :
      ∑ u ∈ U, (if q u = w then
        (∑ e : E, if G.head e = u then f e else 0) -
        (∑ e : E, if G.tail e = u then f e else 0)
      else 0) =
      ∑ e : E, ((if q (G.head e) = w then f e else 0) -
                (if q (G.tail e) = w then f e else 0)) := by
    have hsplit : ∀ (g : E → V), (∀ e : E, g e ∈ U) →
        ∑ u ∈ U, (if q u = w then ∑ e : E, if g e = u then f e else 0 else 0) =
        ∑ e : E, if q (g e) = w then f e else 0 := by
      intro g hgU
      calc
        ∑ u ∈ U, (if q u = w then ∑ e : E, if g e = u then f e else 0 else 0)
            = ∑ u ∈ U, ∑ e : E, if q u = w ∧ g e = u then f e else 0 := by
              refine Finset.sum_congr rfl fun u _ => ?_
              by_cases hqu : q u = w <;> simp [hqu]
        _ = ∑ e : E, ∑ u ∈ U, if q u = w ∧ g e = u then f e else 0 := Finset.sum_comm
        _ = ∑ e : E, if q (g e) = w then f e else 0 := by
              refine Finset.sum_congr rfl fun e _ => ?_
              rw [Finset.sum_eq_single (g e)]
              · simp
              · intro u _ hne
                simp [Ne.symm hne]
              · intro hmem; exact absurd (hgU e) hmem
    have hsub :
        ∑ u ∈ U, (if q u = w then
          (∑ e : E, if G.head e = u then f e else 0) -
          (∑ e : E, if G.tail e = u then f e else 0)
        else 0) =
        (∑ u ∈ U, if q u = w then ∑ e : E, if G.head e = u then f e else 0 else 0) -
        (∑ u ∈ U, if q u = w then ∑ e : E, if G.tail e = u then f e else 0 else 0) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun u _ => ?_
      by_cases hqu : q u = w <;> simp [hqu]
    rw [hsub,
        hsplit G.head (fun e => Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ e))),
        hsplit G.tail (fun e => Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ e))),
        ← Finset.sum_sub_distrib]
  rw [hrhs]
  rw [← Fintype.sum_subtype_add_sum_subtype (p := fun e : E => e ∉ S)]
  have hcancel :
      ∑ e : {e : E // ¬ e ∉ S},
        ((if q (G.head e.1) = w then f e.1 else 0) -
         (if q (G.tail e.1) = w then f e.1 else 0)) = 0 := by
    refine Finset.sum_eq_zero fun e _ => ?_
    have heq : q (G.tail e.1) = q (G.head e.1) := hS e.1 (not_not.mp e.2)
    rw [heq, sub_self]
  rw [hcancel, add_zero]

/-! ### Non-vacuity witnesses -/

theorem nonvacuous_loop_cycle_proved :
    let G : Multigraph Unit Unit := ⟨fun _ => (), fun _ => ()⟩
    (Multigraph.Subgraph.top G).IsCycle ∧ G.IsBridgeless := by
  intro G
  have hcyc : (Multigraph.Subgraph.top G).IsCycle := by
    refine ⟨⟨⟨(), Finset.mem_univ ()⟩, ?_⟩, ?_⟩
    · intro u _ v _
      cases u; cases v
      exact Relation.ReflTransGen.refl
    · intro v _
      cases v
      unfold Multigraph.Subgraph.deg Multigraph.Subgraph.top
      decide
  refine ⟨hcyc, ?_⟩
  intro e hbr
  exact hbr ⟨Multigraph.Subgraph.top G, hcyc, Finset.mem_univ e⟩

end Flow.Proofs
