module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Flow.Defs.Literature
public import Flow.Proofs.Elementary
public import Flow.Proofs.Basic
public import Flow.Proofs.SmallClaims
public import Flow.Proofs.MasterHelpers
public import Flow.Proofs.LiftMove
public import Flow.Proofs.PathAndSub
public import Mathlib.Tactic

@[expose] public section

/-!
# Section 4 proofs (Part 4): Master theorem (`thm_1_3_of`)
-/

namespace Flow.Proofs

open Flow

/-! ### Helper bundle for Section 3 inputs used in the `(SUB)` branch of Theorem 1.3 -/

structure Sec3Bundle (hJLPT : JLPTWellColouring) : Prop where
  aux_exists : ∀ {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : Multigraph V E} {H : G.Subgraph} (sub : SubdivisionData G H),
    ∃ (flip : E → Bool), (∀ e, e ∉ H.edges → flip e = false) ∧
      ∃ (H' : (G.reorient flip).Subgraph) (sub' : SubdivisionData (G.reorient flip) H'),
        H'.verts = H.verts ∧ H'.edges = H.edges ∧
        Nonempty (AuxGraphData (G.reorient flip) H' sub')
  frame_exists : ∀ {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : Multigraph V E} {H : G.Subgraph} (sub : SubdivisionData G H)
    (aux : AuxGraphData G H sub), Nonempty (Frame G H sub aux)
  lem_3_6_a_cyc : ∀ {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : Multigraph V E} {H : G.Subgraph} (sub : SubdivisionData G H)
    (aux : AuxGraphData G H sub) (O : H.toMultigraph.DirectedCycle) (t : sub.E₀),
    ∃ s : ℤ, (s = 1 ∨ s = 0 ∨ s = -1) ∧
      ∀ e (he : e ∈ (sub.thread t).edges), O.sign ⟨e, (sub.thread t).edges_sub e he⟩ = s
  lem_3_6_c_surj : ∀ {V E A : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    [AddCommGroup A] {G : Multigraph V E} {H : G.Subgraph} (sub : SubdivisionData G H)
    (aux : AuxGraphData G H sub) (h : {e // e ∈ H.edges} → A), H.toMultigraph.IsFlow h →
    ∃ Y : aux.EQ → A, aux.Q.IsFlow Y ∧ ∀ e : {e // e ∈ H.edges}, aux.pi Y e.1 = h e
  lem_3_6_d : ∀ {V E A : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    [AddCommGroup A] {G : Multigraph V E} {H : G.Subgraph} (sub : SubdivisionData G H)
    (aux : AuxGraphData G H sub) (C : aux.Q.DirectedCycle),
    ∃ (cycles : List G.DirectedCycle),
      (∀ O ∈ cycles, O.sub ≤ H) ∧
      (∀ i j (hi : i < cycles.length) (hj : j < cycles.length), i ≠ j →
        Disjoint (cycles[i]'hi).sub.edges (cycles[j]'hj).sub.edges) ∧
      (∀ (x : A) (e : E),
        aux.pi (fun eq => C.sign eq • x) e =
          (cycles.map (fun O => O.sign e • x)).sum)
  lem_3_11 : ∀ {V E A : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    [AddCommGroup A] {G : Multigraph V E} {H : G.Subgraph} {sub : SubdivisionData G H}
    {aux : AuxGraphData G H sub} (fr : Frame G H sub aux),
    (∀ g : Fin fr.numNodes → aux.EQ, (∀ i, g i = fr.eNode i ∨ g i = fr.fNode i) →
      (∀ b : Fin aux.numBlocks,
        let Vb := Finset.univ.filter (fun v => aux.comp v = b)
        (Multigraph.Subgraph.ofEdges aux.Q Vb
          ((fr.Tg g).edges.filter (fun e => aux.Q.tail e ∈ Vb ∧ aux.Q.head e ∈ Vb))
          (fun he => (Finset.mem_filter.mp he).2.1)
          (fun he => (Finset.mem_filter.mp he).2.2)).Connected) ∧
      (∀ i : Fin fr.numNodes,
        (Multigraph.Subgraph.ofEdges aux.Q (fr.op1V i)
          ((fr.Tg g).edges.filter (fun e => aux.Q.tail e ∈ fr.op1V i ∧ aux.Q.head e ∈ fr.op1V i))
          (fun he => (Finset.mem_filter.mp he).2.1)
          (fun he => (Finset.mem_filter.mp he).2.2)).Connected ∧
        (Multigraph.Subgraph.ofEdges aux.Q (fr.op2V i)
          ((fr.Tg g).edges.filter (fun e => aux.Q.tail e ∈ fr.op2V i ∧ aux.Q.head e ∈ fr.op2V i))
          (fun he => (Finset.mem_filter.mp he).2.1)
          (fun he => (Finset.mem_filter.mp he).2.2)).Connected)) ∧
    (∀ i : Fin fr.numNodes, ∃! C : aux.Q.DirectedCycle, fr.IsOfficialCycle i C) ∧
    (∀ (C : Fin fr.numNodes → aux.Q.DirectedCycle), (∀ i, fr.IsOfficialCycle i (C i)) →
      (∀ i, fr.eNode i ∈ (C i).sub.edges ∧ fr.fNode i ∈ (C i).sub.edges) ∧
      (∀ l i : Fin fr.numNodes, l < i → fr.eNode i ∉ (C l).sub.edges ∧ fr.fNode i ∉ (C l).sub.edges) ∧
      (∀ l i : Fin fr.numNodes, i < l → fr.fNode i ∉ (C l).sub.edges) ∧
      (∀ Y : aux.EQ → A, aux.Q.IsFlow Y →
        ∃! x : Fin fr.numNodes → A, ∀ eq, Y eq = ∑ i : Fin fr.numNodes, (C i).sign eq • x i)) ∧
    (fr.HProtected.Connected ∧
      (∀ v ∈ H.verts, (∀ t : sub.E₀, fr.IsFree t →
        ¬ (v ∈ (sub.thread t).verts ∧ v ≠ sub.embedV (sub.H₀.tail t) ∧ v ≠ sub.embedV (sub.H₀.head t))) →
        v ∈ fr.HProtected.verts) ∧
      (∀ eps : sub.E₀, fr.IsFree eps →
        ∃ D : G.DirectedCycle,
          D.sub ≤ H ∧
          (∀ e ∈ (sub.thread eps).edges, e ∈ D.sub.edges ∧ D.sign e = 1) ∧
          (∀ t : sub.E₀, fr.IsFree t → t ≠ eps →
            ∀ e ∈ (sub.thread t).edges, e ∉ D.sub.edges)))
  def_3_12 : ∀ {V E Γ : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    [AddCommGroup Γ] (B : AddSubgroup Γ) [DecidableEq (Γ ⧸ B)]
    {G : Multigraph V E} {H : G.Subgraph} {sub : SubdivisionData G H}
    {aux : AuxGraphData G H sub} (fr : Frame G H sub aux)
    (f : G.NZFlow Γ), IsHGoodSub fr B f →
    (∀ t : aux.EQ, ((LamOfFlow B fr f).list t).card ≤ 3) ∧
    (0 : aux.EQ → Γ ⧸ B) ∈ PLam (LamOfFlow B fr f) ∧
    (∀ Y : aux.EQ → Γ ⧸ B, aux.Q.IsFlow Y →
      (Y ∈ PLam (LamOfFlow B fr f) ↔
        ∀ t : sub.E₀, fr.IsProtected t → ∀ e ∈ (sub.thread t).edges,
          quoFlow B f.val e + aux.pi Y e ≠ 0))

/-! ### Elementary graph/flow utilities for the Master Theorem induction -/

/-- Symmetry of `SigmaJoined` for a symmetric step system. -/
lemma sigmaJoined_symm {V E Γ : Type} [Fintype E] [DecidableEq V] [DecidableEq E]
    [AddCommGroup Γ] {G : Multigraph V E} {Sig : StepSystem Γ} {f g : G.NZFlow Γ}
    (h : G.SigmaJoined Sig.carrier f g) : G.SigmaJoined Sig.carrier g f := by
  induction h with
  | refl => exact .refl
  | @tail a b _ hstep ih =>
    rcases hstep with ⟨C, lam, hlam, heq⟩
    have hrev : G.SigmaMove Sig.carrier b a :=
      ⟨C, -lam, Sig.neg_mem hlam, fun e => by rw [heq e, smul_neg, add_neg_cancel_right]⟩
    exact Relation.ReflTransGen.head hrev ih

/-- Reorientation preserves `SigmaJoined`. -/
lemma reorient_sigmaJoined {V E Γ : Type} [Fintype E] [DecidableEq V] [DecidableEq E]
    [AddCommGroup Γ] (G : Multigraph V E) (flip : E → Bool) (Sig : StepSystem Γ)
    {f g : G.NZFlow Γ}
    {f' g' : (G.reorient flip).NZFlow Γ}
    (hf' : ∀ e, f'.val e = Multigraph.reorientVal flip f.val e)
    (hg' : ∀ e, g'.val e = Multigraph.reorientVal flip g.val e)
    (hjoin : (G.reorient flip).SigmaJoined Sig.carrier f' g') :
    G.SigmaJoined Sig.carrier f g := by
  have hmk : ∀ a' : (G.reorient flip).NZFlow Γ,
      ∃ a : G.NZFlow Γ, ∀ e, a.val e = Multigraph.reorientVal flip a'.val e := by
    intro a'
    refine ⟨⟨Multigraph.reorientVal flip a'.val, ?_, ?_⟩, fun _ => rfl⟩
    · rw [← reorient_isFlow_iff G flip]
      have hfun : Multigraph.reorientVal flip (Multigraph.reorientVal flip a'.val) = a'.val :=
        funext (reorientVal_reorientVal flip a'.val)
      rw [hfun]; exact a'.isFlow
    · intro e
      unfold Multigraph.reorientVal
      split_ifs
      · exact neg_ne_zero.mpr (a'.nonzero e)
      · exact a'.nonzero e
  have hstep_rev : ∀ a' b' : (G.reorient flip).NZFlow Γ,
      (G.reorient flip).SigmaMove Sig.carrier a' b' →
      ∀ a b : G.NZFlow Γ,
        (∀ e, a.val e = Multigraph.reorientVal flip a'.val e) →
        (∀ e, b.val e = Multigraph.reorientVal flip b'.val e) →
        G.SigmaMove Sig.carrier a b := by
    rintro a' b' ⟨C', lam, hlam, heq⟩ a b ha hb
    let C : G.DirectedCycle :=
      reorient_reorient G flip ▸ reorientDirectedCycle (G.reorient flip) flip C'
    refine ⟨C, lam, hlam, fun e => ?_⟩
    have hCsign : C.sign e = Multigraph.reorientVal flip C'.sign e := by
      dsimp only [C]
      have hrr := reorient_reorient G flip
      -- Transport sign across Eq.rec on Multigraph
      have htrans : ∀ {G₁ G₂ : Multigraph V E} (he : G₁ = G₂) (D : G₁.DirectedCycle) (e : E),
          (he ▸ D).sign e = D.sign e := by
        intro G₁ G₂ he D e; subst he; rfl
      rw [htrans hrr]
      rfl
    rw [hb e, ha e, hCsign]
    unfold Multigraph.reorientVal
    rw [heq e]
    cases flip e <;> simp <;> abel
  have hgen : ∀ b' : (G.reorient flip).NZFlow Γ,
      (G.reorient flip).SigmaJoined Sig.carrier f' b' →
      ∀ b : G.NZFlow Γ, (∀ e, b.val e = Multigraph.reorientVal flip b'.val e) →
        G.SigmaJoined Sig.carrier f b := by
    intro b' hrtg
    induction hrtg with
    | refl =>
      intro b hb
      have hfb : f = b := by
        ext e
        rw [hb e]
        unfold Multigraph.reorientVal
        rw [hf' e]
        unfold Multigraph.reorientVal
        cases flip e <;> simp
      rw [hfb]; exact .refl
    | @tail a' b' _ hstep ih =>
      intro b hb
      obtain ⟨a, ha⟩ := hmk a'
      exact (ih a ha).tail (hstep_rev a' b' hstep a b ha hb)
  exact hgen g' hjoin g fun e => by
    unfold Multigraph.reorientVal
    rw [hg' e]
    unfold Multigraph.reorientVal
    cases flip e <;> simp

/-- Contraction `G.contractSubgraph H` sends flows of `G` (by restriction) to flows of `G / H`. -/
lemma contractSubgraph_isFlow {V E Γ : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    [AddCommGroup Γ] (G : Multigraph V E) (H : G.Subgraph) (x : E → Γ) (hx : G.IsFlow x) :
    (G.contractSubgraph H).IsFlow (fun e => x e.1) := by
  intro w
  let q : V → Option {v : V // v ∉ H.verts} := fun v => if hv : v ∈ H.verts then none else some ⟨v, hv⟩
  have hcb := sec4_E5_proved G q x hx w
  trans ((G.contractBy q).boundary (fun e => x e.1) w)
  · rw [boundary_eq_sum_ite, boundary_eq_sum_ite]
    -- Non-loop edges of G.contractSubgraph H match G.contractBy q; loops at none cancel!
    have hsub : ∀ e : {e : E // e ∉ H.edges},
        (if (G.contractSubgraph H).head e = w then x e.1 else 0) -
        (if (G.contractSubgraph H).tail e = w then x e.1 else 0) =
        if q (G.tail e.1) ≠ q (G.head e.1) then
          (if q (G.head e.1) = w then x e.1 else 0) - (if q (G.tail e.1) = w then x e.1 else 0)
        else 0 := by
      intro e
      have ht : (G.contractSubgraph H).tail e = q (G.tail e.1) := rfl
      have hh : (G.contractSubgraph H).head e = q (G.head e.1) := rfl
      rw [ht, hh]
      by_cases hne : q (G.tail e.1) ≠ q (G.head e.1)
      · rw [if_pos hne]
      · rw [if_neg hne]
        have heq : q (G.tail e.1) = q (G.head e.1) := not_not.mp hne
        rw [heq, sub_self]
    simp_rw [hsub]
    rw [← Finset.sum_filter]
    symm
    refine Finset.sum_bij (fun e _ => (⟨e.1, fun hH => e.2 (by
        have h1 := H.tail_mem hH; have h2 := H.head_mem hH; simp [q, h1, h2])⟩ : {e : E // e ∉ H.edges}))
      (fun e _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, e.2⟩)
      (fun _ _ _ _ h => Subtype.ext (congrArg (fun x : {e : E // e ∉ H.edges} => x.1) h))
      (fun e he => ⟨⟨e.1, (Finset.mem_filter.mp he).2⟩, Finset.mem_univ _, rfl⟩)
      (fun _ _ => rfl)
  · exact hcb

/-- Every cycle of a bridgeless graph gives a non-zero integer flow through `e`, hence
`G.contractSubgraph H` is bridgeless whenever `G` is bridgeless. -/
lemma contractSubgraph_isBridgeless {V E : Type} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (G : Multigraph V E) (hbr : G.IsBridgeless) (H : G.Subgraph) :
    (G.contractSubgraph H).IsBridgeless := by
  intro e hnot
  by_cases hloop : (G.contractSubgraph H).tail e = (G.contractSubgraph H).head e
  · let C := directedCycleOfLoop (G.contractSubgraph H) e hloop
    exact hnot ⟨C.sub, C.isCycle, Finset.mem_singleton_self e⟩
  · -- Find a cycle of G through e.1; direct it, restrict to G / H, decompose via Lemma 2.1(b)!
    have hex : ∃ C : G.Subgraph, C.IsCycle ∧ e.1 ∈ C.edges := by
      by_contra h; exact hbr e.1 h
    rcases hex with ⟨C, hC, heC⟩
    obtain ⟨DC, hDCle⟩ := exists_directedCycle_of_no_deg_one C ⟨e.1, heC⟩
      (fun v hv => by rw [hC.2 v hv]; decide)
    -- Since DC.sub ≤ C and both are cycles, DC.sub = C
    have hDC_eq : DC.sub = C := by
      have hverts : DC.sub.verts = C.verts := by
        apply Finset.Subset.antisymm hDCle.1
        intro w hw
        obtain ⟨v₀, hv₀⟩ := DC.isCycle.1.1
        have hpath := hC.1.2 v₀ (hDCle.1 hv₀) w hw
        clear hw
        induction hpath with
        | refl => exact hv₀
        | @tail u z _ hs ih =>
          rcases hs with ⟨e', he', ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
          · have hdeg : DC.sub.deg u = C.deg u := by rw [DC.isCycle.2 u ih, hC.2 u (hDCle.1 ih)]
            have ht_sub := Finset.filter_subset_filter (fun e'' => G.tail e'' = u) hDCle.2
            have hh_sub := Finset.filter_subset_filter (fun e'' => G.head e'' = u) hDCle.2
            have ht_le := Finset.card_le_card ht_sub
            have hh_le := Finset.card_le_card hh_sub
            unfold Multigraph.Subgraph.deg at hdeg
            have ht_eq := Finset.eq_of_subset_of_card_le ht_sub (by omega)
            have hmem : e' ∈ C.edges.filter (fun e'' => G.tail e'' = u) := Finset.mem_filter.mpr ⟨he', h1⟩
            rw [← ht_eq] at hmem
            simpa [h2] using DC.sub.head_mem (Finset.mem_filter.mp hmem).1
          · have hdeg : DC.sub.deg u = C.deg u := by rw [DC.isCycle.2 u ih, hC.2 u (hDCle.1 ih)]
            have ht_sub := Finset.filter_subset_filter (fun e'' => G.tail e'' = u) hDCle.2
            have hh_sub := Finset.filter_subset_filter (fun e'' => G.head e'' = u) hDCle.2
            have ht_le := Finset.card_le_card ht_sub
            have hh_le := Finset.card_le_card hh_sub
            unfold Multigraph.Subgraph.deg at hdeg
            have hh_eq := Finset.eq_of_subset_of_card_le hh_sub (by omega)
            have hmem : e' ∈ C.edges.filter (fun e'' => G.head e'' = u) := Finset.mem_filter.mpr ⟨he', h2⟩
            rw [← hh_eq] at hmem
            simpa [h1] using DC.sub.tail_mem (Finset.mem_filter.mp hmem).1
      have hedges : DC.sub.edges = C.edges := by
        apply Finset.Subset.antisymm hDCle.2
        intro e' he'
        have huC := C.tail_mem he'
        have huD : G.tail e' ∈ DC.sub.verts := hverts ▸ huC
        have hdeg : DC.sub.deg (G.tail e') = C.deg (G.tail e') := by rw [DC.isCycle.2 _ huD, hC.2 _ huC]
        have ht_sub := Finset.filter_subset_filter (fun e'' => G.tail e'' = G.tail e') hDCle.2
        have hh_sub := Finset.filter_subset_filter (fun e'' => G.head e'' = G.tail e') hDCle.2
        have ht_le := Finset.card_le_card ht_sub
        have hh_le := Finset.card_le_card hh_sub
        unfold Multigraph.Subgraph.deg at hdeg
        have ht_eq := Finset.eq_of_subset_of_card_le ht_sub (by omega)
        have hmem : e' ∈ C.edges.filter (fun e'' => G.tail e'' = G.tail e') := Finset.mem_filter.mpr ⟨he', rfl⟩
        rw [← ht_eq] at hmem
        exact (Finset.mem_filter.mp hmem).1
      ext x
      · simp [hverts]
      · simp [hedges]
    have hfl : (G.contractSubgraph H).IsFlow (fun e' => DC.sign e'.1) :=
      contractSubgraph_isFlow G H DC.sign DC.isFlow
    obtain ⟨cycles, hsum, _, _, _, _⟩ := lem_2_1_b (G.contractSubgraph H) (fun e' => DC.sign e'.1) hfl
    have hne0 : DC.sign e.1 ≠ 0 := by
      rcases DC.sign_mem (hDC_eq ▸ heC) with h | h <;> omega
    have hex_D : ∃ D ∈ cycles, e ∈ D.sub.edges := by
      by_contra hall
      push Not at hall
      have h0 : (cycles.map (fun D => D.sign e)).sum = 0 := by
        apply List.sum_eq_zero
        intro x hx; rw [List.mem_map] at hx; rcases hx with ⟨D, hD, rfl⟩
        exact D.sign_zero (hall D hD)
      rw [hsum e, h0] at hne0
      exact hne0 rfl
    rcases hex_D with ⟨D, _, heD⟩
    exact hnot ⟨D.sub, D.isCycle, heD⟩

/-- Deleting loops preserves bridgelessness and flows. -/
lemma deleteLoops_isBridgeless {V E : Type} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (G : Multigraph V E) (hbr : G.IsBridgeless) :
    G.deleteLoops.IsBridgeless := by
  intro e hnot
  have hex : ∃ C : G.Subgraph, C.IsCycle ∧ e.1 ∈ C.edges := by
    by_contra h; exact hbr e.1 h
  rcases hex with ⟨C, hC, heC⟩
  -- No edge of C can be a loop (since e.1 ∈ C.edges is not a loop, so C has ≥ 2 vertices and is connected,
  -- whereas a loop at v already contributes 2 to C.deg v leaving no room for any edge to another vertex)
  have hno_loop : ∀ e' ∈ C.edges, G.tail e' ≠ G.head e' := by
    intro e' he' hlp
    have hv : G.tail e' ∈ C.verts := C.tail_mem he'
    have hdeg2 := hC.2 (G.tail e') hv
    -- e' contributes 1 to tail-filter and 1 to head-filter, so C.edges at tail e' = {e'}
    have ht1 : 1 ≤ (C.edges.filter (fun x => G.tail x = G.tail e')).card :=
      Finset.card_pos.mpr ⟨e', Finset.mem_filter.mpr ⟨he', rfl⟩⟩
    have hh1 : 1 ≤ (C.edges.filter (fun x => G.head x = G.tail e')).card :=
      Finset.card_pos.mpr ⟨e', Finset.mem_filter.mpr ⟨he', hlp.symm⟩⟩
    unfold Multigraph.Subgraph.deg at hdeg2
    have hteq : C.edges.filter (fun x => G.tail x = G.tail e') = {e'} :=
      (Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_filter.mpr ⟨he', rfl⟩, fun x hx => by
        have hc : (C.edges.filter (fun y => G.tail y = G.tail e')).card = 1 := by omega
        obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hc
        have h1 : x = y := Finset.mem_singleton.mp (hy ▸ hx)
        have h2 : e' = y := Finset.mem_singleton.mp (hy ▸ Finset.mem_filter.mpr ⟨he', rfl⟩)
        exact h1.trans h2.symm⟩)
    have hheq : C.edges.filter (fun x => G.head x = G.tail e') = {e'} :=
      (Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_filter.mpr ⟨he', hlp.symm⟩, fun x hx => by
        have hc : (C.edges.filter (fun y => G.head y = G.tail e')).card = 1 := by omega
        obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hc
        have h1 : x = y := Finset.mem_singleton.mp (hy ▸ hx)
        have h2 : e' = y := Finset.mem_singleton.mp (hy ▸ Finset.mem_filter.mpr ⟨he', hlp.symm⟩)
        exact h1.trans h2.symm⟩)
    -- Every vertex reachable from G.tail e' in C must equal G.tail e'
    have hstay : ∀ u, Relation.ReflTransGen C.Adj (G.tail e') u → u = G.tail e' := by
      intro u hu
      induction hu with
      | refl => rfl
      | tail _ hs ih =>
        subst ih
        rcases hs with ⟨x, hxC, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
        · have hx : x = e' := Finset.mem_singleton.mp (hteq ▸ Finset.mem_filter.mpr ⟨hxC, h1⟩)
          subst hx; exact h2.symm.trans hlp.symm
        · have hx : x = e' := Finset.mem_singleton.mp (hheq ▸ Finset.mem_filter.mpr ⟨hxC, h2⟩)
          subst hx; exact h1.symm
    have ht_eq := hstay (G.tail e.1) (hC.1.2 _ hv _ (C.tail_mem heC))
    have hh_eq := hstay (G.head e.1) (hC.1.2 _ hv _ (C.head_mem heC))
    exact e.2 (ht_eq.trans hh_eq.symm)
  let C' : G.deleteLoops.Subgraph :=
    { verts := C.verts
      edges := Finset.univ.filter (fun x : {x : E // G.tail x ≠ G.head x} => x.1 ∈ C.edges)
      tail_mem := fun hx => C.tail_mem (Finset.mem_filter.mp hx).2
      head_mem := fun hx => C.head_mem (Finset.mem_filter.mp hx).2 }
  refine hnot ⟨C', ⟨⟨hC.1.1, fun u hu v hv => ?_⟩, fun v hv => ?_⟩,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, heC⟩⟩
  · have hpath := hC.1.2 u hu v hv
    clear hv
    induction hpath with
    | refl => exact .refl
    | tail _ hs ih =>
      rcases hs with ⟨x, hxC, hinc⟩
      exact ih.tail ⟨⟨x, hno_loop x hxC⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxC⟩, hinc⟩
  · have hd := hC.2 v hv
    unfold Multigraph.Subgraph.deg at hd ⊢
    have h1 : (C'.edges.filter (fun x => G.deleteLoops.tail x = v)).card =
        (C.edges.filter (fun x => G.tail x = v)).card := by
      refine Finset.card_bij (fun x _ => x.1) (fun x hx => ?_) (fun _ _ _ _ h => Subtype.ext h)
        (fun x hx => ⟨⟨x, hno_loop x (Finset.mem_filter.mp hx).1⟩, ?_, rfl⟩)
      · rw [Finset.mem_filter] at hx ⊢
        exact ⟨(Finset.mem_filter.mp hx.1).2, hx.2⟩
      · rw [Finset.mem_filter] at hx ⊢
        exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx.1⟩, hx.2⟩
    have h2 : (C'.edges.filter (fun x => G.deleteLoops.head x = v)).card =
        (C.edges.filter (fun x => G.head x = v)).card := by
      refine Finset.card_bij (fun x _ => x.1) (fun x hx => ?_) (fun _ _ _ _ h => Subtype.ext h)
        (fun x hx => ⟨⟨x, hno_loop x (Finset.mem_filter.mp hx).1⟩, ?_, rfl⟩)
      · rw [Finset.mem_filter] at hx ⊢
        exact ⟨(Finset.mem_filter.mp hx.1).2, hx.2⟩
      · rw [Finset.mem_filter] at hx ⊢
        exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx.1⟩, hx.2⟩
    rw [h1, h2]; exact hd

/-- Every flow `x` supported on a subgraph `H` restricts to a flow of `H.toMultigraph`. -/
lemma restrict_isFlow_of_supp_sub {V E A : Type} [Fintype E] [DecidableEq V] [AddCommGroup A]
    {G : Multigraph V E} (H : G.Subgraph) (x : E → A) (hx : G.IsFlow x)
    (hsupp : ∀ e, e ∉ H.edges → x e = 0) :
    H.toMultigraph.IsFlow (fun e => x e.1) := by
  intro v
  have hbd := hx v.1
  trans (G.boundary x v.1)
  · rw [boundary_eq_sum_ite, boundary_eq_sum_ite]
    symm
    rw [← Finset.sum_subset (Finset.subset_univ H.edges)]
    · refine Finset.sum_bij (fun e he => ⟨e, he⟩) (fun _ _ => Finset.mem_univ _)
        (fun _ _ _ _ h => congrArg Subtype.val h) (fun e _ => ⟨e.1, e.2, rfl⟩) (fun e _ => ?_)
      by_cases h1 : G.head e = v.1 <;> by_cases h2 : G.tail e = v.1 <;>
        simp [Multigraph.Subgraph.toMultigraph, Subtype.ext_iff, h1, h2]
    · intro e _ hnot
      simp [hsupp e hnot]
  · exact hbd

/-- Lift a directed cycle from `H.toMultigraph` back to `G` (staying inside `H`). -/
private def liftDCFromSub {V E : Type} [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : Multigraph V E) (H : G.Subgraph) (C : H.toMultigraph.DirectedCycle) : G.DirectedCycle where
  sub :=
    { verts := C.sub.verts.map ⟨Subtype.val, Subtype.val_injective⟩
      edges := C.sub.edges.map ⟨Subtype.val, Subtype.val_injective⟩
      tail_mem := fun he => by
        rw [Finset.mem_map] at he; rcases he with ⟨e', he', rfl⟩
        exact Finset.mem_map.mpr ⟨H.toMultigraph.tail e', C.sub.tail_mem he', rfl⟩
      head_mem := fun he => by
        rw [Finset.mem_map] at he; rcases he with ⟨e', he', rfl⟩
        exact Finset.mem_map.mpr ⟨H.toMultigraph.head e', C.sub.head_mem he', rfl⟩ }
  isCycle := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · obtain ⟨v, hv⟩ := C.isCycle.1.1
      exact ⟨v.1, Finset.mem_map.mpr ⟨v, hv, rfl⟩⟩
    · intro u hu v hv
      rw [Finset.mem_map] at hu hv
      rcases hu with ⟨u', hu', rfl⟩; rcases hv with ⟨v', hv', rfl⟩
      have hrtg := C.isCycle.1.2 u' hu' v' hv'
      clear hv'
      induction hrtg with
      | refl => exact .refl
      | tail _ hs ih =>
        rcases hs with ⟨e', he', ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
        · exact ih.tail ⟨e'.1, Finset.mem_map.mpr ⟨e', he', rfl⟩,
            Or.inl ⟨congrArg Subtype.val h1, congrArg Subtype.val h2⟩⟩
        · exact ih.tail ⟨e'.1, Finset.mem_map.mpr ⟨e', he', rfl⟩,
            Or.inr ⟨congrArg Subtype.val h1, congrArg Subtype.val h2⟩⟩
    · intro v hv
      simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at hv
      rcases hv with ⟨v', hv', rfl⟩
      have hd := C.isCycle.2 v' hv'
      unfold Multigraph.Subgraph.deg at hd ⊢
      have h1 : ((C.sub.edges.map ⟨Subtype.val, Subtype.val_injective⟩).filter (fun e => G.tail e = v'.1)).card =
          (C.sub.edges.filter (fun e => H.toMultigraph.tail e = v')).card := by
        refine Finset.card_bij (fun e he => ⟨e, ?_⟩) (fun e he => ?_)
          (fun _ _ _ _ h => congrArg Subtype.val h) (fun e' he' => ⟨e'.1, ?_, rfl⟩)
        · have hm := (Finset.mem_filter.mp he).1
          simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at hm
          rcases hm with ⟨e', _, rfl⟩; exact e'.2
        · rw [Finset.mem_filter] at he ⊢
          simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at he
          rcases he.1 with ⟨e', he', hval⟩
          have heq : e' = ⟨e, hval ▸ e'.2⟩ := Subtype.ext hval
          exact ⟨heq ▸ he', Subtype.ext he.2⟩
        · rw [Finset.mem_filter] at he' ⊢
          exact ⟨Finset.mem_map.mpr ⟨e', he'.1, rfl⟩, congrArg Subtype.val he'.2⟩
      have h2 : ((C.sub.edges.map ⟨Subtype.val, Subtype.val_injective⟩).filter (fun e => G.head e = v'.1)).card =
          (C.sub.edges.filter (fun e => H.toMultigraph.head e = v')).card := by
        refine Finset.card_bij (fun e he => ⟨e, ?_⟩) (fun e he => ?_)
          (fun _ _ _ _ h => congrArg Subtype.val h) (fun e' he' => ⟨e'.1, ?_, rfl⟩)
        · have hm := (Finset.mem_filter.mp he).1
          simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at hm
          rcases hm with ⟨e', _, rfl⟩; exact e'.2
        · rw [Finset.mem_filter] at he ⊢
          simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at he
          rcases he.1 with ⟨e', he', hval⟩
          have heq : e' = ⟨e, hval ▸ e'.2⟩ := Subtype.ext hval
          exact ⟨heq ▸ he', Subtype.ext he.2⟩
        · rw [Finset.mem_filter] at he' ⊢
          exact ⟨Finset.mem_map.mpr ⟨e', he'.1, rfl⟩, congrArg Subtype.val he'.2⟩
      rw [h1, h2]; exact hd
  sign := fun e => if h : e ∈ H.edges then C.sign ⟨e, h⟩ else 0
  sign_mem := fun {e} he => by
    simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at he
    rcases he with ⟨e', he', rfl⟩
    simp only [e'.2, ↓reduceDIte]
    exact C.sign_mem he'
  sign_zero := fun {e} he => by
    by_cases hH : e ∈ H.edges
    · simp only [hH, ↓reduceDIte]
      exact C.sign_zero fun hmem => he (Finset.mem_map.mpr ⟨⟨e, hH⟩, hmem, rfl⟩)
    · simp [hH]
  isFlow := fun v => by
    by_cases hv : v ∈ H.verts
    · have hbd := C.isFlow ⟨v, hv⟩
      trans (H.toMultigraph.boundary C.sign ⟨v, hv⟩)
      · rw [boundary_eq_sum_ite, boundary_eq_sum_ite]
        rw [← Finset.sum_subset (Finset.subset_univ H.edges)]
        · refine Finset.sum_bij (fun e he => ⟨e, he⟩) (fun _ _ => Finset.mem_univ _)
            (fun _ _ _ _ h => congrArg Subtype.val h) (fun e _ => ⟨e.1, e.2, rfl⟩) (fun e he => ?_)
          rw [dif_pos he]
          by_cases h1 : G.head e = v <;> by_cases h2 : G.tail e = v <;>
            simp [Multigraph.Subgraph.toMultigraph, Subtype.ext_iff, h1, h2]
        · intro e _ hnot
          rw [dif_neg hnot]; simp
      · exact hbd
    · rw [boundary_eq_sum_ite]
      refine Finset.sum_eq_zero fun e _ => ?_
      by_cases he : e ∈ H.edges
      · have ht : G.tail e ≠ v := fun h => hv (h ▸ H.tail_mem he)
        have hh : G.head e ≠ v := fun h => hv (h ▸ H.head_mem he)
        simp [ht, hh]
      · simp [he]

/-- Adding a `B`-flow supported on `H` to `f` when `quoFlow B f` is already nowhere zero on `H`
via `Sig.sigB B` steps (from `CondR2` with `X = ∅`). -/
private lemma join_B_diff_on_subgraph
    {Γ : Type} [AddCommGroup Γ] [Fintype Γ] [DecidableEq Γ]
    (B : AddSubgroup Γ) [Fintype B] [DecidableEq B]
    (Sig : StepSystem Γ) (hR2 : CondR2 B Sig)
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : Multigraph V E) (H : G.Subgraph)
    (f h : G.NZFlow Γ)
    (hquo : ∀ e, quoFlow B f.val e = quoFlow B h.val e)
    (hquo_nz : ∀ e, quoFlow B h.val e ≠ 0)
    (hout : ∀ e, e ∉ H.edges → f.val e = h.val e) :
    G.SigmaJoined Sig.carrier f h := by
  -- Difference d(e) = h(e) - f(e) lies in B and is supported on H.edges
  have hd_inB : ∀ e, h.val e - f.val e ∈ B := fun e => by
    have heq : (QuotientAddGroup.mk' B) (h.val e - f.val e) = 0 := by
      rw [map_sub, sub_eq_zero]; exact (hquo e).symm
    exact (QuotientAddGroup.eq_zero_iff _).mp heq
  let dB : {e : E // e ∈ H.edges} → B := fun e => ⟨h.val e.1 - f.val e.1, hd_inB e.1⟩
  have hdB_flow : H.toMultigraph.IsFlow dB := by
    have hflG : G.IsFlow (fun e => h.val e - f.val e) := isFlow_sub h.isFlow f.isFlow
    have hflH := restrict_isFlow_of_supp_sub H _ hflG (fun e he => by rw [hout e he, sub_self])
    intro v
    have hv := hflH v
    apply Subtype.ext
    change ((H.toMultigraph.boundary dB v : B) : Γ) = 0
    unfold Multigraph.boundary at hv ⊢
    push_cast
    exact hv
  obtain ⟨T₀, hT₀⟩ := exists_spanningForest H.toMultigraph
  obtain ⟨l, hl⟩ := (lem_2_1_a (A := B) H.toMultigraph T₀ hT₀).2.2 dB hdB_flow
  -- Walk a single cycle (y : B) • χ_{liftDCFromSub G H C} via CondR2 ∅
  have hwalk_one : ∀ (cur : G.NZFlow Γ) (hcur_q : ∀ e, quoFlow B cur.val e = quoFlow B h.val e)
      (C : G.DirectedCycle) (y : B),
      ∃ nxt : G.NZFlow Γ,
        G.SigmaJoined Sig.carrier cur nxt ∧
        (∀ e, nxt.val e = cur.val e + C.sign e • (y : Γ)) ∧
        (∀ e, quoFlow B nxt.val e = quoFlow B h.val e) := by
    intro cur hcur_q C y
    obtain ⟨_, _, hrtg⟩ := hR2 ∅ (by simp) 0 y (Finset.notMem_empty _) (Finset.notMem_empty _)
    have hgo : ∀ z : B,
        Relation.ReflTransGen (fun u v => u ∈ {b : B | b ∉ (∅ : Finset B)} ∧
          v ∈ {b : B | b ∉ (∅ : Finset B)} ∧ ∃ s ∈ Sig.sigB B, v = u + s) 0 z →
        ∃ nxt : G.NZFlow Γ,
          G.SigmaJoined Sig.carrier cur nxt ∧
          (∀ e, nxt.val e = cur.val e + C.sign e • (z : Γ)) ∧
          (∀ e, quoFlow B nxt.val e = quoFlow B h.val e) := by
      intro z hz
      induction hz with
      | refl => exact ⟨cur, .refl, fun e => by simp, hcur_q⟩
      | @tail u v _ hstep ih =>
        obtain ⟨fu, hju, hfu_eq, hfu_q⟩ := ih
        rcases hstep with ⟨_, _, s, hs, rfl⟩
        let fvVal : E → Γ := fun e => fu.val e + C.sign e • (s : Γ)
        have hfv_fl : G.IsFlow fvVal := isFlow_add fu.isFlow (isFlow_zsmul C.isFlow (s : Γ))
        have hfv_q : ∀ e, quoFlow B fvVal e = quoFlow B h.val e := fun e => by
          rw [sec4_E2_proved G B fu.val C (s : Γ) s.2 e, hfu_q e]
        have hfv_nz : Multigraph.IsNowhereZero fvVal := fun e =>
          (sec4_E1_proved (V := V) B fvVal e).mpr (Or.inl (by rw [hfv_q e]; exact hquo_nz e))
        let fv : G.NZFlow Γ := ⟨fvVal, hfv_fl, hfv_nz⟩
        refine ⟨fv, hju.tail ⟨C, (s : Γ), hs, fun _ => rfl⟩, fun e => ?_, hfv_q⟩
        dsimp only [fv, fvVal]; rw [hfu_eq e]; push_cast; rw [smul_add, add_assoc]
    exact hgo y hrtg
  -- Induct over l : List (B × H.toMultigraph.DirectedCycle)
  have hwalk_list : ∀ (m : List (B × H.toMultigraph.DirectedCycle)) (cur : G.NZFlow Γ),
      (∀ e, quoFlow B cur.val e = quoFlow B h.val e) →
      ∃ nxt : G.NZFlow Γ,
        G.SigmaJoined Sig.carrier cur nxt ∧
        (∀ e, nxt.val e = cur.val e + (m.map (fun p => (liftDCFromSub G H p.2).sign e • (p.1 : Γ))).sum) := by
    intro m
    induction m with
    | nil => intro cur _; exact ⟨cur, .refl, fun e => by simp⟩
    | cons hd tl ih =>
      intro cur hcur_q
      obtain ⟨mid, hjm, hmid_eq, hmid_q⟩ := hwalk_one cur hcur_q (liftDCFromSub G H hd.2) hd.1
      obtain ⟨fin, hjf, hfin_eq⟩ := ih mid hmid_q
      refine ⟨fin, hjm.trans hjf, fun e => ?_⟩
      rw [hfin_eq e, hmid_eq e]
      simp only [List.map_cons, List.sum_cons, add_assoc]
  obtain ⟨fin, hjfin, hfin_eq⟩ := hwalk_list l f hquo
  have hfeq : fin = h := by
    ext e
    rw [hfin_eq e]
    by_cases heH : e ∈ H.edges
    · have hsum_B := hl ⟨e, heH⟩
      have hcast : ((l.map (fun p => p.2.sign ⟨e, heH⟩ • p.1)).sum : B) = dB ⟨e, heH⟩ := hsum_B.symm
      have hval_eq : (l.map (fun p => (liftDCFromSub G H p.2).sign e • (p.1 : Γ))).sum = h.val e - f.val e := by
        have h1 : (l.map (fun p => (liftDCFromSub G H p.2).sign e • (p.1 : Γ))).sum =
            (((l.map (fun p => p.2.sign ⟨e, heH⟩ • p.1)).sum : B) : Γ) := by
          clear hl hsum_B hcast hfin_eq hjfin
          induction l with
          | nil => simp
          | cons hd tl ihl =>
            rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, AddSubgroup.coe_add,
                AddSubgroup.coe_zsmul, ← ihl]
            dsimp only [liftDCFromSub]
            rw [dif_pos heH]
        rw [h1, hcast]
      rw [hval_eq]; abel
    · have h0 : (l.map (fun p => (liftDCFromSub G H p.2).sign e • (p.1 : Γ))).sum = 0 := by
        apply List.sum_eq_zero
        intro x hx; rw [List.mem_map] at hx; rcases hx with ⟨p, _, rfl⟩
        simp [liftDCFromSub, heH]
      rw [h0, add_zero, hout e heH]
  exact hfeq ▸ hjfin

/-! ### Main Master Theorem (`thm_1_3_of`) -/

theorem thm_1_3_of
    (hSeymour : SeymourSixFlow) (hJLPT : JLPTWellColouring)
    (hSec3 : Sec3Bundle hJLPT)
    {Γ : Type} [AddCommGroup Γ] [Fintype Γ] [DecidableEq Γ]
    (B : AddSubgroup Γ) [Fintype (Γ ⧸ B)] [Fintype B] [DecidableEq (Γ ⧸ B)] [DecidableEq B]
    (hA : 10 ≤ Fintype.card (Γ ⧸ B)) (hB : 4 ≤ Fintype.card B)
    (Sig : StepSystem Γ)
    (hR1 : CondR1 B Sig) (hR2 : CondR2 B Sig) (hR3 : CondR3 Sig) (hAV : CondAV B Sig)
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : Multigraph V E) (hbr : G.IsBridgeless) :
    (∀ (f h : G.NZFlow Γ), (∀ e, quoFlow B h.val e ≠ 0) → G.SigmaJoined Sig.carrier f h) ∧
    (∀ (f g : G.NZFlow Γ), G.SigmaJoined Sig.carrier f g) ∧
    G.FlowGraphConnected Γ := by
  -- Strong induction on n = Fintype.card V for Part 1 (for all finite bridgeless multigraphs)
  have hpart1 : ∀ n : ℕ,
      ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
        (G : Multigraph V E), Fintype.card V = n → G.IsBridgeless →
        ∀ (f h : G.NZFlow Γ), (∀ e, quoFlow B h.val e ≠ 0) → G.SigmaJoined Sig.carrier f h := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      -- Step 1: Prove for loopless bridgeless graphs on n vertices
      have hloopless : ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
          (G : Multigraph V E), Fintype.card V = n → G.IsBridgeless → G.IsLoopless →
          ∀ (f h : G.NZFlow Γ), (∀ e, quoFlow B h.val e ≠ 0) → G.SigmaJoined Sig.carrier f h := by
        intro V E _ _ _ _ G hcard hbr hll f h hh_targ
        -- Subcase 0: n ≤ 1 -> E is empty since G is loopless
        by_cases hn1 : Fintype.card V ≤ 1
        · have hfeq : f = h := by
            ext e
            exfalso
            have hne := hll e
            have hcard2 : 2 ≤ Fintype.card V := by
              have hpair : ({G.tail e, G.head e} : Finset V).card = 2 := Finset.card_pair hne
              calc 2 = ({G.tail e, G.head e} : Finset V).card := hpair.symm
                _ ≤ Fintype.card V := Finset.card_le_univ _
            omega
          rw [hfeq]; exact .refl
        · push Not at hn1
          -- Subcase 1: ¬ G.IsEdgeConnected 1 (disconnected)
          by_cases hconn1 : G.IsEdgeConnected 1
          · -- Subcase 2: ¬ G.IsEdgeConnected 2 is impossible since G is bridgeless!
            have hconn2 : G.IsEdgeConnected 2 := by
              intro S hSne hScne
              have hge1 := hconn1 S hSne hScne
              by_contra hlt2
              have hcard1 : (G.cutEdges S).card = 1 := by omega
              obtain ⟨e0, he0⟩ := Finset.card_eq_one.mp hcard1
              have he0_mem : e0 ∈ G.cutEdges S := he0 ▸ Finset.mem_singleton_self e0
              -- e0 lies on a cycle C since G is bridgeless
              have hexC : ∃ C : G.Subgraph, C.IsCycle ∧ e0 ∈ C.edges := by
                by_contra hnot; exact hbr e0 hnot
              rcases hexC with ⟨C, hC, he0C⟩
              obtain ⟨DC, hDCle⟩ := exists_directedCycle_of_no_deg_one C ⟨e0, he0C⟩
                (fun v hv => by rw [hC.2 v hv]; decide)
              -- DC.sub = C, so e0 ∈ DC.sub.edges
              have he0DC : e0 ∈ DC.sub.edges := by
                -- Reuse quick uniqueness
                have hverts : DC.sub.verts = C.verts := by
                  apply Finset.Subset.antisymm hDCle.1
                  intro w hw
                  obtain ⟨v₀, hv₀⟩ := DC.isCycle.1.1
                  have hpath := hC.1.2 v₀ (hDCle.1 hv₀) w hw
                  clear hw
                  induction hpath with
                  | refl => exact hv₀
                  | @tail u z _ hs ihp =>
                    rcases hs with ⟨e', he', ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
                    · have hdeg : DC.sub.deg u = C.deg u := by rw [DC.isCycle.2 u ihp, hC.2 u (hDCle.1 ihp)]
                      have ht_sub := Finset.filter_subset_filter (fun e'' => G.tail e'' = u) hDCle.2
                      have hh_sub := Finset.filter_subset_filter (fun e'' => G.head e'' = u) hDCle.2
                      have ht_le := Finset.card_le_card ht_sub
                      have hh_le := Finset.card_le_card hh_sub
                      unfold Multigraph.Subgraph.deg at hdeg
                      have ht_eq := Finset.eq_of_subset_of_card_le ht_sub (by omega)
                      have hmem : e' ∈ C.edges.filter (fun e'' => G.tail e'' = u) := Finset.mem_filter.mpr ⟨he', h1⟩
                      rw [← ht_eq] at hmem
                      simpa [h2] using DC.sub.head_mem (Finset.mem_filter.mp hmem).1
                    · have hdeg : DC.sub.deg u = C.deg u := by rw [DC.isCycle.2 u ihp, hC.2 u (hDCle.1 ihp)]
                      have ht_sub := Finset.filter_subset_filter (fun e'' => G.tail e'' = u) hDCle.2
                      have hh_sub := Finset.filter_subset_filter (fun e'' => G.head e'' = u) hDCle.2
                      have ht_le := Finset.card_le_card ht_sub
                      have hh_le := Finset.card_le_card hh_sub
                      unfold Multigraph.Subgraph.deg at hdeg
                      have hh_eq := Finset.eq_of_subset_of_card_le hh_sub (by omega)
                      have hmem : e' ∈ C.edges.filter (fun e'' => G.head e'' = u) := Finset.mem_filter.mpr ⟨he', h2⟩
                      rw [← hh_eq] at hmem
                      simpa [h1] using DC.sub.tail_mem (Finset.mem_filter.mp hmem).1
                have huC := C.tail_mem he0C
                have huD : G.tail e0 ∈ DC.sub.verts := hverts ▸ huC
                have hdeg : DC.sub.deg (G.tail e0) = C.deg (G.tail e0) := by rw [DC.isCycle.2 _ huD, hC.2 _ huC]
                have ht_sub := Finset.filter_subset_filter (fun e'' => G.tail e'' = G.tail e0) hDCle.2
                have hh_sub := Finset.filter_subset_filter (fun e'' => G.head e'' = G.tail e0) hDCle.2
                have ht_le := Finset.card_le_card ht_sub
                have hh_le := Finset.card_le_card hh_sub
                unfold Multigraph.Subgraph.deg at hdeg
                have ht_eq := Finset.eq_of_subset_of_card_le ht_sub (by omega)
                have hmem : e0 ∈ C.edges.filter (fun e'' => G.tail e'' = G.tail e0) := Finset.mem_filter.mpr ⟨he0C, rfl⟩
                rw [← ht_eq] at hmem
                exact (Finset.mem_filter.mp hmem).1
              have hcut_sum := sum_boundary_eq_cut G DC.sign S
              have hzero : ∑ v ∈ S, G.boundary DC.sign v = 0 := Finset.sum_eq_zero fun v _ => DC.isFlow v
              rw [hzero] at hcut_sum
              have hcr := (Finset.mem_filter.mp he0_mem).2
              rcases hcr with ⟨ht, hh⟩ | ⟨ht, hh⟩
              · have hf1 : Finset.univ.filter (fun e => G.head e ∈ S ∧ G.tail e ∉ S) = ∅ := by
                  ext e; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
                  rintro ⟨h1, h2⟩
                  have hm : e ∈ G.cutEdges S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨h2, h1⟩⟩
                  rw [he0, Finset.mem_singleton] at hm; subst hm; exact h2 ht
                have hf2 : Finset.univ.filter (fun e => G.tail e ∈ S ∧ G.head e ∉ S) = {e0} := by
                  ext e; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
                  constructor
                  · rintro ⟨h1, h2⟩
                    have hm : e ∈ G.cutEdges S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ⟨h1, h2⟩⟩
                    rw [he0, Finset.mem_singleton] at hm; exact hm
                  · rintro rfl; exact ⟨ht, hh⟩
                rw [hf1, hf2, Finset.sum_empty, Finset.sum_singleton, zero_sub] at hcut_sum
                rcases DC.sign_mem he0DC with h1 | h1 <;> omega
              · have hf1 : Finset.univ.filter (fun e => G.head e ∈ S ∧ G.tail e ∉ S) = {e0} := by
                  ext e; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
                  constructor
                  · rintro ⟨h1, h2⟩
                    have hm : e ∈ G.cutEdges S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨h2, h1⟩⟩
                    rw [he0, Finset.mem_singleton] at hm; exact hm
                  · rintro rfl; exact ⟨hh, ht⟩
                have hf2 : Finset.univ.filter (fun e => G.tail e ∈ S ∧ G.head e ∉ S) = ∅ := by
                  ext e; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
                  rintro ⟨h1, h2⟩
                  have hm : e ∈ G.cutEdges S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ⟨h1, h2⟩⟩
                  rw [he0, Finset.mem_singleton] at hm; subst hm; exact ht h1
                rw [hf1, hf2, Finset.sum_singleton, Finset.sum_empty, sub_zero] at hcut_sum
                rcases DC.sign_mem he0DC with h1 | h1 <;> omega
            -- Subcase 3 vs Subcase 4: Is G 3-edge-connected?
            by_cases hconn3 : G.IsEdgeConnected 3
            · -- Subcase 4: loopless 3-edge-connected, n ≥ 2!
              obtain ⟨f', H, hjoin_f', hHgood, hf'_quo⟩ := lem_4_1_proved B Sig hAV G hll hconn3 hn1 f
              -- Size of V(G / H) is strictly less than n since |V(H)| ≥ 2
              have hHV2 : 2 ≤ H.verts.card := by
                rcases hHgood with ⟨_, _, hv2⟩ | hsub'
                · exact hv2
                · rcases hsub' with ⟨sub⟩
                  calc 2 ≤ Fintype.card sub.V₀ := sub.card_ge_two
                    _ = (Finset.univ.image sub.embedV).card := by
                        rw [Finset.card_image_of_injective _ sub.embedV.injective, Finset.card_univ]
                    _ ≤ H.verts.card := Finset.card_le_card fun v hv => by
                        rw [Finset.mem_image] at hv; rcases hv with ⟨v₀, _, rfl⟩; exact sub.embedV_mem v₀
              have hcard_star : Fintype.card (Option {v : V // v ∉ H.verts}) < n := by
                rw [Fintype.card_option, Fintype.card_subtype_compl, Fintype.card_coe]
                have hle : H.verts.card ≤ Fintype.card V := Finset.card_le_univ _
                omega
              let Gstar := G.contractSubgraph H
              have hbr_star : Gstar.IsBridgeless := contractSubgraph_isBridgeless G hbr H
              let f'star : Gstar.NZFlow Γ :=
                ⟨fun e => f'.val e.1, contractSubgraph_isFlow G H f'.val f'.isFlow, fun e => f'.nonzero e.1⟩
              let hstar : Gstar.NZFlow Γ :=
                ⟨fun e => h.val e.1, contractSubgraph_isFlow G H h.val h.isFlow, fun e => h.nonzero e.1⟩
              have hstar_join : Gstar.SigmaJoined Sig.carrier f'star hstar :=
                ih (Fintype.card (Option {v : V // v ∉ H.verts})) hcard_star _ _ Gstar rfl hbr_star
                  f'star hstar (fun e => hh_targ e.1)
              rcases hHgood with hcyc | hsub'
              · -- Case (CYC)
                have hlift_path : ∀ gstar : Gstar.NZFlow Γ,
                    Gstar.SigmaJoined Sig.carrier f'star gstar →
                    ∃ g : G.NZFlow Γ,
                      G.SigmaJoined Sig.carrier f' g ∧
                      (∀ e : {e : E // e ∉ H.edges}, g.val e.1 = gstar.val e) ∧
                      IsHGoodCyc G B H g := by
                  intro gstar hrtg
                  induction hrtg with
                  | refl => exact ⟨f', .refl, fun _ => rfl, hf'_quo⟩
                  | @tail astar bstar _ hstep ihp =>
                    obtain ⟨ga, hjga, hga_eq, hga_good⟩ := ihp
                    rcases hstep with ⟨Cstar, lam, hlam, hbeq⟩
                    have hmove : ∃ (Cstar : Gstar.DirectedCycle) (lam : Γ),
                        lam ∈ Sig.carrier ∧ ∀ e, bstar.val e = ga.val e.1 + Cstar.sign e • lam :=
                      ⟨Cstar, lam, hlam, fun e => by rw [hga_eq e, hbeq e]⟩
                    obtain ⟨gb, hjgb, hgb_eq, hgb_good⟩ :=
                      lem_4_8_cyc_proved B hA hB Sig hR1 hR2 G hbr H hcyc ga hga_good bstar hmove
                    exact ⟨gb, hjga.trans hjgb, hgb_eq, hgb_good⟩
                obtain ⟨f_nu, hj_nu, hnu_off, hnu_good⟩ := hlift_path hstar hstar_join
                -- Direct H as DH; quoFlow B h - quoFlow B f_nu = c • χ_{DH}
                have hHne_e : H.edges.Nonempty := by
                  obtain ⟨v, hv⟩ := hcyc.1.1.1
                  have hd := hcyc.1.2 v hv
                  by_contra hempty; rw [Finset.not_nonempty_iff_eq_empty] at hempty
                  simp [Multigraph.Subgraph.deg, hempty] at hd
                obtain ⟨DH, hDHle⟩ := exists_directedCycle_of_no_deg_one H hHne_e
                  (fun v hv => by rw [hcyc.1.2 v hv]; decide)
                have hDHeq : DH.sub = H := by
                  have hverts : DH.sub.verts = H.verts := by
                    apply Finset.Subset.antisymm hDHle.1
                    intro w hw
                    obtain ⟨v₀, hv₀⟩ := DH.isCycle.1.1
                    have hpath := hcyc.1.1.2 v₀ (hDHle.1 hv₀) w hw
                    clear hw
                    induction hpath with
                    | refl => exact hv₀
                    | @tail u z _ hs ihp =>
                      rcases hs with ⟨e', he', ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
                      · have hdeg : DH.sub.deg u = H.deg u := by rw [DH.isCycle.2 u ihp, hcyc.1.2 u (hDHle.1 ihp)]
                        have ht_sub := Finset.filter_subset_filter (fun e'' => G.tail e'' = u) hDHle.2
                        have hh_sub := Finset.filter_subset_filter (fun e'' => G.head e'' = u) hDHle.2
                        have ht_le := Finset.card_le_card ht_sub
                        have hh_le := Finset.card_le_card hh_sub
                        unfold Multigraph.Subgraph.deg at hdeg
                        have ht_eq := Finset.eq_of_subset_of_card_le ht_sub (by omega)
                        have hmem : e' ∈ H.edges.filter (fun e'' => G.tail e'' = u) := Finset.mem_filter.mpr ⟨he', h1⟩
                        rw [← ht_eq] at hmem
                        simpa [h2] using DH.sub.head_mem (Finset.mem_filter.mp hmem).1
                      · have hdeg : DH.sub.deg u = H.deg u := by rw [DH.isCycle.2 u ihp, hcyc.1.2 u (hDHle.1 ihp)]
                        have ht_sub := Finset.filter_subset_filter (fun e'' => G.tail e'' = u) hDHle.2
                        have hh_sub := Finset.filter_subset_filter (fun e'' => G.head e'' = u) hDHle.2
                        have ht_le := Finset.card_le_card ht_sub
                        have hh_le := Finset.card_le_card hh_sub
                        unfold Multigraph.Subgraph.deg at hdeg
                        have hh_eq := Finset.eq_of_subset_of_card_le hh_sub (by omega)
                        have hmem : e' ∈ H.edges.filter (fun e'' => G.head e'' = u) := Finset.mem_filter.mpr ⟨he', h2⟩
                        rw [← hh_eq] at hmem
                        simpa [h1] using DH.sub.tail_mem (Finset.mem_filter.mp hmem).1
                  have hedges : DH.sub.edges = H.edges := by
                    apply Finset.Subset.antisymm hDHle.2
                    intro e' he'
                    have huH := H.tail_mem he'
                    have huD : G.tail e' ∈ DH.sub.verts := hverts ▸ huH
                    have hdeg : DH.sub.deg (G.tail e') = H.deg (G.tail e') := by rw [DH.isCycle.2 _ huD, hcyc.1.2 _ huH]
                    have ht_sub := Finset.filter_subset_filter (fun e'' => G.tail e'' = G.tail e') hDHle.2
                    have hh_sub := Finset.filter_subset_filter (fun e'' => G.head e'' = G.tail e') hDHle.2
                    have ht_le := Finset.card_le_card ht_sub
                    have hh_le := Finset.card_le_card hh_sub
                    unfold Multigraph.Subgraph.deg at hdeg
                    have ht_eq := Finset.eq_of_subset_of_card_le ht_sub (by omega)
                    have hmem : e' ∈ H.edges.filter (fun e'' => G.tail e'' = G.tail e') := Finset.mem_filter.mpr ⟨he', rfl⟩
                    rw [← ht_eq] at hmem
                    exact (Finset.mem_filter.mp hmem).1
                  ext x
                  · simp [hverts]
                  · simp [hedges]
                -- Find c : Γ ⧸ B such that quoFlow B h.val - quoFlow B f_nu.val = c • DH.sign
                obtain ⟨e₀, he₀H⟩ := hHne_e
                let qdiff : E → Γ ⧸ B := fun e => quoFlow B h.val e - quoFlow B f_nu.val e
                have hqdiff_fl : G.IsFlow qdiff := by
                  intro v
                  have h1 : G.boundary (fun e => h.val e - f_nu.val e) v = 0 := isFlow_sub h.isFlow f_nu.isFlow v
                  have hmap : (QuotientAddGroup.mk' B) (G.boundary (fun e => h.val e - f_nu.val e) v) =
                      G.boundary qdiff v := by
                    unfold Multigraph.boundary qdiff quoFlow
                    rw [map_sub, map_sum, map_sum]
                    congr 1 <;> refine Finset.sum_congr rfl fun e _ => map_sub (QuotientAddGroup.mk' B) _ _
                  rw [← hmap, h1, map_zero]
                let c : Γ ⧸ B := DH.sign e₀ • qdiff e₀
                have hqdiff_eq : ∀ e, qdiff e = DH.sign e • c := by
                  let r : E → Γ ⧸ B := fun e => qdiff e - DH.sign e • c
                  have hr_fl : G.IsFlow r := isFlow_sub hqdiff_fl (isFlow_zsmul DH.isFlow c)
                  let T : G.Subgraph :=
                    { verts := H.verts, edges := H.edges.erase e₀,
                      tail_mem := fun he => H.tail_mem (Finset.mem_of_mem_erase he),
                      head_mem := fun he => H.head_mem (Finset.mem_of_mem_erase he) }
                  have hT_for : T.IsForest := by
                    intro K hKT hKcyc
                    have hKH : K ≤ H := ⟨hKT.1, hKT.2.trans (Finset.erase_subset e₀ H.edges)⟩
                    -- K = H contradicts e₀ ∉ T.edges
                    have hKeq : K = H := by
                      have hverts : K.verts = H.verts := by
                        apply Finset.Subset.antisymm hKH.1
                        intro w hw
                        obtain ⟨v₀, hv₀⟩ := hKcyc.1.1
                        have hpath := hcyc.1.1.2 v₀ (hKH.1 hv₀) w hw
                        clear hw
                        induction hpath with
                        | refl => exact hv₀
                        | @tail u z _ hs ihp =>
                          rcases hs with ⟨e', he', ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
                          · have hdeg : K.deg u = H.deg u := by rw [hKcyc.2 u ihp, hcyc.1.2 u (hKH.1 ihp)]
                            have ht_sub := Finset.filter_subset_filter (fun e'' => G.tail e'' = u) hKH.2
                            have hh_sub := Finset.filter_subset_filter (fun e'' => G.head e'' = u) hKH.2
                            have ht_le := Finset.card_le_card ht_sub
                            have hh_le := Finset.card_le_card hh_sub
                            unfold Multigraph.Subgraph.deg at hdeg
                            have ht_eq := Finset.eq_of_subset_of_card_le ht_sub (by omega)
                            have hmem : e' ∈ H.edges.filter (fun e'' => G.tail e'' = u) := Finset.mem_filter.mpr ⟨he', h1⟩
                            rw [← ht_eq] at hmem
                            simpa [h2] using K.head_mem (Finset.mem_filter.mp hmem).1
                          · have hdeg : K.deg u = H.deg u := by rw [hKcyc.2 u ihp, hcyc.1.2 u (hKH.1 ihp)]
                            have ht_sub := Finset.filter_subset_filter (fun e'' => G.tail e'' = u) hKH.2
                            have hh_sub := Finset.filter_subset_filter (fun e'' => G.head e'' = u) hKH.2
                            have ht_le := Finset.card_le_card ht_sub
                            have hh_le := Finset.card_le_card hh_sub
                            unfold Multigraph.Subgraph.deg at hdeg
                            have hh_eq := Finset.eq_of_subset_of_card_le hh_sub (by omega)
                            have hmem : e' ∈ H.edges.filter (fun e'' => G.head e'' = u) := Finset.mem_filter.mpr ⟨he', h2⟩
                            rw [← hh_eq] at hmem
                            simpa [h1] using K.tail_mem (Finset.mem_filter.mp hmem).1
                      have hedges : K.edges = H.edges := by
                        apply Finset.Subset.antisymm hKH.2
                        intro e' he'
                        have huH := H.tail_mem he'
                        have huK : G.tail e' ∈ K.verts := hverts ▸ huH
                        have hdeg : K.deg (G.tail e') = H.deg (G.tail e') := by rw [hKcyc.2 _ huK, hcyc.1.2 _ huH]
                        have ht_sub := Finset.filter_subset_filter (fun e'' => G.tail e'' = G.tail e') hKH.2
                        have hh_sub := Finset.filter_subset_filter (fun e'' => G.head e'' = G.tail e') hKH.2
                        have ht_le := Finset.card_le_card ht_sub
                        have hh_le := Finset.card_le_card hh_sub
                        unfold Multigraph.Subgraph.deg at hdeg
                        have ht_eq := Finset.eq_of_subset_of_card_le ht_sub (by omega)
                        have hmem : e' ∈ H.edges.filter (fun e'' => G.tail e'' = G.tail e') := Finset.mem_filter.mpr ⟨he', rfl⟩
                        rw [← ht_eq] at hmem
                        exact (Finset.mem_filter.mp hmem).1
                      ext x
                      · simp [hverts]
                      · simp [hedges]
                    exact (Finset.mem_erase.mp (hKT.2 (hKeq ▸ he₀H))).1 rfl
                  have hr_supp : ∀ e, r e ≠ 0 → e ∈ T.edges := by
                    intro e hne
                    by_cases heH : e ∈ H.edges
                    · refine Finset.mem_erase.mpr ⟨?_, heH⟩
                      rintro rfl
                      apply hne
                      dsimp only [r, c]
                      rcases DH.sign_mem (hDHeq ▸ he₀H) with hs | hs <;> simp [hs]
                    · exfalso; apply hne
                      have h1 : f_nu.val e = h.val e := hnu_off ⟨e, heH⟩
                      have h2 : DH.sign e = 0 := DH.sign_zero (by rw [hDHeq]; exact heH)
                      simp [r, qdiff, quoFlow, h1, h2]
                  have hr0 := flow_eq_zero_of_supp_subset_forest hT_for hr_fl hr_supp
                  intro e; exact sub_eq_zero.mp (hr0 e)
                -- Walk 0 → c outside X (card ≤ 5) via CondR1
                let X : Finset (Γ ⧸ B) := H.edges.image (fun e => DH.sign e • (-quoFlow B f_nu.val e))
                have hX_le : X.card ≤ 6 := (Finset.card_image_le.trans hcyc.2.1).trans (by decide)
                have h0X : (0 : Γ ⧸ B) ∉ X := by
                  intro h0; rw [Finset.mem_image] at h0; rcases h0 with ⟨e, heH, heq⟩
                  rcases DH.sign_mem (hDHeq ▸ heH) with hs | hs <;> simp_all [hnu_good e heH]
                have hcX : c ∉ X := by
                  intro hc'; rw [Finset.mem_image] at hc'; rcases hc' with ⟨e, heH, heq⟩
                  have h1 : DH.sign e • c = -quoFlow B f_nu.val e := by
                    rw [← heq]; rcases DH.sign_mem (hDHeq ▸ heH) with hs | hs <;> simp [hs]
                  have h2 := hqdiff_eq e
                  dsimp only [qdiff] at h2
                  rw [h1] at h2
                  exact hh_targ e (by
                    have : quoFlow B h.val e = 0 := by
                      have h3 : quoFlow B h.val e - quoFlow B f_nu.val e + quoFlow B f_nu.val e = 0 := by
                        rw [h2]; abel
                      simpa using h3
                    exact this)
                have hnotX_nz : ∀ u ∉ X, ∀ e ∈ H.edges, quoFlow B f_nu.val e + DH.sign e • u ≠ 0 := by
                  intro u hu e heH h0
                  apply hu; rw [Finset.mem_image]; refine ⟨e, heH, ?_⟩
                  have h1 : DH.sign e • u = -quoFlow B f_nu.val e := eq_neg_of_add_eq_zero_right h0
                  rw [← h1]; rcases DH.sign_mem (hDHeq ▸ heH) with hs | hs <;> simp [hs]
                obtain ⟨_, _, hrtg_c⟩ := hR1 X hX_le 0 c h0X hcX
                have hwalk_c : ∀ u : Γ ⧸ B,
                    Relation.ReflTransGen (fun a b => a ∈ {x : Γ ⧸ B | x ∉ X} ∧ b ∈ {x : Γ ⧸ B | x ∉ X} ∧
                      ∃ σ ∈ Sig.sigA B, b = a + σ) 0 u →
                    ∃ f'' : G.NZFlow Γ,
                      G.SigmaJoined Sig.carrier f_nu f'' ∧
                      (∀ e, e ∉ H.edges → f''.val e = h.val e) ∧
                      (∀ e, quoFlow B f''.val e = quoFlow B f_nu.val e + DH.sign e • u) := by
                  intro u hu
                  induction hu with
                  | refl => exact ⟨f_nu, .refl, fun e he => hnu_off ⟨e, he⟩, fun e => by simp⟩
                  | @tail a b _ hs ihw =>
                    obtain ⟨fa, hja, houta, hquaa⟩ := ihw
                    rcases hs with ⟨_, hbX, σ, ⟨_, z, hzSig, hzQ⟩, rfl⟩
                    let fbVal : E → Γ := fun e => fa.val e + DH.sign e • z
                    have hfb_fl : G.IsFlow fbVal := isFlow_add fa.isFlow (isFlow_zsmul DH.isFlow z)
                    have hfb_q : ∀ e, quoFlow B fbVal e = quoFlow B f_nu.val e + DH.sign e • (a + σ) := fun e => by
                      unfold quoFlow
                      change (QuotientAddGroup.mk' B) (fa.val e + DH.sign e • z) = _
                      rw [map_add, map_zsmul]
                      have h1 : (QuotientAddGroup.mk' B) (fa.val e) = quoFlow B f_nu.val e + DH.sign e • a := hquaa e
                      have h2 : (QuotientAddGroup.mk' B) z = σ := hzQ
                      rw [h1, h2, smul_add, add_assoc]; rfl
                    have hfb_out : ∀ e, e ∉ H.edges → fbVal e = h.val e := fun e he => by
                      dsimp only [fbVal]; rw [DH.sign_zero (by rw [hDHeq]; exact he), zero_zsmul, add_zero, houta e he]
                    have hfb_nz : Multigraph.IsNowhereZero fbVal := fun e => by
                      by_cases he : e ∈ H.edges
                      · exact (sec4_E1_proved (V := V) B fbVal e).mpr (Or.inl (by rw [hfb_q e]; exact hnotX_nz (a + σ) hbX e he))
                      · rw [hfb_out e he]; exact h.nonzero e
                    exact ⟨⟨fbVal, hfb_fl, hfb_nz⟩, hja.tail ⟨DH, z, hzSig, fun _ => rfl⟩, hfb_out, hfb_q⟩
                obtain ⟨f'', hj_f'', hout_f'', hquo_f''⟩ := hwalk_c c hrtg_c
                have hquo_eq : ∀ e, quoFlow B f''.val e = quoFlow B h.val e := fun e => by
                  rw [hquo_f'' e, ← hqdiff_eq e]; dsimp only [qdiff]; abel
                exact (hjoin_f'.trans (hj_nu.trans hj_f'')).trans
                  (join_B_diff_on_subgraph B Sig hR2 G H f'' h hquo_eq hh_targ hout_f'')
              · -- Case (SUB): reorient on H.edges via aux_exists, get Frame, lift & finish!
                rcases hsub' with ⟨sub⟩
                obtain ⟨flip, hflip_out, H', sub', hH'v, hH'e, ⟨aux⟩⟩ := hSec3.aux_exists sub
                obtain ⟨fr⟩ := hSec3.frame_exists sub' aux
                -- Build reoriented flows f'_r and h_r on G' = G.reorient flip
                let G' := G.reorient flip
                have hbr' : G'.IsBridgeless := by
                  intro e hnot
                  have hex : ∃ C : G.Subgraph, C.IsCycle ∧ e ∈ C.edges := by
                    by_contra hn'; exact hbr e hn'
                  rcases hex with ⟨C, hC, heC⟩
                  exact hnot ⟨reorientSubgraph G flip C, (reorientSubgraph_isCycle G flip C).mpr hC, heC⟩
                let f'_r : G'.NZFlow Γ :=
                  ⟨Multigraph.reorientVal flip f'.val, (reorient_isFlow_iff G flip f'.val).mpr f'.isFlow,
                   fun e => by unfold Multigraph.reorientVal; split_ifs; exact neg_ne_zero.mpr (f'.nonzero e); exact f'.nonzero e⟩
                let h_r : G'.NZFlow Γ :=
                  ⟨Multigraph.reorientVal flip h.val, (reorient_isFlow_iff G flip h.val).mpr h.isFlow,
                   fun e => by unfold Multigraph.reorientVal; split_ifs; exact neg_ne_zero.mpr (h.nonzero e); exact h.nonzero e⟩
                have hf'_r_good : IsHGoodSub fr B f'_r := by
                  intro t _ e het
                  have heH : e ∈ H.edges := hH'e ▸ (sub'.thread t).edges_sub e het
                  unfold quoFlow; dsimp only [f'_r, Multigraph.reorientVal]
                  split_ifs
                  · change -(quoFlow B f'.val e) ≠ 0; exact neg_ne_zero.mpr (hf'_quo e heH)
                  · exact hf'_quo e heH
                have hh_r_targ : ∀ e, quoFlow B h_r.val e ≠ 0 := by
                  intro e
                  unfold quoFlow; dsimp only [h_r, Multigraph.reorientVal]
                  split_ifs
                  · change -(quoFlow B h.val e) ≠ 0; exact neg_ne_zero.mpr (hh_targ e)
                  · exact hh_targ e
                -- Contract G' / H' (strictly fewer than n vertices) and apply IH
                have hcard_star' : Fintype.card (Option {v : V // v ∉ H'.verts}) < n := by
                  rw [hH'v]; exact hcard_star
                let Gstar' := G'.contractSubgraph H'
                have hbr_star' : Gstar'.IsBridgeless := contractSubgraph_isBridgeless G' hbr' H'
                let f'star' : Gstar'.NZFlow Γ :=
                  ⟨fun e => f'_r.val e.1, contractSubgraph_isFlow G' H' f'_r.val f'_r.isFlow, fun e => f'_r.nonzero e.1⟩
                let hstar' : Gstar'.NZFlow Γ :=
                  ⟨fun e => h_r.val e.1, contractSubgraph_isFlow G' H' h_r.val h_r.isFlow, fun e => h_r.nonzero e.1⟩
                have hstar'_join : Gstar'.SigmaJoined Sig.carrier f'star' hstar' :=
                  ih (Fintype.card (Option {v : V // v ∉ H'.verts})) hcard_star' _ _ Gstar' rfl hbr_star'
                    f'star' hstar' (fun e => hh_r_targ e.1)
                -- Extract official cycles and (O1)-(O6) from hSec3.lem_3_11
                have h311A := hSec3.lem_3_11 (A := Γ ⧸ B) fr
                have h311Z := hSec3.lem_3_11 (A := ℤ) fr
                let C_off : Fin fr.numNodes → aux.Q.DirectedCycle := fun i => (h311A.2.1 i).choose
                have hC_off : ∀ i, fr.IsOfficialCycle i (C_off i) := fun i => (h311A.2.1 i).choose_spec.1
                have hO2345A := h311A.2.2.1 C_off hC_off
                have hO2345Z := h311Z.2.2.1 C_off hC_off
                -- Lift Gstar' path to G' via lem_4_8_sub_of
                have hlift_path' : ∀ gstar : Gstar'.NZFlow Γ,
                    Gstar'.SigmaJoined Sig.carrier f'star' gstar →
                    ∃ g : G'.NZFlow Γ,
                      G'.SigmaJoined Sig.carrier f'_r g ∧
                      (∀ e : {e : E // e ∉ H'.edges}, g.val e.1 = gstar.val e) ∧
                      IsHGoodSub fr B g := by
                  intro gstar hrtg
                  induction hrtg with
                  | refl => exact ⟨f'_r, .refl, fun _ => rfl, hf'_r_good⟩
                  | @tail astar bstar _ hstep ihp =>
                    obtain ⟨ga, hjga, hga_eq, hga_good⟩ := ihp
                    rcases hstep with ⟨Cstar, lam, hlam, hbeq⟩
                    have hmove : ∃ (Cstar : Gstar'.DirectedCycle) (lam : Γ),
                        lam ∈ Sig.carrier ∧ ∀ e, bstar.val e = ga.val e.1 + Cstar.sign e • lam :=
                      ⟨Cstar, lam, hlam, fun e => by rw [hga_eq e, hbeq e]⟩
                    obtain ⟨gb, hjgb, hgb_eq, hgb_good⟩ :=
                      lem_4_8_sub_of B hA hB Sig hR1 hR2 G' hbr' H' sub' aux fr C_off
                        h311A.1 hO2345A.1 hO2345A.2.1 hO2345A.2.2.1 hO2345A.2.2.2 hO2345Z.2.2.2
                        ⟨h311A.2.2.2.1, h311A.2.2.2.2.1⟩ h311A.2.2.2.2.2
                        (hSec3.lem_3_6_a_cyc sub' aux) (hSec3.lem_3_6_d sub' aux)
                        (fun f₀ hf₀ => hSec3.def_3_12 B fr f₀ hf₀)
                        ga hga_good bstar hmove
                    exact ⟨gb, hjga.trans hjgb, hgb_eq, hgb_good⟩
                obtain ⟨f_nu, hj_nu, hnu_off, hnu_good⟩ := hlift_path' hstar' hstar'_join
                -- Lift quoFlow B h_r - quoFlow B f_nu (an A-flow of H') to Y on aux.Q via lem_3_6_c_surj
                let qdiff : E → Γ ⧸ B := fun e => quoFlow B h_r.val e - quoFlow B f_nu.val e
                have hqdiff_flG : G'.IsFlow qdiff := by
                  intro v
                  have h1 : G'.boundary (fun e => h_r.val e - f_nu.val e) v = 0 := isFlow_sub h_r.isFlow f_nu.isFlow v
                  have hmap : (QuotientAddGroup.mk' B) (G'.boundary (fun e => h_r.val e - f_nu.val e) v) =
                      G'.boundary qdiff v := by
                    unfold Multigraph.boundary qdiff quoFlow
                    rw [map_sub, map_sum, map_sum]
                    congr 1 <;> refine Finset.sum_congr rfl fun e _ => map_sub (QuotientAddGroup.mk' B) _ _
                  rw [← hmap, h1, map_zero]
                have hqdiff_flH : H'.toMultigraph.IsFlow (fun e => qdiff e.1) :=
                  restrict_isFlow_of_supp_sub H' qdiff hqdiff_flG
                    (fun e he => by simp [qdiff, quoFlow, show f_nu.val e = h_r.val e from hnu_off ⟨e, he⟩])
                obtain ⟨Y, hYfl, hYpi⟩ := hSec3.lem_3_6_c_surj sub' aux (fun e => qdiff e.1) hqdiff_flH
                have hY_PLam : Y ∈ PLam (LamOfFlow B fr f_nu) := by
                  rw [(hSec3.def_3_12 B fr f_nu hnu_good).2.2 Y hYfl]
                  intro t _ e het
                  have heH' : e ∈ H'.edges := (sub'.thread t).edges_sub e het
                  rw [hYpi ⟨e, heH'⟩]
                  dsimp only [qdiff]
                  rw [add_sub_cancel]
                  exact hh_r_targ e
                obtain ⟨f'', hj_in, hgood'', hquo_f'', hout_f''⟩ :=
                  lem_4_6_of B hA hB Sig hR1 hR2 fr C_off
                    hO2345A.1 hO2345A.2.1 hO2345A.2.2.1 hO2345A.2.2.2
                    (hSec3.lem_3_6_a_cyc sub' aux) (hSec3.lem_3_6_d sub' aux)
                    h311A.2.2.2.2.2 f_nu hnu_good (hSec3.def_3_12 B fr f_nu hnu_good) Y hY_PLam
                have hj_f'' : G'.SigmaJoined Sig.carrier f_nu f'' := by
                  clear hgood'' hquo_f'' hout_f''
                  induction hj_in with
                  | refl => exact .refl
                  | tail _ hs ihp => rcases hs with ⟨C, z, _, hz, heq⟩; exact ihp.tail ⟨C, z, hz, heq⟩
                have hquo_eq : ∀ e, quoFlow B f''.val e = quoFlow B h_r.val e := fun e => by
                  rw [hquo_f'' e]
                  by_cases heH' : e ∈ H'.edges
                  · rw [hYpi ⟨e, heH'⟩]; dsimp only [qdiff]; abel
                  · have hpi0 : aux.pi Y e = 0 := by
                      classical unfold AuxGraphData.pi
                      have hno : ¬ ∃ t : sub'.E₀, e ∈ (sub'.thread t).edges := by
                        rintro ⟨t, het⟩; exact heH' ((sub'.thread t).edges_sub e het)
                      rw [dif_neg hno]
                    rw [hpi0, add_zero]
                    unfold quoFlow
                    rw [show f_nu.val e = h_r.val e from hnu_off ⟨e, heH'⟩]
                have hout_eq : ∀ e, e ∉ H'.edges → f''.val e = h_r.val e := fun e he =>
                  (hout_f'' e he).trans (hnu_off ⟨e, he⟩)
                have hjoin_r : G'.SigmaJoined Sig.carrier f'_r h_r :=
                  (hj_nu.trans hj_f'').trans
                    (join_B_diff_on_subgraph B Sig hR2 G' H' f'' h_r hquo_eq hh_r_targ hout_eq)
                exact hjoin_f'.trans (reorient_sigmaJoined G flip Sig (fun _ => rfl) (fun _ => rfl) hjoin_r)
            · -- Subcase 3: G is 2-edge-connected but has a 2-edge cut {e₁, e₂}!
              unfold Multigraph.IsEdgeConnected at hconn3
              push Not at hconn3
              rcases hconn3 with ⟨S, hSne, hScne, hlt3⟩
              have hge2 := hconn2 S hSne hScne
              have hcard2 : (G.cutEdges S).card = 2 := by omega
              obtain ⟨e₁, e₂, he12_ne, hcut_eq⟩ := Finset.card_eq_two.mp hcard2
              have he₁_cut : e₁ ∈ G.cutEdges S := hcut_eq ▸ Finset.mem_insert_self _ _
              have he₂_cut : e₂ ∈ G.cutEdges S := hcut_eq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
              -- Conservation across S implies x e₁ = ± x e₂ for every flow x of G!
              have hflow_e12 : ∀ {A' : Type} [AddCommGroup A'] (x : E → A'), G.IsFlow x →
                  x e₁ = x e₂ ∨ x e₁ = -x e₂ := by
                intro A' _ x hx
                have hsum := sum_boundary_eq_cut G x S
                have hz : ∑ v ∈ S, G.boundary x v = 0 := Finset.sum_eq_zero fun v _ => hx v
                rw [hz] at hsum
                have h1 := (Finset.mem_filter.mp he₁_cut).2
                have h2 := (Finset.mem_filter.mp he₂_cut).2
                -- Classify e₁, e₂ as in-cut or out-cut
                let F_in := Finset.univ.filter (fun e => G.head e ∈ S ∧ G.tail e ∉ S)
                let F_out := Finset.univ.filter (fun e => G.tail e ∈ S ∧ G.head e ∉ S)
                have hF_sub : ∀ e, e ∈ F_in → e = e₁ ∨ e = e₂ := fun e he => by
                  have hm : e ∈ G.cutEdges S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨(Finset.mem_filter.mp he).2.2, (Finset.mem_filter.mp he).2.1⟩⟩
                  rw [hcut_eq, Finset.mem_insert, Finset.mem_singleton] at hm; exact hm
                have hF_sub2 : ∀ e, e ∈ F_out → e = e₁ ∨ e = e₂ := fun e he => by
                  have hm : e ∈ G.cutEdges S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl (Finset.mem_filter.mp he).2⟩
                  rw [hcut_eq, Finset.mem_insert, Finset.mem_singleton] at hm; exact hm
                rcases h1 with ⟨ht1, hh1⟩ | ⟨ht1, hh1⟩ <;> rcases h2 with ⟨ht2, hh2⟩ | ⟨ht2, hh2⟩
                · have hFi : F_in = ∅ := by
                    ext e; simp only [Finset.notMem_empty, iff_false]; intro he
                    rcases hF_sub e he with rfl | rfl
                    · exact (Finset.mem_filter.mp he).2.2 ht1
                    · exact (Finset.mem_filter.mp he).2.2 ht2
                  have hFo : F_out = {e₁, e₂} := by
                    ext e; simp only [Finset.mem_insert, Finset.mem_singleton]
                    exact ⟨hF_sub2 e, by rintro (rfl | rfl); exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht1, hh1⟩; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht2, hh2⟩⟩
                  rw [show Finset.univ.filter (fun e => G.head e ∈ S ∧ G.tail e ∉ S) = ∅ from hFi,
                      show Finset.univ.filter (fun e => G.tail e ∈ S ∧ G.head e ∉ S) = {e₁, e₂} from hFo,
                      Finset.sum_empty, Finset.sum_pair he12_ne, zero_sub] at hsum
                  exact Or.inr (eq_neg_of_add_eq_zero_left (neg_eq_zero.mp hsum.symm))
                · have hFi : F_in = {e₂} := by
                    ext e; simp only [Finset.mem_singleton]
                    exact ⟨fun he => (hF_sub e he).resolve_left (fun h => (Finset.mem_filter.mp (h ▸ he)).2.2 ht1),
                           fun h => h ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh2, ht2⟩⟩
                  have hFo : F_out = {e₁} := by
                    ext e; simp only [Finset.mem_singleton]
                    exact ⟨fun he => (hF_sub2 e he).resolve_right (fun h => ht2 (Finset.mem_filter.mp (h ▸ he)).2.1),
                           fun h => h ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht1, hh1⟩⟩
                  rw [show Finset.univ.filter (fun e => G.head e ∈ S ∧ G.tail e ∉ S) = {e₂} from hFi,
                      show Finset.univ.filter (fun e => G.tail e ∈ S ∧ G.head e ∉ S) = {e₁} from hFo,
                      Finset.sum_singleton, Finset.sum_singleton] at hsum
                  exact Or.inl (sub_eq_zero.mp hsum.symm).symm
                · have hFi : F_in = {e₁} := by
                    ext e; simp only [Finset.mem_singleton]
                    exact ⟨fun he => (hF_sub e he).resolve_right (fun h => (Finset.mem_filter.mp (h ▸ he)).2.2 ht2),
                           fun h => h ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh1, ht1⟩⟩
                  have hFo : F_out = {e₂} := by
                    ext e; simp only [Finset.mem_singleton]
                    exact ⟨fun he => (hF_sub2 e he).resolve_left (fun h => ht1 (Finset.mem_filter.mp (h ▸ he)).2.1),
                           fun h => h ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht2, hh2⟩⟩
                  rw [show Finset.univ.filter (fun e => G.head e ∈ S ∧ G.tail e ∉ S) = {e₁} from hFi,
                      show Finset.univ.filter (fun e => G.tail e ∈ S ∧ G.head e ∉ S) = {e₂} from hFo,
                      Finset.sum_singleton, Finset.sum_singleton] at hsum
                  exact Or.inl (sub_eq_zero.mp hsum.symm)
                · have hFi : F_in = {e₁, e₂} := by
                    ext e; simp only [Finset.mem_insert, Finset.mem_singleton]
                    exact ⟨hF_sub e, by rintro (rfl | rfl); exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh1, ht1⟩; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh2, ht2⟩⟩
                  have hFo : F_out = ∅ := by
                    ext e; simp only [Finset.notMem_empty, iff_false]; intro he
                    rcases hF_sub2 e he with rfl | rfl
                    · exact ht1 (Finset.mem_filter.mp he).2.1
                    · exact ht2 (Finset.mem_filter.mp he).2.1
                  rw [show Finset.univ.filter (fun e => G.head e ∈ S ∧ G.tail e ∉ S) = {e₁, e₂} from hFi,
                      show Finset.univ.filter (fun e => G.tail e ∈ S ∧ G.head e ∉ S) = ∅ from hFo,
                      Finset.sum_pair he12_ne, Finset.sum_empty, sub_zero] at hsum
                  exact Or.inr (eq_neg_of_add_eq_zero_left hsum.symm)
              -- Contract the 1-edge subgraph H1 = ({tail e₁, head e₁}, {e₁}) -> n - 1 vertices!
              let H1 : G.Subgraph :=
                { verts := {G.tail e₁, G.head e₁}
                  edges := {e₁}
                  tail_mem := fun he => by rw [Finset.mem_singleton.mp he]; exact Finset.mem_insert_self _ _
                  head_mem := fun he => by rw [Finset.mem_singleton.mp he]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _) }
              have hH1_card : H1.verts.card = 2 := Finset.card_pair (hll e₁)
              have hcard_star : Fintype.card (Option {v : V // v ∉ H1.verts}) < n := by
                rw [Fintype.card_option, Fintype.card_subtype_compl, Fintype.card_coe, hH1_card]
                have hle : H1.verts.card ≤ Fintype.card V := Finset.card_le_univ _
                omega
              let Gstar := G.contractSubgraph H1
              have hbr_star : Gstar.IsBridgeless := contractSubgraph_isBridgeless G hbr H1
              let fstar : Gstar.NZFlow Γ :=
                ⟨fun e => f.val e.1, contractSubgraph_isFlow G H1 f.val f.isFlow, fun e => f.nonzero e.1⟩
              let hstar : Gstar.NZFlow Γ :=
                ⟨fun e => h.val e.1, contractSubgraph_isFlow G H1 h.val h.isFlow, fun e => h.nonzero e.1⟩
              have hstar_join : Gstar.SigmaJoined Sig.carrier fstar hstar :=
                ih (Fintype.card (Option {v : V // v ∉ H1.verts})) hcard_star _ _ Gstar rfl hbr_star
                  fstar hstar (fun e => hh_targ e.1)
              -- Lift every move of Gstar to a single move of G via liftContractedCycle G H1!
              have hlift_H1 : ∀ gstar : Gstar.NZFlow Γ,
                  Gstar.SigmaJoined Sig.carrier fstar gstar →
                  ∃ g : G.NZFlow Γ,
                    G.SigmaJoined Sig.carrier f g ∧
                    ∀ e : {e : E // e ∉ H1.edges}, g.val e.1 = gstar.val e := by
                intro gstar hrtg
                induction hrtg with
                | refl => exact ⟨f, .refl, fun _ => rfl⟩
                | @tail astar bstar _ hstep ihp =>
                  obtain ⟨ga, hjga, hga_eq⟩ := ihp
                  rcases hstep with ⟨Cstar, lam, hlam, hbeq⟩
                  have hC_lift : ∃ C : G.DirectedCycle,
                      ∀ e (he : e ∉ H1.edges), C.sign e = Cstar.sign ⟨e, he⟩ := by
                    rcases liftContractedCycle G H1 Cstar with ⟨C, _, hCs⟩ | ⟨p, p', hp, hp', hne, hsp⟩
                    · exact ⟨C, hCs⟩
                    · simp only [H1, Finset.mem_insert, Finset.mem_singleton] at hp hp'
                      have hcases : (p = G.tail e₁ ∧ p' = G.head e₁) ∨ (p = G.head e₁ ∧ p' = G.tail e₁) := by
                        rcases hp with rfl | rfl <;> rcases hp' with rfl | rfl
                        · exact absurd rfl hne
                        · exact Or.inl ⟨rfl, rfl⟩
                        · exact Or.inr ⟨rfl, rfl⟩
                        · exact absurd rfl hne
                      obtain ⟨C, hCs, _⟩ := hsp [p, p'] [e₁] rfl (by simp [hne])
                        (fun v hv => by simp at hv; rcases hv with rfl | rfl; exact Finset.mem_insert.mpr (by rcases hcases with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp); exact Finset.mem_insert.mpr (by rcases hcases with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp))
                        (fun e he => by simp at he; subst he; exact Finset.mem_singleton_self _)
                        rfl rfl (fun k hk => by
                          have hk0 : k = 0 := by simp at hk; omega
                          subst hk0
                          rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                          · exact Or.inl ⟨rfl, rfl⟩
                          · exact Or.inr ⟨rfl, rfl⟩)
                      exact ⟨C, hCs⟩
                  obtain ⟨C, hCs⟩ := hC_lift
                  let gbVal : E → Γ := fun e => ga.val e + C.sign e • lam
                  have hgb_fl : G.IsFlow gbVal := isFlow_add ga.isFlow (isFlow_zsmul C.isFlow lam)
                  have hgb_off : ∀ e : {e : E // e ∉ H1.edges}, gbVal e.1 = bstar.val e := fun e => by
                    dsimp only [gbVal]; rw [hga_eq e, hCs e.1 e.2, hbeq e]
                  have hgb_nz : Multigraph.IsNowhereZero gbVal := fun e => by
                    by_cases he : e = e₁
                    · subst he
                      have he2_not : e₂ ∉ H1.edges := by simp [H1, he12_ne.symm]
                      have hnz2 : gbVal e₂ ≠ 0 := by rw [hgb_off ⟨e₂, he2_not⟩]; exact bstar.nonzero _
                      rcases hflow_e12 gbVal hgb_fl with heq | heq <;> rw [heq]
                      · exact hnz2
                      · exact neg_ne_zero.mpr hnz2
                    · have henot : e ∉ H1.edges := by simp [H1, he]
                      rw [hgb_off ⟨e, henot⟩]; exact bstar.nonzero _
                  exact ⟨⟨gbVal, hgb_fl, hgb_nz⟩, hjga.tail ⟨C, lam, hlam, fun _ => rfl⟩, hgb_off⟩
              obtain ⟨g, hjg, hg_off⟩ := hlift_H1 hstar hstar_join
              -- Now g agrees with h on all e ≠ e₁; by vertex conservation at G.head e₁, g = h!
              have hgh : g = h := by
                ext e
                by_cases he : e = e₁
                · rw [he]
                  have hbd : G.boundary (fun e' => g.val e' - h.val e') (G.head e₁) = 0 :=
                    isFlow_sub g.isFlow h.isFlow (G.head e₁)
                  rw [boundary_eq_sum_ite] at hbd
                  rw [Finset.sum_eq_single e₁] at hbd
                  · simp [hll e₁] at hbd; exact sub_eq_zero.mp hbd
                  · intro e' _ hne
                    have hnot : e' ∉ H1.edges := by simp [H1, hne]
                    have heq' : g.val e' = h.val e' := hg_off ⟨e', hnot⟩
                    simp [heq']
                  · intro hm; exact absurd (Finset.mem_univ _) hm
                · exact hg_off ⟨e, by simp [H1, he]⟩
              exact hgh ▸ hjg
          · -- Subcase 1: G is disconnected (∃ non-trivial S with cutEdges S = ∅)
            unfold Multigraph.IsEdgeConnected at hconn1
            push Not at hconn1
            rcases hconn1 with ⟨S, hSne, hScne, hlt1⟩
            have hcut0 : G.cutEdges S = ∅ := Finset.card_eq_zero.mp (by omega)
            have hno_cross : ∀ e : E, (G.tail e ∈ S ∧ G.head e ∈ S) ∨ (G.tail e ∉ S ∧ G.head e ∉ S) := by
              intro e
              by_cases ht : G.tail e ∈ S <;> by_cases hh : G.head e ∈ S
              · exact Or.inl ⟨ht, hh⟩
              · exfalso; have : e ∈ G.cutEdges S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ⟨ht, hh⟩⟩
                rw [hcut0] at this; exact Finset.notMem_empty _ this
              · exfalso; have : e ∈ G.cutEdges S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨ht, hh⟩⟩
                rw [hcut0] at this; exact Finset.notMem_empty _ this
              · exact Or.inr ⟨ht, hh⟩
            -- Split into G₁ = induced G S and G₂ = induced G (univ \ S), each < n vertices
            have hsolve_comp : ∀ (U : Finset V), U.card < n →
                (∀ e : E, (G.tail e ∈ U ∧ G.head e ∈ U) ∨ (G.tail e ∉ U ∧ G.head e ∉ U)) →
                ∀ cur : G.NZFlow Γ,
                  ∃ nxt : G.NZFlow Γ,
                    G.SigmaJoined Sig.carrier cur nxt ∧
                    (∀ e, G.tail e ∈ U → nxt.val e = h.val e) ∧
                    (∀ e, G.tail e ∉ U → nxt.val e = cur.val e) := by
              intro U hUcard hUcl cur
              let HU := Multigraph.Subgraph.induced G U
              let GU := HU.toMultigraph
              have hcardU : Fintype.card {v : V // v ∈ HU.verts} = U.card := Fintype.card_coe U
              have hbrU : GU.IsBridgeless := by
                intro e hnot
                have hex : ∃ C : G.Subgraph, C.IsCycle ∧ e.1 ∈ C.edges := by
                  by_contra hn'; exact hbr e.1 hn'
                rcases hex with ⟨C, hC, heC⟩
                have hCU : C.verts ⊆ U ∧ C.edges ⊆ HU.edges := by
                  have htU : G.tail e.1 ∈ U := (Finset.mem_filter.mp e.2).2.1
                  have hv_inU : ∀ v ∈ C.verts, v ∈ U := by
                    intro v hv
                    have hrtg := hC.1.2 (G.tail e.1) (C.tail_mem heC) v hv
                    clear hv
                    induction hrtg with
                    | refl => exact htU
                    | tail _ hs ihp =>
                      rcases hs with ⟨x, _, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
                      · rcases hUcl x with ⟨htx, hhx⟩ | ⟨htx, _⟩
                        · exact h2 ▸ hhx
                        · exact absurd (h1 ▸ ihp) htx
                      · rcases hUcl x with ⟨htx, _⟩ | ⟨_, hhx⟩
                        · exact h1 ▸ htx
                        · exact absurd (h2 ▸ ihp) hhx
                  refine ⟨hv_inU, fun x hx => Finset.mem_filter.mpr ⟨Finset.mem_univ _,
                    hv_inU _ (C.tail_mem hx), hv_inU _ (C.head_mem hx)⟩⟩
                -- Restrict C to GU
                let CU : GU.Subgraph :=
                  { verts := Finset.univ.filter (fun v : {v // v ∈ HU.verts} => v.1 ∈ C.verts)
                    edges := Finset.univ.filter (fun x : {x // x ∈ HU.edges} => x.1 ∈ C.edges)
                    tail_mem := fun hx => Finset.mem_filter.mpr ⟨Finset.mem_univ _, C.tail_mem (Finset.mem_filter.mp hx).2⟩
                    head_mem := fun hx => Finset.mem_filter.mpr ⟨Finset.mem_univ _, C.head_mem (Finset.mem_filter.mp hx).2⟩ }
                refine hnot ⟨CU, ⟨⟨?_, ?_⟩, ?_⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, heC⟩⟩
                · obtain ⟨v, hv⟩ := hC.1.1; exact ⟨⟨v, hCU.1 hv⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩⟩
                · intro u hu v hv
                  have hrtg := hC.1.2 u.1 (Finset.mem_filter.mp hu).2 v.1 (Finset.mem_filter.mp hv).2
                  have hgo : ∀ a b, Relation.ReflTransGen C.Adj a b → ∀ (ha : a ∈ HU.verts) (hb : b ∈ HU.verts),
                      Relation.ReflTransGen CU.Adj ⟨a, ha⟩ ⟨b, hb⟩ := by
                    intro a b hab
                    induction hab with
                    | refl => intro _ _; exact .refl
                    | @tail x y _ hs ihp =>
                      intro ha hy
                      rcases hs with ⟨e', he', ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
                      · have hxU : x ∈ HU.verts := h1 ▸ HU.tail_mem (hCU.2 he')
                        exact (ihp ha hxU).tail ⟨⟨e', hCU.2 he'⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he'⟩,
                          Or.inl ⟨Subtype.ext h1, Subtype.ext h2⟩⟩
                      · have hxU : x ∈ HU.verts := h2 ▸ HU.head_mem (hCU.2 he')
                        exact (ihp ha hxU).tail ⟨⟨e', hCU.2 he'⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he'⟩,
                          Or.inr ⟨Subtype.ext h1, Subtype.ext h2⟩⟩
                  exact hgo u.1 v.1 hrtg u.2 v.2
                · intro v hv
                  have hd := hC.2 v.1 (Finset.mem_filter.mp hv).2
                  unfold Multigraph.Subgraph.deg at hd ⊢
                  have h1 : (CU.edges.filter (fun x => GU.tail x = v)).card = (C.edges.filter (fun x => G.tail x = v.1)).card := by
                    refine Finset.card_bij (fun x _ => x.1) (fun x hx => ?_) (fun _ _ _ _ h => Subtype.ext h)
                      (fun x hx => ⟨⟨x, hCU.2 (Finset.mem_filter.mp hx).1⟩, ?_, rfl⟩)
                    · rw [Finset.mem_filter] at hx ⊢; exact ⟨(Finset.mem_filter.mp hx.1).2, congrArg Subtype.val hx.2⟩
                    · rw [Finset.mem_filter] at hx ⊢; exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx.1⟩, Subtype.ext hx.2⟩
                  have h2 : (CU.edges.filter (fun x => GU.head x = v)).card = (C.edges.filter (fun x => G.head x = v.1)).card := by
                    refine Finset.card_bij (fun x _ => x.1) (fun x hx => ?_) (fun _ _ _ _ h => Subtype.ext h)
                      (fun x hx => ⟨⟨x, hCU.2 (Finset.mem_filter.mp hx).1⟩, ?_, rfl⟩)
                    · rw [Finset.mem_filter] at hx ⊢; exact ⟨(Finset.mem_filter.mp hx.1).2, congrArg Subtype.val hx.2⟩
                    · rw [Finset.mem_filter] at hx ⊢; exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx.1⟩, Subtype.ext hx.2⟩
                  rw [h1, h2]; exact hd
              have hfl_res : ∀ (x : E → Γ), G.IsFlow x → GU.IsFlow (fun e => x e.1) := fun x hx v => by
                have hbd := hx v.1
                trans (G.boundary x v.1)
                · rw [boundary_eq_sum_ite, boundary_eq_sum_ite]; symm
                  rw [← Finset.sum_subset (Finset.subset_univ HU.edges)]
                  · refine Finset.sum_bij (fun e he => ⟨e, he⟩) (fun _ _ => Finset.mem_univ _)
                      (fun _ _ _ _ h => congrArg Subtype.val h) (fun e _ => ⟨e.1, e.2, rfl⟩) (fun e _ => ?_)
                    by_cases h1 : G.head e = v.1 <;> by_cases h2 : G.tail e = v.1 <;>
                      simp [GU, Multigraph.Subgraph.toMultigraph, Subtype.ext_iff, h1, h2]
                  · intro e _ hnot
                    have hnt : G.tail e ≠ v.1 := fun ht => by
                      rcases hUcl e with ⟨htU, hhU⟩ | ⟨htU, _⟩
                      · exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, htU, hhU⟩)
                      · exact htU (ht.symm ▸ v.2)
                    have hnh : G.head e ≠ v.1 := fun hh => by
                      rcases hUcl e with ⟨htU, hhU⟩ | ⟨_, hhU⟩
                      · exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, htU, hhU⟩)
                      · exact hhU (hh.symm ▸ v.2)
                    simp [hnt, hnh]
                · exact hbd
              let curU : GU.NZFlow Γ := ⟨fun e => cur.val e.1, hfl_res cur.val cur.isFlow, fun e => cur.nonzero e.1⟩
              let hU : GU.NZFlow Γ := ⟨fun e => h.val e.1, hfl_res h.val h.isFlow, fun e => h.nonzero e.1⟩
              have hjU : GU.SigmaJoined Sig.carrier curU hU :=
                ih U.card hUcard _ _ GU hcardU hbrU curU hU (fun e => hh_targ e.1)
              have hlift_U : ∀ gU : GU.NZFlow Γ, GU.SigmaJoined Sig.carrier curU gU →
                  ∃ g : G.NZFlow Γ, G.SigmaJoined Sig.carrier cur g ∧
                    (∀ e : {e : E // e ∈ HU.edges}, g.val e.1 = gU.val e) ∧
                    (∀ e, e ∉ HU.edges → g.val e = cur.val e) := by
                intro gU hrtg
                induction hrtg with
                | refl => exact ⟨cur, .refl, fun _ => rfl, fun _ _ => rfl⟩
                | @tail aU bU _ hstep ihp =>
                  obtain ⟨ga, hjga, hga_in, hga_out⟩ := ihp
                  rcases hstep with ⟨CU, lam, hlam, hbeq⟩
                  let C := liftDCFromSub G HU CU
                  let gbVal : E → Γ := fun e => ga.val e + C.sign e • lam
                  have hgb_fl : G.IsFlow gbVal := isFlow_add ga.isFlow (isFlow_zsmul C.isFlow lam)
                  have hgb_in : ∀ e : {e : E // e ∈ HU.edges}, gbVal e.1 = bU.val e := fun e => by
                    dsimp only [gbVal, C, liftDCFromSub]; rw [dif_pos e.2, hga_in e, hbeq e]
                  have hgb_out : ∀ e, e ∉ HU.edges → gbVal e = cur.val e := fun e he => by
                    dsimp only [gbVal, C, liftDCFromSub]; rw [dif_neg he, zero_zsmul, add_zero, hga_out e he]
                  have hgb_nz : Multigraph.IsNowhereZero gbVal := fun e => by
                    by_cases he : e ∈ HU.edges
                    · rw [hgb_in ⟨e, he⟩]; exact bU.nonzero _
                    · rw [hgb_out e he]; exact cur.nonzero e
                  exact ⟨⟨gbVal, hgb_fl, hgb_nz⟩, hjga.tail ⟨C, lam, hlam, fun _ => rfl⟩, hgb_in, hgb_out⟩
              obtain ⟨nxt, hjn, hn_in, hn_out⟩ := hlift_U hU hjU
              refine ⟨nxt, hjn, fun e htU => ?_, fun e htnot => ?_⟩
              · have heHU : e ∈ HU.edges := by
                  rcases hUcl e with ⟨h1, h2⟩ | ⟨h1, _⟩
                  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1, h2⟩
                  · exact absurd htU h1
                exact hn_in ⟨e, heHU⟩
              · have henot : e ∉ HU.edges := fun hm => htnot (Finset.mem_filter.mp hm).2.1
                exact hn_out e henot
            have hScard_lt : S.card < n := by
              have hpos : 0 < (Finset.univ \ S).card := Finset.card_pos.mpr hScne
              have hsd : (Finset.univ \ S).card = Fintype.card V - S.card := by
                rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
              omega
            have hSccard_lt : (Finset.univ \ S).card < n := by
              have hpos : 0 < S.card := Finset.card_pos.mpr hSne
              have hsd : (Finset.univ \ S).card = Fintype.card V - S.card := by
                rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
              omega
            obtain ⟨mid, hj1, hmid_S, _⟩ := hsolve_comp S hScard_lt hno_cross f
            have hno_cross_c : ∀ e : E,
                (G.tail e ∈ Finset.univ \ S ∧ G.head e ∈ Finset.univ \ S) ∨
                (G.tail e ∉ Finset.univ \ S ∧ G.head e ∉ Finset.univ \ S) := fun e => by
              simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, not_not]
              rcases hno_cross e with h | h
              · exact Or.inr h
              · exact Or.inl h
            obtain ⟨fin, hj2, hfin_Sc, hfin_S⟩ := hsolve_comp (Finset.univ \ S) hSccard_lt hno_cross_c mid
            have hfeq : fin = h := by
              ext e
              by_cases ht : G.tail e ∈ S
              · rw [hfin_S e (by simp [ht]), hmid_S e ht]
              · exact hfin_Sc e (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ht⟩)
            exact hfeq ▸ hj1.trans hj2
      -- Step 2: General bridgeless graphs on n vertices (delete loops -> loopless case -> fix loops via R3)
      intro V E _ _ _ _ G hcard hbr f h hh_targ
      let G' := G.deleteLoops
      have hll' : G'.IsLoopless := fun e => e.2
      have hbr' : G'.IsBridgeless := deleteLoops_isBridgeless G hbr
      have hfl_dl : ∀ (x : E → Γ), G.IsFlow x → G'.IsFlow (fun e => x e.1) := fun x hx v => by
        have hbd := hx v
        trans (G.boundary x v)
        · rw [boundary_eq_sum_ite, boundary_eq_sum_ite]; symm
          rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.filter (fun e : E => G.tail e ≠ G.head e)))]
          · refine Finset.sum_bij (fun e he => ⟨e, (Finset.mem_filter.mp he).2⟩) (fun _ _ => Finset.mem_univ _)
              (fun _ _ _ _ h => congrArg Subtype.val h)
              (fun e _ => ⟨e.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, e.2⟩, rfl⟩)
              (fun _ _ => rfl)
          · intro e _ hnot
            have hlp : G.tail e = G.head e := by
              by_contra hne; exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
            rw [hlp, sub_self]
        · exact hbd
      let f' : G'.NZFlow Γ := ⟨fun e => f.val e.1, hfl_dl f.val f.isFlow, fun e => f.nonzero e.1⟩
      let h' : G'.NZFlow Γ := ⟨fun e => h.val e.1, hfl_dl h.val h.isFlow, fun e => h.nonzero e.1⟩
      have hj' : G'.SigmaJoined Sig.carrier f' h' :=
        hloopless V _ G' hcard hbr' hll' f' h' (fun e => hh_targ e.1)
      -- Lift moves from G.deleteLoops to G (leaving loops fixed)
      have hlift_dl : ∀ g' : G'.NZFlow Γ, G'.SigmaJoined Sig.carrier f' g' →
          ∃ g : G.NZFlow Γ, G.SigmaJoined Sig.carrier f g ∧
            (∀ e : {e : E // G.tail e ≠ G.head e}, g.val e.1 = g'.val e) := by
        intro g' hrtg
        induction hrtg with
        | refl => exact ⟨f, .refl, fun _ => rfl⟩
        | @tail a' b' _ hstep ihp =>
          obtain ⟨ga, hjga, hga_eq⟩ := ihp
          rcases hstep with ⟨C', lam, hlam, hbeq⟩
          let C : G.DirectedCycle :=
            { sub :=
                { verts := C'.sub.verts
                  edges := C'.sub.edges.map ⟨Subtype.val, Subtype.val_injective⟩
                  tail_mem := fun he => by
                    rw [Finset.mem_map] at he; rcases he with ⟨e', he', rfl⟩; exact C'.sub.tail_mem he'
                  head_mem := fun he => by
                    rw [Finset.mem_map] at he; rcases he with ⟨e', he', rfl⟩; exact C'.sub.head_mem he' }
              isCycle := by
                refine ⟨⟨C'.isCycle.1.1, fun u hu v hv => ?_⟩, fun v hv => ?_⟩
                · have hrtg' := C'.isCycle.1.2 u hu v hv
                  clear hv
                  induction hrtg' with
                  | refl => exact .refl
                  | tail _ hs ihc =>
                    rcases hs with ⟨e', he', hinc⟩
                    exact ihc.tail ⟨e'.1, Finset.mem_map.mpr ⟨e', he', rfl⟩, hinc⟩
                · have hd := C'.isCycle.2 v hv
                  unfold Multigraph.Subgraph.deg at hd ⊢
                  have h1 : ((C'.sub.edges.map ⟨Subtype.val, Subtype.val_injective⟩).filter (fun e => G.tail e = v)).card =
                      (C'.sub.edges.filter (fun e => G'.tail e = v)).card := by
                    refine Finset.card_bij (fun e he => ⟨e, ?_⟩) (fun e he => ?_)
                      (fun _ _ _ _ h => congrArg Subtype.val h) (fun e' he' => ⟨e'.1, ?_, rfl⟩)
                    · have hm := (Finset.mem_filter.mp he).1; rw [Finset.mem_map] at hm
                      rcases hm with ⟨e', _, rfl⟩; exact e'.2
                    · rw [Finset.mem_filter] at he ⊢; rw [Finset.mem_map] at he
                      rcases he.1 with ⟨e', he', hval⟩
                      have heq : e' = ⟨e, hval ▸ e'.2⟩ := Subtype.ext hval
                      exact ⟨heq ▸ he', he.2⟩
                    · rw [Finset.mem_filter] at he' ⊢
                      exact ⟨Finset.mem_map.mpr ⟨e', he'.1, rfl⟩, he'.2⟩
                  have h2 : ((C'.sub.edges.map ⟨Subtype.val, Subtype.val_injective⟩).filter (fun e => G.head e = v)).card =
                      (C'.sub.edges.filter (fun e => G'.head e = v)).card := by
                    refine Finset.card_bij (fun e he => ⟨e, ?_⟩) (fun e he => ?_)
                      (fun _ _ _ _ h => congrArg Subtype.val h) (fun e' he' => ⟨e'.1, ?_, rfl⟩)
                    · have hm := (Finset.mem_filter.mp he).1; rw [Finset.mem_map] at hm
                      rcases hm with ⟨e', _, rfl⟩; exact e'.2
                    · rw [Finset.mem_filter] at he ⊢; rw [Finset.mem_map] at he
                      rcases he.1 with ⟨e', he', hval⟩
                      have heq : e' = ⟨e, hval ▸ e'.2⟩ := Subtype.ext hval
                      exact ⟨heq ▸ he', he.2⟩
                    · rw [Finset.mem_filter] at he' ⊢
                      exact ⟨Finset.mem_map.mpr ⟨e', he'.1, rfl⟩, he'.2⟩
                  rw [h1, h2]; exact hd
              sign := fun e => if hne : G.tail e ≠ G.head e then C'.sign ⟨e, hne⟩ else 0
              sign_mem := fun {e} he => by
                simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at he
                rcases he with ⟨e', he', rfl⟩
                change (if hne : G.tail e'.1 ≠ G.head e'.1 then C'.sign ⟨e'.1, hne⟩ else 0) = 1 ∨
                  (if hne : G.tail e'.1 ≠ G.head e'.1 then C'.sign ⟨e'.1, hne⟩ else 0) = -1
                rw [dif_pos e'.2]; exact C'.sign_mem he'
              sign_zero := fun {e} he => by
                change (if hne : G.tail e ≠ G.head e then C'.sign ⟨e, hne⟩ else 0) = 0
                by_cases hne : G.tail e ≠ G.head e
                · rw [dif_pos hne]
                  exact C'.sign_zero fun hm => he (Finset.mem_map.mpr ⟨⟨e, hne⟩, hm, rfl⟩)
                · rw [dif_neg hne]
              isFlow := fun v => by
                have hbd := C'.isFlow v
                trans (G'.boundary C'.sign v)
                · rw [boundary_eq_sum_ite, boundary_eq_sum_ite]
                  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.filter (fun e : E => G.tail e ≠ G.head e)))]
                  · refine Finset.sum_bij (fun e he => ⟨e, (Finset.mem_filter.mp he).2⟩) (fun _ _ => Finset.mem_univ _)
                      (fun _ _ _ _ h => congrArg Subtype.val h)
                      (fun e _ => ⟨e.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, e.2⟩, rfl⟩)
                      (fun e he => by simp [(Finset.mem_filter.mp he).2, G', Multigraph.deleteLoops])
                  · intro e _ hnot
                    have hlp : G.tail e = G.head e := by
                      by_contra hne; exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
                    simp [hlp]
                · exact hbd }
          let gbVal : E → Γ := fun e => ga.val e + C.sign e • lam
          have hgb_fl : G.IsFlow gbVal := isFlow_add ga.isFlow (isFlow_zsmul C.isFlow lam)
          have hgb_nl : ∀ e : {e : E // G.tail e ≠ G.head e}, gbVal e.1 = b'.val e := fun e => by
            dsimp only [gbVal, C]; rw [dif_pos e.2, hga_eq e, hbeq e]
          have hgb_nz : Multigraph.IsNowhereZero gbVal := fun e => by
            by_cases hne : G.tail e ≠ G.head e
            · rw [hgb_nl ⟨e, hne⟩]; exact b'.nonzero _
            · dsimp only [gbVal, C]; rw [dif_neg hne, zero_zsmul, add_zero]; exact ga.nonzero e
          exact ⟨⟨gbVal, hgb_fl, hgb_nz⟩, hjga.tail ⟨C, lam, hlam, fun _ => rfl⟩, hgb_nl⟩
      obtain ⟨fmid, hjmid, hfmid_nl⟩ := hlift_dl h' hj'
      -- Now fix every loop e via CondR3 on directedCycleOfLoop G e
      let Loops : Finset E := Finset.univ.filter (fun e => G.tail e = G.head e)
      have hfix_loops : ∀ (L : Finset E), L ⊆ Loops →
          ∃ g : G.NZFlow Γ, G.SigmaJoined Sig.carrier fmid g ∧
            (∀ e, G.tail e ≠ G.head e → g.val e = h.val e) ∧
            (∀ e ∈ L, g.val e = h.val e) := by
        intro L
        induction L using Finset.induction_on with
        | empty =>
          intro _
          exact ⟨fmid, .refl, fun e hne => hfmid_nl ⟨e, hne⟩, fun _ he => absurd he (Finset.notMem_empty _)⟩
        | @insert e0 L' he0_not ihL =>
          intro hsub
          obtain ⟨g1, hj1, hg1_nl, hg1_L'⟩ := ihL ((Finset.subset_insert _ _).trans hsub)
          have hlp0 : G.tail e0 = G.head e0 := (Finset.mem_filter.mp (hsub (Finset.mem_insert_self _ _))).2
          let C0 := directedCycleOfLoop G e0 hlp0
          obtain ⟨_, _, hrtg0⟩ := hR3 (g1.val e0) (h.val e0) (g1.nonzero e0) (h.nonzero e0)
          have hwalk0 : ∀ x : Γ,
              Relation.ReflTransGen (fun u v => u ∈ {a : Γ | a ≠ 0} ∧ v ∈ {a : Γ | a ≠ 0} ∧
                ∃ s ∈ Sig.carrier, v = u + s) (g1.val e0) x →
              ∃ g2 : G.NZFlow Γ, G.SigmaJoined Sig.carrier g1 g2 ∧
                g2.val e0 = x ∧ ∀ e, e ≠ e0 → g2.val e = g1.val e := by
            intro x hx
            induction hx with
            | refl => exact ⟨g1, .refl, rfl, fun _ _ => rfl⟩
            | @tail u v _ hstep ihw =>
              obtain ⟨gu, hju, hgu0, hgu_oth⟩ := ihw
              rcases hstep with ⟨_, hvne, s, hs, rfl⟩
              let gvVal : E → Γ := fun e => gu.val e + C0.sign e • s
              have hgv_fl : G.IsFlow gvVal := isFlow_add gu.isFlow (isFlow_zsmul C0.isFlow s)
              have hgv0 : gvVal e0 = u + s := by
                dsimp only [gvVal, C0, directedCycleOfLoop]; simp [hgu0]
              have hgv_oth : ∀ e, e ≠ e0 → gvVal e = g1.val e := fun e hne => by
                dsimp only [gvVal, C0, directedCycleOfLoop]; simp [hne, hgu_oth e hne]
              have hgv_nz : Multigraph.IsNowhereZero gvVal := fun e => by
                by_cases he : e = e0
                · subst he; rw [hgv0]; exact hvne
                · rw [hgv_oth e he]; exact g1.nonzero e
              exact ⟨⟨gvVal, hgv_fl, hgv_nz⟩, hju.tail ⟨C0, s, hs, fun _ => rfl⟩, hgv0, hgv_oth⟩
          obtain ⟨g2, hj2, hg2_0, hg2_oth⟩ := hwalk0 (h.val e0) hrtg0
          refine ⟨g2, hj1.trans hj2, fun e hne => ?_, fun e he => ?_⟩
          · have hne0 : e ≠ e0 := fun h => hne (h ▸ hlp0)
            rw [hg2_oth e hne0, hg1_nl e hne]
          · rw [Finset.mem_insert] at he
            rcases he with rfl | he'
            · exact hg2_0
            · have hne0 : e ≠ e0 := fun h => he0_not (h ▸ he')
              rw [hg2_oth e hne0, hg1_L' e he']
      obtain ⟨gfin, hjfin, hgfin_nl, hgfin_L⟩ := hfix_loops Loops Finset.Subset.rfl
      have hgeq : gfin = h := by
        ext e
        by_cases hne : G.tail e ≠ G.head e
        · exact hgfin_nl e hne
        · push Not at hne
          exact hgfin_L e (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
      exact hgeq ▸ hjmid.trans hjfin
  -- Assemble all three conclusions of Theorem 1.3!
  have h1 : ∀ (f h : G.NZFlow Γ), (∀ e, quoFlow B h.val e ≠ 0) → G.SigmaJoined Sig.carrier f h :=
    hpart1 (Fintype.card V) V E G rfl hbr
  -- Construct a target h via SeymourSixFlow + (E4)
  have hex_targ : ∃ h : G.NZFlow Γ, ∀ e, quoFlow B h.val e ≠ 0 := by
    obtain ⟨v⟩ := hSeymour V E G (Γ ⧸ B) hbr (by omega)
    obtain ⟨T₀, hT₀⟩ := exists_spanningForest G
    have hE3 := (lem_2_1_a (A := Γ ⧸ B) G T₀ hT₀).2.2 v.val v.isFlow
    obtain ⟨hval, hfl, hquo⟩ := sec4_E4_of_E3 G B v.val v.isFlow hE3
    have hnz : Multigraph.IsNowhereZero hval := fun e =>
      (sec4_E1_proved (V := V) B hval e).mpr (Or.inl (by rw [hquo e]; exact v.nonzero e))
    exact ⟨⟨hval, hfl, hnz⟩, fun e => by rw [hquo e]; exact v.nonzero e⟩
  have h2 : ∀ (f g : G.NZFlow Γ), G.SigmaJoined Sig.carrier f g := by
    intro f g
    obtain ⟨h, hh⟩ := hex_targ
    exact (h1 f h hh).trans (sigmaJoined_symm (h1 g h hh))
  have h3 : G.FlowGraphConnected Γ := by
    intro f g
    have hj := h2 f g
    induction hj with
    | refl => exact .refl
    | tail _ hs ih =>
      rcases hs with ⟨C, lam, hlam, heq⟩
      have hne0 : lam ≠ 0 := fun h0 => Sig.zero_not_mem (h0 ▸ hlam)
      exact ih.tail ⟨C, lam, hne0, heq⟩
  exact ⟨h1, h2, h3⟩

end Flow.Proofs
