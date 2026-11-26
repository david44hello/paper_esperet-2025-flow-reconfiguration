-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Flow.Defs.Literature
import Flow.Proofs.Elementary
import Flow.Proofs.Basic
import Flow.Proofs.Blocks
import Flow.Proofs.FlowsQ
import Flow.Proofs.TutteFlowPoly
import Flow.Proofs.LiftMove
import Flow.Proofs.Master
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Tactic

/-!
# Deriving `SeymourSixFlow` from `JLPTWellColouring`

Using:
1. Bottom-up `ZMod 3`-connectivity of every `2`-constructible multigraph (`twoConstr_ZMod3_connected`),
2. `ZMod 2`-fundamental cycles of red edges in the blue spanning tree (`tc3ec_has_zmod6_flow`),
3. Reduction of general bridgeless graphs to loopless `3`-edge-connected cut-vertex-free graphs
   + Lemma 3.4(b) (`lem_3_4_b`),
4. Tutte's flow polynomial invariance (`nzflow_of_zmod6`).
-/

namespace Flow.Proofs

open Flow

/-! ### Step 1: Every `2`-constructible graph is `ZMod 3`-connected -/

private lemma zmod3_split_nonzero (d : ZMod 3) :
    ∃ a b : ZMod 3, a ≠ 0 ∧ b ≠ 0 ∧ a + b = d := by
  decide +revert

/-- On any `2`-constructible subgraph `(W₀, F₀)` of `M`, every zero-sum `ZMod 3` demand `β`
on `W₀` is realized by an edge map supported and nowhere zero on `F₀`. -/
lemma twoConstr_ZMod3_connected {W F : Type} [DecidableEq W] [DecidableEq F]
    (M : Multigraph W F) :
    ∀ {W₀ : Finset W} {F₀ : Finset F} (_tc : TwoConstruction M W₀ F₀)
      (β : W → ZMod 3), ∑ w ∈ W₀, β w = 0 →
      ∃ g : F → ZMod 3,
        (∀ e ∈ F₀, g e ≠ 0) ∧
        (∀ e ∉ F₀, g e = 0) ∧
        (∀ w ∈ W₀,
          (∑ e ∈ F₀.filter (fun e => M.head e = w), g e) -
          (∑ e ∈ F₀.filter (fun e => M.tail e = w), g e) = β w) := by
  intro W₀ F₀ tc
  induction tc with
  | single w =>
    intro β hsum
    rw [Finset.sum_singleton] at hsum
    refine ⟨fun _ => 0, fun _ h => absurd h (Finset.notMem_empty _), fun _ _ => rfl, fun u hu => ?_⟩
    rw [Finset.mem_singleton.mp hu, hsum]; simp
  | @join W₁ W₂ F₁ F₂ left right e f hdisjW hdisjF he_ne_f he1 he2 hf1 hf2 he_cr hf_cr ihl ihr =>
    intro β hsum
    let d : ZMod 3 := ∑ w ∈ W₁, β w
    obtain ⟨a, b, ha, hb, hab⟩ := zmod3_split_nonzero d
    let ge : ZMod 3 := if M.head e ∈ W₁ then a else -a
    let gf : ZMod 3 := if M.head f ∈ W₁ then b else -b
    have hge_ne : ge ≠ 0 := by dsimp only [ge]; split_ifs; exact ha; exact neg_ne_zero.mpr ha
    have hgf_ne : gf ≠ 0 := by dsimp only [gf]; split_ifs; exact hb; exact neg_ne_zero.mpr hb
    let bd1 (x : F) (gx : ZMod 3) (w : W) : ZMod 3 :=
      (if M.head x = w then gx else 0) - (if M.tail x = w then gx else 0)
    have hsum_bd1_W1 : ∀ (x : F) (c : ZMod 3),
        ((M.tail x ∈ W₁ ∧ M.head x ∈ W₂) ∨ (M.tail x ∈ W₂ ∧ M.head x ∈ W₁)) →
        ∑ w ∈ W₁, bd1 x (if M.head x ∈ W₁ then c else -c) w = c := by
      intro x c hcr
      dsimp only [bd1]
      rw [Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq]
      rcases hcr with ⟨ht1, hh2⟩ | ⟨ht2, hh1⟩
      · have hnot : M.head x ∉ W₁ := Finset.disjoint_right.mp hdisjW hh2
        simp [ht1, hnot]
      · have hnot : M.tail x ∉ W₁ := Finset.disjoint_right.mp hdisjW ht2
        simp [hh1, hnot]
    have hsum_bd1_W2 : ∀ (x : F) (c : ZMod 3),
        ((M.tail x ∈ W₁ ∧ M.head x ∈ W₂) ∨ (M.tail x ∈ W₂ ∧ M.head x ∈ W₁)) →
        ∑ w ∈ W₂, bd1 x (if M.head x ∈ W₁ then c else -c) w = -c := by
      intro x c hcr
      dsimp only [bd1]
      rw [Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq]
      rcases hcr with ⟨ht1, hh2⟩ | ⟨ht2, hh1⟩
      · have hnot1 : M.head x ∉ W₁ := Finset.disjoint_right.mp hdisjW hh2
        have hnot2 : M.tail x ∉ W₂ := Finset.disjoint_left.mp hdisjW ht1
        simp [hh2, hnot1, hnot2]
      · have hnot2 : M.head x ∉ W₂ := Finset.disjoint_left.mp hdisjW hh1
        simp [hh1, ht2, hnot2]
    let β' : W → ZMod 3 := fun w => β w - bd1 e ge w - bd1 f gf w
    have hsum1 : ∑ w ∈ W₁, β' w = 0 := by
      dsimp only [β']
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
          hsum_bd1_W1 e a he_cr, hsum_bd1_W1 f b hf_cr]
      change d - a - b = 0
      rw [← hab]; abel
    have hsum2 : ∑ w ∈ W₂, β' w = 0 := by
      have htot : ∑ w ∈ W₁, β w + ∑ w ∈ W₂, β w = 0 := by
        rw [← Finset.sum_union hdisjW]; exact hsum
      dsimp only [β']
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
          hsum_bd1_W2 e a he_cr, hsum_bd1_W2 f b hf_cr]
      have hW2 : ∑ w ∈ W₂, β w = -d := eq_neg_of_add_eq_zero_right htot
      rw [hW2, ← hab]; abel
    obtain ⟨g₁, hg₁_nz, hg₁_0, hg₁_bd⟩ := ihl β' hsum1
    obtain ⟨g₂, hg₂_nz, hg₂_0, hg₂_bd⟩ := ihr β' hsum2
    let g : F → ZMod 3 := fun x => if x = e then ge else if x = f then gf else g₁ x + g₂ x
    have hF_split : ∀ (p : F → Prop) [DecidablePred p],
        ∑ x ∈ (insert e (insert f (F₁ ∪ F₂))).filter p, g x =
        (if p e then ge else 0) + (if p f then gf else 0) +
        (∑ x ∈ F₁.filter p, g₁ x) + (∑ x ∈ F₂.filter p, g₂ x) := by
      intro p _
      have he_not : e ∉ insert f (F₁ ∪ F₂) := by simp [he_ne_f, he1, he2]
      have hf_not : f ∉ F₁ ∪ F₂ := by simp [hf1, hf2]
      rw [Finset.filter_insert, Finset.filter_insert, Finset.filter_union]
      have h1 : ∀ (a₀ : F) (S : Finset F) (hnot : a₀ ∉ S),
          ∑ x ∈ (if p a₀ then insert a₀ S else S), g x = (if p a₀ then g a₀ else 0) + ∑ x ∈ S, g x := by
        intro a₀ S hnot
        split_ifs with hp
        · rw [Finset.sum_insert hnot]
        · rw [zero_add]
      have he_not' : e ∉ (if p f then insert f ((F₁.filter p) ∪ (F₂.filter p)) else (F₁.filter p) ∪ (F₂.filter p)) := by
        intro hm; apply he_not; split_ifs at hm
        · rw [Finset.mem_insert] at hm; rcases hm with rfl | hm
          · exact Finset.mem_insert_self _ _
          · rw [Finset.mem_union] at hm
            exact Finset.mem_insert_of_mem (by rcases hm with h | h; exact Finset.mem_union_left _ (Finset.mem_filter.mp h).1; exact Finset.mem_union_right _ (Finset.mem_filter.mp h).1)
        · rw [Finset.mem_union] at hm
          exact Finset.mem_insert_of_mem (by rcases hm with h | h; exact Finset.mem_union_left _ (Finset.mem_filter.mp h).1; exact Finset.mem_union_right _ (Finset.mem_filter.mp h).1)
      have hf_not' : f ∉ (F₁.filter p) ∪ (F₂.filter p) := fun hm => hf_not (by
        rw [Finset.mem_union] at hm
        rcases hm with h | h
        · exact Finset.mem_union_left _ (Finset.mem_filter.mp h).1
        · exact Finset.mem_union_right _ (Finset.mem_filter.mp h).1)
      rw [h1 e _ he_not', h1 f _ hf_not',
          Finset.sum_union (Disjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _) hdisjF)]
      have hge_v : g e = ge := by simp [g]
      have hgf_v : g f = gf := by simp [g, Ne.symm he_ne_f]
      have hgF1 : ∑ x ∈ F₁.filter p, g x = ∑ x ∈ F₁.filter p, g₁ x :=
        Finset.sum_congr rfl fun x hx => by
          have hx1 := (Finset.mem_filter.mp hx).1
          have hne_e : x ≠ e := fun h => he1 (h ▸ hx1)
          have hne_f : x ≠ f := fun h => hf1 (h ▸ hx1)
          have hnot2 : x ∉ F₂ := Finset.disjoint_left.mp hdisjF hx1
          simp [g, hne_e, hne_f, hg₂_0 x hnot2]
      have hgF2 : ∑ x ∈ F₂.filter p, g x = ∑ x ∈ F₂.filter p, g₂ x :=
        Finset.sum_congr rfl fun x hx => by
          have hx2 := (Finset.mem_filter.mp hx).1
          have hne_e : x ≠ e := fun h => he2 (h ▸ hx2)
          have hne_f : x ≠ f := fun h => hf2 (h ▸ hx2)
          have hnot1 : x ∉ F₁ := Finset.disjoint_right.mp hdisjF hx2
          simp [g, hne_e, hne_f, hg₁_0 x hnot1]
      rw [hge_v, hgf_v, hgF1, hgF2]; abel
    -- Endpoints of F₁ stay inside W₁ and endpoints of F₂ stay inside W₂
    have hF_in_W : ∀ {W' : Finset W} {F' : Finset F}, TwoConstruction M W' F' →
        ∀ x ∈ F', M.tail x ∈ W' ∧ M.head x ∈ W' := by
      intro W' F' tc'
      induction tc' with
      | single _ => intro _ h; exact absurd h (Finset.notMem_empty _)
      | @join Wa Wb Fa Fb _ _ ea fa _ _ _ _ _ _ _ hea hfa iha ihb =>
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_union] at hx
        rcases hx with rfl | rfl | h | h
        · rcases hea with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact ⟨Finset.mem_union_left _ h1, Finset.mem_union_right _ h2⟩
          · exact ⟨Finset.mem_union_right _ h1, Finset.mem_union_left _ h2⟩
        · rcases hfa with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact ⟨Finset.mem_union_left _ h1, Finset.mem_union_right _ h2⟩
          · exact ⟨Finset.mem_union_right _ h1, Finset.mem_union_left _ h2⟩
        · exact ⟨Finset.mem_union_left _ (iha x h).1, Finset.mem_union_left _ (iha x h).2⟩
        · exact ⟨Finset.mem_union_right _ (ihb x h).1, Finset.mem_union_right _ (ihb x h).2⟩
    refine ⟨g, ?_, ?_, ?_⟩
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_union] at hx
      rcases hx with rfl | rfl | hx1 | hx2
      · simp [g, hge_ne]
      · simp [g, Ne.symm he_ne_f, hgf_ne]
      · have hne_e : x ≠ e := fun h => he1 (h ▸ hx1)
        have hne_f : x ≠ f := fun h => hf1 (h ▸ hx1)
        have hnot2 : x ∉ F₂ := Finset.disjoint_left.mp hdisjF hx1
        simp [g, hne_e, hne_f, hg₂_0 x hnot2, hg₁_nz x hx1]
      · have hne_e : x ≠ e := fun h => he2 (h ▸ hx2)
        have hne_f : x ≠ f := fun h => hf2 (h ▸ hx2)
        have hnot1 : x ∉ F₁ := Finset.disjoint_right.mp hdisjF hx2
        simp [g, hne_e, hne_f, hg₁_0 x hnot1, hg₂_nz x hx2]
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_union, not_or] at hx
      simp [g, hx.1, hx.2.1, hg₁_0 x hx.2.2.1, hg₂_0 x hx.2.2.2]
    · intro w hw
      rw [hF_split (fun x => M.head x = w), hF_split (fun x => M.tail x = w)]
      rw [Finset.mem_union] at hw
      rcases hw with hw1 | hw2
      · have hF2h : F₂.filter (fun x => M.head x = w) = ∅ := by
          ext x; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
          intro hx2 hh; exact Finset.disjoint_left.mp hdisjW hw1 (hh ▸ (hF_in_W right x hx2).2)
        have hF2t : F₂.filter (fun x => M.tail x = w) = ∅ := by
          ext x; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
          intro hx2 ht; exact Finset.disjoint_left.mp hdisjW hw1 (ht ▸ (hF_in_W right x hx2).1)
        rw [hF2h, hF2t, Finset.sum_empty]
        have h1 := hg₁_bd w hw1
        dsimp only [β', bd1] at h1
        have hcalc :
            ((if M.head e = w then ge else 0) + (if M.head f = w then gf else 0) +
              ∑ x ∈ F₁.filter (fun x => M.head x = w), g₁ x + 0) -
            ((if M.tail e = w then ge else 0) + (if M.tail f = w then gf else 0) +
              ∑ x ∈ F₁.filter (fun x => M.tail x = w), g₁ x + 0) =
            ((∑ x ∈ F₁.filter (fun x => M.head x = w), g₁ x) -
             (∑ x ∈ F₁.filter (fun x => M.tail x = w), g₁ x)) +
            ((if M.head e = w then ge else 0) - (if M.tail e = w then ge else 0)) +
            ((if M.head f = w then gf else 0) - (if M.tail f = w then gf else 0)) := by abel
        rw [hcalc, h1]; abel
      · have hF1h : F₁.filter (fun x => M.head x = w) = ∅ := by
          ext x; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
          intro hx1 hh; exact Finset.disjoint_right.mp hdisjW hw2 (hh ▸ (hF_in_W left x hx1).2)
        have hF1t : F₁.filter (fun x => M.tail x = w) = ∅ := by
          ext x; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
          intro hx1 ht; exact Finset.disjoint_right.mp hdisjW hw2 (ht ▸ (hF_in_W left x hx1).1)
        rw [hF1h, hF1t, Finset.sum_empty]
        have h2 := hg₂_bd w hw2
        dsimp only [β', bd1] at h2
        have hcalc :
            ((if M.head e = w then ge else 0) + (if M.head f = w then gf else 0) + 0 +
              ∑ x ∈ F₂.filter (fun x => M.head x = w), g₂ x) -
            ((if M.tail e = w then ge else 0) + (if M.tail f = w then gf else 0) + 0 +
              ∑ x ∈ F₂.filter (fun x => M.tail x = w), g₂ x) =
            ((∑ x ∈ F₂.filter (fun x => M.head x = w), g₂ x) -
             (∑ x ∈ F₂.filter (fun x => M.tail x = w), g₂ x)) +
            ((if M.head e = w then ge else 0) - (if M.tail e = w then ge else 0)) +
            ((if M.head f = w then gf else 0) - (if M.tail f = w then gf else 0)) := by abel
        rw [hcalc, h2]; abel

/-! ### Step 2: Every well-coloured graph admits a nowhere-zero `ZMod 6`-flow -/

lemma wellColouring_has_zmod6_flow {V E : Type} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (Q : Multigraph V E) (wc : WellColouring Q) :
    Nonempty (Q.NZFlow (ZMod 6)) := by
  classical
  -- 1. Build ZMod 3-flow f3 non-zero on every blue edge via twoConstr_ZMod3_connected + red components
  obtain ⟨gB, hgB_nz, _, hgB_bd⟩ :=
    twoConstr_ZMod3_connected (redQuotient Q wc.blue) wc.twoConstr (fun _ => 0) (by simp)
  let f3b : E → ZMod 3 := fun e => if h : e ∈ wc.blue then gB ⟨e, h⟩ else 0
  -- Inside each red component q, Q.boundary f3b sums to 0!
  let redCompV (q : Quotient (redSetoid Q wc.blue)) : Type :=
    {v : V // Quotient.mk (redSetoid Q wc.blue) v = q}
  let redCompE (q : Quotient (redSetoid Q wc.blue)) : Type :=
    {e : E // e ∉ wc.blue ∧ Quotient.mk (redSetoid Q wc.blue) (Q.tail e) = q}
  have hred_head_q : ∀ (q : Quotient (redSetoid Q wc.blue)) (e : redCompE q),
      Quotient.mk (redSetoid Q wc.blue) (Q.head e.1) = q := by
    intro q e
    have hstep : Relation.ReflTransGen (redAdj Q wc.blue) (Q.tail e.1) (Q.head e.1) :=
      Relation.ReflTransGen.single ⟨e.1, e.2.1, Or.inl ⟨rfl, rfl⟩⟩
    exact (Quotient.sound hstep).symm.trans e.2.2
  let redG (q : Quotient (redSetoid Q wc.blue)) : Multigraph (redCompV q) (redCompE q) :=
    { tail := fun e => ⟨Q.tail e.1, e.2.2⟩
      head := fun e => ⟨Q.head e.1, hred_head_q q e⟩ }
  have hredG_conn : ∀ q, (redG q).Connected := by
    intro q ⟨u, hu⟩ ⟨v, hv⟩
    have hrel : Relation.ReflTransGen (redAdj Q wc.blue) u v := Quotient.exact (hu.trans hv.symm)
    have hgo : ∀ a b, Relation.ReflTransGen (redAdj Q wc.blue) a b →
        ∀ (ha : Quotient.mk (redSetoid Q wc.blue) a = q) (hb : Quotient.mk (redSetoid Q wc.blue) b = q),
        Relation.ReflTransGen (redG q).Adj ⟨a, ha⟩ ⟨b, hb⟩ := by
      intro a b hab
      induction hab with
      | refl => intro ha hb; exact .refl
      | @tail x y _ hs ih =>
        intro ha hy
        rcases hs with ⟨e, heR, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
        · have hx : Quotient.mk (redSetoid Q wc.blue) x = q :=
            (Quotient.sound (Relation.ReflTransGen.single ⟨e, heR, Or.inl ⟨h1, h2⟩⟩)).trans hy
          exact (ih ha hx).tail ⟨⟨e, heR, h1.symm ▸ hx⟩, Or.inl ⟨Subtype.ext h1, Subtype.ext h2⟩⟩
        · have hx : Quotient.mk (redSetoid Q wc.blue) x = q :=
            (Quotient.sound (Relation.ReflTransGen.single ⟨e, heR, Or.inr ⟨h1, h2⟩⟩)).trans hy
          have hte : Quotient.mk (redSetoid Q wc.blue) (Q.tail e) = q := h1.symm ▸ hy
          exact (ih ha hx).tail ⟨⟨e, heR, hte⟩, Or.inr ⟨Subtype.ext h1, Subtype.ext h2⟩⟩
    exact hgo u v hrel hu hv
  have hred_sum0 : ∀ q : Quotient (redSetoid Q wc.blue),
      ∑ u : redCompV q, (-Q.boundary f3b u.1) = 0 := by
    intro q
    rw [Finset.sum_neg_distrib, neg_eq_zero]
    have hq0 := hgB_bd q (Finset.mem_univ q)
    rw [← hq0]
    simp_rw [boundary_eq_sum_ite]
    rw [Finset.sum_comm]
    rw [← Finset.sum_subset (Finset.subset_univ wc.blue)]
    · have h1 : ∑ e ∈ wc.blue, ∑ u : redCompV q, (if Q.head e = u.1 then f3b e else 0) =
          ∑ e ∈ (Finset.univ : Finset {e : E // e ∈ wc.blue}).filter (fun e => (redQuotient Q wc.blue).head e = q), gB e := by
        rw [Finset.sum_filter]
        refine Finset.sum_bij (fun e he => ⟨e, he⟩) (fun _ _ => Finset.mem_univ _)
          (fun _ _ _ _ h => congrArg Subtype.val h) (fun e _ => ⟨e.1, e.2, rfl⟩) (fun e he => ?_)
        dsimp only [f3b, redQuotient]; rw [dif_pos he]
        by_cases hq : Quotient.mk (redSetoid Q wc.blue) (Q.head e) = q
        · simp only [hq, ↓reduceIte]
          rw [Finset.sum_eq_single (⟨Q.head e, hq⟩ : redCompV q)]
          · simp
          · intro u _ hne; have : Q.head e ≠ u.1 := fun h => hne (Subtype.ext h.symm); simp [this]
          · intro hm; exact absurd (Finset.mem_univ _) hm
        · simp only [hq, ↓reduceIte]
          refine Finset.sum_eq_zero fun u _ => ?_
          have : Q.head e ≠ u.1 := fun h => hq (h.symm ▸ u.2)
          simp [this]
      have h2 : ∑ e ∈ wc.blue, ∑ u : redCompV q, (if Q.tail e = u.1 then f3b e else 0) =
          ∑ e ∈ (Finset.univ : Finset {e : E // e ∈ wc.blue}).filter (fun e => (redQuotient Q wc.blue).tail e = q), gB e := by
        rw [Finset.sum_filter]
        refine Finset.sum_bij (fun e he => ⟨e, he⟩) (fun _ _ => Finset.mem_univ _)
          (fun _ _ _ _ h => congrArg Subtype.val h) (fun e _ => ⟨e.1, e.2, rfl⟩) (fun e he => ?_)
        dsimp only [f3b, redQuotient]; rw [dif_pos he]
        by_cases hq : Quotient.mk (redSetoid Q wc.blue) (Q.tail e) = q
        · simp only [hq, ↓reduceIte]
          rw [Finset.sum_eq_single (⟨Q.tail e, hq⟩ : redCompV q)]
          · simp
          · intro u _ hne; have : Q.tail e ≠ u.1 := fun h => hne (Subtype.ext h.symm); simp [this]
          · intro hm; exact absurd (Finset.mem_univ _) hm
        · simp only [hq, ↓reduceIte]
          refine Finset.sum_eq_zero fun u _ => ?_
          have : Q.tail e ≠ u.1 := fun h => hq (h.symm ▸ u.2)
          simp [this]
      have hsub_s : ∑ e ∈ wc.blue, ∑ u : redCompV q,
          ((if Q.head e = u.1 then f3b e else 0) - if Q.tail e = u.1 then f3b e else 0) =
          (∑ e ∈ wc.blue, ∑ u : redCompV q, (if Q.head e = u.1 then f3b e else 0)) -
          (∑ e ∈ wc.blue, ∑ u : redCompV q, (if Q.tail e = u.1 then f3b e else 0)) := by
        simp_rw [Finset.sum_sub_distrib]
      rw [hsub_s, h1, h2]
    · intro e _ hnot
      refine Finset.sum_eq_zero fun u _ => by simp [f3b, hnot]
  let sol (q : Quotient (redSetoid Q wc.blue)) : redCompE q → ZMod 3 :=
    (exists_edge_map_with_boundary (Fintype.card (redCompV q)) (redCompV q) (redCompE q)
      (redG q) (hredG_conn q) le_rfl (fun u => -Q.boundary f3b u.1) (hred_sum0 q)).choose
  have hsol_spec : ∀ q u, (redG q).boundary (sol q) u = -Q.boundary f3b u.1 := fun q =>
    (exists_edge_map_with_boundary (Fintype.card (redCompV q)) (redCompV q) (redCompE q)
      (redG q) (hredG_conn q) le_rfl (fun u => -Q.boundary f3b u.1) (hred_sum0 q)).choose_spec
  let f3r : E → ZMod 3 := fun e =>
    if h : e ∉ wc.blue then sol (Quotient.mk (redSetoid Q wc.blue) (Q.tail e)) ⟨e, h, rfl⟩ else 0
  let f3 : E → ZMod 3 := fun e => f3b e + f3r e
  have hf3_fl : Q.IsFlow f3 := by
    intro v
    dsimp only [f3]
    rw [boundary_add]
    let q := Quotient.mk (redSetoid Q wc.blue) v
    have hsol_congr : ∀ {q₁ q₂ : Quotient (redSetoid Q wc.blue)} (hq : q₁ = q₂)
        (e : E) (heR : e ∉ wc.blue) (h1 : Quotient.mk (redSetoid Q wc.blue) (Q.tail e) = q₁),
        sol q₁ ⟨e, heR, h1⟩ = sol q₂ ⟨e, heR, h1.trans hq⟩ := by
      intro q₁ q₂ hq; subst hq; intro _ _ _; rfl
    have hf3r_bd : Q.boundary f3r v = (redG q).boundary (sol q) ⟨v, rfl⟩ := by
      rw [boundary_eq_sum_ite, boundary_eq_sum_ite]
      rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.filter (fun e : E =>
        e ∉ wc.blue ∧ Quotient.mk (redSetoid Q wc.blue) (Q.tail e) = q)))]
      · refine Finset.sum_bij (fun e he => ⟨e, (Finset.mem_filter.mp he).2⟩) (fun _ _ => Finset.mem_univ _)
          (fun _ _ _ _ h => congrArg Subtype.val h)
          (fun e _ => ⟨e.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, e.2⟩, rfl⟩)
          (fun e he => ?_)
        have ⟨heR, hqt⟩ := (Finset.mem_filter.mp he).2
        dsimp only [f3r, redG]
        rw [dif_pos heR, hsol_congr hqt e heR rfl]
        have hh : (⟨Q.head e, hred_head_q q ⟨e, heR, hqt⟩⟩ : redCompV q) = ⟨v, rfl⟩ ↔ Q.head e = v :=
          Subtype.ext_iff
        have ht : (⟨Q.tail e, hqt⟩ : redCompV q) = ⟨v, rfl⟩ ↔ Q.tail e = v :=
          Subtype.ext_iff
        rw [if_congr hh.symm rfl rfl, if_congr ht.symm rfl rfl]
      · intro e _ hnot
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hnot
        by_cases heR : e ∉ wc.blue
        · have hnt : Q.tail e ≠ v := fun ht => hnot ⟨heR, ht.symm ▸ rfl⟩
          have hnh : Q.head e ≠ v := fun hh => by
            have hstep : Relation.ReflTransGen (redAdj Q wc.blue) (Q.tail e) (Q.head e) :=
              Relation.ReflTransGen.single ⟨e, heR, Or.inl ⟨rfl, rfl⟩⟩
            exact hnot ⟨heR, (Quotient.sound hstep).trans (hh.symm ▸ rfl)⟩
          simp [hnt, hnh]
        · have heB : e ∈ wc.blue := not_not.mp heR
          simp [f3r, heB]
    rw [hf3r_bd, hsol_spec q ⟨v, rfl⟩, add_neg_cancel]
  have hf3_blue : ∀ e ∈ wc.blue, f3 e ≠ 0 := fun e he => by
    have hnot : ¬ (e ∉ wc.blue) := not_not.mpr he
    dsimp only [f3, f3b, f3r]
    rw [dif_pos he, dif_neg hnot, add_zero]
    exact hgB_nz ⟨e, he⟩ (Finset.mem_univ _)
  -- 2. Build ZMod 2-flow f2 non-zero on every red edge via fundamental cycles in blue spanning tree
  let T := Multigraph.Subgraph.ofEdges Q Finset.univ wc.blue
    (fun _ => Finset.mem_univ _) (fun _ => Finset.mem_univ _)
  have hT_sf : T.IsSpanningForest :=
    ⟨wc.blue_tree.1, wc.blue_tree.2.2, fun u v _ =>
      wc.blue_tree.2.1.2 u (Finset.mem_univ _) v (Finset.mem_univ _)⟩
  let fund (r : {e : E // e ∉ wc.blue}) : Q.DirectedCycle :=
    (existsUnique_fundamentalCycle Q T hT_sf r.1 r.2).choose
  have hfund : ∀ r : {e : E // e ∉ wc.blue}, Q.IsFundamentalCycle T r.1 (fund r) := fun r =>
    (existsUnique_fundamentalCycle Q T hT_sf r.1 r.2).choose_spec.1
  let f2 : E → ZMod 2 := fun e => ∑ r : {e : E // e ∉ wc.blue}, ((fund r).sign e : ZMod 2)
  have hf2_fl : Q.IsFlow f2 :=
    isFlow_finset_sum Finset.univ fun r _ => by
      have h := isFlow_zsmul (fund r).isFlow (1 : ZMod 2)
      simpa using h
  have hf2_red : ∀ e, e ∉ wc.blue → f2 e ≠ 0 := by
    intro e heR
    dsimp only [f2]
    rw [Finset.sum_eq_single (⟨e, heR⟩ : {x : E // x ∉ wc.blue})]
    · rw [(hfund ⟨e, heR⟩).2]; decide
    · intro r _ hne
      have hnot_in : e ∉ (fund r).sub.edges := fun hm => by
        have hsub := (hfund r).1 hm
        rw [Finset.mem_insert] at hsub
        rcases hsub with rfl | hbl
        · exact hne rfl
        · exact heR hbl
      rw [(fund r).sign_zero hnot_in]; simp
    · intro hm; exact absurd (Finset.mem_univ _) hm
  -- 3. Combine (f2, f3) into ZMod 2 × ZMod 3 ≃+ ZMod 6!
  let crt : ZMod 6 ≃+ ZMod 2 × ZMod 3 :=
    (ZMod.chineseRemainder (by decide : Nat.Coprime 2 3)).toAddEquiv
  let f6 : E → ZMod 6 := fun e => crt.symm (f2 e, f3 e)
  refine ⟨⟨f6, fun v => ?_, fun e h0 => ?_⟩⟩
  · have hsum_crt : ∀ S : Finset E, crt.symm (∑ x ∈ S, f2 x, ∑ x ∈ S, f3 x) = ∑ x ∈ S, f6 x := by
      intro S
      induction S using Finset.induction_on with
      | empty => simp
      | @insert a S ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha,
            ← Prod.mk_add_mk, map_add, ih]
    have hmap : crt.symm (Q.boundary f2 v, Q.boundary f3 v) = Q.boundary f6 v := by
      unfold Multigraph.boundary
      rw [← Prod.mk_sub_mk, map_sub, hsum_crt, hsum_crt]
    rw [← hmap, hf2_fl v, hf3_fl v]
    exact map_zero crt.symm
  · have hp : (f2 e, f3 e) = (0, 0) := by
      have := congrArg crt h0
      simpa [f6] using this
    by_cases hbl : e ∈ wc.blue
    · exact hf3_blue e hbl (congrArg Prod.snd hp)
    · exact hf2_red e hbl (congrArg Prod.fst hp)

/-! ### Step 3: `JLPTWellColouring → SeymourSixFlow` -/

theorem seymour_of_jlpt (hJLPT : JLPTWellColouring) : SeymourSixFlow := by
  -- First prove every finite bridgeless multigraph has a nowhere-zero ZMod 6-flow by strong induction on |V|
  have hz6 : ∀ n : ℕ,
      ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
        (G : Multigraph V E), Fintype.card V = n → G.IsBridgeless → Nonempty (G.NZFlow (ZMod 6)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      -- Step A: loopless bridgeless graphs on n vertices
      have hll_case : ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
          (G : Multigraph V E), Fintype.card V = n → G.IsBridgeless → G.IsLoopless →
          Nonempty (G.NZFlow (ZMod 6)) := by
        intro V E _ _ _ _ G hcard hbr hll
        by_cases hn1 : Fintype.card V ≤ 1
        · have hE0 : IsEmpty E := ⟨fun e => by
            have h2 : 2 ≤ Fintype.card V :=
              (Finset.card_pair (hll e)).symm.le.trans (Finset.card_le_univ _)
            omega⟩
          exact ⟨⟨fun e => hE0.elim e, fun v => by
            unfold Multigraph.boundary
            have h1 : Finset.univ.filter (fun e : E => G.head e = v) = ∅ := by ext e; exact hE0.elim e
            have h2 : Finset.univ.filter (fun e : E => G.tail e = v) = ∅ := by ext e; exact hE0.elim e
            rw [h1, h2]; simp, fun e => hE0.elim e⟩⟩
        · push Not at hn1
          -- Case 1: disconnected
          by_cases hconn1 : G.IsEdgeConnected 1
          · -- Case 2: 2-edge-connected follows from bridgeless
            have hconn2 : G.IsEdgeConnected 2 := by
              intro S hSne hScne
              have hge1 := hconn1 S hSne hScne
              by_contra hlt2
              have hcard1 : (G.cutEdges S).card = 1 := by omega
              obtain ⟨e0, he0⟩ := Finset.card_eq_one.mp hcard1
              have he0_mem : e0 ∈ G.cutEdges S := he0 ▸ Finset.mem_singleton_self e0
              have hexC : ∃ C : G.Subgraph, C.IsCycle ∧ e0 ∈ C.edges := by
                by_contra hnot; exact hbr e0 hnot
              rcases hexC with ⟨C, hC, he0C⟩
              obtain ⟨DC, hDCle⟩ := exists_directedCycle_of_no_deg_one C ⟨e0, he0C⟩
                (fun v hv => by rw [hC.2 v hv]; decide)
              have he0DC : e0 ∈ DC.sub.edges := by
                have hverts : DC.sub.verts = C.verts := by
                  apply Finset.Subset.antisymm hDCle.1
                  intro w hw
                  obtain ⟨v₀, hv₀⟩ := DC.isCycle.1.1
                  have hpath := hC.1.2 v₀ (hDCle.1 hv₀) w hw; clear hw
                  induction hpath with
                  | refl => exact hv₀
                  | @tail u z _ hs ihp =>
                    rcases hs with ⟨e', he', ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
                    · have hdeg : DC.sub.deg u = C.deg u := by rw [DC.isCycle.2 u ihp, hC.2 u (hDCle.1 ihp)]
                      have ht_sub := Finset.filter_subset_filter (fun e'' => G.tail e'' = u) hDCle.2
                      have hh_sub := Finset.filter_subset_filter (fun e'' => G.head e'' = u) hDCle.2
                      have ht_le := Finset.card_le_card ht_sub; have hh_le := Finset.card_le_card hh_sub
                      unfold Multigraph.Subgraph.deg at hdeg
                      have ht_eq := Finset.eq_of_subset_of_card_le ht_sub (by omega)
                      have hmem : e' ∈ C.edges.filter (fun e'' => G.tail e'' = u) := Finset.mem_filter.mpr ⟨he', h1⟩
                      rw [← ht_eq] at hmem; simpa [h2] using DC.sub.head_mem (Finset.mem_filter.mp hmem).1
                    · have hdeg : DC.sub.deg u = C.deg u := by rw [DC.isCycle.2 u ihp, hC.2 u (hDCle.1 ihp)]
                      have ht_sub := Finset.filter_subset_filter (fun e'' => G.tail e'' = u) hDCle.2
                      have hh_sub := Finset.filter_subset_filter (fun e'' => G.head e'' = u) hDCle.2
                      have ht_le := Finset.card_le_card ht_sub; have hh_le := Finset.card_le_card hh_sub
                      unfold Multigraph.Subgraph.deg at hdeg
                      have hh_eq := Finset.eq_of_subset_of_card_le hh_sub (by omega)
                      have hmem : e' ∈ C.edges.filter (fun e'' => G.head e'' = u) := Finset.mem_filter.mpr ⟨he', h2⟩
                      rw [← hh_eq] at hmem; simpa [h1] using DC.sub.tail_mem (Finset.mem_filter.mp hmem).1
                have huC := C.tail_mem he0C
                have huD : G.tail e0 ∈ DC.sub.verts := hverts ▸ huC
                have hdeg : DC.sub.deg (G.tail e0) = C.deg (G.tail e0) := by rw [DC.isCycle.2 _ huD, hC.2 _ huC]
                have ht_sub := Finset.filter_subset_filter (fun e'' => G.tail e'' = G.tail e0) hDCle.2
                have hh_sub := Finset.filter_subset_filter (fun e'' => G.head e'' = G.tail e0) hDCle.2
                have ht_le := Finset.card_le_card ht_sub; have hh_le := Finset.card_le_card hh_sub
                unfold Multigraph.Subgraph.deg at hdeg
                have ht_eq := Finset.eq_of_subset_of_card_le ht_sub (by omega)
                have hmem : e0 ∈ C.edges.filter (fun e'' => G.tail e'' = G.tail e0) := Finset.mem_filter.mpr ⟨he0C, rfl⟩
                rw [← ht_eq] at hmem; exact (Finset.mem_filter.mp hmem).1
              have hcut_sum := sum_boundary_eq_cut G DC.sign S
              have hzero : ∑ v ∈ S, G.boundary DC.sign v = 0 := Finset.sum_eq_zero fun v _ => DC.isFlow v
              rw [hzero] at hcut_sum
              rcases (Finset.mem_filter.mp he0_mem).2 with ⟨ht, hh⟩ | ⟨ht, hh⟩
              · have hf1 : Finset.univ.filter (fun e => G.head e ∈ S ∧ G.tail e ∉ S) = ∅ := by
                  ext e; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
                  rintro ⟨h1, h2⟩; have hm : e ∈ G.cutEdges S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨h2, h1⟩⟩
                  rw [he0, Finset.mem_singleton] at hm; subst hm; exact h2 ht
                have hf2 : Finset.univ.filter (fun e => G.tail e ∈ S ∧ G.head e ∉ S) = {e0} := by
                  ext e; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
                  exact ⟨fun ⟨h1, h2⟩ => Finset.mem_singleton.mp (he0 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ⟨h1, h2⟩⟩),
                    fun h => h ▸ ⟨ht, hh⟩⟩
                rw [hf1, hf2, Finset.sum_empty, Finset.sum_singleton, zero_sub] at hcut_sum
                rcases DC.sign_mem he0DC with h1 | h1 <;> omega
              · have hf1 : Finset.univ.filter (fun e => G.head e ∈ S ∧ G.tail e ∉ S) = {e0} := by
                  ext e; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
                  exact ⟨fun ⟨h1, h2⟩ => Finset.mem_singleton.mp (he0 ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨h2, h1⟩⟩),
                    fun h => h ▸ ⟨hh, ht⟩⟩
                have hf2 : Finset.univ.filter (fun e => G.tail e ∈ S ∧ G.head e ∉ S) = ∅ := by
                  ext e; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
                  rintro ⟨h1, h2⟩; have hm : e ∈ G.cutEdges S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ⟨h1, h2⟩⟩
                  rw [he0, Finset.mem_singleton] at hm; subst hm; exact ht h1
                rw [hf1, hf2, Finset.sum_singleton, Finset.sum_empty, sub_zero] at hcut_sum
                rcases DC.sign_mem he0DC with h1 | h1 <;> omega
            -- Case 3 vs Case 4: 3-edge-connected?
            by_cases hconn3 : G.IsEdgeConnected 3
            · -- Check if G has a cut vertex!
              by_cases hnc : (Multigraph.Subgraph.top G).HasNoCutVertex
              · -- Loopless, 3-edge-connected, n ≥ 2, no cut vertex: apply Lemma 3.4(b) + JLPT!
                obtain ⟨exp⟩ := lem_3_4_b G hll hconn3 hn1 hnc
                obtain ⟨wc⟩ := hJLPT exp.VQ exp.EQ exp.Q exp.isTC3EC
                obtain ⟨fQ⟩ := wellColouring_has_zmod6_flow exp.Q wc
                -- Contract exp.Q by exp.contractV to get a nowhere-zero ZMod 6-flow on G!
                have hfl_cb := sec4_E5_proved exp.Q exp.contractV fQ.val fQ.isFlow
                refine ⟨⟨fun e => fQ.val (exp.origEdge e), fun v => ?_, fun e => fQ.nonzero (exp.origEdge e)⟩⟩
                trans ((exp.Q.contractBy exp.contractV).boundary (fun eq => fQ.val eq.1) v)
                · rw [boundary_eq_sum_ite, boundary_eq_sum_ite]
                  refine Finset.sum_bij
                    (fun e _ => ⟨exp.origEdge e, by rw [exp.orig_tail e, exp.orig_head e]; exact hll e⟩)
                    (fun _ _ => Finset.mem_univ _)
                    (fun _ _ _ _ h => exp.origEdge.injective (congrArg Subtype.val h))
                    (fun eq _ => ?_)
                    (fun e _ => by simp [Multigraph.contractBy, exp.orig_tail e, exp.orig_head e])
                  have hex : ∃ k : E, exp.origEdge k = eq.1 := by
                    by_contra hno; push Not at hno
                    exact eq.2 (exp.exp_fiber eq.1 hno)
                  rcases hex with ⟨k, hk⟩
                  exact ⟨k, Finset.mem_univ _, Subtype.ext hk⟩
                · exact hfl_cb v
              · -- G has a cut vertex v₀: split G into two strictly smaller bridgeless subgraphs!
                unfold Multigraph.Subgraph.HasNoCutVertex Multigraph.Subgraph.IsCutVertex at hnc
                push Not at hnc
                rcases hnc with ⟨v₀, _, _, u, w, hu, hw, hnr⟩
                classical
                let Gdel := (Multigraph.Subgraph.top G).deleteVertex v₀
                let A : Finset V := Gdel.verts.filter (fun x => Relation.ReflTransGen Gdel.Adj u x)
                have huA : u ∈ A := Finset.mem_filter.mpr ⟨hu, .refl⟩
                have hwA : w ∉ A := fun h => hnr (Finset.mem_filter.mp h).2
                have hv0_notA : v₀ ∉ A := fun h => (Finset.mem_erase.mp (Finset.mem_filter.mp h).1).1 rfl
                let U₁ : Finset V := insert v₀ A
                let U₂ : Finset V := Finset.univ \ A
                have hU₁_lt : U₁.card < n := by
                  have hsub : U₁ ⊆ Finset.univ.erase w := fun x hx => by
                    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
                    rw [Finset.mem_insert] at hx; rcases hx with rfl | hx
                    · exact (Finset.mem_erase.mp hw).1.symm
                    · exact fun heq => hwA (heq ▸ hx)
                  have hle := Finset.card_le_card hsub
                  rw [Finset.card_erase_of_mem (Finset.mem_univ w), Finset.card_univ] at hle
                  omega
                have hU₂_lt : U₂.card < n := by
                  have hsd : U₂.card = Fintype.card V - A.card := by
                    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
                  have hpos : 0 < A.card := Finset.card_pos.mpr ⟨u, huA⟩
                  omega
                -- No edge crosses between A and (univ \ U₁)
                have hedge_side : ∀ e : E,
                    (G.tail e ∈ U₁ ∧ G.head e ∈ U₁) ∨ (G.tail e ∈ U₂ ∧ G.head e ∈ U₂) := by
                  intro e
                  by_cases ht : G.tail e ∈ A
                  · left; refine ⟨Finset.mem_insert_of_mem ht, ?_⟩
                    by_cases hh : G.head e = v₀
                    · rw [hh]; exact Finset.mem_insert_self _ _
                    · refine Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hh, Finset.mem_univ _⟩, ?_⟩)
                      have htne : G.tail e ≠ v₀ := fun h => hv0_notA (h ▸ ht)
                      exact (Finset.mem_filter.mp ht).2.tail ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, htne, hh⟩, Or.inl ⟨rfl, rfl⟩⟩
                  · by_cases hh : G.head e ∈ A
                    · left; refine ⟨?_, Finset.mem_insert_of_mem hh⟩
                      by_cases ht0 : G.tail e = v₀
                      · rw [ht0]; exact Finset.mem_insert_self _ _
                      · exfalso
                        have hhne : G.head e ≠ v₀ := fun h => hv0_notA (h ▸ hh)
                        exact ht (Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨ht0, Finset.mem_univ _⟩,
                          (Finset.mem_filter.mp hh).2.tail ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht0, hhne⟩, Or.inr ⟨rfl, rfl⟩⟩⟩)
                    · right; exact ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ht⟩, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hh⟩⟩
                -- Every edge lies in EXACTLY ONE of E₁ = induced U₁, E₂ = induced U₂ (since G is loopless and U₁ ∩ U₂ = {v₀})
                have hU12_inter : ∀ v : V, v ∈ U₁ → v ∈ U₂ → v = v₀ := fun v h1 h2 => by
                  rw [Finset.mem_insert] at h1; rcases h1 with rfl | hA
                  · rfl
                  · exact absurd hA (Finset.mem_sdiff.mp h2).2
                have hH_br : ∀ (U : Finset V),
                    (∀ e : E, (G.tail e ∈ U ∧ G.head e ∈ U) ∨ (G.tail e ∉ U \ {v₀} ∧ G.head e ∉ U \ {v₀})) →
                    (Multigraph.Subgraph.induced G U).toMultigraph.IsBridgeless := by
                  intro U hUcl e hnot
                  have hex : ∃ C : G.Subgraph, C.IsCycle ∧ e.1 ∈ C.edges := by
                    by_contra hn'; exact hbr e.1 hn'
                  rcases hex with ⟨C, hC, heC⟩
                  -- Since G is loopless, at least one end of e.1 is in U \ {v₀}!
                  have hend_in : G.tail e.1 ∈ U \ {v₀} ∨ G.head e.1 ∈ U \ {v₀} := by
                    have ⟨htU, hhU⟩ := (Finset.mem_filter.mp e.2).2
                    by_cases ht0 : G.tail e.1 = v₀
                    · right; exact Finset.mem_sdiff.mpr ⟨hhU, fun h => hll e.1 (ht0.trans (Finset.mem_singleton.mp h).symm)⟩
                    · left; exact Finset.mem_sdiff.mpr ⟨htU, fun h => ht0 (Finset.mem_singleton.mp h)⟩
                  -- C - v₀ is connected (since C is a cycle!), so EVERY vertex of C lies in U!
                  have hCv_U : ∀ x ∈ C.verts, x ∈ U := by
                    intro x hx
                    by_cases hx0 : x = v₀
                    · rcases hend_in with ht | hh
                      · rcases hUcl e.1 with ⟨_, _⟩ | ⟨h1, _⟩
                        · exact hx0 ▸ (by
                            -- v₀ ∈ U since otherwise U = U \ {v₀} and C stays in U
                            by_cases hvU : v₀ ∈ U
                            · exact hvU
                            · exfalso
                              -- Check if v₀ ∈ C.verts: if v₀ ∉ U, then every edge with an end in U \ {v₀} has both ends in U,
                              -- so no vertex of C can leave U!
                              have hstay : ∀ z, Relation.ReflTransGen C.Adj (G.tail e.1) z → z ∈ U := by
                                intro z hz
                                induction hz with
                                | refl => exact (Finset.mem_sdiff.mp ht).1
                                | tail _ hs ihz =>
                                  rcases hs with ⟨y, _, ⟨h1', h2'⟩ | ⟨h1', h2'⟩⟩
                                  · have hy1 : G.tail y ∈ U \ {v₀} := Finset.mem_sdiff.mpr ⟨h1'.symm ▸ ihz, fun h => hvU (Finset.mem_singleton.mp h ▸ h1'.symm ▸ ihz)⟩
                                    rcases hUcl y with ⟨_, hy2⟩ | ⟨hy1n, _⟩
                                    · exact h2' ▸ hy2
                                    · exact absurd hy1 hy1n
                                  · have hy2 : G.head y ∈ U \ {v₀} := Finset.mem_sdiff.mpr ⟨h2'.symm ▸ ihz, fun h => hvU (Finset.mem_singleton.mp h ▸ h2'.symm ▸ ihz)⟩
                                    rcases hUcl y with ⟨hy1, _⟩ | ⟨_, hy2n⟩
                                    · exact h1' ▸ hy1
                                    · exact absurd hy2 hy2n
                              exact hvU (hx0 ▸ hstay x (hC.1.2 _ (C.tail_mem heC) x hx)))
                        · exact absurd ht h1
                      · by_cases hvU : v₀ ∈ U
                        · exact hx0 ▸ hvU
                        · exfalso
                          have hstay : ∀ z, Relation.ReflTransGen C.Adj (G.head e.1) z → z ∈ U := by
                            intro z hz
                            induction hz with
                            | refl => exact (Finset.mem_sdiff.mp hh).1
                            | tail _ hs ihz =>
                              rcases hs with ⟨y, _, ⟨h1', h2'⟩ | ⟨h1', h2'⟩⟩
                              · have hy1 : G.tail y ∈ U \ {v₀} := Finset.mem_sdiff.mpr ⟨h1'.symm ▸ ihz, fun h => hvU (Finset.mem_singleton.mp h ▸ h1'.symm ▸ ihz)⟩
                                rcases hUcl y with ⟨_, hy2⟩ | ⟨hy1n, _⟩
                                · exact h2' ▸ hy2
                                · exact absurd hy1 hy1n
                              · have hy2 : G.head y ∈ U \ {v₀} := Finset.mem_sdiff.mpr ⟨h2'.symm ▸ ihz, fun h => hvU (Finset.mem_singleton.mp h ▸ h2'.symm ▸ ihz)⟩
                                rcases hUcl y with ⟨hy1, _⟩ | ⟨_, hy2n⟩
                                · exact h1' ▸ hy1
                                · exact absurd hy2 hy2n
                          exact hvU (hx0 ▸ hstay x (hC.1.2 _ (C.head_mem heC) x hx))
                    · -- x ≠ v₀: a cycle C has no cut vertex, so x is reachable from an end of e.1 in C - v₀!
                      obtain ⟨s, hsC, hsU⟩ : ∃ s ∈ C.verts, s ∈ U \ {v₀} := by
                        rcases hend_in with ht | hh
                        · exact ⟨G.tail e.1, C.tail_mem heC, ht⟩
                        · exact ⟨G.head e.1, C.head_mem heC, hh⟩
                      -- C - v₀ is connected: if not, handshake parity in C - v₀ contradicts deg = 2!
                      have hreach_del : Relation.ReflTransGen (C.deleteVertex v₀).Adj s x := by
                        by_cases hvC : v₀ ∈ C.verts
                        · -- In C - v₀, all vertices have deg 2 except the ≤ 2 neighbors of v₀; by connectedness of C,
                          -- take a simple path from s to x in C; if it avoids v₀ we're done, else the complementary path in C avoids v₀!
                          by_cases hsx : s = x
                          · rw [hsx]
                          · obtain ⟨v1, e1, hlen1, hnd1, hhead1, hlast1, he1, hstep1⟩ :=
                              exists_simplePath_of_reflTransGen (hC.1.2 s hsC x hx)
                            by_cases hv_in : v₀ ∈ v1
                            · -- Take the complementary path in C \ e1.toFinset (which cannot contain v₀ since v₀ is interior to v1, deg 0 in C \ e1!)
                              let C2 : G.Subgraph :=
                                { verts := C.verts, edges := C.edges \ e1.toFinset,
                                  tail_mem := fun he => C.tail_mem (Finset.mem_sdiff.mp he).1,
                                  head_mem := fun he => C.head_mem (Finset.mem_sdiff.mp he).1 }
                              have hP1 := simplePath_deg_eq G v1 e1 hlen1 hnd1 hstep1 s x hhead1 hlast1 hsx
                              have hdeg_sp : ∀ z ∈ C.verts, C2.deg z +
                                  ((e1.toFinset.filter (fun y => G.tail y = z)).card +
                                   (e1.toFinset.filter (fun y => G.head y = z)).card) = 2 := by
                                intro z hz
                                have hsub : e1.toFinset ⊆ C.edges := fun y hy => he1 y (List.mem_toFinset.mp hy)
                                have hEq : C.edges = C2.edges ∪ e1.toFinset := (Finset.sdiff_union_of_subset hsub).symm
                                have hd := hC.2 z hz
                                unfold Multigraph.Subgraph.deg at hd ⊢
                                rw [hEq, Finset.filter_union, Finset.filter_union,
                                    Finset.card_union_of_disjoint (Disjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _) Finset.sdiff_disjoint),
                                    Finset.card_union_of_disjoint (Disjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _) Finset.sdiff_disjoint)] at hd
                                dsimp only [C2] at hd ⊢
                                omega
                              have hC2_v0 : C2.deg v₀ = 0 := by
                                have h1 := hdeg_sp v₀ hvC
                                have hsne : v₀ ≠ s := fun h => (Finset.mem_sdiff.mp hsU).2 (Finset.mem_singleton.mpr h.symm)
                                have h2 := hP1.2.2.1 v₀ hv_in hsne (Ne.symm hx0)
                                unfold Multigraph.Subgraph.deg at h2; dsimp at h2; omega
                              -- Parity in component K of s in C2 forces x ∈ K!
                              have hreach_C2 : Relation.ReflTransGen C2.Adj s x := by
                                let K : Finset V := C.verts.filter (fun z => Relation.ReflTransGen C2.Adj s z)
                                have hK_cl : ∀ y ∈ C2.edges, G.tail y ∈ K ↔ G.head y ∈ K := fun y hy => by
                                  simp only [K, Finset.mem_filter]
                                  exact ⟨fun ht => ⟨C2.head_mem hy, ht.2.tail ⟨y, hy, Or.inl ⟨rfl, rfl⟩⟩⟩,
                                    fun hh => ⟨C2.tail_mem hy, hh.2.tail ⟨y, hy, Or.inr ⟨rfl, rfl⟩⟩⟩⟩
                                have hK_even : Even (∑ z ∈ K, C2.deg z) := by
                                  let EK := C2.edges.filter (fun y => G.tail y ∈ K)
                                  have h1 : ∑ z ∈ K, (C2.edges.filter (fun y => G.tail y = z)).card = EK.card := by
                                    rw [← Finset.card_biUnion]
                                    · congr 1; ext y; simp only [EK, Finset.mem_biUnion, Finset.mem_filter]
                                      exact ⟨fun ⟨_, hzK, hy, ht⟩ => ⟨hy, ht.symm ▸ hzK⟩, fun ⟨hy, htK⟩ => ⟨G.tail y, htK, hy, rfl⟩⟩
                                    · intro a _ b _ hab; dsimp [Function.onFun]; rw [Finset.disjoint_left]
                                      intro y ha hb; exact hab ((Finset.mem_filter.mp ha).2.symm.trans (Finset.mem_filter.mp hb).2)
                                  have h2 : ∑ z ∈ K, (C2.edges.filter (fun y => G.head y = z)).card = EK.card := by
                                    rw [← Finset.card_biUnion]
                                    · congr 1; ext y; simp only [EK, Finset.mem_biUnion, Finset.mem_filter]
                                      exact ⟨fun ⟨_, hzK, hy, hh⟩ => ⟨hy, (hK_cl y hy).mpr (hh.symm ▸ hzK)⟩,
                                        fun ⟨hy, htK⟩ => ⟨G.head y, (hK_cl y hy).mp htK, hy, rfl⟩⟩
                                    · intro a _ b _ hab; dsimp [Function.onFun]; rw [Finset.disjoint_left]
                                      intro y ha hb; exact hab ((Finset.mem_filter.mp ha).2.symm.trans (Finset.mem_filter.mp hb).2)
                                  unfold Multigraph.Subgraph.deg; rw [Finset.sum_add_distrib, h1, h2]; exact ⟨EK.card, rfl⟩
                                by_contra hnx
                                have hsK : s ∈ K := Finset.mem_filter.mpr ⟨hsC, .refl⟩
                                have hxK : x ∉ K := fun h => hnx (Finset.mem_filter.mp h).2
                                have hC2s : C2.deg s = 1 := by
                                  have h1 := hdeg_sp s hsC; have h2 := hP1.1; unfold Multigraph.Subgraph.deg at h2; dsimp at h2; omega
                                rw [← Finset.add_sum_erase _ _ hsK, hC2s] at hK_even
                                have hrest : Even (∑ z ∈ K.erase s, C2.deg z) := by
                                  have hall : ∀ z ∈ K.erase s, Even (C2.deg z) := fun z hz => by
                                    have hzC := (Finset.mem_filter.mp (Finset.mem_of_mem_erase hz)).1
                                    have hzs := Finset.ne_of_mem_erase hz
                                    have hzx : z ≠ x := fun h => hxK (h ▸ Finset.mem_of_mem_erase hz)
                                    have h1 := hdeg_sp z hzC
                                    by_cases hz1 : z ∈ v1
                                    · have h2 := hP1.2.2.1 z hz1 hzs hzx; unfold Multigraph.Subgraph.deg at h2; dsimp at h2
                                      exact ⟨0, by omega⟩
                                    · have h2 := hP1.2.2.2 z hz1; unfold Multigraph.Subgraph.deg at h2; dsimp at h2
                                      exact ⟨1, by omega⟩
                                  clear hK_even; generalize K.erase s = T at hall ⊢
                                  induction T using Finset.induction_on with
                                  | empty => exact ⟨0, rfl⟩
                                  | @insert a S' ha ihT =>
                                    rw [Finset.sum_insert ha]
                                    exact (hall a (Finset.mem_insert_self _ _)).add (ihT fun z hz => hall z (Finset.mem_insert_of_mem hz))
                                rcases hK_even with ⟨m1, hm1⟩; rcases hrest with ⟨m2, hm2⟩; omega
                              -- Every edge of C2 avoids v₀ since C2.deg v₀ = 0!
                              have hgo_C2 : ∀ z, Relation.ReflTransGen C2.Adj s z → Relation.ReflTransGen (C.deleteVertex v₀).Adj s z := by
                                intro z hz
                                induction hz with
                                | refl => exact .refl
                                | tail _ hs ihc =>
                                  rcases hs with ⟨y, hyC2, hinc⟩
                                  have hnt : G.tail y ≠ v₀ := fun h => by
                                    have : 0 < (C2.edges.filter (fun y' => G.tail y' = v₀)).card :=
                                      Finset.card_pos.mpr ⟨y, Finset.mem_filter.mpr ⟨hyC2, h⟩⟩
                                    unfold Multigraph.Subgraph.deg at hC2_v0; omega
                                  have hnh : G.head y ≠ v₀ := fun h => by
                                    have : 0 < (C2.edges.filter (fun y' => G.head y' = v₀)).card :=
                                      Finset.card_pos.mpr ⟨y, Finset.mem_filter.mpr ⟨hyC2, h⟩⟩
                                    unfold Multigraph.Subgraph.deg at hC2_v0; omega
                                  exact ihc.tail ⟨y, Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hyC2).1, hnt, hnh⟩, hinc⟩
                              exact hgo_C2 x hreach_C2
                            · -- v1 avoids v₀ directly!
                              have hgo : ∀ k (hk : k < v1.length), Relation.ReflTransGen (C.deleteVertex v₀).Adj s (v1[k]'hk) := by
                                intro k
                                induction k with
                                | zero =>
                                  intro hk
                                  have hv0s : v1[0]'hk = s := by
                                    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hk, Option.some.injEq] at hhead1; exact hhead1
                                  rw [hv0s]
                                | succ k ihk =>
                                  intro hk
                                  have hk' : k < e1.length := by omega
                                  have hprev := ihk (by omega)
                                  have hst := hstep1 k hk'
                                  have hne1 : v1[k]'(by omega) ≠ v₀ := fun h => hv_in (h ▸ List.getElem_mem _)
                                  have hne2 : v1[k + 1]'hk ≠ v₀ := fun h => hv_in (h ▸ List.getElem_mem _)
                                  have hnt : G.tail (e1[k]'hk') ≠ v₀ := by rcases hst with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1]; exact hne1; exact hne2
                                  have hnh : G.head (e1[k]'hk') ≠ v₀ := by rcases hst with ⟨_, h2⟩ | ⟨_, h2⟩ <;> rw [h2]; exact hne2; exact hne1
                                  exact hprev.tail ⟨e1[k]'hk', Finset.mem_filter.mpr ⟨he1 _ (List.getElem_mem _), hnt, hnh⟩, hst⟩
                              have hlast_eq : v1[e1.length]'(by omega) = x := by
                                rw [List.getLast?_eq_getElem?] at hlast1
                                have hidx : v1.length - 1 = e1.length := by omega
                                rw [hidx, List.getElem?_eq_getElem (by omega), Option.some.injEq] at hlast1; exact hlast1
                              rw [← hlast_eq]; exact hgo e1.length (by omega)
                        · -- v₀ ∉ C.verts: every edge of C avoids v₀ directly
                          have hgo_no : ∀ z, Relation.ReflTransGen C.Adj s z → Relation.ReflTransGen (C.deleteVertex v₀).Adj s z := by
                            intro z hz
                            induction hz with
                            | refl => exact .refl
                            | tail _ hs ihc =>
                              rcases hs with ⟨y, hyC, hinc⟩
                              have hnt : G.tail y ≠ v₀ := fun h => hvC (h ▸ C.tail_mem hyC)
                              have hnh : G.head y ≠ v₀ := fun h => hvC (h ▸ C.head_mem hyC)
                              exact ihc.tail ⟨y, Finset.mem_filter.mpr ⟨hyC, hnt, hnh⟩, hinc⟩
                          exact hgo_no x (hC.1.2 s hsC x hx)
                      -- Now walk along C - v₀ from s ∈ U \ {v₀} to x: every step stays in U \ {v₀}!
                      have hstay : ∀ z, Relation.ReflTransGen (C.deleteVertex v₀).Adj s z → z ∈ U \ {v₀} := by
                        intro z hz
                        induction hz with
                        | refl => exact hsU
                        | tail _ hs ihz =>
                          rcases hs with ⟨y, hy, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
                          · have ⟨_, hnt, hnh⟩ := Finset.mem_filter.mp hy
                            rcases hUcl y with ⟨_, hhU⟩ | ⟨htn, _⟩
                            · exact Finset.mem_sdiff.mpr ⟨h2 ▸ hhU, fun h => hnh (h2.trans (Finset.mem_singleton.mp h))⟩
                            · exact absurd (h1.symm ▸ ihz) htn
                          · have ⟨_, hnt, hnh⟩ := Finset.mem_filter.mp hy
                            rcases hUcl y with ⟨htU, _⟩ | ⟨_, hhn⟩
                            · exact Finset.mem_sdiff.mpr ⟨h1 ▸ htU, fun h => hnt (h1.trans (Finset.mem_singleton.mp h))⟩
                            · exact absurd (h2.symm ▸ ihz) hhn
                      exact (Finset.mem_sdiff.mp (hstay x hreach_del)).1
                  -- Restrict C to (induced G U).toMultigraph
                  let HU := Multigraph.Subgraph.induced G U
                  let CU : HU.toMultigraph.Subgraph :=
                    { verts := Finset.univ.filter (fun z : {z // z ∈ HU.verts} => z.1 ∈ C.verts)
                      edges := Finset.univ.filter (fun y : {y // y ∈ HU.edges} => y.1 ∈ C.edges)
                      tail_mem := fun hy => Finset.mem_filter.mpr ⟨Finset.mem_univ _, C.tail_mem (Finset.mem_filter.mp hy).2⟩
                      head_mem := fun hy => Finset.mem_filter.mpr ⟨Finset.mem_univ _, C.head_mem (Finset.mem_filter.mp hy).2⟩ }
                  have hCe_U : ∀ y ∈ C.edges, y ∈ HU.edges := fun y hy =>
                    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hCv_U _ (C.tail_mem hy), hCv_U _ (C.head_mem hy)⟩
                  refine hnot ⟨CU, ⟨⟨?_, ?_⟩, ?_⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, heC⟩⟩
                  · obtain ⟨z, hz⟩ := hC.1.1; exact ⟨⟨z, hCv_U z hz⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩⟩
                  · intro a ha b hb
                    have hrtg := hC.1.2 a.1 (Finset.mem_filter.mp ha).2 b.1 (Finset.mem_filter.mp hb).2
                    have hgo : ∀ x y, Relation.ReflTransGen C.Adj x y → ∀ (hxU : x ∈ HU.verts) (hyU : y ∈ HU.verts),
                        Relation.ReflTransGen CU.Adj ⟨x, hxU⟩ ⟨y, hyU⟩ := by
                      intro x y hxy
                      induction hxy with
                      | refl => intro _ _; exact .refl
                      | @tail p q _ hs ihp =>
                        intro hxU hqU
                        rcases hs with ⟨y', hy', ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
                        · have hpU : p ∈ HU.verts := h1 ▸ hCv_U _ (C.tail_mem hy')
                          exact (ihp hxU hpU).tail ⟨⟨y', hCe_U y' hy'⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy'⟩,
                            Or.inl ⟨Subtype.ext h1, Subtype.ext h2⟩⟩
                        · have hpU : p ∈ HU.verts := h2 ▸ hCv_U _ (C.head_mem hy')
                          exact (ihp hxU hpU).tail ⟨⟨y', hCe_U y' hy'⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy'⟩,
                            Or.inr ⟨Subtype.ext h1, Subtype.ext h2⟩⟩
                    exact hgo a.1 b.1 hrtg a.2 b.2
                  · intro z hz
                    have hd := hC.2 z.1 (Finset.mem_filter.mp hz).2
                    unfold Multigraph.Subgraph.deg at hd ⊢
                    have h1 : (CU.edges.filter (fun y => HU.toMultigraph.tail y = z)).card =
                        (C.edges.filter (fun y => G.tail y = z.1)).card := by
                      refine Finset.card_bij (fun y _ => y.1) (fun y hy => ?_) (fun _ _ _ _ h => Subtype.ext h)
                        (fun y hy => ⟨⟨y, hCe_U y (Finset.mem_filter.mp hy).1⟩, ?_, rfl⟩)
                      · rw [Finset.mem_filter] at hy ⊢; exact ⟨(Finset.mem_filter.mp hy.1).2, congrArg Subtype.val hy.2⟩
                      · rw [Finset.mem_filter] at hy ⊢; exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy.1⟩, Subtype.ext hy.2⟩
                    have h2 : (CU.edges.filter (fun y => HU.toMultigraph.head y = z)).card =
                        (C.edges.filter (fun y => G.head y = z.1)).card := by
                      refine Finset.card_bij (fun y _ => y.1) (fun y hy => ?_) (fun _ _ _ _ h => Subtype.ext h)
                        (fun y hy => ⟨⟨y, hCe_U y (Finset.mem_filter.mp hy).1⟩, ?_, rfl⟩)
                      · rw [Finset.mem_filter] at hy ⊢; exact ⟨(Finset.mem_filter.mp hy.1).2, congrArg Subtype.val hy.2⟩
                      · rw [Finset.mem_filter] at hy ⊢; exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy.1⟩, Subtype.ext hy.2⟩
                    rw [h1, h2]; exact hd
                have hU1_cl : ∀ e : E, (G.tail e ∈ U₁ ∧ G.head e ∈ U₁) ∨ (G.tail e ∉ U₁ \ {v₀} ∧ G.head e ∉ U₁ \ {v₀}) := fun e => by
                  rcases hedge_side e with h | ⟨h1, h2⟩
                  · exact Or.inl h
                  · right
                    exact ⟨fun hm => (Finset.mem_sdiff.mp h1).2 (by
                        have hm1 := (Finset.mem_sdiff.mp hm).1
                        have hm2 := (Finset.mem_sdiff.mp hm).2
                        rw [Finset.mem_insert] at hm1; exact hm1.resolve_left (fun h => hm2 (Finset.mem_singleton.mpr h))),
                      fun hm => (Finset.mem_sdiff.mp h2).2 (by
                        have hm1 := (Finset.mem_sdiff.mp hm).1
                        have hm2 := (Finset.mem_sdiff.mp hm).2
                        rw [Finset.mem_insert] at hm1; exact hm1.resolve_left (fun h => hm2 (Finset.mem_singleton.mpr h)))⟩
                have hU2_cl : ∀ e : E, (G.tail e ∈ U₂ ∧ G.head e ∈ U₂) ∨ (G.tail e ∉ U₂ \ {v₀} ∧ G.head e ∉ U₂ \ {v₀}) := fun e => by
                  rcases hedge_side e with ⟨h1, h2⟩ | h
                  · right
                    exact ⟨fun hm => (Finset.mem_sdiff.mp hm).2 (Finset.mem_singleton.mpr (hU12_inter _ h1 (Finset.mem_sdiff.mp hm).1)),
                      fun hm => (Finset.mem_sdiff.mp hm).2 (Finset.mem_singleton.mpr (hU12_inter _ h2 (Finset.mem_sdiff.mp hm).1))⟩
                  · exact Or.inl h
                let H₁ := Multigraph.Subgraph.induced G U₁
                let H₂ := Multigraph.Subgraph.induced G U₂
                obtain ⟨f₁⟩ := ih U₁.card hU₁_lt _ _ H₁.toMultigraph (Fintype.card_coe U₁) (hH_br U₁ hU1_cl)
                obtain ⟨f₂⟩ := ih U₂.card hU₂_lt _ _ H₂.toMultigraph (Fintype.card_coe U₂) (hH_br U₂ hU2_cl)
                have hdisj_E12 : Disjoint H₁.edges H₂.edges := by
                  rw [Finset.disjoint_left]
                  intro e he1 he2
                  have ⟨ht1, hh1⟩ := (Finset.mem_filter.mp he1).2
                  have ⟨ht2, hh2⟩ := (Finset.mem_filter.mp he2).2
                  exact hll e ((hU12_inter _ ht1 ht2).trans (hU12_inter _ hh1 hh2).symm)
                let f : E → ZMod 6 := fun e =>
                  (if h1 : e ∈ H₁.edges then f₁.val ⟨e, h1⟩ else 0) +
                  (if h2 : e ∈ H₂.edges then f₂.val ⟨e, h2⟩ else 0)
                have hext_fl : ∀ (H : G.Subgraph) (g : H.toMultigraph.NZFlow (ZMod 6)),
                    G.IsFlow (fun e => if h : e ∈ H.edges then g.val ⟨e, h⟩ else 0) := by
                  intro H g v
                  by_cases hv : v ∈ H.verts
                  · trans (H.toMultigraph.boundary g.val ⟨v, hv⟩)
                    · rw [boundary_eq_sum_ite, boundary_eq_sum_ite, ← Finset.sum_subset (Finset.subset_univ H.edges)]
                      · refine Finset.sum_bij (fun e he => ⟨e, he⟩) (fun _ _ => Finset.mem_univ _)
                          (fun _ _ _ _ h => congrArg Subtype.val h) (fun e _ => ⟨e.1, e.2, rfl⟩) (fun e he => by
                            rw [dif_pos he]; by_cases h1 : G.head e = v <;> by_cases h2 : G.tail e = v <;>
                              simp [Multigraph.Subgraph.toMultigraph, Subtype.ext_iff, h1, h2])
                      · intro e _ hnot; rw [dif_neg hnot]; simp
                    · exact g.isFlow ⟨v, hv⟩
                  · rw [boundary_eq_sum_ite]
                    refine Finset.sum_eq_zero fun e _ => by
                      by_cases he : e ∈ H.edges
                      · have hnt : G.tail e ≠ v := fun h => hv (h ▸ H.tail_mem he)
                        have hnh : G.head e ≠ v := fun h => hv (h ▸ H.head_mem he)
                        simp [hnt, hnh]
                      · rw [dif_neg he]; simp
                refine ⟨⟨f, isFlow_add (hext_fl H₁ f₁) (hext_fl H₂ f₂), fun e => ?_⟩⟩
                rcases hedge_side e with ⟨ht1, hh1⟩ | ⟨ht2, hh2⟩
                · have he1 : e ∈ H₁.edges := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht1, hh1⟩
                  have he2 : e ∉ H₂.edges := Finset.disjoint_left.mp hdisj_E12 he1
                  dsimp only [f]; rw [dif_pos he1, dif_neg he2, add_zero]; exact f₁.nonzero ⟨e, he1⟩
                · have he2 : e ∈ H₂.edges := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht2, hh2⟩
                  have he1 : e ∉ H₁.edges := Finset.disjoint_right.mp hdisj_E12 he2
                  dsimp only [f]; rw [dif_neg he1, dif_pos he2, zero_add]; exact f₂.nonzero ⟨e, he2⟩
            · -- Case 3: 2-edge cut {e₁, e₂} -> contract e₁ (< n vertices), extend via x e₁ = ± x e₂!
              unfold Multigraph.IsEdgeConnected at hconn3; push Not at hconn3
              rcases hconn3 with ⟨S, hSne, hScne, hlt3⟩
              have hge2 := hconn2 S hSne hScne
              have hcard2 : (G.cutEdges S).card = 2 := by omega
              obtain ⟨e₁, e₂, he12_ne, hcut_eq⟩ := Finset.card_eq_two.mp hcard2
              let H1 : G.Subgraph :=
                { verts := {G.tail e₁, G.head e₁}, edges := {e₁},
                  tail_mem := fun he => by rw [Finset.mem_singleton.mp he]; exact Finset.mem_insert_self _ _,
                  head_mem := fun he => by rw [Finset.mem_singleton.mp he]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _) }
              have hcard_star : Fintype.card (Option {v : V // v ∉ H1.verts}) < n := by
                rw [Fintype.card_option, Fintype.card_subtype_compl, Fintype.card_coe, Finset.card_pair (hll e₁)]
                have hle : H1.verts.card ≤ Fintype.card V := Finset.card_le_univ _
                rw [Finset.card_pair (hll e₁)] at hle; omega
              obtain ⟨fstar⟩ := ih _ hcard_star _ _ (G.contractSubgraph H1) rfl (contractSubgraph_isBridgeless G hbr H1)
              -- Extend fstar uniquely to e₁ via boundary at G.head e₁!
              let Gd := deleteEdge G e₁
              let f' : {e : E // e ≠ e₁} → ZMod 6 := fun e => fstar.val ⟨e.1, by simp [H1, e.2]⟩
              let val : E → ZMod 6 := fun e => if h : e = e₁ then -Gd.boundary f' (G.head e₁) else f' ⟨e, h⟩
              have hval_fl : G.IsFlow val := by
                -- Same unique extension as TutteFlowPoly!
                have hbd_head : G.boundary val (G.head e₁) = 0 := by
                  rw [boundary_eq_sum_ite, ← Finset.add_sum_erase _ _ (Finset.mem_univ e₁)]
                  have hrest : ∑ e ∈ Finset.univ.erase e₁,
                      ((if G.head e = G.head e₁ then val e else 0) - if G.tail e = G.head e₁ then val e else 0) =
                      Gd.boundary f' (G.head e₁) := by
                    rw [boundary_eq_sum_ite]
                    refine Finset.sum_bij (fun e he => ⟨e, Finset.ne_of_mem_erase he⟩) (fun _ _ => Finset.mem_univ _)
                      (fun _ _ _ _ h => congrArg Subtype.val h) (fun e _ => ⟨e.1, Finset.mem_erase.mpr ⟨e.2, Finset.mem_univ _⟩, rfl⟩)
                      (fun e he => by dsimp only [val, Gd, deleteEdge]; rw [dif_neg (Finset.ne_of_mem_erase he)]; rfl)
                  rw [hrest]; simp [val, hll e₁]
                have hbd_out : ∀ v, v ∉ H1.verts → G.boundary val v = 0 := by
                  intro v hv
                  have hfs := fstar.isFlow (some ⟨v, hv⟩)
                  trans ((G.contractSubgraph H1).boundary fstar.val (some ⟨v, hv⟩))
                  · rw [boundary_eq_sum_ite, boundary_eq_sum_ite, ← Finset.add_sum_erase _ _ (Finset.mem_univ e₁)]
                    have hnt : G.tail e₁ ≠ v := fun h => hv (h ▸ Finset.mem_insert_self _ _)
                    have hnh : G.head e₁ ≠ v := fun h => hv (h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
                    simp only [hnt, hnh, ↓reduceIte, sub_self, zero_add]
                    refine Finset.sum_bij (fun e he => ⟨e, by simp [H1, Finset.ne_of_mem_erase he]⟩)
                      (fun _ _ => Finset.mem_univ _) (fun _ _ _ _ h => congrArg Subtype.val h)
                      (fun e _ => ⟨e.1, Finset.mem_erase.mpr ⟨by simpa [H1] using e.2, Finset.mem_univ _⟩, rfl⟩)
                      (fun e he => by
                        have hne1 := Finset.ne_of_mem_erase he
                        dsimp only [val, f', Multigraph.contractSubgraph]
                        rw [dif_neg hne1]
                        have hh : (if h : G.head e ∈ H1.verts then (none : Option {u : V // u ∉ H1.verts}) else some ⟨G.head e, h⟩) = some ⟨v, hv⟩ ↔ G.head e = v := by
                          split_ifs with h
                          · exact ⟨fun h' => by simp at h', fun heq => absurd (heq ▸ h) hv⟩
                          · simp [Subtype.ext_iff]
                        have ht : (if h : G.tail e ∈ H1.verts then (none : Option {u : V // u ∉ H1.verts}) else some ⟨G.tail e, h⟩) = some ⟨v, hv⟩ ↔ G.tail e = v := by
                          split_ifs with h
                          · exact ⟨fun h' => by simp at h', fun heq => absurd (heq ▸ h) hv⟩
                          · simp [Subtype.ext_iff]
                        rw [if_congr hh.symm rfl rfl, if_congr ht.symm rfl rfl]; rfl)
                  · exact hfs
                intro v
                by_cases hv : v = G.head e₁
                · rw [hv]; exact hbd_head
                · by_cases hv2 : v = G.tail e₁
                  · rw [hv2]
                    -- Sum of all boundaries is 0, and every vertex ≠ G.tail e₁ already has boundary 0!
                    have hsum_all : ∑ u : V, G.boundary val u = 0 := by
                      have h := sum_boundary_eq_cut G val Finset.univ
                      have hf1 : Finset.univ.filter (fun e : E => G.head e ∈ (Finset.univ : Finset V) ∧ G.tail e ∉ (Finset.univ : Finset V)) = ∅ := by ext; simp
                      have hf2 : Finset.univ.filter (fun e : E => G.tail e ∈ (Finset.univ : Finset V) ∧ G.head e ∉ (Finset.univ : Finset V)) = ∅ := by ext; simp
                      rw [hf1, hf2] at h; simpa using h
                    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (G.tail e₁))] at hsum_all
                    have hrest : ∑ u ∈ Finset.univ.erase (G.tail e₁), G.boundary val u = 0 :=
                      Finset.sum_eq_zero fun u hu => by
                        have hne_t := Finset.ne_of_mem_erase hu
                        by_cases hhu : u = G.head e₁
                        · rw [hhu]; exact hbd_head
                        · exact hbd_out u (by simp [H1, hne_t, hhu])
                    rw [hrest, add_zero] at hsum_all; exact hsum_all
                  · exact hbd_out v (by simp [H1, hv, hv2])
              -- Conservation across 2-edge cut S forces val e₁ = ± val e₂ ≠ 0!
              have hval_nz : Multigraph.IsNowhereZero val := fun e => by
                by_cases he : e = e₁
                · rw [he]
                  have hsum := sum_boundary_eq_cut G val S
                  have hz : ∑ v ∈ S, G.boundary val v = 0 := Finset.sum_eq_zero fun v _ => hval_fl v
                  rw [hz] at hsum
                  have he₁_cut : e₁ ∈ G.cutEdges S := hcut_eq ▸ Finset.mem_insert_self _ _
                  have he₂_cut : e₂ ∈ G.cutEdges S := hcut_eq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
                  have hnz2 : val e₂ ≠ 0 := by
                    dsimp only [val, f']; rw [dif_neg he12_ne.symm]; exact fstar.nonzero _
                  have hrel : val e₁ = val e₂ ∨ val e₁ = -val e₂ := by
                    have hF1 : ∀ x, x ∈ Finset.univ.filter (fun x => G.head x ∈ S ∧ G.tail x ∉ S) → x = e₁ ∨ x = e₂ := fun x hx => by
                      have hm : x ∈ G.cutEdges S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨(Finset.mem_filter.mp hx).2.2, (Finset.mem_filter.mp hx).2.1⟩⟩
                      rw [hcut_eq, Finset.mem_insert, Finset.mem_singleton] at hm; exact hm
                    have hF2 : ∀ x, x ∈ Finset.univ.filter (fun x => G.tail x ∈ S ∧ G.head x ∉ S) → x = e₁ ∨ x = e₂ := fun x hx => by
                      have hm : x ∈ G.cutEdges S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl (Finset.mem_filter.mp hx).2⟩
                      rw [hcut_eq, Finset.mem_insert, Finset.mem_singleton] at hm; exact hm
                    rcases (Finset.mem_filter.mp he₁_cut).2 with ⟨ht1, hh1⟩ | ⟨ht1, hh1⟩ <;>
                    rcases (Finset.mem_filter.mp he₂_cut).2 with ⟨ht2, hh2⟩ | ⟨ht2, hh2⟩
                    · have hi : Finset.univ.filter (fun x => G.head x ∈ S ∧ G.tail x ∉ S) = ∅ := by
                        ext x; simp only [Finset.notMem_empty, iff_false]; intro hx
                        rcases hF1 x hx with rfl | rfl; exact (Finset.mem_filter.mp hx).2.2 ht1; exact (Finset.mem_filter.mp hx).2.2 ht2
                      have ho : Finset.univ.filter (fun x => G.tail x ∈ S ∧ G.head x ∉ S) = {e₁, e₂} := by
                        ext x; simp only [Finset.mem_insert, Finset.mem_singleton]
                        exact ⟨hF2 x, by rintro (rfl | rfl); exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht1, hh1⟩; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht2, hh2⟩⟩
                      rw [hi, ho, Finset.sum_empty, Finset.sum_pair he12_ne, zero_sub] at hsum
                      exact Or.inr (eq_neg_of_add_eq_zero_left (neg_eq_zero.mp hsum.symm))
                    · have hi : Finset.univ.filter (fun x => G.head x ∈ S ∧ G.tail x ∉ S) = {e₂} := by
                        ext x; simp only [Finset.mem_singleton]
                        exact ⟨fun hx => (hF1 x hx).resolve_left (fun h => (Finset.mem_filter.mp (h ▸ hx)).2.2 ht1),
                          fun h => h ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh2, ht2⟩⟩
                      have ho : Finset.univ.filter (fun x => G.tail x ∈ S ∧ G.head x ∉ S) = {e₁} := by
                        ext x; simp only [Finset.mem_singleton]
                        exact ⟨fun hx => (hF2 x hx).resolve_right (fun h => ht2 (Finset.mem_filter.mp (h ▸ hx)).2.1),
                          fun h => h ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht1, hh1⟩⟩
                      rw [hi, ho, Finset.sum_singleton, Finset.sum_singleton] at hsum
                      exact Or.inl (sub_eq_zero.mp hsum.symm).symm
                    · have hi : Finset.univ.filter (fun x => G.head x ∈ S ∧ G.tail x ∉ S) = {e₁} := by
                        ext x; simp only [Finset.mem_singleton]
                        exact ⟨fun hx => (hF1 x hx).resolve_right (fun h => (Finset.mem_filter.mp (h ▸ hx)).2.2 ht2),
                          fun h => h ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh1, ht1⟩⟩
                      have ho : Finset.univ.filter (fun x => G.tail x ∈ S ∧ G.head x ∉ S) = {e₂} := by
                        ext x; simp only [Finset.mem_singleton]
                        exact ⟨fun hx => (hF2 x hx).resolve_left (fun h => ht1 (Finset.mem_filter.mp (h ▸ hx)).2.1),
                          fun h => h ▸ Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht2, hh2⟩⟩
                      rw [hi, ho, Finset.sum_singleton, Finset.sum_singleton] at hsum
                      exact Or.inl (sub_eq_zero.mp hsum.symm)
                    · have hi : Finset.univ.filter (fun x => G.head x ∈ S ∧ G.tail x ∉ S) = {e₁, e₂} := by
                        ext x; simp only [Finset.mem_insert, Finset.mem_singleton]
                        exact ⟨hF1 x, by rintro (rfl | rfl); exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh1, ht1⟩; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh2, ht2⟩⟩
                      have ho : Finset.univ.filter (fun x => G.tail x ∈ S ∧ G.head x ∉ S) = ∅ := by
                        ext x; simp only [Finset.notMem_empty, iff_false]; intro hx
                        rcases hF2 x hx with rfl | rfl; exact ht1 (Finset.mem_filter.mp hx).2.1; exact ht2 (Finset.mem_filter.mp hx).2.1
                      rw [hi, ho, Finset.sum_pair he12_ne, Finset.sum_empty, sub_zero] at hsum
                      exact Or.inr (eq_neg_of_add_eq_zero_left hsum.symm)
                  rcases hrel with h1 | h1 <;> rw [h1]
                  · exact hnz2
                  · exact neg_ne_zero.mpr hnz2
                · dsimp only [val, f']; rw [dif_neg he]; exact fstar.nonzero _
              exact ⟨⟨val, hval_fl, hval_nz⟩⟩
          · -- Case 1: disconnected -> split into S and univ \ S
            unfold Multigraph.IsEdgeConnected at hconn1; push Not at hconn1
            rcases hconn1 with ⟨S, hSne, hScne, hlt1⟩
            have hcut0 : G.cutEdges S = ∅ := Finset.card_eq_zero.mp (by omega)
            have hcl : ∀ e : E, (G.tail e ∈ S ∧ G.head e ∈ S) ∨ (G.tail e ∉ S ∧ G.head e ∉ S) := fun e => by
              by_cases ht : G.tail e ∈ S <;> by_cases hh : G.head e ∈ S
              · exact Or.inl ⟨ht, hh⟩
              · exfalso; have : e ∈ G.cutEdges S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ⟨ht, hh⟩⟩; rw [hcut0] at this; exact Finset.notMem_empty _ this
              · exfalso; have : e ∈ G.cutEdges S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨ht, hh⟩⟩; rw [hcut0] at this; exact Finset.notMem_empty _ this
              · exact Or.inr ⟨ht, hh⟩
            have hbrU : ∀ (U : Finset V),
                (∀ e : E, (G.tail e ∈ U ∧ G.head e ∈ U) ∨ (G.tail e ∉ U ∧ G.head e ∉ U)) →
                (Multigraph.Subgraph.induced G U).toMultigraph.IsBridgeless := by
              intro U hUcl e hnot
              have hex : ∃ C : G.Subgraph, C.IsCycle ∧ e.1 ∈ C.edges := by by_contra hn'; exact hbr e.1 hn'
              rcases hex with ⟨C, hC, heC⟩
              have hCv : ∀ v ∈ C.verts, v ∈ U := fun v hv => by
                have htU := (Finset.mem_filter.mp e.2).2.1
                have hrtg := hC.1.2 (G.tail e.1) (C.tail_mem heC) v hv; clear hv
                induction hrtg with
                | refl => exact htU
                | tail _ hs ihp =>
                  rcases hs with ⟨x, _, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
                  · rcases hUcl x with ⟨_, hhx⟩ | ⟨htx, _⟩; exact h2 ▸ hhx; exact absurd (h1 ▸ ihp) htx
                  · rcases hUcl x with ⟨htx, _⟩ | ⟨_, hhx⟩; exact h1 ▸ htx; exact absurd (h2 ▸ ihp) hhx
              let HU := Multigraph.Subgraph.induced G U
              have hCe : ∀ x ∈ C.edges, x ∈ HU.edges := fun x hx =>
                Finset.mem_filter.mpr ⟨Finset.mem_univ _, hCv _ (C.tail_mem hx), hCv _ (C.head_mem hx)⟩
              let CU : HU.toMultigraph.Subgraph :=
                { verts := Finset.univ.filter (fun v : {v // v ∈ HU.verts} => v.1 ∈ C.verts)
                  edges := Finset.univ.filter (fun x : {x // x ∈ HU.edges} => x.1 ∈ C.edges)
                  tail_mem := fun hx => Finset.mem_filter.mpr ⟨Finset.mem_univ _, C.tail_mem (Finset.mem_filter.mp hx).2⟩
                  head_mem := fun hx => Finset.mem_filter.mpr ⟨Finset.mem_univ _, C.head_mem (Finset.mem_filter.mp hx).2⟩ }
              refine hnot ⟨CU, ⟨⟨?_, ?_⟩, ?_⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, heC⟩⟩
              · obtain ⟨v, hv⟩ := hC.1.1; exact ⟨⟨v, hCv v hv⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩⟩
              · intro a ha b hb
                have hrtg := hC.1.2 a.1 (Finset.mem_filter.mp ha).2 b.1 (Finset.mem_filter.mp hb).2
                have hgo : ∀ x y, Relation.ReflTransGen C.Adj x y → ∀ (hxU : x ∈ HU.verts) (hyU : y ∈ HU.verts),
                    Relation.ReflTransGen CU.Adj ⟨x, hxU⟩ ⟨y, hyU⟩ := by
                  intro x y hxy; induction hxy with
                  | refl => intro _ _; exact .refl
                  | @tail p q _ hs ihp =>
                    intro hxU hqU
                    rcases hs with ⟨y', hy', ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
                    · exact (ihp hxU (h1 ▸ hCv _ (C.tail_mem hy'))).tail ⟨⟨y', hCe y' hy'⟩,
                        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy'⟩, Or.inl ⟨Subtype.ext h1, Subtype.ext h2⟩⟩
                    · exact (ihp hxU (h2 ▸ hCv _ (C.head_mem hy'))).tail ⟨⟨y', hCe y' hy'⟩,
                        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy'⟩, Or.inr ⟨Subtype.ext h1, Subtype.ext h2⟩⟩
                exact hgo a.1 b.1 hrtg a.2 b.2
              · intro z hz
                have hd := hC.2 z.1 (Finset.mem_filter.mp hz).2
                unfold Multigraph.Subgraph.deg at hd ⊢
                have h1 : (CU.edges.filter (fun y => HU.toMultigraph.tail y = z)).card = (C.edges.filter (fun y => G.tail y = z.1)).card := by
                  refine Finset.card_bij (fun y _ => y.1) (fun y hy => ?_) (fun _ _ _ _ h => Subtype.ext h)
                    (fun y hy => ⟨⟨y, hCe y (Finset.mem_filter.mp hy).1⟩, ?_, rfl⟩)
                  · rw [Finset.mem_filter] at hy ⊢; exact ⟨(Finset.mem_filter.mp hy.1).2, congrArg Subtype.val hy.2⟩
                  · rw [Finset.mem_filter] at hy ⊢; exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy.1⟩, Subtype.ext hy.2⟩
                have h2 : (CU.edges.filter (fun y => HU.toMultigraph.head y = z)).card = (C.edges.filter (fun y => G.head y = z.1)).card := by
                  refine Finset.card_bij (fun y _ => y.1) (fun y hy => ?_) (fun _ _ _ _ h => Subtype.ext h)
                    (fun y hy => ⟨⟨y, hCe y (Finset.mem_filter.mp hy).1⟩, ?_, rfl⟩)
                  · rw [Finset.mem_filter] at hy ⊢; exact ⟨(Finset.mem_filter.mp hy.1).2, congrArg Subtype.val hy.2⟩
                  · rw [Finset.mem_filter] at hy ⊢; exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy.1⟩, Subtype.ext hy.2⟩
                rw [h1, h2]; exact hd
            have hS_lt : S.card < n := by
              have hpos := Finset.card_pos.mpr hScne
              have hsd : (Finset.univ \ S).card = Fintype.card V - S.card := by rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
              omega
            have hSc_lt : (Finset.univ \ S).card < n := by
              have hpos := Finset.card_pos.mpr hSne
              have hsd : (Finset.univ \ S).card = Fintype.card V - S.card := by rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
              omega
            have hcl_c : ∀ e : E, (G.tail e ∈ Finset.univ \ S ∧ G.head e ∈ Finset.univ \ S) ∨
                (G.tail e ∉ Finset.univ \ S ∧ G.head e ∉ Finset.univ \ S) := fun e => by
              simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, not_not]
              rcases hcl e with h | h; exact Or.inr h; exact Or.inl h
            let H₁ := Multigraph.Subgraph.induced G S
            let H₂ := Multigraph.Subgraph.induced G (Finset.univ \ S)
            obtain ⟨f₁⟩ := ih S.card hS_lt _ _ H₁.toMultigraph (Fintype.card_coe S) (hbrU S hcl)
            obtain ⟨f₂⟩ := ih (Finset.univ \ S).card hSc_lt _ _ H₂.toMultigraph (Fintype.card_coe _) (hbrU _ hcl_c)
            let f : E → ZMod 6 := fun e =>
              (if h1 : e ∈ H₁.edges then f₁.val ⟨e, h1⟩ else 0) +
              (if h2 : e ∈ H₂.edges then f₂.val ⟨e, h2⟩ else 0)
            have hext_fl : ∀ (H : G.Subgraph) (g : H.toMultigraph.NZFlow (ZMod 6)),
                G.IsFlow (fun e => if h : e ∈ H.edges then g.val ⟨e, h⟩ else 0) := by
              intro H g v
              by_cases hv : v ∈ H.verts
              · trans (H.toMultigraph.boundary g.val ⟨v, hv⟩)
                · rw [boundary_eq_sum_ite, boundary_eq_sum_ite, ← Finset.sum_subset (Finset.subset_univ H.edges)]
                  · refine Finset.sum_bij (fun e he => ⟨e, he⟩) (fun _ _ => Finset.mem_univ _)
                      (fun _ _ _ _ h => congrArg Subtype.val h) (fun e _ => ⟨e.1, e.2, rfl⟩) (fun e he => by
                        rw [dif_pos he]; by_cases h1 : G.head e = v <;> by_cases h2 : G.tail e = v <;>
                          simp [Multigraph.Subgraph.toMultigraph, Subtype.ext_iff, h1, h2])
                  · intro e _ hnot; rw [dif_neg hnot]; simp
                · exact g.isFlow ⟨v, hv⟩
              · rw [boundary_eq_sum_ite]
                refine Finset.sum_eq_zero fun e _ => by
                  by_cases he : e ∈ H.edges
                  · have hnt : G.tail e ≠ v := fun h => hv (h ▸ H.tail_mem he)
                    have hnh : G.head e ≠ v := fun h => hv (h ▸ H.head_mem he)
                    simp [hnt, hnh]
                  · rw [dif_neg he]; simp
            refine ⟨⟨f, isFlow_add (hext_fl H₁ f₁) (hext_fl H₂ f₂), fun e => ?_⟩⟩
            rcases hcl e with ⟨ht, hh⟩ | ⟨ht, hh⟩
            · have he1 : e ∈ H₁.edges := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht, hh⟩
              have he2 : e ∉ H₂.edges := fun h => (Finset.mem_sdiff.mp (Finset.mem_filter.mp h).2.1).2 ht
              dsimp only [f]; rw [dif_pos he1, dif_neg he2, add_zero]; exact f₁.nonzero ⟨e, he1⟩
            · have he2 : e ∈ H₂.edges := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
                Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ht⟩, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hh⟩⟩
              have he1 : e ∉ H₁.edges := fun h => ht (Finset.mem_filter.mp h).2.1
              dsimp only [f]; rw [dif_neg he1, dif_pos he2, zero_add]; exact f₂.nonzero ⟨e, he2⟩
      -- Step B: General bridgeless graph -> deleteLoops + put 1 on loops!
      intro V E _ _ _ _ G hcard hbr
      obtain ⟨f'⟩ := hll_case V _ G.deleteLoops hcard (deleteLoops_isBridgeless G hbr) (fun e => e.2)
      let f : E → ZMod 6 := fun e => if h : G.tail e ≠ G.head e then f'.val ⟨e, h⟩ else 1
      refine ⟨⟨f, fun v => ?_, fun e => by dsimp only [f]; split_ifs with h; exact f'.nonzero ⟨e, h⟩; decide⟩⟩
      trans (G.deleteLoops.boundary f'.val v)
      · rw [boundary_eq_sum_ite, boundary_eq_sum_ite,
            ← Finset.sum_subset (Finset.subset_univ (Finset.univ.filter (fun e : E => G.tail e ≠ G.head e)))]
        · refine Finset.sum_bij (fun e he => ⟨e, (Finset.mem_filter.mp he).2⟩) (fun _ _ => Finset.mem_univ _)
            (fun _ _ _ _ h => congrArg Subtype.val h)
            (fun e _ => ⟨e.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, e.2⟩, rfl⟩)
            (fun e he => by simp [f, (Finset.mem_filter.mp he).2, Multigraph.deleteLoops]; rfl)
        · intro e _ hnot
          have hlp : G.tail e = G.head e := by by_contra hne; exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
          simp [hlp]
      · exact f'.isFlow v
  intro V E _ _ _ _ G A _ _ _ hbr hA
  exact nzflow_of_zmod6 G A hA (hz6 (Fintype.card V) V E G rfl hbr)

end Flow.Proofs
