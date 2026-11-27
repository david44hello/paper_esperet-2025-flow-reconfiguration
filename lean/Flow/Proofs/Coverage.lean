module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Flow.Defs.Literature
public import Flow.Proofs.Elementary
public import Mathlib.Data.Nat.Totient
public import Mathlib.NumberTheory.SumPrimeReciprocals
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Tactic

@[expose] public section

/-!
# Additional coverage proofs: Section 1 `ℤ_3` counterexample, Section 2 move invariance under
reorientation, and Figure 1 density-1 theorem
-/

namespace Flow.Proofs

open Flow

/-! ### Section 1: `ℤ_3` fails on three parallel edges between two vertices -/

private lemma zmod3_const_of_sum_zero :
    ∀ a b c : ZMod 3, a ≠ 0 → b ≠ 0 → c ≠ 0 → a + b + c = 0 → a = b ∧ b = c := by
  decide

theorem sec1_Z3_three_parallel_disconnected_proved :
    let G : Multigraph (Fin 2) (Fin 3) := ⟨fun _ => 0, fun _ => 1⟩
    G.IsBridgeless ∧ G.IsLoopless ∧ ¬ G.FlowGraphConnected (ZMod 3) := by
  dsimp only
  let G : Multigraph (Fin 2) (Fin 3) := ⟨fun _ => 0, fun _ => 1⟩
  have hll : G.IsLoopless := fun _ => by change (0 : Fin 2) ≠ 1; decide
  have hbr : G.IsBridgeless := by
    intro e hnot
    let e' : Fin 3 := if e = 0 then 1 else 0
    let C : G.Subgraph :=
      { verts := Finset.univ
        edges := {e, e'}
        tail_mem := fun _ => Finset.mem_univ _
        head_mem := fun _ => Finset.mem_univ _ }
    have hcyc : C.IsCycle := by
      refine ⟨⟨⟨0, Finset.mem_univ 0⟩, ?_⟩, ?_⟩
      · intro u _ v _
        fin_cases u <;> fin_cases v
        · exact Relation.ReflTransGen.refl
        · exact Relation.ReflTransGen.single ⟨e, Finset.mem_insert_self _ _, Or.inl ⟨rfl, rfl⟩⟩
        · exact Relation.ReflTransGen.single ⟨e, Finset.mem_insert_self _ _, Or.inr ⟨rfl, rfl⟩⟩
        · exact Relation.ReflTransGen.refl
      · intro v _
        fin_cases v <;> fin_cases e <;>
          (dsimp only [Multigraph.Subgraph.deg, C, e', G]; decide)
    exact hnot ⟨C, hcyc, Finset.mem_insert_self e {e'}⟩
  refine ⟨hbr, hll, ?_⟩
  intro hconn
  let f1 : G.NZFlow (ZMod 3) :=
    { val := fun _ => (1 : ZMod 3)
      isFlow := fun v => by fin_cases v <;> (dsimp only [Multigraph.boundary, G]; decide)
      nonzero := fun _ => by change (1 : ZMod 3) ≠ 0; decide }
  let f2 : G.NZFlow (ZMod 3) :=
    { val := fun _ => (2 : ZMod 3)
      isFlow := fun v => by fin_cases v <;> (dsimp only [Multigraph.boundary, G]; decide)
      nonzero := fun _ => by change (2 : ZMod 3) ≠ 0; decide }
  have hno_move : ∀ g : G.NZFlow (ZMod 3), ¬ G.FlowMove f1 g := by
    rintro g ⟨C, lam, hlam, heq⟩
    have hcard_C : C.sub.edges.card = 2 := by
      have hv0 : (0 : Fin 2) ∈ C.sub.verts := by
        obtain ⟨u, hu⟩ := C.isCycle.1.1
        have hdeg := C.isCycle.2 u hu
        have hne_e : C.sub.edges.Nonempty := by
          by_contra hempty
          rw [Finset.not_nonempty_iff_eq_empty] at hempty
          simp [Multigraph.Subgraph.deg, hempty] at hdeg
        obtain ⟨e, he⟩ := hne_e
        exact C.sub.tail_mem he
      have hdeg0 := C.isCycle.2 0 hv0
      unfold Multigraph.Subgraph.deg at hdeg0
      have hfilt_t : C.sub.edges.filter (fun e => G.tail e = 0) = C.sub.edges := by
        ext e; simp [G]
      have hfilt_h : C.sub.edges.filter (fun e => G.head e = 0) = ∅ := by
        ext e; simp [G]
      rw [hfilt_t, hfilt_h, Finset.card_empty, add_zero] at hdeg0
      exact hdeg0
    have hex_out : ∃ e0 : Fin 3, e0 ∉ C.sub.edges := by
      by_contra hall
      push Not at hall
      have huniv : C.sub.edges = Finset.univ := by ext e; simp [hall e]
      rw [huniv] at hcard_C
      simp at hcard_C
    obtain ⟨e0, he0⟩ := hex_out
    have hg_sum : g.val 0 + g.val 1 + g.val 2 = 0 := by
      have h0 := g.isFlow 0
      unfold Multigraph.boundary at h0
      have h1 : Finset.univ.filter (fun e : Fin 3 => G.head e = 0) = ∅ := by
        ext e; simp [G]
      have h2 : Finset.univ.filter (fun e : Fin 3 => G.tail e = 0) = Finset.univ := by
        ext e; simp [G]
      rw [h1, h2, Finset.sum_empty, zero_sub, neg_eq_zero] at h0
      simpa [Fin.sum_univ_three, add_assoc] using h0
    have hge := zmod3_const_of_sum_zero (g.val 0) (g.val 1) (g.val 2)
      (g.nonzero 0) (g.nonzero 1) (g.nonzero 2) hg_sum
    have hge0 : g.val e0 = 1 := by
      rw [heq e0, C.sign_zero he0, zero_zsmul, add_zero]
    have hall1 : ∀ e : Fin 3, g.val e = 1 := by
      intro e
      have h012 : g.val e = g.val e0 := by
        fin_cases e <;> fin_cases e0 <;>
          first | rfl | exact hge.1 | exact hge.1.symm | exact hge.2 | exact hge.2.symm |
            exact hge.1.trans hge.2 | exact (hge.1.trans hge.2).symm
      exact h012.trans hge0
    have hex_in : ∃ e1 : Fin 3, e1 ∈ C.sub.edges := Finset.card_pos.mp (by omega)
    obtain ⟨e1, he1⟩ := hex_in
    have h1eq := heq e1
    rw [hall1 e1] at h1eq
    have hzero : C.sign e1 • lam = 0 := by
      have : (1 : ZMod 3) = (1 : ZMod 3) + C.sign e1 • lam := h1eq
      simpa using (eq_sub_of_add_eq' this.symm).symm
    rcases C.sign_mem he1 with hs | hs
    · rw [hs, one_zsmul] at hzero; exact hlam hzero
    · rw [hs, neg_one_zsmul, neg_eq_zero] at hzero; exact hlam hzero
  rcases Relation.ReflTransGen.cases_head (hconn f1 f2) with heq | ⟨g, hmv, _⟩
  · have h0 := congrArg (fun φ : G.NZFlow (ZMod 3) => φ.val 0) heq
    exact absurd h0 (by decide)
  · exact hno_move g hmv

/-! ### Section 2: Reorientation preserves `FlowMove` -/

private def reorientDirectedCycle {V E : Type} [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : Multigraph V E) (flip : E → Bool) (C : G.DirectedCycle) :
    (G.reorient flip).DirectedCycle where
  sub :=
    { verts := C.sub.verts
      edges := C.sub.edges
      tail_mem := fun {e} he => by
        change (if flip e then G.head e else G.tail e) ∈ C.sub.verts
        split_ifs
        · exact C.sub.head_mem he
        · exact C.sub.tail_mem he
      head_mem := fun {e} he => by
        change (if flip e then G.tail e else G.head e) ∈ C.sub.verts
        split_ifs
        · exact C.sub.tail_mem he
        · exact C.sub.head_mem he }
  isCycle := by
    refine ⟨⟨C.isCycle.1.1, ?_⟩, ?_⟩
    · intro u hu v hv
      have hw := C.isCycle.1.2 u hu v hv
      clear hv
      induction hw with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ hstep ih =>
        rcases hstep with ⟨e, he, h⟩
        refine Relation.ReflTransGen.tail ih ⟨e, he, ?_⟩
        change ((if flip e then G.head e else G.tail e) = _ ∧
                (if flip e then G.tail e else G.head e) = _) ∨
               ((if flip e then G.head e else G.tail e) = _ ∧
                (if flip e then G.tail e else G.head e) = _)
        cases flip e <;> simp only [Bool.false_eq_true, ↓reduceIte]
        · exact h
        · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inr ⟨h2, h1⟩
          · exact Or.inl ⟨h2, h1⟩
    · intro v hv
      have hdeg := C.isCycle.2 v hv
      unfold Multigraph.Subgraph.deg at hdeg ⊢
      have hsum : ∀ (P Q : E → Prop) [DecidablePred P] [DecidablePred Q],
          (C.sub.edges.filter P).card + (C.sub.edges.filter Q).card =
          ∑ e ∈ C.sub.edges, ((if P e then 1 else 0) + (if Q e then 1 else 0)) := by
        intro P Q _ _
        rw [Finset.sum_add_distrib, Finset.sum_boole, Finset.sum_boole]
        simp
      rw [hsum] at hdeg
      rw [hsum, ← hdeg]
      refine Finset.sum_congr rfl fun e _ => ?_
      change ((if (if flip e then G.head e else G.tail e) = v then 1 else 0) +
              (if (if flip e then G.tail e else G.head e) = v then 1 else 0)) = _
      cases flip e <;> simp [add_comm]
  sign := Multigraph.reorientVal flip C.sign
  sign_mem := fun {e} he => by
    unfold Multigraph.reorientVal
    rcases C.sign_mem he with h | h <;> cases flip e <;> simp [h]
  sign_zero := fun {e} he => by
    unfold Multigraph.reorientVal
    cases flip e <;> simp [C.sign_zero he]
  isFlow := (sec2_reorient_preserves_flow_proved G flip C.sign).mpr C.isFlow

private def unReorientDirectedCycle {V E : Type} [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : Multigraph V E) (flip : E → Bool) (C : (G.reorient flip).DirectedCycle) :
    G.DirectedCycle where
  sub :=
    { verts := C.sub.verts
      edges := C.sub.edges
      tail_mem := fun {e} he => by
        have ht := C.sub.tail_mem he
        have hh := C.sub.head_mem he
        cases hfl : flip e <;> simp [Multigraph.reorient, hfl] at ht hh
        · exact ht
        · exact hh
      head_mem := fun {e} he => by
        have ht := C.sub.tail_mem he
        have hh := C.sub.head_mem he
        cases hfl : flip e <;> simp [Multigraph.reorient, hfl] at ht hh
        · exact hh
        · exact ht }
  isCycle := by
    refine ⟨⟨C.isCycle.1.1, ?_⟩, ?_⟩
    · intro u hu v hv
      have hw := C.isCycle.1.2 u hu v hv
      clear hv
      induction hw with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ hstep ih =>
        rcases hstep with ⟨e, he, h⟩
        refine Relation.ReflTransGen.tail ih ⟨e, he, ?_⟩
        cases hfl : flip e <;> simp [Multigraph.reorient, hfl] at h
        · exact h
        · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inr ⟨h2, h1⟩
          · exact Or.inl ⟨h2, h1⟩
    · intro v hv
      have hdeg := C.isCycle.2 v hv
      unfold Multigraph.Subgraph.deg at hdeg ⊢
      have hsum : ∀ (P Q : E → Prop) [DecidablePred P] [DecidablePred Q],
          (C.sub.edges.filter P).card + (C.sub.edges.filter Q).card =
          ∑ e ∈ C.sub.edges, ((if P e then 1 else 0) + (if Q e then 1 else 0)) := by
        intro P Q _ _
        rw [Finset.sum_add_distrib, Finset.sum_boole, Finset.sum_boole]
        simp
      rw [hsum] at hdeg
      rw [hsum, ← hdeg]
      refine Finset.sum_congr rfl fun e _ => ?_
      change _ = ((if (if flip e then G.head e else G.tail e) = v then 1 else 0) +
                  (if (if flip e then G.tail e else G.head e) = v then 1 else 0))
      cases flip e <;> simp [add_comm]
  sign := Multigraph.reorientVal flip C.sign
  sign_mem := fun {e} he => by
    unfold Multigraph.reorientVal
    rcases C.sign_mem he with h | h <;> cases flip e <;> simp [h]
  sign_zero := fun {e} he => by
    unfold Multigraph.reorientVal
    cases flip e <;> simp [C.sign_zero he]
  isFlow := by
    have hinv : Multigraph.reorientVal flip (Multigraph.reorientVal flip C.sign) = C.sign := by
      funext e; unfold Multigraph.reorientVal; cases flip e <;> simp
    rw [← sec2_reorient_preserves_flow_proved G flip (Multigraph.reorientVal flip C.sign), hinv]
    exact C.isFlow

theorem sec2_reorient_preserves_flowMove_proved
    {V E Γ : Type} [Fintype E] [DecidableEq V] [DecidableEq E] [AddCommGroup Γ]
    (G : Multigraph V E) (flip : E → Bool) (f g : G.NZFlow Γ)
    (f' g' : (G.reorient flip).NZFlow Γ)
    (hf' : ∀ e, f'.val e = Multigraph.reorientVal flip f.val e)
    (hg' : ∀ e, g'.val e = Multigraph.reorientVal flip g.val e) :
    (G.reorient flip).FlowMove f' g' ↔ G.FlowMove f g := by
  constructor
  · rintro ⟨C, lam, hlam, heq⟩
    refine ⟨unReorientDirectedCycle G flip C, lam, hlam, fun e => ?_⟩
    have h1 := heq e
    rw [hg' e, hf' e] at h1
    dsimp only [unReorientDirectedCycle]
    unfold Multigraph.reorientVal at h1 ⊢
    cases hfl : flip e <;> simp only [hfl, Bool.false_eq_true, ↓reduceIte] at h1 ⊢
    · exact h1
    · rw [neg_zsmul]
      have h2 := congrArg Neg.neg h1
      simpa only [neg_neg, neg_add, sub_eq_add_neg] using h2
  · rintro ⟨C, lam, hlam, heq⟩
    refine ⟨reorientDirectedCycle G flip C, lam, hlam, fun e => ?_⟩
    rw [hg' e, hf' e]
    dsimp only [reorientDirectedCycle]
    unfold Multigraph.reorientVal
    rw [heq e]
    cases hfl : flip e
    · simp [hfl]
    · simp only [↓reduceIte, neg_add, neg_zsmul]

/-! ### Figure 1 caption: Natural density `1` of covered orders -/

private lemma card_coprime_Icc_le (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (N : ℕ) :
    let M := ∏ p ∈ P, p
    ((Finset.Icc 1 N).filter (fun n => ∀ p ∈ P, ¬ p ∣ n)).card ≤
      (N / M + 1) * Nat.totient M := by
  intro M
  have hM_pos : 0 < M := Finset.prod_pos fun p hp => (hP p hp).pos
  have hcop : ∀ n : ℕ, (∀ p ∈ P, ¬ p ∣ n) → Nat.Coprime M n := by
    intro n hn
    apply Nat.Coprime.prod_left
    intro p hp
    exact (hP p hp).coprime_iff_not_dvd.mpr (hn p hp)
  let S := (Finset.Icc 1 N).filter (fun n => ∀ p ∈ P, ¬ p ∣ n)
  let block : ℕ → Finset ℕ := fun k =>
    (Finset.Ico (k * M) ((k + 1) * M)).filter (fun n => Nat.Coprime M n)
  have hsub : S ⊆ (Finset.range (N / M + 1)).biUnion block := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    rw [Finset.mem_biUnion]
    refine ⟨n / M, Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hn.1.2)), ?_⟩
    rw [Finset.mem_filter, Finset.mem_Ico]
    refine ⟨⟨Nat.div_mul_le_self n M, ?_⟩, hcop n hn.2⟩
    have := Nat.lt_div_mul_add hM_pos (a := n)
    linarith
  have hblock_card : ∀ k : ℕ, (block k).card = Nat.totient M := by
    intro k
    rw [Nat.totient_eq_card_coprime]
    refine Finset.card_bij (fun n _ => n % M) ?_ ?_ ?_
    · intro n hn
      rw [Finset.mem_filter] at hn ⊢
      refine ⟨Finset.mem_range.mpr (Nat.mod_lt n hM_pos), ?_⟩
      rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm, ← Nat.gcd_rec]
      exact hn.2.gcd_eq_one
    · intro n₁ hn₁ n₂ hn₂ hmod
      rw [Finset.mem_filter, Finset.mem_Ico] at hn₁ hn₂
      have hd1 : n₁ / M = k := by
        have hlo : k ≤ n₁ / M := (Nat.le_div_iff_mul_le hM_pos).mpr hn₁.1.1
        have hhi : n₁ / M < k + 1 := (Nat.div_lt_iff_lt_mul hM_pos).mpr hn₁.1.2
        omega
      have hd2 : n₂ / M = k := by
        have hlo : k ≤ n₂ / M := (Nat.le_div_iff_mul_le hM_pos).mpr hn₂.1.1
        have hhi : n₂ / M < k + 1 := (Nat.div_lt_iff_lt_mul hM_pos).mpr hn₂.1.2
        omega
      have e1 := Nat.div_add_mod n₁ M
      have e2 := Nat.div_add_mod n₂ M
      rw [hd1] at e1; rw [hd2] at e2
      omega
    · intro r hr
      rw [Finset.mem_filter, Finset.mem_range] at hr
      refine ⟨k * M + r, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, by nlinarith⟩, ?_⟩, ?_⟩
      · have h1 : Nat.Coprime M (r + k * M) := (Nat.coprime_add_mul_right_right M r k).mpr hr.2
        simpa [add_comm] using h1
      · rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hr.1]
  calc S.card ≤ ((Finset.range (N / M + 1)).biUnion block).card := Finset.card_le_card hsub
    _ ≤ ∑ k ∈ Finset.range (N / M + 1), (block k).card := Finset.card_biUnion_le
    _ = ∑ _k ∈ Finset.range (N / M + 1), Nat.totient M := Finset.sum_congr rfl fun k _ => hblock_card k
    _ = (N / M + 1) * Nat.totient M := by simp

private lemma totient_prod_primes (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) :
    (Nat.totient (∏ p ∈ P, p) : ℝ) / (∏ p ∈ P, p : ℕ) = ∏ p ∈ P, (1 - 1 / (p : ℝ)) := by
  induction P using Finset.induction_on with
  | empty => simp
  | @insert q Q hq ih =>
    have hq_prime : Nat.Prime q := hP q (Finset.mem_insert_self _ _)
    have hQ_prime : ∀ p ∈ Q, Nat.Prime p := fun p hp => hP p (Finset.mem_insert_of_mem hp)
    have hcop : Nat.Coprime q (∏ p ∈ Q, p) := by
      apply Nat.Coprime.prod_right
      intro p hp
      have hne : q ≠ p := fun h => hq (h ▸ hp)
      exact (hq_prime.coprime_iff_not_dvd).mpr fun hd =>
        hne ((Nat.prime_dvd_prime_iff_eq hq_prime (hQ_prime p hp)).mp hd)
    rw [Finset.prod_insert hq, Nat.totient_mul hcop, Nat.totient_prime hq_prime,
        Finset.prod_insert hq, Nat.cast_mul, Nat.cast_mul, mul_div_mul_comm, ih hQ_prime]
    congr 1
    have hq_pos : (0 : ℝ) < (q : ℝ) := Nat.cast_pos.mpr hq_prime.pos
    have hq1 : 1 ≤ q := hq_prime.one_le
    rw [Nat.cast_sub hq1, Nat.cast_one]
    field_simp

private lemma exists_prime_set_sum_gt (F : Finset ℕ) (B : ℝ) :
    ∃ P : Finset ℕ, (∀ p ∈ P, Nat.Prime p ∧ 5 ≤ p ∧ p ∉ F) ∧ B < ∑ p ∈ P, (1 : ℝ) / (p : ℝ) := by
  classical
  let bad : Finset ℕ := insert 2 (insert 3 F)
  have hnot : ¬ Summable (fun n : ℕ => if Nat.Prime n ∧ n ∉ bad then (1 : ℝ) / (n : ℝ) else 0) := by
    intro hsum
    have hbad_sum : Summable (fun n : ℕ => if Nat.Prime n ∧ n ∈ bad then (1 : ℝ) / (n : ℝ) else 0) := by
      apply summable_of_ne_finset_zero (s := bad)
      intro n hn; simp [hn]
    have hall : Summable (fun n : ℕ => if Nat.Prime n then (1 : ℝ) / (n : ℝ) else 0) := by
      have heq : (fun n : ℕ => if Nat.Prime n then (1 : ℝ) / (n : ℝ) else 0) =
          fun n => (if Nat.Prime n ∧ n ∉ bad then (1 : ℝ) / (n : ℝ) else 0) +
                   (if Nat.Prime n ∧ n ∈ bad then (1 : ℝ) / (n : ℝ) else 0) := by
        funext n
        by_cases hp : Nat.Prime n <;> by_cases hb : n ∈ bad <;> simp [hp, hb]
      rw [heq]
      exact hsum.add hbad_sum
    have hdiv := Nat.Primes.not_summable_one_div
    apply hdiv
    have hcomp : Summable ((fun n : ℕ => if Nat.Prime n then (1 : ℝ) / (n : ℝ) else 0) ∘
        (Subtype.val : Nat.Primes → ℕ)) :=
      hall.comp_injective Subtype.val_injective
    refine hcomp.congr fun p => ?_
    simp [p.prop]
  have hunb : ∃ s : Finset ℕ, B < ∑ n ∈ s, (if Nat.Prime n ∧ n ∉ bad then (1 : ℝ) / (n : ℝ) else 0) := by
    by_contra hbdd
    push Not at hbdd
    apply hnot
    exact summable_of_sum_le (fun n => by split_ifs <;> positivity) hbdd
  obtain ⟨s, hs⟩ := hunb
  let P := s.filter (fun n => Nat.Prime n ∧ n ∉ bad)
  refine ⟨P, ?_, ?_⟩
  · intro p hp
    rcases Finset.mem_filter.mp hp with ⟨_, hprime, hnbad⟩
    have hp2 : p ≠ 2 := fun h => hnbad (h ▸ Finset.mem_insert_self 2 _)
    have hp3 : p ≠ 3 := fun h => hnbad (h ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self 3 _))
    have hpF : p ∉ F := fun h => hnbad (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have hp5 : 5 ≤ p := by
      have hge2 := hprime.two_le
      have hp4 : p ≠ 4 := fun h => absurd (h ▸ hprime) (by decide)
      omega
    exact ⟨hprime, hp5, hpF⟩
  · rwa [← Finset.sum_filter] at hs

private lemma prod_one_sub_le_exp (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) :
    ∏ p ∈ P, (1 - 1 / (p : ℝ)) ≤ ∏ p ∈ P, Real.exp (-(1 / (p : ℝ))) := by
  induction P using Finset.induction_on with
  | empty => simp
  | @insert q Q hq ih =>
    have hq_prime : Nat.Prime q := hP q (Finset.mem_insert_self _ _)
    have hQ_prime : ∀ p ∈ Q, Nat.Prime p := fun p hp => hP p (Finset.mem_insert_of_mem hp)
    rw [Finset.prod_insert hq, Finset.prod_insert hq]
    have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq_prime.one_le
    have hq_nn : 0 ≤ 1 - 1 / (q : ℝ) := by
      have : 1 / (q : ℝ) ≤ 1 := div_le_one_of_le₀ hq1 (by positivity)
      linarith
    have hq_le : 1 - 1 / (q : ℝ) ≤ Real.exp (-(1 / (q : ℝ))) := by
      linarith [Real.add_one_le_exp (-(1 / (q : ℝ)))]
    have hQ_nn : 0 ≤ ∏ p ∈ Q, (1 - 1 / (p : ℝ)) := by
      refine Finset.prod_nonneg fun p hp => ?_
      have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hQ_prime p hp).one_le
      have : 1 / (p : ℝ) ≤ 1 := div_le_one_of_le₀ hp1 (by positivity)
      linarith
    exact mul_le_mul hq_le (ih hQ_prime) hQ_nn (le_of_lt (Real.exp_pos _))

theorem fig1_density_one_proved :
    let covered : ℕ → Prop := fun n =>
      (¬ ∃ p r, Nat.Prime p ∧ 1 ≤ r ∧ n = p ^ r) ∧
      (∃ d : ℕ, d ∣ n ∧ 4 ≤ d ∧ 10 * d ≤ n)
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 N ∧ (∀ n ∈ S, covered n) ∧
        (1 - ε) * (N : ℝ) ≤ (S.card : ℝ) := by
  classical
  intro covered ε hε
  obtain ⟨B, hB⟩ : ∃ B : ℝ, Real.exp (-B) < ε / 4 := by
    refine ⟨-Real.log (ε / 8) + 1, ?_⟩
    have h8 : 0 < ε / 8 := by linarith
    calc Real.exp (-(-Real.log (ε / 8) + 1)) = Real.exp (Real.log (ε / 8) - 1) := by ring_nf
      _ = (ε / 8) * Real.exp (-1) := by rw [sub_eq_add_neg, Real.exp_add, Real.exp_log h8]
      _ < (ε / 8) * 1 := by
          apply mul_lt_mul_of_pos_left _ h8
          rw [Real.exp_lt_one_iff]; norm_num
      _ < ε / 4 := by linarith
  obtain ⟨P₁, hP₁, hsum₁⟩ := exists_prime_set_sum_gt ∅ B
  obtain ⟨P₂, hP₂, hsum₂⟩ := exists_prime_set_sum_gt P₁ B
  have hprod_lt : ∀ (P : Finset ℕ), (∀ p ∈ P, Nat.Prime p) →
      B < ∑ p ∈ P, (1 : ℝ) / (p : ℝ) →
      ∏ p ∈ P, (1 - 1 / (p : ℝ)) < ε / 4 := by
    intro P hP hsum
    calc ∏ p ∈ P, (1 - 1 / (p : ℝ))
        ≤ ∏ p ∈ P, Real.exp (-(1 / (p : ℝ))) := prod_one_sub_le_exp P hP
      _ = Real.exp (∑ p ∈ P, -(1 / (p : ℝ))) := (Real.exp_sum P _).symm
      _ = Real.exp (-(∑ p ∈ P, (1 : ℝ) / (p : ℝ))) := by rw [Finset.sum_neg_distrib]
      _ < Real.exp (-B) := Real.exp_lt_exp.mpr (by linarith)
      _ < ε / 4 := hB
  have hρ₁ : ∏ p ∈ P₁, (1 - 1 / (p : ℝ)) < ε / 4 :=
    hprod_lt P₁ (fun p hp => (hP₁ p hp).1) hsum₁
  have hρ₂ : ∏ p ∈ P₂, (1 - 1 / (p : ℝ)) < ε / 4 :=
    hprod_lt P₂ (fun p hp => (hP₂ p hp).1) hsum₂
  set M₁ : ℕ := ∏ p ∈ P₁, p
  set M₂ : ℕ := ∏ p ∈ P₂, p
  set K : ℕ := P₁.sup id
  have hM₁_pos : 0 < M₁ := Finset.prod_pos fun p hp => (hP₁ p hp).1.pos
  have hM₂_pos : 0 < M₂ := Finset.prod_pos fun p hp => (hP₂ p hp).1.pos
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt ((2 * ((M₁ + M₂ + 10 * K : ℕ) : ℝ)) / ε)
  refine ⟨N₀, fun N hN => ?_⟩
  let S : Finset ℕ := (Finset.Icc 1 N).filter (fun n =>
    10 * K ≤ n ∧ (∃ p₁ ∈ P₁, p₁ ∣ n) ∧ (∃ p₂ ∈ P₂, p₂ ∣ n))
  refine ⟨S, Finset.filter_subset _ _, ?_, ?_⟩
  · intro n hn
    rcases Finset.mem_filter.mp hn with ⟨_, h10K, ⟨p₁, hp₁, hd₁⟩, ⟨p₂, hp₂, hd₂⟩⟩
    have hne : p₁ ≠ p₂ := fun heq => (hP₂ p₂ hp₂).2.2 (heq ▸ hp₁)
    refine ⟨?_, ⟨p₁, hd₁, by have := (hP₁ p₁ hp₁).2.1; omega, ?_⟩⟩
    · rintro ⟨p, r, hp, _, hpow⟩
      have heq1 : p₁ = p := (Nat.prime_dvd_prime_iff_eq (hP₁ p₁ hp₁).1 hp).mp
        ((hP₁ p₁ hp₁).1.dvd_of_dvd_pow (hpow ▸ hd₁))
      have heq2 : p₂ = p := (Nat.prime_dvd_prime_iff_eq (hP₂ p₂ hp₂).1 hp).mp
        ((hP₂ p₂ hp₂).1.dvd_of_dvd_pow (hpow ▸ hd₂))
      exact hne (heq1.trans heq2.symm)
    · have hleK : p₁ ≤ K := Finset.le_sup (f := id) hp₁
      omega
  · let B₀ := (Finset.Icc 1 N).filter (fun n => n < 10 * K)
    let B₁ := (Finset.Icc 1 N).filter (fun n => ∀ p ∈ P₁, ¬ p ∣ n)
    let B₂ := (Finset.Icc 1 N).filter (fun n => ∀ p ∈ P₂, ¬ p ∣ n)
    have hcomp_sub : Finset.Icc 1 N \ S ⊆ B₀ ∪ B₁ ∪ B₂ := by
      intro n hn
      rw [Finset.mem_sdiff] at hn
      rcases hn with ⟨hnI, hnS⟩
      simp only [S, Finset.mem_filter, hnI, true_and, not_and_or, not_le, not_exists] at hnS
      rw [Finset.mem_union, Finset.mem_union]
      rcases hnS with hlt | hno1 | hno2
      · left; left; exact Finset.mem_filter.mpr ⟨hnI, hlt⟩
      · left; right; exact Finset.mem_filter.mpr ⟨hnI, fun p hp => (hno1 p).resolve_left (not_not.mpr hp)⟩
      · right; exact Finset.mem_filter.mpr ⟨hnI, fun p hp => (hno2 p).resolve_left (not_not.mpr hp)⟩
    have hB0_le : B₀.card ≤ 10 * K := by
      have hsub : B₀ ⊆ Finset.range (10 * K) := fun n hn =>
        Finset.mem_range.mpr (Finset.mem_filter.mp hn).2
      calc B₀.card ≤ (Finset.range (10 * K)).card := Finset.card_le_card hsub
        _ = 10 * K := Finset.card_range _
    have hB1_le : (B₁.card : ℝ) ≤ (N : ℝ) * (ε / 4) + (M₁ : ℝ) := by
      have hc := card_coprime_Icc_le P₁ (fun p hp => (hP₁ p hp).1) N
      have hcR : (B₁.card : ℝ) ≤ ((N / M₁ : ℕ) : ℝ) * (Nat.totient M₁ : ℝ) + (Nat.totient M₁ : ℝ) := by
        have : (B₁.card : ℝ) ≤ (((N / M₁ + 1) * Nat.totient M₁ : ℕ) : ℝ) := by exact_mod_cast hc
        push_cast at this; linarith
      have hdiv_le : ((N / M₁ : ℕ) : ℝ) ≤ (N : ℝ) / (M₁ : ℝ) := by
        rw [le_div_iff₀ (Nat.cast_pos.mpr hM₁_pos)]
        exact_mod_cast Nat.div_mul_le_self N M₁
      have htot_le : (Nat.totient M₁ : ℝ) ≤ (M₁ : ℝ) := by exact_mod_cast Nat.totient_le M₁
      have hmul : ((N / M₁ : ℕ) : ℝ) * (Nat.totient M₁ : ℝ) ≤ (N : ℝ) * (ε / 4) := by
        calc ((N / M₁ : ℕ) : ℝ) * (Nat.totient M₁ : ℝ)
            ≤ ((N : ℝ) / (M₁ : ℝ)) * (Nat.totient M₁ : ℝ) :=
              mul_le_mul_of_nonneg_right hdiv_le (Nat.cast_nonneg _)
          _ = (N : ℝ) * ((Nat.totient M₁ : ℝ) / (M₁ : ℝ)) := by ring
          _ = (N : ℝ) * ∏ p ∈ P₁, (1 - 1 / (p : ℝ)) := by
              rw [totient_prod_primes P₁ (fun p hp => (hP₁ p hp).1)]
          _ ≤ (N : ℝ) * (ε / 4) := mul_le_mul_of_nonneg_left (le_of_lt hρ₁) (Nat.cast_nonneg _)
      linarith
    have hB2_le : (B₂.card : ℝ) ≤ (N : ℝ) * (ε / 4) + (M₂ : ℝ) := by
      have hc := card_coprime_Icc_le P₂ (fun p hp => (hP₂ p hp).1) N
      have hcR : (B₂.card : ℝ) ≤ ((N / M₂ : ℕ) : ℝ) * (Nat.totient M₂ : ℝ) + (Nat.totient M₂ : ℝ) := by
        have : (B₂.card : ℝ) ≤ (((N / M₂ + 1) * Nat.totient M₂ : ℕ) : ℝ) := by exact_mod_cast hc
        push_cast at this; linarith
      have hdiv_le : ((N / M₂ : ℕ) : ℝ) ≤ (N : ℝ) / (M₂ : ℝ) := by
        rw [le_div_iff₀ (Nat.cast_pos.mpr hM₂_pos)]
        exact_mod_cast Nat.div_mul_le_self N M₂
      have htot_le : (Nat.totient M₂ : ℝ) ≤ (M₂ : ℝ) := by exact_mod_cast Nat.totient_le M₂
      have hmul : ((N / M₂ : ℕ) : ℝ) * (Nat.totient M₂ : ℝ) ≤ (N : ℝ) * (ε / 4) := by
        calc ((N / M₂ : ℕ) : ℝ) * (Nat.totient M₂ : ℝ)
            ≤ ((N : ℝ) / (M₂ : ℝ)) * (Nat.totient M₂ : ℝ) :=
              mul_le_mul_of_nonneg_right hdiv_le (Nat.cast_nonneg _)
          _ = (N : ℝ) * ((Nat.totient M₂ : ℝ) / (M₂ : ℝ)) := by ring
          _ = (N : ℝ) * ∏ p ∈ P₂, (1 - 1 / (p : ℝ)) := by
              rw [totient_prod_primes P₂ (fun p hp => (hP₂ p hp).1)]
          _ ≤ (N : ℝ) * (ε / 4) := mul_le_mul_of_nonneg_left (le_of_lt hρ₂) (Nat.cast_nonneg _)
      linarith
    have hIcc_card : (Finset.Icc 1 N).card = N := by simp
    have hsplit : S.card + (Finset.Icc 1 N \ S).card = N := by
      rw [add_comm, Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ _), hIcc_card]
    have hcomp_card : (Finset.Icc 1 N \ S).card ≤ B₀.card + B₁.card + B₂.card := by
      calc (Finset.Icc 1 N \ S).card
          ≤ (B₀ ∪ B₁ ∪ B₂).card := Finset.card_le_card hcomp_sub
        _ ≤ (B₀ ∪ B₁).card + B₂.card := Finset.card_union_le _ _
        _ ≤ B₀.card + B₁.card + B₂.card := by linarith [Finset.card_union_le B₀ B₁]
    have hconst_le : ((M₁ + M₂ + 10 * K : ℕ) : ℝ) ≤ (ε / 2) * (N : ℝ) := by
      have h1 : (2 * ((M₁ + M₂ + 10 * K : ℕ) : ℝ)) / ε < (N : ℝ) :=
        lt_of_lt_of_le hN₀ (by exact_mod_cast hN)
      rw [div_lt_iff₀ hε] at h1
      linarith
    have hB0R : (B₀.card : ℝ) ≤ (10 * K : ℕ) := by exact_mod_cast hB0_le
    have hcompR : ((Finset.Icc 1 N \ S).card : ℝ) ≤ (B₀.card : ℝ) + (B₁.card : ℝ) + (B₂.card : ℝ) := by
      exact_mod_cast hcomp_card
    have hsplitR : (S.card : ℝ) + ((Finset.Icc 1 N \ S).card : ℝ) = (N : ℝ) := by
      exact_mod_cast hsplit
    push_cast at hconst_le hB0R
    linarith

end Flow.Proofs
