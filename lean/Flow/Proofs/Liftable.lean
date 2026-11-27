module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Flow.Proofs.Basic
public import Flow.Defs.StepSystem
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Section 2 proofs: rounding, integer lifts, connected fibres, and liftable divisor steps

This module proves Lemma 2.2 (`lem_2_2`), Corollary 2.3 (`cor_2_3`), Lemma 2.4 (`lem_2_4`),
Lemma 2.6 (`lem_2_6`), Lemma 2.7 (`lem_2_7` with Claims 1 and 2), and Corollary 2.8
(`cor_2_8_a` and `cor_2_8_b`).
-/

namespace Flow.Proofs

open Flow Multigraph

/-- Monotonicity of `Relation.ReflTransGen` with implicit endpoints. -/
lemma reflTransGen_mono {α : Type*} {r s : α → α → Prop}
    (h : ∀ a b, r a b → s a b) {a b : α} (hr : Relation.ReflTransGen r a b) :
    Relation.ReflTransGen s a b := by
  induction hr with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hab ih => exact Relation.ReflTransGen.tail ih (h _ _ hab)

section RoundingAndLifting

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- Helper for Lemma 2.2 by induction on the number of fractional edges. -/
private lemma lem_2_2_aux (G : Multigraph V E) :
    ∀ (N : ℕ) (x : E → ℝ),
      (∀ e, 0 ≤ x e ∧ x e ≤ 1) →
      (∀ v, ∃ n : ℤ, G.boundary x v = (n : ℝ)) →
      (Finset.univ.filter (fun e => 0 < x e ∧ x e < 1)).card ≤ N →
      ∃ z : E → ℤ,
        (∀ e, z e = 0 ∨ z e = 1) ∧
        (∀ v, (G.boundary (Γ := ℤ) z v : ℝ) = G.boundary x v) ∧
        (∀ e, x e = 0 → z e = 0) ∧
        (∀ e, x e = 1 → z e = 1) := by
  intro N
  induction N with
  | zero =>
    intro x hx_range _ hcard
    have hno_frac : ∀ e, x e = 0 ∨ x e = 1 := by
      intro e
      have h0 : (Finset.univ.filter (fun e => 0 < x e ∧ x e < 1)).card = 0 :=
        Nat.eq_zero_of_le_zero hcard
      have hnot : e ∉ Finset.univ.filter (fun e => 0 < x e ∧ x e < 1) := by
        rw [Finset.card_eq_zero.mp h0]; simp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_lt] at hnot
      have ⟨hge, hle⟩ := hx_range e
      by_cases hgt : 0 < x e
      · right; linarith [hnot hgt]
      · left; linarith
    classical
    let z : E → ℤ := fun e => if x e = 1 then 1 else 0
    have hz_cast : ∀ e, (z e : ℝ) = x e := by
      intro e
      rcases hno_frac e with h0 | h1
      · simp [z, h0]
      · simp [z, h1]
    refine ⟨z, fun e => by dsimp only [z]; split_ifs <;> simp, fun v => ?_, ?_, ?_⟩
    · unfold Multigraph.boundary
      simp [hz_cast]
    · intro e he; simp [z, he]
    · intro e he; simp [z, he]
  | succ N ih =>
    intro x hx_range hx_int hcard
    classical
    let Efrac : Finset E := Finset.univ.filter (fun e => 0 < x e ∧ x e < 1)
    by_cases hne : Efrac.Nonempty
    · let Hfrac : G.Subgraph :=
        { verts := Finset.univ
          edges := Efrac
          tail_mem := fun _ => Finset.mem_univ _
          head_mem := fun _ => Finset.mem_univ _ }
      -- No vertex has degree 1 in Hfrac (else boundary at v wouldn't be an integer)
      have hdeg_ne1 : ∀ v ∈ Hfrac.verts, Hfrac.deg v ≠ 1 := by
        intro v _ hdeg1
        -- Every non-fractional edge takes integer value 0 or 1
        have hnonfrac_int : ∀ e ∉ Efrac, ∃ m : ℤ, x e = (m : ℝ) := by
          intro e he
          simp only [Efrac, Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_lt] at he
          have ⟨hge, hle⟩ := hx_range e
          by_cases hgt : 0 < x e
          · exact ⟨1, by push_cast; linarith [he hgt]⟩
          · exact ⟨0, by push_cast; linarith⟩
        -- Split `G.boundary x v` into `Efrac` and `E \ Efrac`
        have hsplit_sum : ∀ (S : Finset E),
            ∑ e ∈ S, x e = (∑ e ∈ S ∩ Efrac, x e) + (∑ e ∈ S \ Efrac, x e) := by
          intro S
          have hdisj : Disjoint (S ∩ Efrac) (S \ Efrac) :=
            Finset.disjoint_left.mpr (fun _ h1 h2 => (Finset.mem_sdiff.mp h2).2 (Finset.mem_inter.mp h1).2)
          have hunion : (S ∩ Efrac) ∪ (S \ Efrac) = S := by
            ext e; simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
            by_cases he : e ∈ Efrac <;> simp [he]
          rw [← Finset.sum_union hdisj, hunion]
        have hbd_split : G.boundary x v =
            ((∑ e ∈ Efrac.filter (fun e => G.head e = v), x e) -
             (∑ e ∈ Efrac.filter (fun e => G.tail e = v), x e)) +
            ((∑ e ∈ (Finset.univ \ Efrac).filter (fun e => G.head e = v), x e) -
             (∑ e ∈ (Finset.univ \ Efrac).filter (fun e => G.tail e = v), x e)) := by
          unfold Multigraph.boundary
          have h1 : Finset.univ.filter (fun e => G.head e = v) ∩ Efrac =
              Efrac.filter (fun e => G.head e = v) := by
            ext e; simp [and_comm]
          have h2 : Finset.univ.filter (fun e => G.head e = v) \ Efrac =
              (Finset.univ \ Efrac).filter (fun e => G.head e = v) := by
            ext e; simp [and_comm]
          have h3 : Finset.univ.filter (fun e => G.tail e = v) ∩ Efrac =
              Efrac.filter (fun e => G.tail e = v) := by
            ext e; simp [and_comm]
          have h4 : Finset.univ.filter (fun e => G.tail e = v) \ Efrac =
              (Finset.univ \ Efrac).filter (fun e => G.tail e = v) := by
            ext e; simp [and_comm]
          rw [hsplit_sum (Finset.univ.filter (fun e => G.head e = v)),
              hsplit_sum (Finset.univ.filter (fun e => G.tail e = v)), h1, h2, h3, h4]
          ring
        have hsum_int : ∀ (S : Finset E), (∀ e ∈ S, e ∉ Efrac) → ∃ m : ℤ, ∑ e ∈ S, x e = (m : ℝ) := by
          intro S hS
          refine ⟨∑ e ∈ S, if x e = 1 then 1 else 0, ?_⟩
          rw [Int.cast_sum]
          refine Finset.sum_congr rfl (fun e he => ?_)
          rcases hnonfrac_int e (hS e he) with ⟨m, hm⟩
          have ⟨hge, hle⟩ := hx_range e
          by_cases h1 : x e = 1
          · simp [h1]
          · have hm0 : m = 0 := by
              have hlt1 : (m : ℝ) < 1 := by rw [← hm]; exact lt_of_le_of_ne hle h1
              have hge0 : (0 : ℝ) ≤ (m : ℝ) := by rw [← hm]; exact hge
              have : (0 : ℤ) ≤ m := by exact_mod_cast hge0
              have : m < 1 := by exact_mod_cast hlt1
              omega
            simp [h1, hm, hm0]
        obtain ⟨mh, hmh⟩ := hsum_int ((Finset.univ \ Efrac).filter (fun e => G.head e = v))
          (fun e he => (Finset.mem_sdiff.mp (Finset.mem_filter.mp he).1).2)
        obtain ⟨mt, hmt⟩ := hsum_int ((Finset.univ \ Efrac).filter (fun e => G.tail e = v))
          (fun e he => (Finset.mem_sdiff.mp (Finset.mem_filter.mp he).1).2)
        obtain ⟨nv, hnv⟩ := hx_int v
        unfold Subgraph.deg at hdeg1
        simp only [Hfrac] at hdeg1
        have hcases : ((Efrac.filter (fun e => G.head e = v)).card = 1 ∧
            (Efrac.filter (fun e => G.tail e = v)).card = 0) ∨
            ((Efrac.filter (fun e => G.head e = v)).card = 0 ∧
            (Efrac.filter (fun e => G.tail e = v)).card = 1) := by omega
        rcases hcases with ⟨hh1, ht0⟩ | ⟨hh0, ht1⟩
        · rw [Finset.card_eq_one] at hh1; rw [Finset.card_eq_zero] at ht0
          rcases hh1 with ⟨e₀, he₀⟩
          have he₀_frac : e₀ ∈ Efrac := (Finset.mem_filter.mp (he₀ ▸ Finset.mem_singleton_self e₀)).1
          have ⟨hgt0, hlt1⟩ := (Finset.mem_filter.mp he₀_frac).2
          rw [hnv, he₀, ht0, hmh, hmt, Finset.sum_singleton, Finset.sum_empty, sub_zero] at hbd_split
          have hxe₀ : x e₀ = ((nv - (mh - mt) : ℤ) : ℝ) := by push_cast; linarith
          have h0lt : (0 : ℤ) < nv - (mh - mt) := by
            have : (0 : ℝ) < ((nv - (mh - mt) : ℤ) : ℝ) := hxe₀ ▸ hgt0
            exact Int.cast_pos.mp this
          have hlt1' : nv - (mh - mt) < (1 : ℤ) := by
            have : ((nv - (mh - mt) : ℤ) : ℝ) < (1 : ℝ) := hxe₀ ▸ hlt1
            exact Int.cast_lt.mp (by simpa using this)
          omega
        · rw [Finset.card_eq_zero] at hh0; rw [Finset.card_eq_one] at ht1
          rcases ht1 with ⟨e₀, he₀⟩
          have he₀_frac : e₀ ∈ Efrac := (Finset.mem_filter.mp (he₀ ▸ Finset.mem_singleton_self e₀)).1
          have ⟨hgt0, hlt1⟩ := (Finset.mem_filter.mp he₀_frac).2
          rw [hnv, hh0, he₀, hmh, hmt, Finset.sum_empty, Finset.sum_singleton, zero_sub] at hbd_split
          have hxe₀ : x e₀ = (((mh - mt) - nv : ℤ) : ℝ) := by push_cast; linarith
          have h0lt : (0 : ℤ) < (mh - mt) - nv := by
            have : (0 : ℝ) < (((mh - mt) - nv : ℤ) : ℝ) := hxe₀ ▸ hgt0
            exact Int.cast_pos.mp this
          have hlt1' : (mh - mt) - nv < (1 : ℤ) := by
            have : (((mh - mt) - nv : ℤ) : ℝ) < (1 : ℝ) := hxe₀ ▸ hlt1
            exact Int.cast_lt.mp (by simpa using this)
          omega
      obtain ⟨C, hCle⟩ := exists_directedCycle_of_no_deg_one Hfrac hne hdeg_ne1
      have hCne : C.sub.edges.Nonempty := by
        rcases C.isCycle.1.1 with ⟨v, hv⟩
        have hd := C.isCycle.2 v hv
        unfold Subgraph.deg at hd
        by_cases ht : 0 < (C.sub.edges.filter (fun e => G.tail e = v)).card
        · rcases Finset.card_pos.mp ht with ⟨e, he⟩; exact ⟨e, (Finset.mem_filter.mp he).1⟩
        · have hh : 0 < (C.sub.edges.filter (fun e => G.head e = v)).card := by omega
          rcases Finset.card_pos.mp hh with ⟨e, he⟩; exact ⟨e, (Finset.mem_filter.mp he).1⟩
      let dist : E → ℝ := fun e => if C.sign e = 1 then 1 - x e else x e
      let δ : ℝ := C.sub.edges.inf' hCne dist
      obtain ⟨e₀, he₀C, he₀_eq⟩ := Finset.exists_mem_eq_inf' hCne dist
      have hδ_pos : 0 < δ := by
        dsimp only [δ]
        rw [he₀_eq]
        have ⟨hgt0, hlt1⟩ := (Finset.mem_filter.mp (hCle.2 he₀C)).2
        dsimp only [dist]; split_ifs <;> linarith
      have hδ_le : ∀ e ∈ C.sub.edges, δ ≤ dist e := fun e he => Finset.inf'_le dist he
      let x' : E → ℝ := fun e => x e + δ * (C.sign e : ℝ)
      have hx'_range : ∀ e, 0 ≤ x' e ∧ x' e ≤ 1 := by
        intro e
        by_cases heC : e ∈ C.sub.edges
        · have hle := hδ_le e heC
          have ⟨hgt0, hlt1⟩ := (Finset.mem_filter.mp (hCle.2 heC)).2
          rcases C.sign_mem heC with hs | hs
          · simp only [x', dist, hs, ↓reduceIte, Int.cast_one, mul_one] at hle ⊢
            constructor <;> linarith
          · simp only [x', dist, hs, Int.cast_neg, Int.cast_one, mul_neg, mul_one] at hle ⊢
            have hne1 : (-1 : ℤ) ≠ 1 := by decide
            simp only [hne1, ↓reduceIte] at hle
            constructor <;> linarith
        · simp only [x', C.sign_zero heC, Int.cast_zero, mul_zero, add_zero]
          exact hx_range e
      have hx'_bd : ∀ v, G.boundary x' v = G.boundary x v := by
        intro v
        have hC_real : G.boundary (fun e => δ * (C.sign e : ℝ)) v = 0 := by
          unfold Multigraph.boundary
          rw [← Finset.mul_sum, ← Finset.mul_sum, ← mul_sub]
          have hZ := C.isFlow v
          unfold Multigraph.boundary at hZ
          have hcast : (∑ e ∈ Finset.univ.filter (fun e => G.head e = v), (C.sign e : ℝ)) -
              (∑ e ∈ Finset.univ.filter (fun e => G.tail e = v), (C.sign e : ℝ)) = 0 := by
            rw [← Int.cast_sum, ← Int.cast_sum, ← Int.cast_sub, hZ, Int.cast_zero]
          rw [hcast, mul_zero]
        have := boundary_add G x (fun e => δ * (C.sign e : ℝ)) v
        simpa only [x', hC_real, add_zero] using this
      have hx'_int : ∀ v, ∃ n : ℤ, G.boundary x' v = (n : ℝ) := fun v => by
        rw [hx'_bd v]; exact hx_int v
      have hx'_pres0 : ∀ e, x e = 0 → x' e = 0 := by
        intro e he0
        have henot : e ∉ C.sub.edges := fun hm => by
          have := (Finset.mem_filter.mp (hCle.2 hm)).2; linarith
        simp [x', C.sign_zero henot, he0]
      have hx'_pres1 : ∀ e, x e = 1 → x' e = 1 := by
        intro e he1
        have henot : e ∉ C.sub.edges := fun hm => by
          have := (Finset.mem_filter.mp (hCle.2 hm)).2; linarith
        simp [x', C.sign_zero henot, he1]
      have hss : Finset.univ.filter (fun e => 0 < x' e ∧ x' e < 1) ⊂ Efrac := by
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨fun e he => ?_, fun heq => ?_⟩
        · rw [Finset.mem_filter] at he
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          have ⟨hge, hle⟩ := hx_range e
          constructor
          · by_contra h0; exact absurd (hx'_pres0 e (by linarith)) (by linarith [he.2.1])
          · by_contra h1; exact absurd (hx'_pres1 e (by linarith)) (by linarith [he.2.2])
        · have he₀_in : e₀ ∈ Finset.univ.filter (fun e => 0 < x' e ∧ x' e < 1) := by
            rw [heq]; exact hCle.2 he₀C
          have ⟨hgt0, hlt1⟩ := (Finset.mem_filter.mp he₀_in).2
          rcases C.sign_mem he₀C with hs | hs
          · have h1 : x' e₀ = 1 := by
              dsimp only [x', δ]
              rw [hs, he₀_eq]
              simp only [dist, hs, ↓reduceIte, Int.cast_one, mul_one]; ring
            linarith
          · have h0 : x' e₀ = 0 := by
              have hne1 : (-1 : ℤ) ≠ 1 := by decide
              dsimp only [x', δ]
              rw [hs, he₀_eq]
              simp only [dist, hs, hne1, ↓reduceIte, Int.cast_neg, Int.cast_one, mul_neg, mul_one]; ring
            linarith
      have hcard' : (Finset.univ.filter (fun e => 0 < x' e ∧ x' e < 1)).card ≤ N := by
        have := Finset.card_lt_card hss; dsimp only [Efrac] at this; omega
      obtain ⟨z, hz01, hz_bd, hz0, hz1⟩ := ih x' hx'_range hx'_int hcard'
      exact ⟨z, hz01, fun v => by rw [hz_bd v, hx'_bd v],
        fun e he => hz0 e (hx'_pres0 e he), fun e he => hz1 e (hx'_pres1 e he)⟩
    · -- Already 0 fractional edges
      rw [Finset.not_nonempty_iff_eq_empty] at hne
      have hcard0 : (Finset.univ.filter (fun e => 0 < x e ∧ x e < 1)).card ≤ 0 := by
        have hEq : Finset.univ.filter (fun e => 0 < x e ∧ x e < 1) = Efrac := rfl
        rw [hEq, hne]; simp
      exact ih x hx_range hx_int (by omega)

/-- **Lemma 2.2 (Rounding).** -/
theorem lem_2_2
    (G : Multigraph V E) (x : E → ℝ)
    (hx_range : ∀ e, 0 ≤ x e ∧ x e ≤ 1)
    (hx_int : ∀ v, ∃ n : ℤ, G.boundary x v = (n : ℝ)) :
    ∃ z : E → ℤ,
      (∀ e, z e = 0 ∨ z e = 1) ∧
      (∀ v, (G.boundary (Γ := ℤ) z v : ℝ) = G.boundary x v) ∧
      (∀ e, x e = 0 → z e = 0) ∧
      (∀ e, x e = 1 → z e = 1) :=
  lem_2_2_aux G (Finset.univ.filter (fun e => 0 < x e ∧ x e < 1)).card x hx_range hx_int le_rfl

/-- **Corollary 2.3 (Integer lifts).** -/
theorem cor_2_3
    (G : Multigraph V E) {k : ℕ} (hk : 2 ≤ k)
    (f : E → ZMod k) (hf : G.IsFlow f) :
    ∃ F : E → ℤ,
      G.IsFlow F ∧
      (∀ e, (F e : ZMod k) = f e) ∧
      (∀ e, |F e| ≤ (k : ℤ) - 1) ∧
      (∀ e, F e = 0 ↔ f e = 0) := by
  haveI : NeZero k := ⟨by omega⟩
  have hk_pos_real : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (by omega)
  let r : E → ℕ := fun e => (f e).val
  have hr_lt : ∀ e, r e < k := fun e => ZMod.val_lt (f e)
  let x : E → ℝ := fun e => (r e : ℝ) / (k : ℝ)
  have hx_range : ∀ e, 0 ≤ x e ∧ x e ≤ 1 := by
    intro e
    refine ⟨div_nonneg (Nat.cast_nonneg _) (le_of_lt hk_pos_real), ?_⟩
    rw [div_le_one hk_pos_real]
    exact_mod_cast le_of_lt (hr_lt e)
  have hx_int : ∀ v, ∃ n : ℤ, G.boundary x v = (n : ℝ) := by
    intro v
    have hmod : ((G.boundary (fun e => (r e : ℤ)) v : ℤ) : ZMod k) = 0 := by
      unfold Multigraph.boundary
      push_cast
      have hcast : ∀ e, (r e : ZMod k) = f e := fun e => ZMod.natCast_zmod_val (f e)
      simp_rw [hcast]
      exact hf v
    obtain ⟨n, hn⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ k).mp hmod
    refine ⟨n, ?_⟩
    have hbd_eq : G.boundary x v = (G.boundary (Γ := ℤ) (fun e => (r e : ℤ)) v : ℝ) / (k : ℝ) := by
      unfold Multigraph.boundary x
      rw [Int.cast_sub, Int.cast_sum, Int.cast_sum, sub_div, Finset.sum_div, Finset.sum_div]
      simp only [Int.cast_natCast]
    rw [hbd_eq, hn]
    push_cast
    rw [mul_div_cancel_left₀ _ (ne_of_gt hk_pos_real)]
  obtain ⟨z, hz01, hz_bd, hz0, _⟩ := lem_2_2 G x hx_range hx_int
  let F : E → ℤ := fun e => (r e : ℤ) - (k : ℤ) * z e
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · intro v
    have hreal : (G.boundary (Γ := ℤ) F v : ℝ) = 0 := by
      have hF_bd : G.boundary (Γ := ℤ) F v =
          G.boundary (Γ := ℤ) (fun e => (r e : ℤ)) v - (k : ℤ) * G.boundary (Γ := ℤ) z v := by
        unfold Multigraph.boundary F
        simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
        ring
      rw [hF_bd]
      push_cast
      rw [hz_bd v]
      have hbd_eq : G.boundary x v = (G.boundary (Γ := ℤ) (fun e => (r e : ℤ)) v : ℝ) / (k : ℝ) := by
        unfold Multigraph.boundary x
        rw [Int.cast_sub, Int.cast_sum, Int.cast_sum, sub_div, Finset.sum_div, Finset.sum_div]
        simp only [Int.cast_natCast]
      rw [hbd_eq, mul_div_cancel₀ _ (ne_of_gt hk_pos_real), sub_self]
    exact_mod_cast hreal
  · intro e
    simp only [F, Int.cast_sub, Int.cast_natCast, Int.cast_mul, ZMod.natCast_self, zero_mul,
      sub_zero, r, ZMod.natCast_zmod_val]
  · intro e
    have hlt : (r e : ℤ) < (k : ℤ) := by exact_mod_cast hr_lt e
    have hge : (0 : ℤ) ≤ (r e : ℤ) := Nat.cast_nonneg _
    rcases hz01 e with h0 | h1
    · simp only [F, h0, mul_zero, sub_zero]
      rw [abs_of_nonneg (by omega)]; omega
    · simp only [F, h1, mul_one]
      have hr_pos : (1 : ℤ) ≤ (r e : ℤ) := by
        by_contra hle
        have hr0 : r e = 0 := by omega
        have hz0' : z e = 0 := hz0 e (by simp [x, hr0])
        omega
      rw [abs_of_nonpos (by omega)]; omega
  · intro e
    have hlt : (r e : ℤ) < (k : ℤ) := by exact_mod_cast hr_lt e
    have hge : (0 : ℤ) ≤ (r e : ℤ) := Nat.cast_nonneg _
    constructor
    · intro hF0
      rcases hz01 e with h0 | h1
      · simp only [F, h0, mul_zero, sub_zero] at hF0
        have hr0 : r e = 0 := by exact_mod_cast hF0
        exact (ZMod.val_eq_zero (f e)).mp hr0
      · simp only [F, h1, mul_one] at hF0
        omega
    · intro hf0
      have hr0 : r e = 0 := by simp [r, hf0]
      have hx0 : x e = 0 := by simp [x, hr0]
      have hz0' : z e = 0 := hz0 e hx0
      simp [F, hr0, hz0']

/-- **Lemma 2.4 (Connected fibres).** -/
theorem lem_2_4
    (G : Multigraph V E) {k : ℕ} (hk : 2 ≤ k)
    (f : G.NZFlow (ZMod k)) (F F' : G.IntKFlow k)
    (hF : G.IsIntLift f F) (hF' : G.IsIntLift f F') :
    Relation.ReflTransGen
      (fun A B => G.IsIntLift f A ∧ G.IsIntLift f B ∧ G.IntKFlowMove A B) F F' := by
  haveI : NeZero k := ⟨by omega⟩
  have hk_ne : (k : ℤ) ≠ 0 := by omega
  have hdvd : ∀ e, (k : ℤ) ∣ F'.val e - F.val e := by
    intro e
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hF' e, hF e, sub_self]
  let h : E → ℤ := fun e => (F'.val e - F.val e) / (k : ℤ)
  have hmul : ∀ e, F'.val e - F.val e = (k : ℤ) * h e := fun e =>
    (Int.mul_ediv_cancel' (hdvd e)).symm
  have hunit : ∀ e, h e = -1 ∨ h e = 0 ∨ h e = 1 := by
    intro e
    have h1 := F.bound e
    have h2 := F'.bound e
    have h3 := hmul e
    have hle1 : |F'.val e - F.val e| ≤ 2 * (k : ℤ) - 2 := by
      rw [abs_le] at h1 h2 ⊢; constructor <;> omega
    rw [h3, abs_mul, abs_of_pos (by omega : (0 : ℤ) < (k : ℤ))] at hle1
    have habs : |h e| ≤ 1 := by nlinarith
    rw [abs_le] at habs
    omega
  have hh_flow : G.IsFlow h := by
    intro v
    have hmul_bd : (k : ℤ) * G.boundary h v = 0 := by
      have h1 : (k : ℤ) * G.boundary h v = G.boundary (fun e => F'.val e - F.val e) v := by
        unfold Multigraph.boundary
        rw [mul_sub, Finset.mul_sum, Finset.mul_sum]
        simp_rw [← hmul]
      rw [h1, boundary_sub, F'.isFlow v, F.isFlow v, sub_self]
    exact (mul_eq_zero.mp hmul_bd).resolve_left hk_ne
  obtain ⟨cycles, hsum, _, _, _, hdisj⟩ := lem_2_1_b G h hh_flow
  have hdisj' := hdisj hunit
  -- Walk through partial sums `F_cur` along `cycles`
  have hwalk : ∀ (l : List G.DirectedCycle) (F_cur : G.IntKFlow k),
      G.IsIntLift f F_cur →
      (∀ e, F'.val e = F_cur.val e + (k : ℤ) * (l.map (fun C => C.sign e)).sum) →
      (∀ i j (hi : i < l.length) (hj : j < l.length), i ≠ j →
        Disjoint (l[i]'hi).sub.edges (l[j]'hj).sub.edges) →
      Relation.ReflTransGen
        (fun A B => G.IsIntLift f A ∧ G.IsIntLift f B ∧ G.IntKFlowMove A B) F_cur F' := by
    intro l
    induction l with
    | nil =>
      intro F_cur _ hdiff _
      have heq : F_cur = F' := by
        ext e; have := hdiff e; simp at this; exact this.symm
      subst heq; exact Relation.ReflTransGen.refl
    | cons C rest ih =>
      intro F_cur hFcur hdiff hdisj_l
      -- Every edge of `C` does not lie in any cycle of `rest`, so `F_cur + k * C.sign` equals `F'` on `C`
      have hC_disj_rest : ∀ D ∈ rest, Disjoint C.sub.edges D.sub.edges := by
        intro D hD
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hD
        exact hdisj_l 0 (j + 1) (by simp) (by simp [hj]) (by omega)
      have hrest_zero_on_C : ∀ e ∈ C.sub.edges, (rest.map (fun D => D.sign e)).sum = 0 := by
        intro e heC
        apply List.sum_eq_zero
        intro x hx
        rw [List.mem_map] at hx
        rcases hx with ⟨D, hD, rfl⟩
        have heD : e ∉ D.sub.edges := Finset.disjoint_left.mp (hC_disj_rest D hD) heC
        exact D.sign_zero heD
      let F_next : G.IntKFlow k :=
        { val := fun e => F_cur.val e + C.sign e * (k : ℤ)
          isFlow := isFlow_add F_cur.isFlow (by
            have := isFlow_zsmul C.isFlow (k : ℤ)
            simpa only [zsmul_eq_mul, Int.cast_id] using this)
          nonzero := fun e => by
            by_cases heC : e ∈ C.sub.edges
            · have h1 := hdiff e
              simp only [List.map_cons, List.sum_cons, hrest_zero_on_C e heC, add_zero] at h1
              have heq : F_cur.val e + C.sign e * (k : ℤ) = F'.val e := by linarith
              rw [heq]; exact F'.nonzero e
            · simp [C.sign_zero heC, F_cur.nonzero e]
          bound := fun e => by
            by_cases heC : e ∈ C.sub.edges
            · have h1 := hdiff e
              simp only [List.map_cons, List.sum_cons, hrest_zero_on_C e heC, add_zero] at h1
              have heq : F_cur.val e + C.sign e * (k : ℤ) = F'.val e := by linarith
              rw [heq]; exact F'.bound e
            · simp [C.sign_zero heC, F_cur.bound e] }
      have hFnext_lift : G.IsIntLift f F_next := fun e => by
        simp [F_next, hFcur e]
      have hmove : G.IntKFlowMove F_cur F_next :=
        ⟨C, (k : ℤ), hk_ne, fun e => rfl⟩
      refine Relation.ReflTransGen.head ⟨hFcur, hFnext_lift, hmove⟩ (ih F_next hFnext_lift ?_ ?_)
      · intro e
        have h1 := hdiff e
        simp only [List.map_cons, List.sum_cons] at h1
        simp only [F_next]
        linarith
      · intro i j hi hj hij
        exact hdisj_l (i + 1) (j + 1) (by simp [hi]) (by simp [hj]) (by omega)
  exact hwalk cycles F hF (fun e => by rw [← hsum e, ← hmul e]; ring) hdisj'

/-- **Lemma 2.6 (Step of size 1).** -/
theorem lem_2_6
    (G : Multigraph V E) {k : ℕ} (hk : 2 ≤ k)
    (C : G.DirectedCycle) (f f' : G.NZFlow (ZMod k))
    (hstep : ∀ e, f'.val e = f.val e + (C.sign e : ZMod k))
    (F : G.IntKFlow k) (hF : G.IsIntLift f F) :
    ∃ F' : G.IntKFlow k,
      (∀ e, F'.val e = F.val e + C.sign e) ∧ G.IsIntLift f' F' := by
  haveI : NeZero k := ⟨by omega⟩
  have hcast_nz : ∀ e, ((F.val e + C.sign e : ℤ) : ZMod k) = f'.val e := fun e => by
    push_cast; rw [hF e, hstep e]
  refine ⟨
    { val := fun e => F.val e + C.sign e
      isFlow := isFlow_add F.isFlow C.isFlow
      nonzero := fun e h0 => by
        have := hcast_nz e
        rw [h0, Int.cast_zero] at this
        exact f'.nonzero e this.symm
      bound := fun e => by
        by_cases heC : e ∈ C.sub.edges
        · have hb := F.bound e
          rw [abs_le] at hb ⊢
          rcases C.sign_mem heC with hs | hs <;> rw [hs]
          · constructor
            · omega
            · by_contra hgt
              have hval : F.val e = (k : ℤ) - 1 := by omega
              have h0 := hcast_nz e
              rw [hs, hval] at h0
              have : (((k : ℤ) - 1 + 1 : ℤ) : ZMod k) = 0 := by simp
              rw [this] at h0
              exact f'.nonzero e h0.symm
          · constructor
            · by_contra hlt
              have hval : F.val e = -((k : ℤ) - 1) := by omega
              have h0 := hcast_nz e
              rw [hs, hval] at h0
              have : ((-((k : ℤ) - 1) + -1 : ℤ) : ZMod k) = 0 := by
                have : -((k : ℤ) - 1) + -1 = -(k : ℤ) := by ring
                rw [this]; simp
              rw [this] at h0
              exact f'.nonzero e h0.symm
            · omega
        · simp [C.sign_zero heC, F.bound e] },
    ⟨fun _ => rfl, hcast_nz⟩⟩

end RoundingAndLifting

section DivisorMove

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- **Lemma 2.7, Claim 1 (Standard lift of a state).** -/
lemma lem_2_7_claim1
    (G : Multigraph V E) {m q : ℕ} (hm : 2 ≤ m) (hq : 2 ≤ q)
    (W : E → ℤ) (hW_flow : G.IsFlow W)
    (hW_range : ∀ e, 0 ≤ W e ∧ W e ≤ (q : ℤ) - 1)
    (h : G.NZFlow (ZMod (m * q)))
    (hstate : ∀ e, ZMod.castHom (dvd_mul_left q m) (ZMod q) (h.val e) = (W e : ZMod q)) :
    ∃ (L : E → ℤ) (F : G.IntKFlow (m * q)),
      G.IsFlow L ∧
      (∀ e, |L e| ≤ (m : ℤ) - 1) ∧
      (∀ e, F.val e = W e + (q : ℤ) * L e) ∧
      G.IsIntLift h F ∧
      (∀ e, W e = 0 → L e ≠ 0) := by
  haveI : NeZero q := ⟨by omega⟩
  haveI : NeZero m := ⟨by omega⟩
  haveI : NeZero (m * q) := ⟨by positivity⟩
  let hdiv : q ∣ m * q := dvd_mul_left q m
  -- For each `e`, `q ∣ (h.val e).val - W e`
  have hq_dvd : ∀ e, (q : ℤ) ∣ ((h.val e).val : ℤ) - W e := by
    intro e
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    have h1 : (((h.val e).val : ℕ) : ZMod q) = ZMod.castHom hdiv (ZMod q) (h.val e) := by
      have hval : (((h.val e).val : ℕ) : ZMod (m * q)) = h.val e := ZMod.natCast_zmod_val (h.val e)
      calc (((h.val e).val : ℕ) : ZMod q)
          = ZMod.castHom hdiv (ZMod q) (((h.val e).val : ℕ) : ZMod (m * q)) := (map_natCast _ _).symm
        _ = ZMod.castHom hdiv (ZMod q) (h.val e) := by rw [hval]
    rw [h1, hstate e, sub_self]
  let y_int : E → ℤ := fun e => (((h.val e).val : ℤ) - W e) / (q : ℤ)
  have hy_mul : ∀ e, (q : ℤ) * y_int e = ((h.val e).val : ℤ) - W e := fun e =>
    Int.mul_ediv_cancel' (hq_dvd e)
  let y : E → ZMod m := fun e => (y_int e : ZMod m)
  have hy_flow : G.IsFlow y := by
    intro v
    have hbd_int : (q : ℤ) * G.boundary y_int v =
        G.boundary (fun e => ((h.val e).val : ℤ)) v - G.boundary W v := by
      unfold Multigraph.boundary
      rw [mul_sub, Finset.mul_sum, Finset.mul_sum]
      simp_rw [hy_mul, Finset.sum_sub_distrib]
      ring
    rw [hW_flow v, sub_zero] at hbd_int
    have hdvd_mq : ((m * q : ℕ) : ℤ) ∣ G.boundary (fun e => ((h.val e).val : ℤ)) v := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      unfold Multigraph.boundary
      push_cast
      simp_rw [ZMod.natCast_zmod_val]
      exact h.isFlow v
    rw [← hbd_int] at hdvd_mq
    have hdvd_m : (m : ℤ) ∣ G.boundary y_int v := by
      rcases hdvd_mq with ⟨c, hc⟩
      refine ⟨c, ?_⟩
      have hq_ne : (q : ℤ) ≠ 0 := by omega
      push_cast at hc
      have : (q : ℤ) * G.boundary y_int v = (q : ℤ) * ((m : ℤ) * c) := by linarith
      exact mul_left_cancel₀ hq_ne this
    have h0 : ((G.boundary y_int v : ℤ) : ZMod m) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).mpr hdvd_m
    unfold Multigraph.boundary at h0 ⊢
    simpa only [Int.cast_sub, Int.cast_sum, y] using h0
  obtain ⟨L, hL_flow, hL_mod, hL_bound, hL_zero⟩ := cor_2_3 G hm y hy_flow
  -- Verify `F e = W e + q * L e`
  have hF_mod : ∀ e, ((W e + (q : ℤ) * L e : ℤ) : ZMod (m * q)) = h.val e := by
    intro e
    have hLm : (m : ℤ) ∣ L e - y_int e := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [hL_mod e, sub_self]
    rcases hLm with ⟨c, hc⟩
    have hdiff : W e + (q : ℤ) * L e - ((h.val e).val : ℤ) = ((m * q : ℕ) : ℤ) * c := by
      have h1 := hy_mul e
      push_cast
      nlinarith
    have h0 : ((W e + (q : ℤ) * L e - ((h.val e).val : ℤ) : ℤ) : ZMod (m * q)) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ (m * q)).mpr ⟨c, hdiff⟩
    push_cast at h0 ⊢
    rw [ZMod.natCast_zmod_val] at h0
    exact sub_eq_zero.mp h0
  have hF_nz : ∀ e, W e + (q : ℤ) * L e ≠ 0 := by
    intro e h0
    have := hF_mod e
    rw [h0, Int.cast_zero] at this
    exact h.nonzero e this.symm
  have hF_bound : ∀ e, |W e + (q : ℤ) * L e| ≤ ((m * q : ℕ) : ℤ) - 1 := by
    intro e
    have hW := hW_range e
    have hL := hL_bound e
    rw [abs_le] at hL ⊢
    push_cast
    constructor <;> nlinarith
  let F : G.IntKFlow (m * q) :=
    { val := fun e => W e + (q : ℤ) * L e
      isFlow := isFlow_add hW_flow (by
        have := isFlow_zsmul hL_flow (q : ℤ)
        simpa only [zsmul_eq_mul, Int.cast_id, mul_comm] using this)
      nonzero := hF_nz
      bound := hF_bound }
  refine ⟨L, F, hL_flow, hL_bound, fun _ => rfl, hF_mod, fun e hWe0 hLe0 => ?_⟩
  exact hF_nz e (by simp [hWe0, hLe0])

/-- **Lemma 2.7, Claim 2 (One step of size `q`).** -/
lemma lem_2_7_claim2
    (G : Multigraph V E) {m q : ℕ} (hm : 2 ≤ m) (hq : 2 ≤ q)
    (W : E → ℤ) (hW_flow : G.IsFlow W)
    (hW_range : ∀ e, 0 ≤ W e ∧ W e ≤ (q : ℤ) - 1)
    (O : G.DirectedCycle)
    (hO_fwd : ∀ e ∈ O.sub.edges, W e ≠ 0 → O.sign e = 1)
    (h h' : G.NZFlow (ZMod (m * q)))
    (hstate : ∀ e, ZMod.castHom (dvd_mul_left q m) (ZMod q) (h.val e) = (W e : ZMod q))
    (hstep : ∀ e, h'.val e = h.val e - O.sign e • (q : ZMod (m * q))) :
    ∃ (F F' : G.IntKFlow (m * q)),
      G.IsIntLift h F ∧ G.IsIntLift h' F' ∧ G.IntKFlowMove F F' := by
  haveI : NeZero (m * q) := ⟨by positivity⟩
  obtain ⟨L, F, _, hL_bound, hF_eq, hF_lift, _⟩ := lem_2_7_claim1 G hm hq W hW_flow hW_range h hstate
  have hcast : ∀ e, ((F.val e - O.sign e * (q : ℤ) : ℤ) : ZMod (m * q)) = h'.val e := fun e => by
    push_cast
    rw [hF_lift e, hstep e]
    simp [zsmul_eq_mul]
  let F' : G.IntKFlow (m * q) :=
    { val := fun e => F.val e - O.sign e * (q : ℤ)
      isFlow := isFlow_sub F.isFlow (by
        have := isFlow_zsmul O.isFlow (q : ℤ)
        simpa only [zsmul_eq_mul, Int.cast_id] using this)
      nonzero := fun e h0 => by
        have := hcast e
        rw [h0, Int.cast_zero] at this
        exact h'.nonzero e this.symm
      bound := fun e => by
        by_cases heO : e ∈ O.sub.edges
        · by_cases hW0 : W e = 0
          · -- On `E₀`: `F e - O.sign e * q = q * (L e - O.sign e)`
            have hL := hL_bound e
            rw [abs_le] at hL
            have hnot_dvd : ¬ ((m : ℤ) ∣ L e - O.sign e) := by
              rintro ⟨c, hc⟩
              have h0 : ((F.val e - O.sign e * (q : ℤ) : ℤ) : ZMod (m * q)) = 0 := by
                rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
                refine ⟨c, ?_⟩
                rw [hF_eq e, hW0, zero_add]
                push_cast; nlinarith
              rw [hcast e] at h0
              exact h'.nonzero e h0
            have habs_L : |L e - O.sign e| ≤ (m : ℤ) - 1 := by
              rw [abs_le]
              rcases O.sign_mem heO with hs | hs <;> rw [hs] at hnot_dvd ⊢
              · constructor
                · by_contra hlt
                  have : L e - 1 = -(m : ℤ) := by omega
                  exact hnot_dvd ⟨-1, by omega⟩
                · omega
              · constructor
                · omega
                · by_contra hgt
                  have : L e - (-1) = (m : ℤ) := by omega
                  exact hnot_dvd ⟨1, by omega⟩
            rw [hF_eq e, hW0, zero_add]
            have hfac : (q : ℤ) * L e - O.sign e * (q : ℤ) = (q : ℤ) * (L e - O.sign e) := by ring
            rw [hfac, abs_mul, abs_of_pos (by omega : (0 : ℤ) < (q : ℤ))]
            push_cast; nlinarith
          · -- Outside `E₀`: `O.sign e = 1`, `1 ≤ W e ≤ q - 1`
            have hs1 : O.sign e = 1 := hO_fwd e heO hW0
            have hW := hW_range e
            have hWge1 : 1 ≤ W e := by omega
            have hL := hL_bound e
            rw [abs_le] at hL ⊢
            rw [hF_eq e, hs1, one_mul]
            push_cast
            constructor <;> nlinarith
        · have hb := F.bound e
          simpa [O.sign_zero heO] using hb }
  refine ⟨F, F', hF_lift, hcast, O, -(q : ℤ), by omega, fun e => ?_⟩
  simp only [F']; ring

/-- Helper: transport `ReflTransGen IntKFlowMove` across reorientation. -/
private lemma reorient_intKFlowMove_iff {k : ℕ} (G : Multigraph V E) (flip : E → Bool)
    (F₁ F₂ : G.IntKFlow k) :
    let G' := G.reorient flip
    let tr : G.IntKFlow k → G'.IntKFlow k := fun F =>
      { val := Multigraph.reorientVal flip F.val
        isFlow := (reorient_isFlow_iff G flip F.val).mpr F.isFlow
        nonzero := fun e => by
          unfold Multigraph.reorientVal; cases flip e <;> simp [F.nonzero e]
        bound := fun e => by
          unfold Multigraph.reorientVal; cases flip e <;> simp [F.bound e] }
    G'.IntKFlowMove (tr F₁) (tr F₂) ↔ G.IntKFlowMove F₁ F₂ := by
  intro G' tr
  constructor
  · rintro ⟨C', lam, hlam, hdiff⟩
    let C : G.DirectedCycle := reorient_reorient G flip ▸ reorientDirectedCycle G' flip C'
    have hCsign : ∀ e, C.sign e = Multigraph.reorientVal flip C'.sign e := fun e => by
      dsimp only [C]
      have hcast : ∀ (G₁ G₂ : Multigraph V E) (heq : G₁ = G₂) (D : G₁.DirectedCycle),
          (heq ▸ D : G₂.DirectedCycle).sign e = D.sign e := by
        intro G₁ G₂ heq D; subst heq; rfl
      rw [hcast]; rfl
    refine ⟨C, lam, hlam, fun e => ?_⟩
    have hd := hdiff e
    simp only [tr, hCsign] at hd ⊢
    unfold Multigraph.reorientVal at hd ⊢
    cases hfl : flip e <;> simp [hfl] at hd ⊢ <;> linarith
  · rintro ⟨C, lam, hlam, hdiff⟩
    refine ⟨reorientDirectedCycle G flip C, lam, hlam, fun e => ?_⟩
    have hd := hdiff e
    simp only [tr, reorientDirectedCycle]
    unfold Multigraph.reorientVal
    cases hfl : flip e <;> simp [hfl, hd] <;> ring

/-- **Lemma 2.7 (Divisor move).** -/
theorem lem_2_7
    (G : Multigraph V E) {k q : ℕ} (hk : 3 ≤ k)
    (hq_pos : 1 ≤ q) (hq_lt : q < k) (hq_div : q ∣ k)
    (C : G.DirectedCycle) (f f' : G.NZFlow (ZMod k))
    (hstep : ∀ e, f'.val e = f.val e + C.sign e • (q : ZMod k)) :
    ∃ (F F' : G.IntKFlow k),
      G.IsIntLift f F ∧ G.IsIntLift f' F' ∧ Relation.ReflTransGen G.IntKFlowMove F F' := by
  haveI : NeZero k := ⟨by omega⟩
  by_cases hq1 : q = 1
  · subst hq1
    obtain ⟨F_val, hF_flow, hF_mod, hF_bound, hF_zero⟩ := cor_2_3 G (by omega) f.val f.isFlow
    let F : G.IntKFlow k :=
      { val := F_val
        isFlow := hF_flow
        nonzero := fun e h0 => f.nonzero e ((hF_zero e).mp h0)
        bound := hF_bound }
    have hstep1 : ∀ e, f'.val e = f.val e + (C.sign e : ZMod k) := fun e => by
      simpa using hstep e
    obtain ⟨F', hF'_eq, hF'_lift⟩ := lem_2_6 G (by omega) C f f' hstep1 F hF_mod
    refine ⟨F, F', hF_mod, hF'_lift, Relation.ReflTransGen.single ⟨C, 1, one_ne_zero, ?_⟩⟩
    intro e; simp [hF'_eq e]
  · -- Case `q ≥ 2`, write `k = m * q` with `m ≥ 2`
    have hq2 : 2 ≤ q := by omega
    rcases hq_div with ⟨m, hkm⟩
    have hm2 : 2 ≤ m := by nlinarith
    have hkq : k = m * q := by linarith
    subst hkq
    haveI : NeZero q := ⟨by omega⟩
    let hdiv : q ∣ m * q := dvd_mul_left q m
    let proj : ZMod (m * q) →+* ZMod q := ZMod.castHom hdiv (ZMod q)
    let w : E → ZMod q := fun e => proj (f.val e)
    have hw_flow : G.IsFlow w := by
      intro v
      have := congrArg proj (f.isFlow v)
      unfold Multigraph.boundary at this ⊢
      simpa only [map_sub, map_sum, map_zero, w] using this
    obtain ⟨W₀, hW₀_flow, hW₀_mod, hW₀_bound, hW₀_zero⟩ := cor_2_3 G hq2 w hw_flow
    -- Reorient `G` so that `W ≥ 0` everywhere
    let flip : E → Bool := fun e => decide (W₀ e < 0)
    let G₁ := G.reorient flip
    let W := Multigraph.reorientVal flip W₀
    let C₁ := reorientDirectedCycle G flip C
    let f₁ : G₁.NZFlow (ZMod (m * q)) :=
      { val := Multigraph.reorientVal flip f.val
        isFlow := (reorient_isFlow_iff G flip f.val).mpr f.isFlow
        nonzero := fun e => by
          unfold Multigraph.reorientVal; cases flip e <;> simp [f.nonzero e] }
    let f₁' : G₁.NZFlow (ZMod (m * q)) :=
      { val := Multigraph.reorientVal flip f'.val
        isFlow := (reorient_isFlow_iff G flip f'.val).mpr f'.isFlow
        nonzero := fun e => by
          unfold Multigraph.reorientVal; cases flip e <;> simp [f'.nonzero e] }
    have hW_flow : G₁.IsFlow W := (reorient_isFlow_iff G flip W₀).mpr hW₀_flow
    have hW_range : ∀ e, 0 ≤ W e ∧ W e ≤ (q : ℤ) - 1 := by
      intro e
      have hb := hW₀_bound e
      rw [abs_le] at hb
      unfold W Multigraph.reorientVal flip
      by_cases hlt : W₀ e < 0 <;> simp [hlt] <;> omega
    have hf₁_state : ∀ e, proj (f₁.val e) = (W e : ZMod q) := by
      intro e
      simp only [f₁, W]
      unfold Multigraph.reorientVal
      cases hfl : flip e
      · simp [hfl, w, hW₀_mod e]
      · simp [hfl, w, hW₀_mod e]
    have hstep₁ : ∀ e, f₁'.val e = f₁.val e + C₁.sign e • (q : ZMod (m * q)) := by
      intro e
      have hs := hstep e
      simp only [f₁, f₁', C₁, reorientDirectedCycle]
      unfold Multigraph.reorientVal
      cases hfl : flip e
      · simp [hs]
      · simp [hs, zsmul_eq_mul]; ring
    -- Decompose `D = m * W - C₁.sign` via Lemma 2.1(b)
    let D : E → ℤ := fun e => (m : ℤ) * W e - C₁.sign e
    have hD_flow : G₁.IsFlow D :=
      isFlow_sub (by
        have := isFlow_zsmul hW_flow (m : ℤ)
        simpa only [zsmul_eq_mul, Int.cast_id, mul_comm] using this) C₁.isFlow
    obtain ⟨cycles, hcyc_sum, hcyc_pos, hcyc_count, _, _⟩ := lem_2_1_b G₁ D hD_flow
    -- Outside `E₀` (`W e ≠ 0`), `D e ≥ m - 1 ≥ 1`, so every `O ∈ cycles` goes forward on `e`
    have hcyc_fwd : ∀ O ∈ cycles, ∀ e ∈ O.sub.edges, W e ≠ 0 → O.sign e = 1 := by
      intro O hO e heO hWne
      have hpos := hcyc_pos O hO e heO
      have hWge1 : 1 ≤ W e := by have := (hW_range e).1; omega
      have hC_le : C₁.sign e ≤ 1 := by
        by_cases hm : e ∈ C₁.sub.edges
        · rcases C₁.sign_mem hm with hs | hs <;> omega
        · rw [C₁.sign_zero hm]; omega
      have hDpos : 0 < D e := by dsimp only [D]; nlinarith
      rcases O.sign_mem heO with hs | hs
      · exact hs
      · rw [hs] at hpos; nlinarith
    -- On `E₀` (`W e = 0`), `D e = -C₁.sign e ∈ {-1, 0, 1}`, so at most one cycle in `cycles` meets `e`
    have hcyc_E0 : ∀ e, W e = 0 →
        ∀ (l₁ l₂ : List G₁.DirectedCycle), cycles = l₁ ++ l₂ →
        (l₁.map (fun O => O.sign e)).sum = 0 ∨ (l₁.map (fun O => O.sign e)).sum = -C₁.sign e := by
      intro e hWe0 l₁ l₂ hsplit
      have hD_eq : D e = -C₁.sign e := by simp [D, hWe0]
      have hcnt := hcyc_count e
      rw [hD_eq, abs_neg] at hcnt
      have hle1 : |C₁.sign e| ≤ 1 := by
        by_cases hm : e ∈ C₁.sub.edges
        · rcases C₁.sign_mem hm with hs | hs <;> simp [hs]
        · simp [C₁.sign_zero hm]
      have hsum_eq := hcyc_sum e
      rw [hD_eq, hsplit, List.map_append, List.sum_append] at hsum_eq
      -- In `l₁`, at most one cycle meets `e`, and if one does, its sign equals `-C₁.sign e`
      have hfilt_len : (l₁.filter (fun O => decide (e ∈ O.sub.edges))).length ≤ 1 := by
        have hlen_tot : (cycles.filter (fun O => decide (e ∈ O.sub.edges))).length ≤ 1 := by omega
        rw [hsplit, List.filter_append, List.length_append] at hlen_tot
        omega
      by_cases h0 : (l₁.filter (fun O => decide (e ∈ O.sub.edges))).length = 0
      · left
        apply List.sum_eq_zero
        intro x hx
        rw [List.mem_map] at hx
        rcases hx with ⟨O, hO, rfl⟩
        have henot : e ∉ O.sub.edges := by
          intro hm
          have hpos : 0 < (l₁.filter (fun O => decide (e ∈ O.sub.edges))).length := by
            apply List.length_pos_of_mem (a := O)
            simp [hO, hm]
          omega
        exact O.sign_zero henot
      · right
        have hlen1 : (l₁.filter (fun O => decide (e ∈ O.sub.edges))).length = 1 := by omega
        rw [List.length_eq_one_iff] at hlen1
        rcases hlen1 with ⟨O₀, hO₀_eq⟩
        have hO₀_in : O₀ ∈ l₁ := (List.mem_filter.mp (hO₀_eq ▸ List.mem_singleton_self O₀)).1
        have heO₀ : e ∈ O₀.sub.edges := by
          have := (List.mem_filter.mp (hO₀_eq ▸ List.mem_singleton_self O₀)).2
          simpa using this
        have hO₀_cyc : O₀ ∈ cycles := by rw [hsplit]; exact List.mem_append_left _ hO₀_in
        have hpos₀ := hcyc_pos O₀ hO₀_cyc e heO₀
        rw [hD_eq] at hpos₀
        have hO₀_sign : O₀.sign e = -C₁.sign e := by
          have h1 := O₀.sign_mem heO₀
          by_cases hm : e ∈ C₁.sub.edges
          · rcases h1 with h1 | h1 <;> rcases C₁.sign_mem hm with h2 | h2 <;>
              rw [h1, h2] at hpos₀ ⊢ <;> omega
          · rw [C₁.sign_zero hm] at hpos₀; simp at hpos₀
        -- Show `(l₁.map (·.sign e)).sum = O₀.sign e`
        have hsum_l1 : (l₁.map (fun O => O.sign e)).sum =
            ((l₁.filter (fun O => decide (e ∈ O.sub.edges))).map (fun O => O.sign e)).sum := by
          clear hO₀_eq hO₀_in hO₀_cyc hpos₀ hO₀_sign hfilt_len h0 hsplit hsum_eq
          induction l₁ with
          | nil => simp
          | cons A t ih =>
            by_cases heA : e ∈ A.sub.edges
            · simp [heA, ih]
            · simp [heA, A.sign_zero heA, ih]
        rw [hsum_l1, hO₀_eq, List.map_singleton, List.sum_singleton, hO₀_sign]
    -- Walk along prefixes of `cycles`: from `h_cur` (after prefix `l₁`) to `f₁'`
    have hchain : ∀ (l₂ l₁ : List G₁.DirectedCycle),
        cycles = l₁ ++ l₂ →
        ∀ (h_cur : G₁.NZFlow (ZMod (m * q))),
        (∀ e, h_cur.val e = f₁.val e - (l₁.map (fun O => O.sign e)).sum • (q : ZMod (m * q))) →
        ∃ (F₁ F₁' : G₁.IntKFlow (m * q)),
          G₁.IsIntLift h_cur F₁ ∧ G₁.IsIntLift f₁' F₁' ∧
          Relation.ReflTransGen G₁.IntKFlowMove F₁ F₁' := by
      intro l₂
      induction l₂ with
      | nil =>
        intro l₁ hsplit h_cur hcur_eq
        have heq_f' : h_cur = f₁' := by
          ext e
          rw [hcur_eq e, hstep₁ e]
          have hsum_e := hcyc_sum e
          rw [hsplit, List.append_nil] at hsum_e
          rw [← hsum_e]
          simp only [D, sub_smul, zsmul_eq_mul, Int.cast_mul, Int.cast_natCast]
          have hmq0 : ((m : ZMod (m * q)) * (q : ZMod (m * q))) = 0 := by
            rw [← Nat.cast_mul, ZMod.natCast_self]
          have : ((m : ZMod (m * q)) * (W e : ZMod (m * q))) * (q : ZMod (m * q)) = 0 := by
            calc ((m : ZMod (m * q)) * (W e : ZMod (m * q))) * (q : ZMod (m * q))
                = ((m : ZMod (m * q)) * (q : ZMod (m * q))) * (W e : ZMod (m * q)) := by ring
              _ = 0 * (W e : ZMod (m * q)) := by rw [hmq0]
              _ = 0 := zero_mul _
          rw [this, zero_sub, sub_neg_eq_add]
        subst heq_f'
        obtain ⟨F_val, hF_flow, hF_mod, hF_bound, hF_zero⟩ :=
          cor_2_3 G₁ (by nlinarith : 2 ≤ m * q) f₁'.val f₁'.isFlow
        let F₁ : G₁.IntKFlow (m * q) :=
          { val := F_val
            isFlow := hF_flow
            nonzero := fun e h0 => f₁'.nonzero e ((hF_zero e).mp h0)
            bound := hF_bound }
        exact ⟨F₁, F₁, hF_mod, hF_mod, Relation.ReflTransGen.refl⟩
      | cons O rest ih =>
        intro l₁ hsplit h_cur hcur_eq
        have hO_cyc : O ∈ cycles := by rw [hsplit]; simp
        have hcur_state : ∀ e, proj (h_cur.val e) = (W e : ZMod q) := by
          intro e
          rw [hcur_eq e, map_sub, hf₁_state e]
          have hq0 : proj (q : ZMod (m * q)) = 0 := by
            simp [proj]
          rw [map_zsmul, hq0, smul_zero, sub_zero]
        let h_next_val : E → ZMod (m * q) := fun e =>
          h_cur.val e - O.sign e • (q : ZMod (m * q))
        have hnext_eq : ∀ e, h_next_val e =
            f₁.val e - ((l₁ ++ [O]).map (fun O' => O'.sign e)).sum • (q : ZMod (m * q)) := by
          intro e
          simp only [h_next_val, hcur_eq e, List.map_append, List.map_singleton, List.sum_append,
            List.sum_singleton, add_smul]
          abel
        have hnext_nz : IsNowhereZero h_next_val := by
          intro e h0
          by_cases hW0 : W e = 0
          · have hcases := hcyc_E0 e hW0 (l₁ ++ [O]) rest (by rw [hsplit]; simp)
            rw [hnext_eq e] at h0
            rcases hcases with hs0 | hsc
            · rw [hs0, zero_zsmul, sub_zero] at h0
              exact f₁.nonzero e h0
            · rw [hsc, neg_smul, sub_neg_eq_add, ← hstep₁ e] at h0
              exact f₁'.nonzero e h0
          · have hproj := congrArg proj h0
            rw [map_zero] at hproj
            have hq0 : proj (q : ZMod (m * q)) = 0 := by simp [proj]
            simp only [h_next_val, map_sub, map_zsmul, hq0, smul_zero, sub_zero,
              hcur_state e] at hproj
            have hdvd_W : (q : ℤ) ∣ W e := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp hproj
            have hWr := hW_range e
            rcases hdvd_W with ⟨c, hc⟩
            have hc0 : c = 0 := by nlinarith
            exact hW0 (by rw [hc, hc0, mul_zero])
        let h_next : G₁.NZFlow (ZMod (m * q)) :=
          { val := h_next_val
            isFlow := isFlow_sub h_cur.isFlow (isFlow_zsmul O.isFlow (q : ZMod (m * q)))
            nonzero := hnext_nz }
        obtain ⟨Fa, Fb, hFa_lift, hFb_lift, hmove_ab⟩ :=
          lem_2_7_claim2 G₁ hm2 hq2 W hW_flow hW_range O (hcyc_fwd O hO_cyc)
            h_cur h_next hcur_state (fun _ => rfl)
        obtain ⟨Fc, Fd, hFc_lift, hFd_lift, hwalk_cd⟩ :=
          ih (l₁ ++ [O]) (by rw [hsplit]; simp) h_next hnext_eq
        -- Connect `Fb` to `Fc` inside the fibre of `h_next` using Lemma 2.4!
        have hfibre := lem_2_4 G₁ (by nlinarith) h_next Fb Fc hFb_lift hFc_lift
        have hwalk_bc : Relation.ReflTransGen G₁.IntKFlowMove Fb Fc :=
          reflTransGen_mono (fun _ _ h => h.2.2) hfibre
        exact ⟨Fa, Fd, hFa_lift, hFd_lift,
          Relation.ReflTransGen.head hmove_ab (Relation.ReflTransGen.trans hwalk_bc hwalk_cd)⟩
    obtain ⟨F₁, F₁', hF₁_lift, hF₁'_lift, hwalk₁⟩ :=
      hchain cycles [] rfl f₁ (fun e => by simp)
    -- Transport `F₁`, `F₁'`, and `hwalk₁` back to `G` across `flip`
    let trBack : G₁.IntKFlow (m * q) → G.IntKFlow (m * q) := fun F =>
      { val := Multigraph.reorientVal flip F.val
        isFlow := by
          rw [← reorient_isFlow_iff G flip]
          have heq : Multigraph.reorientVal flip (Multigraph.reorientVal flip F.val) = F.val :=
            funext (reorientVal_reorientVal flip F.val)
          rw [heq]; exact F.isFlow
        nonzero := fun e => by
          unfold Multigraph.reorientVal; cases flip e <;> simp [F.nonzero e]
        bound := fun e => by
          have hb := F.bound e
          unfold Multigraph.reorientVal
          cases flip e <;> simpa using hb }
    have hlift_back : ∀ (g : G.NZFlow (ZMod (m * q))) (g₁ : G₁.NZFlow (ZMod (m * q)))
        (F : G₁.IntKFlow (m * q)),
        (∀ e, g₁.val e = Multigraph.reorientVal flip g.val e) →
        G₁.IsIntLift g₁ F → G.IsIntLift g (trBack F) := by
      intro g g₁ F hg hFl e
      have h1 := hFl e
      rw [hg e] at h1
      simp only [trBack]
      unfold Multigraph.reorientVal at h1 ⊢
      cases hfl : flip e
      · simpa [hfl] using h1
      · simp only [hfl, ↓reduceIte, Int.cast_neg] at h1 ⊢
        rw [h1, neg_neg]
    have hwalk_back : ∀ A B : G₁.IntKFlow (m * q),
        Relation.ReflTransGen G₁.IntKFlowMove A B →
        Relation.ReflTransGen G.IntKFlowMove (trBack A) (trBack B) := by
      intro A B hw
      induction hw with
      | refl => exact Relation.ReflTransGen.refl
      | @tail B' C' _ hstep' ih =>
        refine Relation.ReflTransGen.tail ih ?_
        have hiff := reorient_intKFlowMove_iff G flip (trBack B') (trBack C')
        dsimp only at hiff
        rw [← hiff]
        convert hstep' using 1 <;> (ext e; simp [trBack])
    exact ⟨trBack F₁, trBack F₁',
      hlift_back f f₁ F₁ (fun _ => rfl) hF₁_lift,
      hlift_back f' f₁' F₁' (fun _ => rfl) hF₁'_lift,
      hwalk_back F₁ F₁' hwalk₁⟩

/-- **Corollary 2.8(a) (Liftable divisor steps).** -/
theorem cor_2_8_a
    {k q : ℕ} (hk : 3 ≤ k) (hq_pos : 1 ≤ q) (hq_lt : q < k) (hq_div : q ∣ k) :
    Multigraph.IsLiftable k (q : ZMod k) ∧ Multigraph.IsLiftable k (-(q : ZMod k)) := by
  haveI : NeZero k := ⟨by omega⟩
  have hq_nz : (q : ZMod k) ≠ 0 := by
    intro h0
    have hdvd : k ∣ q := (ZMod.natCast_eq_zero_iff q k).mp h0
    have hle : k ≤ q := Nat.le_of_dvd (by omega) hdvd
    omega
  constructor
  · refine ⟨hq_nz, fun V E _ _ _ _ G _ f f' C hstep F F' hF hF' => ?_⟩
    obtain ⟨F₀, F₀', hF₀, hF₀', hwalk⟩ := lem_2_7 G hk hq_pos hq_lt hq_div C f f' hstep
    have h1 := reflTransGen_mono (fun _ _ h => h.2.2) (lem_2_4 G (by omega) f F F₀ hF hF₀)
    have h2 := reflTransGen_mono (fun _ _ h => h.2.2) (lem_2_4 G (by omega) f' F₀' F' hF₀' hF')
    exact Relation.ReflTransGen.trans (Relation.ReflTransGen.trans h1 hwalk) h2
  · refine ⟨neg_ne_zero.mpr hq_nz, fun V E _ _ _ _ G _ f f' C hstep F F' hF hF' => ?_⟩
    have hstep_rev : ∀ e, f'.val e = f.val e + C.reverse.sign e • (q : ZMod k) := fun e => by
      simp [DirectedCycle.reverse, hstep e]
    obtain ⟨F₀, F₀', hF₀, hF₀', hwalk⟩ := lem_2_7 G hk hq_pos hq_lt hq_div C.reverse f f' hstep_rev
    have h1 := reflTransGen_mono (fun _ _ h => h.2.2) (lem_2_4 G (by omega) f F F₀ hF hF₀)
    have h2 := reflTransGen_mono (fun _ _ h => h.2.2) (lem_2_4 G (by omega) f' F₀' F' hF₀' hF')
    exact Relation.ReflTransGen.trans (Relation.ReflTransGen.trans h1 hwalk) h2

/-- **Corollary 2.8(b) (Liftable step systems connect `I_k(G)`).** -/
theorem cor_2_8_b
    (G : Multigraph V E) (hll : G.IsLoopless)
    {k : ℕ} (hk : 3 ≤ k) (Sig : StepSystem (ZMod k))
    (hlift : ∀ z ∈ Sig.carrier, Multigraph.IsLiftable k z)
    (hjoin : ∀ f g : G.NZFlow (ZMod k), G.SigmaJoined Sig.carrier f g) :
    G.IntFlowConnected k := by
  haveI : NeZero k := ⟨by omega⟩
  intro F F'
  let redFlow : G.IntKFlow k → G.NZFlow (ZMod k) := fun X =>
    { val := fun e => (X.val e : ZMod k)
      isFlow := fun v => by
        have h0 := congrArg (fun n : ℤ => (n : ZMod k)) (X.isFlow v)
        unfold Multigraph.boundary at h0 ⊢
        simpa only [Int.cast_sub, Int.cast_sum, Int.cast_zero] using h0
      nonzero := fun e h0 => by
        have hdvd : (k : ℤ) ∣ X.val e := (ZMod.intCast_zmod_eq_zero_iff_dvd _ k).mp h0
        have hb := X.bound e
        have hnz := X.nonzero e
        rcases hdvd with ⟨c, hc⟩
        rw [hc, abs_mul, abs_of_pos (by omega : (0 : ℤ) < (k : ℤ))] at hb
        have hc0 : c = 0 := by
          have habs_nn : 0 ≤ |c| := abs_nonneg c
          have : |c| = 0 := by nlinarith
          exact abs_eq_zero.mp this
        exact hnz (by rw [hc, hc0, mul_zero]) }
  have hwalk_mod := hjoin (redFlow F) (redFlow F')
  have hlift_chain : ∀ (f g : G.NZFlow (ZMod k)),
      G.SigmaJoined Sig.carrier f g →
      ∀ (X Y : G.IntKFlow k), G.IsIntLift f X → G.IsIntLift g Y →
        Relation.ReflTransGen G.IntKFlowMove X Y := by
    intro f g hfg
    induction hfg with
    | refl =>
      intro X Y hX hY
      exact reflTransGen_mono (fun _ _ h => h.2.2) (lem_2_4 G (by omega) f X Y hX hY)
    | @tail f₁ f₂ _ hstep ih =>
      intro X Y hX hY
      obtain ⟨F₁_val, hF₁_flow, hF₁_mod, hF₁_bound, hF₁_zero⟩ :=
        cor_2_3 G (by omega) f₁.val f₁.isFlow
      let F₁ : G.IntKFlow k :=
        { val := F₁_val
          isFlow := hF₁_flow
          nonzero := fun e h0 => f₁.nonzero e ((hF₁_zero e).mp h0)
          bound := hF₁_bound }
      have h1 := ih X F₁ hX hF₁_mod
      rcases hstep with ⟨C, lam, hlam, hdiff⟩
      have h2 := (hlift lam hlam).2 V E G hll f₁ f₂ C hdiff F₁ Y hF₁_mod hY
      exact Relation.ReflTransGen.trans h1 h2
  exact hlift_chain (redFlow F) (redFlow F') hwalk_mod F F' (fun _ => rfl) (fun _ => rfl)

end DivisorMove

end Flow.Proofs
