module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Flow.Defs.Literature
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
# Section 6: Lemmas 6.1, 6.2, Remark 6.3, and Section 4 integer consequence
-/

namespace Flow.Proofs

open Flow

/-! ### Lemma 6.1: At most two non-steps in `ℤ_a` -/

private lemma walkIn_symm {α : Type} [AddCommGroup α] {S Step : Set α}
    (hsym : ∀ s ∈ Step, -s ∈ Step) {x y : α} (h : WalkIn S Step x y) :
    WalkIn S Step y x := by
  rcases h with ⟨hx, hy, hwalk⟩
  refine ⟨hy, hx, ?_⟩
  induction hwalk with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
    rcases hstep with ⟨hu, hv, s, hs, rfl⟩
    exact Relation.ReflTransGen.head ⟨hv, hu, -s, hsym s hs, by abel⟩ (ih hu)

private lemma walkIn_trans {α : Type} [Add α] {S Step : Set α} {x y z : α}
    (h1 : WalkIn S Step x y) (h2 : WalkIn S Step y z) :
    WalkIn S Step x z :=
  ⟨h1.1, h2.2.1, h1.2.2.trans h2.2.2⟩

private lemma walkIn_step {α : Type} [Add α] {S Step : Set α} {x y s : α}
    (hx : x ∈ S) (hy : y ∈ S) (hs : s ∈ Step) (heq : y = x + s) :
    WalkIn S Step x y :=
  ⟨hx, hy, Relation.ReflTransGen.single ⟨hx, hy, s, hs, heq⟩⟩

private lemma zmod10_selfinv : ∀ d : ZMod 10, d ≠ 0 → -d = d → d = 5 := by decide

private lemma zmod10_mul4 : ∀ d : ZMod 10, (4 : ZMod 10) * d = 0 → d = -d := by decide

theorem lem_6_1_proved
    {a : ℕ} (ha : 10 ≤ a)
    (D : Finset (ZMod a))
    (hzero : (0 : ZMod a) ∉ D)
    (hsym : ∀ x ∈ D, -x ∈ D)
    (hcard : a - 3 ≤ D.card)
    (X : Finset (ZMod a)) (hX : X.card ≤ 6)
    (x y : ZMod a) (hx : x ∉ X) (hy : y ∉ X) :
    WalkIn {u : ZMod a | u ∉ X} (D : Set (ZMod a)) x y := by
  classical
  have : NeZero a := ⟨by omega⟩
  set S : Finset (ZMod a) := Finset.univ \ X
  set Dc : Finset (ZMod a) := (Finset.univ.erase 0) \ D
  have hcard_univ : (Finset.univ : Finset (ZMod a)).card = a := ZMod.card a
  have hD_sub : D ⊆ Finset.univ.erase 0 := by
    intro d hd
    exact Finset.mem_erase.mpr ⟨fun h0 => hzero (h0 ▸ hd), Finset.mem_univ d⟩
  have hDc_card : Dc.card ≤ 2 := by
    have h1 : (Finset.univ.erase (0 : ZMod a)).card = a - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), hcard_univ]
    have h2 : Dc.card = (Finset.univ.erase (0 : ZMod a)).card - D.card := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hD_sub]
    omega
  have hDc_sym : ∀ d ∈ Dc, -d ∈ Dc := by
    intro d hd
    rw [Finset.mem_sdiff, Finset.mem_erase] at hd ⊢
    refine ⟨⟨by intro h0; exact hd.1.1 (neg_eq_zero.mp h0), Finset.mem_univ _⟩, ?_⟩
    intro hmem
    have := hsym (-d) hmem
    rw [neg_neg] at this
    exact hd.2 this
  set U : Finset (ZMod a) := S.filter (fun u => WalkIn {w : ZMod a | w ∉ X} (D : Set (ZMod a)) x u)
  set V : Finset (ZMod a) := S \ U
  by_contra hnot
  have hxS : x ∈ S := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hx⟩
  have hyS : y ∈ S := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hy⟩
  have hxU : x ∈ U := Finset.mem_filter.mpr ⟨hxS, ⟨hx, hx, Relation.ReflTransGen.refl⟩⟩
  have hyV : y ∈ V := by
    refine Finset.mem_sdiff.mpr ⟨hyS, ?_⟩
    intro hyU
    exact hnot (Finset.mem_filter.mp hyU).2
  have hdiff_in_Dc : ∀ u ∈ U, ∀ v ∈ V, v - u ∈ Dc := by
    intro u hu v hv
    have huS := (Finset.mem_filter.mp hu).1
    have huW := (Finset.mem_filter.mp hu).2
    have hvS := (Finset.mem_sdiff.mp hv).1
    have hv_notU := (Finset.mem_sdiff.mp hv).2
    have huv_ne : v ≠ u := fun h => hv_notU (h ▸ hu)
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨sub_ne_zero.mpr huv_ne, Finset.mem_univ _⟩, ?_⟩
    intro hD
    have hvX : v ∉ X := (Finset.mem_sdiff.mp hvS).2
    have huX : u ∉ X := (Finset.mem_sdiff.mp huS).2
    have hstep : WalkIn {w : ZMod a | w ∉ X} (D : Set (ZMod a)) u v :=
      walkIn_step huX hvX hD (by abel)
    exact hv_notU (Finset.mem_filter.mpr ⟨hvS, walkIn_trans huW hstep⟩)
  have hV_le : V.card ≤ Dc.card := by
    have hsub : V.image (fun v => v - x) ⊆ Dc := by
      intro d hd
      rcases Finset.mem_image.mp hd with ⟨v, hv, rfl⟩
      exact hdiff_in_Dc x hxU v hv
    have hinj : (V.image (fun v => v - x)).card = V.card :=
      Finset.card_image_of_injective _ (fun v₁ v₂ h => sub_left_inj.mp h)
    rw [← hinj]
    exact Finset.card_le_card hsub
  have hU_le : U.card ≤ Dc.card := by
    have hsub : U.image (fun u => y - u) ⊆ Dc := by
      intro d hd
      rcases Finset.mem_image.mp hd with ⟨u, hu, rfl⟩
      exact hdiff_in_Dc u hu y hyV
    have hinj : (U.image (fun u => y - u)).card = U.card :=
      Finset.card_image_of_injective _ (fun u₁ u₂ h => sub_right_inj.mp h)
    rw [← hinj]
    exact Finset.card_le_card hsub
  have hU_sub_S : U ⊆ S := Finset.filter_subset _ _
  have hS_card : U.card + V.card = S.card := by
    have h := Finset.card_sdiff_add_card_eq_card hU_sub_S
    change V.card + U.card = S.card at h
    omega
  have hS_ge : a - 6 ≤ S.card := by
    have h : S.card = (Finset.univ : Finset (ZMod a)).card - X.card := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ _)]
    rw [hcard_univ] at h
    omega
  have ha10 : a = 10 := by omega
  subst ha10
  have hU2 : U.card = 2 := by omega
  have hV2 : V.card = 2 := by omega
  have hDc2 : Dc.card = 2 := by omega
  obtain ⟨u₁, u₂, hu12, hU_eq⟩ := Finset.card_eq_two.mp hU2
  obtain ⟨d₁, d₂, hd12, hDc_eq⟩ := Finset.card_eq_two.mp hDc2
  have hd1_mem : d₁ ∈ Dc := hDc_eq ▸ Finset.mem_insert_self d₁ {d₂}
  have hd2_mem : d₂ ∈ Dc := hDc_eq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self d₂)
  have hd1_ne0 : d₁ ≠ 0 := (Finset.mem_erase.mp (Finset.mem_sdiff.mp hd1_mem).1).1
  have hd2_ne0 : d₂ ≠ 0 := (Finset.mem_erase.mp (Finset.mem_sdiff.mp hd2_mem).1).1
  have hd2_eq_neg : d₂ = -d₁ := by
    have hneg1 : -d₁ ∈ Dc := hDc_sym d₁ hd1_mem
    rw [hDc_eq, Finset.mem_insert, Finset.mem_singleton] at hneg1
    rcases hneg1 with h1 | h2
    · have h51 : d₁ = 5 := zmod10_selfinv d₁ hd1_ne0 h1
      have hneg2 : -d₂ ∈ Dc := hDc_sym d₂ hd2_mem
      rw [hDc_eq, Finset.mem_insert, Finset.mem_singleton] at hneg2
      rcases hneg2 with h21 | h22
      · exfalso; apply hd12
        calc d₁ = -d₁ := h1.symm
          _ = -(-d₂) := by rw [← h21]
          _ = d₂ := neg_neg d₂
      · exfalso; exact hd12 (h51.trans (zmod10_selfinv d₂ hd2_ne0 h22).symm)
    · exact h2.symm
  have hd1_ne_neg : d₁ ≠ -d₁ := hd2_eq_neg ▸ hd12
  have hV_eq : ∀ u ∈ U, V = {u + d₁, u + (-d₁)} := by
    intro u hu
    have hsub : V ⊆ {u + d₁, u + (-d₁)} := by
      intro v hv
      have hd : v - u ∈ Dc := hdiff_in_Dc u hu v hv
      rw [hDc_eq, hd2_eq_neg, Finset.mem_insert, Finset.mem_singleton] at hd
      rw [Finset.mem_insert, Finset.mem_singleton]
      rcases hd with h | h
      · left; exact eq_add_of_sub_eq' h
      · right; exact eq_add_of_sub_eq' h
    have hcard_pair : ({u + d₁, u + (-d₁)} : Finset (ZMod 10)).card = 2 := by
      rw [Finset.card_pair]
      intro heq
      exact hd1_ne_neg (add_left_cancel heq)
    exact Finset.eq_of_subset_of_card_le hsub (by rw [hV2, hcard_pair])
  have hV1 := hV_eq u₁ (hU_eq ▸ Finset.mem_insert_self u₁ {u₂})
  have hV2' := hV_eq u₂ (hU_eq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self u₂))
  have hmem1 : u₂ + d₁ ∈ ({u₁ + d₁, u₁ + (-d₁)} : Finset (ZMod 10)) := by
    rw [← hV1, hV2']; exact Finset.mem_insert_self _ _
  have hmem2 : u₂ + (-d₁) ∈ ({u₁ + d₁, u₁ + (-d₁)} : Finset (ZMod 10)) := by
    rw [← hV1, hV2']; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  rw [Finset.mem_insert, Finset.mem_singleton] at hmem1 hmem2
  have heq1 : u₂ + d₁ = u₁ + (-d₁) := by
    rcases hmem1 with h | h
    · exact absurd (add_right_cancel h).symm hu12
    · exact h
  have heq2 : u₂ + (-d₁) = u₁ + d₁ := by
    rcases hmem2 with h | h
    · exact h
    · exact absurd (add_right_cancel h).symm hu12
  have h4 : (4 : ZMod 10) * d₁ = 0 := by
    have hsub : (u₂ + d₁) - (u₂ + (-d₁)) = (u₁ + (-d₁)) - (u₁ + d₁) := by rw [heq1, heq2]
    linear_combination hsub
  exact hd1_ne_neg (zmod10_mul4 d₁ h4)

/-! ### Lemma 6.2: `ℤ_b` minus two elements -/

private lemma walk_arc_up {b : ℕ} [NeZero b] {X : Finset (ZMod b)} {Step : Set (ZMod b)}
    (h1 : (1 : ZMod b) ∈ Step) :
    ∀ (m k : ℕ), (∀ j, m ≤ j → j ≤ m + k → (j : ZMod b) ∉ X) →
      WalkIn {u : ZMod b | u ∉ X} Step (m : ZMod b) ((m + k : ℕ) : ZMod b) := by
  intro m k
  induction k with
  | zero =>
    intro h
    have hm : (m : ZMod b) ∉ X := h m le_rfl (by omega)
    exact ⟨hm, by simpa using hm, by simpa using Relation.ReflTransGen.refl⟩
  | succ k ih =>
    intro h
    have hprev := ih (fun j h1' h2' => h j h1' (by omega))
    have hcur : ((m + k : ℕ) : ZMod b) ∉ X := h (m + k) (by omega) (by omega)
    have hnext : ((m + (k + 1) : ℕ) : ZMod b) ∉ X := h (m + (k + 1)) (by omega) le_rfl
    refine walkIn_trans hprev (walkIn_step hcur hnext h1 ?_)
    push_cast; ring

private lemma walk_arc_interval {b : ℕ} [NeZero b] {X : Finset (ZMod b)} {Step : Set (ZMod b)}
    (h1 : (1 : ZMod b) ∈ Step)
    (hsym : ∀ s ∈ Step, -s ∈ Step)
    {lo hi i j : ℕ} (hlo : lo ≤ i) (hi_le : i ≤ hi) (hlo' : lo ≤ j) (hj_le : j ≤ hi)
    (havoid : ∀ t, lo ≤ t → t ≤ hi → (t : ZMod b) ∉ X) :
    WalkIn {u : ZMod b | u ∉ X} Step (i : ZMod b) (j : ZMod b) := by
  by_cases hij : i ≤ j
  · have h := walk_arc_up (X := X) (Step := Step) h1 i (j - i)
      (fun t ht1 ht2 => havoid t (by omega) (by omega))
    simpa [Nat.add_sub_of_le hij] using h
  · have h := walk_arc_up (X := X) (Step := Step) h1 j (i - j)
      (fun t ht1 ht2 => havoid t (by omega) (by omega))
    have h' : WalkIn {u : ZMod b | u ∉ X} Step (j : ZMod b) (i : ZMod b) := by
      simpa [Nat.add_sub_of_le (le_of_not_ge hij)] using h
    exact walkIn_symm hsym h'

private lemma walkIn_translate {α : Type} [AddCommGroup α] [DecidableEq α]
    {X : Finset α} {Step : Set α} (c : α) {x y : α}
    (h : WalkIn {u : α | u ∉ X.image (fun z => z - c)} Step (x - c) (y - c)) :
    WalkIn {u : α | u ∉ X} Step x y := by
  rcases h with ⟨hx, hy, hw⟩
  have hmem : ∀ z : α, z - c ∉ X.image (fun w => w - c) ↔ z ∉ X := by
    intro z
    simp
  refine ⟨(hmem x).mp hx, (hmem y).mp hy, ?_⟩
  have hgen : ∀ u v : α,
      Relation.ReflTransGen
        (fun a b => a ∉ X.image (fun w => w - c) ∧ b ∉ X.image (fun w => w - c) ∧
          ∃ s ∈ Step, b = a + s) u v →
      Relation.ReflTransGen (fun a b => a ∉ X ∧ b ∉ X ∧ ∃ s ∈ Step, b = a + s) (u + c) (v + c) := by
    intro u v hrel
    induction hrel with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hstep ih =>
      rcases hstep with ⟨hu, hv, s, hs, rfl⟩
      refine ih.tail ⟨?_, ?_, s, hs, by abel⟩
      · exact (hmem _).mp (by simpa using hu)
      · exact (hmem _).mp (by simpa using hv)
  simpa using hgen (x - c) (y - c) hw

theorem lem_6_2_proved
    {b d : ℕ} (hb : 4 ≤ b) (hd_gt : 1 < d) (hd_lt : d < b) (hd_div : d ∣ b)
    (X : Finset (ZMod b)) (hX : X.card ≤ 2)
    (x y : ZMod b) (hx : x ∉ X) (hy : y ∉ X) :
    WalkIn {u : ZMod b | u ∉ X} ({(1 : ZMod b), -1, (d : ZMod b), -(d : ZMod b)}) x y := by
  classical
  have : NeZero b := ⟨by omega⟩
  set Step : Set (ZMod b) := {(1 : ZMod b), -1, (d : ZMod b), -(d : ZMod b)}
  have h1 : (1 : ZMod b) ∈ Step := by simp [Step]
  have hd_mem : (d : ZMod b) ∈ Step := by simp [Step]
  have hsym : ∀ s ∈ Step, -s ∈ Step := by
    intro s hs
    simp only [Step, Set.mem_insert_iff, Set.mem_singleton_iff] at hs ⊢
    rcases hs with rfl | rfl | rfl | rfl <;> simp
  by_cases hX1 : X.card ≤ 1
  · have hanchor : ∃ c : ZMod b, ∀ z ∈ X, z = c := by
      have h := Finset.card_le_one.mp hX1
      by_cases hne : X.Nonempty
      · obtain ⟨c, hc⟩ := hne
        exact ⟨c, fun z hz => h z hz c hc⟩
      · exact ⟨0, fun z hz => absurd ⟨z, hz⟩ hne⟩
    obtain ⟨c, hc⟩ := hanchor
    apply walkIn_translate c
    set X' := X.image (fun z => z - c)
    have hX'_sub : ∀ z ∈ X', z = 0 := by
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨w, hw, rfl⟩
      rw [hc w hw, sub_self]
    have hx' : x - c ∉ X' := by
      intro h; rcases Finset.mem_image.mp h with ⟨w, hw, heq⟩
      exact hx (by have := sub_left_inj.mp heq; rwa [← this])
    have hy' : y - c ∉ X' := by
      intro h; rcases Finset.mem_image.mp h with ⟨w, hw, heq⟩
      exact hy (by have := sub_left_inj.mp heq; rwa [← this])
    by_cases h0X : (0 : ZMod b) ∈ X'
    · have hval_pos : ∀ z : ZMod b, z ∉ X' → 1 ≤ z.val ∧ z.val ≤ b - 1 := by
        intro z hz
        have hz0 : z ≠ 0 := fun h => hz (h ▸ h0X)
        have hlt := z.val_lt
        have hne0 : z.val ≠ 0 := fun h => hz0 ((ZMod.val_eq_zero z).mp h)
        omega
      have hxval := hval_pos (x - c) hx'
      have hyval := hval_pos (y - c) hy'
      have hw := walk_arc_interval (b := b) (X := X') h1 hsym
        hxval.1 hxval.2 hyval.1 hyval.2 (fun t ht1 ht2 htX => by
          have ht0 := hX'_sub (t : ZMod b) htX
          have hval := congrArg ZMod.val ht0
          rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega), ZMod.val_zero] at hval
          omega)
      simpa [ZMod.natCast_zmod_val] using hw
    · have hX'_empty : X' = ∅ := by
        ext z; simp only [Finset.notMem_empty, iff_false]
        intro hz; exact h0X (hX'_sub z hz ▸ hz)
      have hw := walk_arc_interval (b := b) (X := X') h1 hsym
        (Nat.zero_le (x - c).val) (Nat.le_pred_of_lt (x - c).val_lt)
        (Nat.zero_le (y - c).val) (Nat.le_pred_of_lt (y - c).val_lt)
        (fun t _ _ htX => by simp [hX'_empty] at htX)
      simpa [ZMod.natCast_zmod_val] using hw
  · have hX2 : X.card = 2 := by omega
    obtain ⟨x₁, x₂, hx12, hXeq⟩ := Finset.card_eq_two.mp hX2
    have hsum_val : (x₂ - x₁).val + (x₁ - x₂).val = b := by
      have hne : x₂ - x₁ ≠ 0 := sub_ne_zero.mpr hx12.symm
      have hneg : x₁ - x₂ = -(x₂ - x₁) := by abel
      rw [hneg, ZMod.neg_val']
      have hpos : 0 < (x₂ - x₁).val := Nat.pos_of_ne_zero (fun h => hne ((ZMod.val_eq_zero _).mp h))
      have hlt : (x₂ - x₁).val < b := (x₂ - x₁).val_lt
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    have hchoose : ∃ k : ℕ, ∃ c₀ : ZMod b,
        1 ≤ k ∧ 2 * k ≤ b ∧
        X.image (fun z => z - c₀) = {0, (k : ZMod b)} := by
      by_cases hle : (x₂ - x₁).val ≤ (x₁ - x₂).val
      · refine ⟨(x₂ - x₁).val, x₁, ?_, by omega, ?_⟩
        · have hne : x₂ - x₁ ≠ 0 := sub_ne_zero.mpr hx12.symm
          exact Nat.pos_of_ne_zero (fun h => hne ((ZMod.val_eq_zero _).mp h))
        · rw [hXeq]; ext z; simp [ZMod.natCast_zmod_val]
      · refine ⟨(x₁ - x₂).val, x₂, ?_, by omega, ?_⟩
        · have hne : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx12
          exact Nat.pos_of_ne_zero (fun h => hne ((ZMod.val_eq_zero _).mp h))
        · rw [hXeq]; ext z; simp [ZMod.natCast_zmod_val, or_comm]
    obtain ⟨k, c₀, hk1, hk2, hX'eq⟩ := hchoose
    apply walkIn_translate c₀
    set X' := X.image (fun z => z - c₀)
    have hx' : x - c₀ ∉ X' := by
      intro h; rcases Finset.mem_image.mp h with ⟨w, hw, heq⟩
      exact hx (by have := sub_left_inj.mp heq; rwa [← this])
    have hy' : y - c₀ ∉ X' := by
      intro h; rcases Finset.mem_image.mp h with ⟨w, hw, heq⟩
      exact hy (by have := sub_left_inj.mp heq; rwa [← this])
    have hnotX' : ∀ t : ℕ, 1 ≤ t → t ≤ b - 1 → t ≠ k → (t : ZMod b) ∉ X' := by
      intro t ht1 ht2 htk htX
      rw [hX'eq, Finset.mem_insert, Finset.mem_singleton] at htX
      rcases htX with h0 | hk'
      · have hv := congrArg ZMod.val h0
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega), ZMod.val_zero] at hv
        omega
      · have hv := congrArg ZMod.val hk'
        rw [ZMod.val_natCast, ZMod.val_natCast,
            Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hv
        exact htk hv
    have hmem_arc : ∀ z : ZMod b, z ∉ X' →
        (1 ≤ z.val ∧ z.val ≤ k - 1) ∨ (k + 1 ≤ z.val ∧ z.val ≤ b - 1) := by
      intro z hz
      have hz0 : z.val ≠ 0 := by
        intro h0
        apply hz
        rw [hX'eq, Finset.mem_insert]
        left; exact (ZMod.val_eq_zero z).mp h0
      have hzk : z.val ≠ k := by
        intro hk'
        apply hz
        rw [hX'eq, Finset.mem_insert, Finset.mem_singleton]
        right; rw [← hk', ZMod.natCast_zmod_val]
      have hlt := z.val_lt
      omega
    have h2d : 2 * d ≤ b := by
      rcases hd_div with ⟨q, hq⟩
      have hq2 : 2 ≤ q := by nlinarith
      nlinarith
    have hwalk_arc1 : ∀ i j : ℕ, 1 ≤ i → i ≤ k - 1 → 1 ≤ j → j ≤ k - 1 →
        WalkIn {u : ZMod b | u ∉ X'} Step (i : ZMod b) (j : ZMod b) := by
      intro i j hi1 hi2 hj1 hj2
      exact walk_arc_interval (b := b) (X := X') h1 hsym hi1 hi2 hj1 hj2
        (fun t ht1 ht2 => hnotX' t (by omega) (by omega) (by omega))
    have hwalk_arc2 : ∀ i j : ℕ, k + 1 ≤ i → i ≤ b - 1 → k + 1 ≤ j → j ≤ b - 1 →
        WalkIn {u : ZMod b | u ∉ X'} Step (i : ZMod b) (j : ZMod b) := by
      intro i j hi1 hi2 hj1 hj2
      exact walk_arc_interval (b := b) (X := X') h1 hsym hi1 hi2 hj1 hj2
        (fun t ht1 ht2 => hnotX' t (by omega) (by omega) (by omega))
    have hbridge : 2 ≤ k →
        WalkIn {u : ZMod b | u ∉ X'} Step ((k - 1 : ℕ) : ZMod b) (((k - 1) + d : ℕ) : ZMod b) := by
      intro hk_ge2
      have hsrc : ((k - 1 : ℕ) : ZMod b) ∉ X' := hnotX' (k - 1) (by omega) (by omega) (by omega)
      have hdst : (((k - 1) + d : ℕ) : ZMod b) ∉ X' :=
        hnotX' ((k - 1) + d) (by omega) (by omega) (by omega)
      refine walkIn_step hsrc hdst hd_mem ?_
      push_cast; ring
    rcases hmem_arc (x - c₀) hx' with ⟨hx1, hx2⟩ | ⟨hx1, hx2⟩ <;>
    rcases hmem_arc (y - c₀) hy' with ⟨hy1, hy2⟩ | ⟨hy1, hy2⟩
    · simpa [ZMod.natCast_zmod_val] using hwalk_arc1 _ _ hx1 hx2 hy1 hy2
    · have hk_ge2 : 2 ≤ k := by omega
      have hw1 := hwalk_arc1 (x - c₀).val (k - 1) hx1 hx2 (by omega) le_rfl
      have hw2 := hbridge hk_ge2
      have hw3 := hwalk_arc2 ((k - 1) + d) (y - c₀).val (by omega) (by omega) hy1 hy2
      simpa [ZMod.natCast_zmod_val] using walkIn_trans (walkIn_trans hw1 hw2) hw3
    · have hk_ge2 : 2 ≤ k := by omega
      have hw1 := hwalk_arc1 (y - c₀).val (k - 1) hy1 hy2 (by omega) le_rfl
      have hw2 := hbridge hk_ge2
      have hw3 := hwalk_arc2 ((k - 1) + d) (x - c₀).val (by omega) (by omega) hx1 hx2
      have hrev := walkIn_symm hsym (walkIn_trans (walkIn_trans hw1 hw2) hw3)
      simpa [ZMod.natCast_zmod_val] using hrev
    · simpa [ZMod.natCast_zmod_val] using hwalk_arc2 _ _ hx1 hx2 hy1 hy2

/-! ### Section 5 orders 40..50 & Table 2 moduli coverage -/

theorem sec5_orders_40_to_50_proved :
    ∀ n : ℕ, 40 ≤ n → n ≤ 50 →
      ((∃ d : ℕ, d ∣ n ∧ 4 ≤ d ∧ 10 * d ≤ n) ↔
        (n = 40 ∨ n = 44 ∨ n = 48 ∨ n = 50)) ∧
      ((n = 40 ∨ n = 44 ∨ n = 48 ∨ n = 50) →
        ¬ ∃ p r : ℕ, Nat.Prime p ∧ 1 ≤ r ∧ n = p ^ r) := by
  intro n h40 h50
  have hnotpp : ∀ m : ℕ, (m = 40 ∨ m = 44 ∨ m = 48 ∨ m = 50) →
      ¬ ∃ p r : ℕ, Nat.Prime p ∧ 1 ≤ r ∧ m = p ^ r := by
    intro m hm
    rintro ⟨p, r, hp, hr, hpow⟩
    have h2 : 2 ∣ m := by rcases hm with rfl | rfl | rfl | rfl <;> norm_num
    have h2p : 2 = p :=
      (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp (Nat.prime_two.dvd_of_dvd_pow (hpow ▸ h2))
    subst h2p
    have hodd : ∃ q : ℕ, Nat.Prime q ∧ q ≠ 2 ∧ q ∣ m := by
      rcases hm with rfl | rfl | rfl | rfl
      · exact ⟨5, by norm_num, by norm_num, by norm_num⟩
      · exact ⟨11, by norm_num, by norm_num, by norm_num⟩
      · exact ⟨3, by norm_num, by norm_num, by norm_num⟩
      · exact ⟨5, by norm_num, by norm_num, by norm_num⟩
    rcases hodd with ⟨q, hq, hq2, hqm⟩
    have hqdvd : q ∣ 2 := hq.dvd_of_dvd_pow (hpow ▸ hqm)
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hqdvd)
  refine ⟨?_, hnotpp n⟩
  constructor
  · rintro ⟨d, hd, h4, h10⟩
    have hdle : d ≤ 5 := by omega
    interval_cases n <;> interval_cases d <;> (try omega) <;> norm_num at hd ⊢
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨4, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨4, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨4, by norm_num, by norm_num, by norm_num⟩
    · exact ⟨5, by norm_num, by norm_num, by norm_num⟩

theorem sec6_table2_moduli_proved :
    (∀ z : ZMod 10, z ≠ 0 → z ≠ 3 → z ≠ -3 →
      ∃ q : ℕ, 1 ≤ q ∧ q < 40 ∧ q ∣ 40 ∧ (z = (q : ZMod 10) ∨ z = -(q : ZMod 10))) ∧
    (∀ z : ZMod 12, z ≠ 0 → z ≠ 5 → z ≠ -5 →
      ∃ q : ℕ, 1 ≤ q ∧ q < 48 ∧ q ∣ 48 ∧ (z = (q : ZMod 12) ∨ z = -(q : ZMod 12))) ∧
    (∀ z : ZMod 11, z ≠ 0 → z ≠ 4 → z ≠ -4 →
      ∃ q : ℕ, 1 ≤ q ∧ q < 66 ∧ q ∣ 66 ∧ (z = (q : ZMod 11) ∨ z = -(q : ZMod 11))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro z h0 h3 hm3
    fin_cases z
    · exact absurd rfl h0
    · exact ⟨1, by norm_num, by norm_num, by norm_num, Or.inl rfl⟩
    · exact ⟨2, by norm_num, by norm_num, by norm_num, Or.inl rfl⟩
    · exact absurd rfl h3
    · exact ⟨4, by norm_num, by norm_num, by norm_num, Or.inl rfl⟩
    · exact ⟨5, by norm_num, by norm_num, by norm_num, Or.inl rfl⟩
    · exact ⟨4, by norm_num, by norm_num, by norm_num, Or.inr rfl⟩
    · exact absurd rfl hm3
    · exact ⟨8, by norm_num, by norm_num, by norm_num, Or.inl rfl⟩
    · exact ⟨1, by norm_num, by norm_num, by norm_num, Or.inr rfl⟩
  · intro z h0 h5 hm5
    fin_cases z
    · exact absurd rfl h0
    · exact ⟨1, by norm_num, by norm_num, by norm_num, Or.inl rfl⟩
    · exact ⟨2, by norm_num, by norm_num, by norm_num, Or.inl rfl⟩
    · exact ⟨3, by norm_num, by norm_num, by norm_num, Or.inl rfl⟩
    · exact ⟨4, by norm_num, by norm_num, by norm_num, Or.inl rfl⟩
    · exact absurd rfl h5
    · exact ⟨6, by norm_num, by norm_num, by norm_num, Or.inl rfl⟩
    · exact absurd rfl hm5
    · exact ⟨8, by norm_num, by norm_num, by norm_num, Or.inl rfl⟩
    · exact ⟨3, by norm_num, by norm_num, by norm_num, Or.inr rfl⟩
    · exact ⟨2, by norm_num, by norm_num, by norm_num, Or.inr rfl⟩
    · exact ⟨1, by norm_num, by norm_num, by norm_num, Or.inr rfl⟩
  · intro z h0 h4 hm4
    fin_cases z
    · exact absurd rfl h0
    · exact ⟨1, by norm_num, by norm_num, by norm_num, Or.inl rfl⟩
    · exact ⟨2, by norm_num, by norm_num, by norm_num, Or.inl rfl⟩
    · exact ⟨3, by norm_num, by norm_num, by norm_num, Or.inl rfl⟩
    · exact absurd rfl h4
    · exact ⟨6, by norm_num, by norm_num, by norm_num, Or.inr rfl⟩
    · exact ⟨6, by norm_num, by norm_num, by norm_num, Or.inl rfl⟩
    · exact absurd rfl hm4
    · exact ⟨3, by norm_num, by norm_num, by norm_num, Or.inr rfl⟩
    · exact ⟨2, by norm_num, by norm_num, by norm_num, Or.inr rfl⟩
    · exact ⟨1, by norm_num, by norm_num, by norm_num, Or.inr rfl⟩

/-! ### Remark 6.3: Sharpness at 40, obstruction at 44, and indecomposability of `ℤ_{p^r}` -/

theorem rem_6_3_sharpness_proved :
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
          Nonempty (ZMod (p ^ r) ≃+ Γ₁ × Γ₂)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b hab ha hb
    have hb_le : b ≤ 4 := by nlinarith
    have hb4 : b = 4 := by omega
    subst hb4
    exact ⟨by omega, rfl⟩
  · intro q hq1 hq44 hqdvd
    have hq_mem : q ∈ ({1, 2, 4, 11, 22} : Finset ℕ) := by
      interval_cases q <;> first | decide | (exfalso; norm_num at hqdvd)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq_mem
    rcases hq_mem with rfl | rfl | rfl | rfl | rfl
    · right; decide
    · right; decide
    · right; decide
    · left; decide
    · left; decide
  · refine ⟨{(1 : ZMod 11), -1, 2, -2, 4, -4}, by decide, ?_⟩
    intro hall
    have h0 : (0 : ZMod 11) ∉ ({(1 : ZMod 11), -1, 2, -2, 4, -4} : Finset (ZMod 11)) := by decide
    have h3 : (3 : ZMod 11) ∉ ({(1 : ZMod 11), -1, 2, -2, 4, -4} : Finset (ZMod 11)) := by decide
    have hw := hall 0 3 h0 h3
    rcases hw with ⟨_, _, hrel⟩
    have hstep0 : ∀ v : ZMod 11,
        Relation.ReflTransGen
          (fun u w => u ∉ ({(1 : ZMod 11), -1, 2, -2, 4, -4} : Finset (ZMod 11)) ∧
            w ∉ ({(1 : ZMod 11), -1, 2, -2, 4, -4} : Finset (ZMod 11)) ∧
            ∃ s ∈ ({(1 : ZMod 11), -1, 2, -2, 4, -4} : Set (ZMod 11)), w = u + s) 0 v →
        v = 0 := by
      intro v hv
      cases hv using Relation.ReflTransGen.head_induction_on with
      | refl => rfl
      | head hstep _ ih =>
        rcases hstep with ⟨_, hw_notX, s, hs, rfl⟩
        exfalso
        apply hw_notX
        simpa [zero_add] using hs
    have h30 : (3 : ZMod 11) = 0 := hstep0 3 hrel
    exact absurd h30 (by decide)
  · classical
    intro p r hp hr
    rintro ⟨Γ₁, Γ₂, _, _, _, _, h1, h2, ⟨e⟩⟩
    have : Fact p.Prime := ⟨hp⟩
    have : NeZero (p ^ r) := ⟨pow_ne_zero r hp.ne_zero⟩
    have hcard_eq : p ^ r = Fintype.card Γ₁ * Fintype.card Γ₂ := by
      have h1' := Fintype.card_congr e.toEquiv
      rw [ZMod.card, Fintype.card_prod] at h1'
      exact h1'
    have hp1 : p ∣ Fintype.card Γ₁ := by
      have hd : Fintype.card Γ₁ ∣ p ^ r := ⟨Fintype.card Γ₂, hcard_eq⟩
      obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow hp).mp hd
      have hk_pos : 1 ≤ k := by
        by_contra h0
        have : k = 0 := by omega
        subst this; simp at hk; omega
      rw [hk]; exact dvd_pow_self p (by omega)
    have hp2 : p ∣ Fintype.card Γ₂ := by
      have hd : Fintype.card Γ₂ ∣ p ^ r := ⟨Fintype.card Γ₁, by rw [mul_comm]; exact hcard_eq⟩
      obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow hp).mp hd
      have hk_pos : 1 ≤ k := by
        by_contra h0
        have : k = 0 := by omega
        subst this; simp at hk; omega
      rw [hk]; exact dvd_pow_self p (by omega)
    obtain ⟨g₁, hg₁⟩ := exists_prime_addOrderOf_dvd_card p hp1
    obtain ⟨g₂, hg₂⟩ := exists_prime_addOrderOf_dvd_card p hp2
    let Tprod : Finset (Γ₁ × Γ₂) := Finset.univ.filter (fun x => p • x = 0)
    let Tzmod : Finset (ZMod (p ^ r)) := Finset.univ.filter (fun x => p • x = 0)
    have hcard_T : Tzmod.card = Tprod.card := by
      refine Finset.card_bij (fun x _ => e x) ?_ ?_ ?_
      · intro x hx
        rw [Finset.mem_filter] at hx ⊢
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [← map_nsmul, hx.2, map_zero]
      · intro x₁ _ x₂ _ h; exact e.injective h
      · intro y hy
        rw [Finset.mem_filter] at hy
        refine ⟨e.symm y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, e.apply_symm_apply y⟩
        rw [← map_nsmul, hy.2, map_zero]
    have hlow : p * p ≤ Tprod.card := by
      let f : Fin p × Fin p → Γ₁ × Γ₂ := fun ab => (ab.1.1 • g₁, ab.2.1 • g₂)
      have hf_inj : Function.Injective f := by
        intro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ heq
        simp only [f, Prod.mk.injEq] at heq
        have ha : a₁.1 = a₂.1 := by
          have hsub : (a₁.1 : ℤ) • g₁ = (a₂.1 : ℤ) • g₁ := by simpa using heq.1
          have h0 : ((a₁.1 : ℤ) - (a₂.1 : ℤ)) • g₁ = 0 := by
            rw [sub_zsmul, hsub, add_neg_cancel]
          have hdvd := addOrderOf_dvd_iff_zsmul_eq_zero.mpr h0
          rw [hg₁] at hdvd
          have h1' : a₁.1 < p := a₁.2
          have h2' : a₂.1 < p := a₂.2
          rcases hdvd with ⟨q, hq⟩
          have hq0 : q = 0 := by nlinarith
          subst hq0; omega
        have hb : b₁.1 = b₂.1 := by
          have hsub : (b₁.1 : ℤ) • g₂ = (b₂.1 : ℤ) • g₂ := by simpa using heq.2
          have h0 : ((b₁.1 : ℤ) - (b₂.1 : ℤ)) • g₂ = 0 := by
            rw [sub_zsmul, hsub, add_neg_cancel]
          have hdvd := addOrderOf_dvd_iff_zsmul_eq_zero.mpr h0
          rw [hg₂] at hdvd
          have h1' : b₁.1 < p := b₁.2
          have h2' : b₂.1 < p := b₂.2
          rcases hdvd with ⟨q, hq⟩
          have hq0 : q = 0 := by nlinarith
          subst hq0; omega
        exact Prod.ext (Fin.ext ha) (Fin.ext hb)
      have hf_mem : Finset.univ.image f ⊆ Tprod := by
        intro y hy
        rcases Finset.mem_image.mp hy with ⟨⟨a, b⟩, _, rfl⟩
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        ext
        · change p • (a.1 • g₁) = 0
          have hpg₁ : p • g₁ = 0 := hg₁ ▸ addOrderOf_nsmul_eq_zero g₁
          rw [smul_comm, hpg₁, smul_zero]
        · change p • (b.1 • g₂) = 0
          have hpg₂ : p • g₂ = 0 := hg₂ ▸ addOrderOf_nsmul_eq_zero g₂
          rw [smul_comm, hpg₂, smul_zero]
      calc p * p = Fintype.card (Fin p × Fin p) := by simp
        _ = (Finset.univ.image f).card := (Finset.card_image_of_injective _ hf_inj).symm
        _ ≤ Tprod.card := Finset.card_le_card hf_mem
    have hhigh : Tzmod.card ≤ p := by
      let g : Fin p → ZMod (p ^ r) := fun k => ((k.1 * p ^ (r - 1) : ℕ) : ZMod (p ^ r))
      have hsub : Tzmod ⊆ Finset.univ.image g := by
        intro x hx
        rw [Finset.mem_filter] at hx
        have hpx : ((p * x.val : ℕ) : ZMod (p ^ r)) = 0 := by
          push_cast
          simpa [nsmul_eq_mul, ZMod.natCast_zmod_val] using hx.2
        have hdvd : p ^ r ∣ p * x.val := (ZMod.natCast_eq_zero_iff _ _).mp hpx
        have hpr : p ^ r = p * p ^ (r - 1) := by
          conv_lhs => rw [← Nat.sub_add_cancel hr, pow_succ']
        have hdvd_mul : p * p ^ (r - 1) ∣ p * x.val := by
          rcases hdvd with ⟨t, ht⟩
          exact ⟨t, by rw [← hpr]; exact ht⟩
        have hdvd' : p ^ (r - 1) ∣ x.val := (mul_dvd_mul_iff_left hp.ne_zero).mp hdvd_mul
        rcases hdvd' with ⟨k, hk⟩
        have hk_lt : k < p := by
          have hxlt : x.val < p * p ^ (r - 1) := hpr ▸ x.val_lt
          rw [hk] at hxlt
          have hpos : 0 < p ^ (r - 1) := pow_pos hp.pos _
          nlinarith
        refine Finset.mem_image.mpr ⟨⟨k, hk_lt⟩, Finset.mem_univ _, ?_⟩
        simp only [g, mul_comm k (p ^ (r - 1)), ← hk, ZMod.natCast_zmod_val]
      calc Tzmod.card ≤ (Finset.univ.image g).card := Finset.card_le_card hsub
        _ ≤ (Finset.univ : Finset (Fin p)).card := Finset.card_image_le
        _ = p := by simp
    have hp2' : 2 ≤ p := hp.two_le
    nlinarith

/-! ### Section 4 closing remark -/

theorem sec4_integer_consequence_of
    {a b : ℕ} (ha : 10 ≤ a) (hb : 4 ≤ b)
    (Sig : StepSystem (ZMod (a * b)))
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : Multigraph V E)
    (hMaster :
      (∀ (f g : G.NZFlow (ZMod (a * b))), G.SigmaJoined Sig.carrier f g) ∧
      G.FlowGraphConnected (ZMod (a * b)))
    (hCor28b : G.IsLoopless → 3 ≤ a * b →
      (∀ f g : G.NZFlow (ZMod (a * b)), G.SigmaJoined Sig.carrier f g) →
      G.IntFlowConnected (a * b)) :
    G.ModularFlowConnected (a * b) ∧ (G.IsLoopless → G.IntFlowConnected (a * b)) :=
  ⟨hMaster.2, fun hll => hCor28b hll (by nlinarith) hMaster.1⟩

end Flow.Proofs
