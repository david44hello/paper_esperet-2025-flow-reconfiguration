module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Flow.Proofs.Moduli
public import Flow.Proofs.Averaging
public import Mathlib.Data.Nat.Factorization.Basic

@[expose] public section

/-!
# Section 6: Proof of Theorem 1.1 (Integer and modular flows for positive multiples of 40, 48, 66)
-/

namespace Flow.Proofs

open Flow

private lemma zmod10_sdiff_card : ((Finset.univ : Finset (ZMod 10)) \ {0, 3, -3}).card = 7 := by decide
private lemma zmod12_sdiff_card : ((Finset.univ : Finset (ZMod 12)) \ {0, 5, -5}).card = 9 := by decide
private lemma zmod11_sdiff_card : ((Finset.univ : Finset (ZMod 11)) \ {0, 4, -4}).card = 8 := by decide

private lemma walkIn_symm_main {α : Type} [AddCommGroup α] {S Step : Set α}
    (hsym : ∀ s ∈ Step, -s ∈ Step) {x y : α} (h : WalkIn S Step x y) :
    WalkIn S Step y x := by
  rcases h with ⟨hx, hy, hwalk⟩
  refine ⟨hy, hx, ?_⟩
  induction hwalk with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
    rcases hstep with ⟨hu, hv, s, hs, rfl⟩
    exact Relation.ReflTransGen.head ⟨hv, hu, -s, hsym s hs, by abel⟩ (ih hu)

/-- Transport `WalkIn` across an additive equivalence `e : α ≃+ β`. -/
private lemma walkIn_of_addEquiv {α β : Type} [AddCommGroup α] [AddCommGroup β]
    (e : α ≃+ β) {S : Set α} {S' : Set β} {Step : Set α} {Step' : Set β}
    (hS : ∀ a, a ∈ S ↔ e a ∈ S')
    (hStep : ∀ s ∈ Step', e.symm s ∈ Step)
    {x y : α} (hw : WalkIn S' Step' (e x) (e y)) :
    WalkIn S Step x y := by
  rcases hw with ⟨hx, hy, hrel⟩
  refine ⟨(hS x).mpr hx, (hS y).mpr hy, ?_⟩
  have hgen : ∀ u v : β,
      Relation.ReflTransGen (fun a b => a ∈ S' ∧ b ∈ S' ∧ ∃ s ∈ Step', b = a + s) u v →
      Relation.ReflTransGen (fun a b => a ∈ S ∧ b ∈ S ∧ ∃ s ∈ Step, b = a + s) (e.symm u) (e.symm v) := by
    intro u v h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hstep ih =>
      rcases hstep with ⟨ha, hb, s, hs, rfl⟩
      refine Relation.ReflTransGen.tail ih
        ⟨(hS _).mpr (by simpa using ha), (hS _).mpr (by simpa using hb),
          e.symm s, hStep s hs, by rw [map_add]⟩
  simpa using hgen (e x) (e y) hrel

/-- Helper: `zmultiples (a : ZMod (a * b))` has cardinality `b`, and quotient `≃+ ZMod a`. -/
private lemma zmod_subgroup_mul_card_and_quot {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    let k := a * b
    let B : AddSubgroup (ZMod k) := AddSubgroup.zmultiples (a : ZMod k)
    Nonempty (B ≃+ ZMod b) ∧ Nonempty ((ZMod k ⧸ B) ≃+ ZMod a) := by
  classical
  intro k B
  have hk_pos : 0 < k := Nat.mul_pos (by omega) (by omega)
  haveI : NeZero k := ⟨Nat.ne_of_gt hk_pos⟩
  haveI : NeZero a := ⟨by omega⟩
  haveI : NeZero b := ⟨by omega⟩
  have hord : addOrderOf (a : ZMod k) = b := by
    rw [ZMod.addOrderOf_coe a (Nat.ne_of_gt hk_pos)]
    have hgcd : k.gcd a = a := Nat.gcd_eq_right (dvd_mul_right a b)
    rw [hgcd]
    exact Nat.mul_div_cancel_left b (by omega)
  let proj : ZMod k →+ ZMod a := (ZMod.castHom (dvd_mul_right a b) (ZMod a)).toAddMonoidHom
  have hproj_surj : Function.Surjective proj := by
    intro x
    refine ⟨(x.val : ZMod k), ?_⟩
    change ZMod.castHom (dvd_mul_right a b) (ZMod a) (x.val : ZMod k) = x
    rw [map_natCast, ZMod.natCast_zmod_val]
  have hproj_ker : proj.ker = B := by
    ext x
    simp only [AddMonoidHom.mem_ker, B, AddSubgroup.mem_zmultiples_iff]
    constructor
    · intro h0
      have hx : ((x.val : ℕ) : ZMod a) = 0 := by
        change ZMod.castHom (dvd_mul_right a b) (ZMod a) x = 0 at h0
        rw [← ZMod.natCast_zmod_val x, map_natCast] at h0
        exact h0
      rcases (ZMod.natCast_eq_zero_iff x.val a).mp hx with ⟨q, hq⟩
      refine ⟨(q : ℤ), ?_⟩
      simp only [zsmul_eq_mul, Int.cast_natCast]
      rw [← Nat.cast_mul, mul_comm q a, ← hq, ZMod.natCast_zmod_val]
    · rintro ⟨m, rfl⟩
      rw [map_zsmul]
      change m • ZMod.castHom (dvd_mul_right a b) (ZMod a) (a : ZMod k) = 0
      rw [map_natCast, ZMod.natCast_self, smul_zero]
  have heQuot : Nonempty ((ZMod k ⧸ B) ≃+ ZMod a) := by
    rw [← hproj_ker]
    exact ⟨QuotientAddGroup.quotientKerEquivOfSurjective proj hproj_surj⟩
  let toB : ZMod b →+ B :=
    { toFun := fun j => ⟨(j.val : ℤ) • (a : ZMod k), ⟨j.val, rfl⟩⟩
      map_zero' := by ext; simp
      map_add' := fun j₁ j₂ => by
        ext
        simp only [AddSubgroup.coe_add, zsmul_eq_mul, Int.cast_natCast]
        have hba : (b : ZMod k) * (a : ZMod k) = 0 := by
          rw [← Nat.cast_mul, mul_comm b a]; exact ZMod.natCast_self k
        have hdiv := Nat.div_add_mod (j₁.val + j₂.val) b
        have hval : (j₁ + j₂).val = (j₁.val + j₂.val) % b := ZMod.val_add j₁ j₂
        rw [hval]
        have hcast : ((j₁.val + j₂.val : ℕ) : ZMod k) * (a : ZMod k) =
            ((b * ((j₁.val + j₂.val) / b) + (j₁.val + j₂.val) % b : ℕ) : ZMod k) * (a : ZMod k) := by
          rw [hdiv]
        push_cast at hcast
        calc (((j₁.val + j₂.val) % b : ℕ) : ZMod k) * (a : ZMod k)
            = ((b : ZMod k) * (((j₁.val + j₂.val) / b : ℕ) : ZMod k) +
               (((j₁.val + j₂.val) % b : ℕ) : ZMod k)) * (a : ZMod k) := by
              rw [add_mul, mul_assoc, mul_comm (((j₁.val + j₂.val) / b : ℕ) : ZMod k), ← mul_assoc,
                  hba, zero_mul, zero_add]
          _ = ((j₁.val : ZMod k) + (j₂.val : ZMod k)) * (a : ZMod k) := hcast.symm
          _ = (j₁.val : ZMod k) * (a : ZMod k) + (j₂.val : ZMod k) * (a : ZMod k) := add_mul _ _ _ }
  have htoB_inj : Function.Injective toB := by
    rw [injective_iff_map_eq_zero]
    intro j hj
    have h0 : (j.val : ℕ) • (a : ZMod k) = 0 := by
      have h' := congrArg Subtype.val hj
      simpa [toB] using h'
    have hord_dvd : addOrderOf (a : ZMod k) ∣ j.val := addOrderOf_dvd_of_nsmul_eq_zero h0
    have hdvd : b ∣ j.val := by rcases hord_dvd with ⟨t, ht⟩; exact ⟨t, by rw [ht, hord]⟩
    have hv0 : j.val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd j.val_lt
    exact (ZMod.val_eq_zero j).mp hv0
  have htoB_surj : Function.Surjective toB := by
    rintro ⟨x, ⟨m, rfl⟩⟩
    refine ⟨(m : ZMod b), ?_⟩
    ext
    simp only [toB, AddMonoidHom.coe_mk, ZeroHom.coe_mk, zsmul_eq_mul, Int.cast_natCast]
    have hba : (b : ZMod k) * (a : ZMod k) = 0 := by
      rw [← Nat.cast_mul, mul_comm b a]; exact ZMod.natCast_self k
    have hsub : ((((m : ZMod b).val : ℤ) - m) : ℤ) % (b : ℤ) = 0 := by
      have h1 : (((m : ZMod b).val : ℕ) : ZMod b) = (m : ZMod b) := ZMod.natCast_zmod_val _
      have h2 : ((((m : ZMod b).val : ℤ) - m : ℤ) : ZMod b) = 0 := by
        rw [Int.cast_sub, Int.cast_natCast, h1, sub_self]
      have hdvd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ b).mp h2
      exact Int.emod_eq_zero_of_dvd hdvd
    obtain ⟨t, ht⟩ := Int.dvd_of_emod_eq_zero hsub
    have heq_m : ((m : ZMod b).val : ℤ) = m + (b : ℤ) * t := by omega
    have hcast : (((m : ZMod b).val : ℤ) : ZMod k) * (a : ZMod k) =
        ((m : ZMod k) + (b : ZMod k) * (t : ZMod k)) * (a : ZMod k) := by
      rw [heq_m]; push_cast; rfl
    have hcast' : (((m : ZMod b).val : ℕ) : ZMod k) * (a : ZMod k) =
        ((m : ZMod k) + (b : ZMod k) * (t : ZMod k)) * (a : ZMod k) := by
      simpa using hcast
    rw [hcast', add_mul, mul_assoc, mul_comm (t : ZMod k), ← mul_assoc, hba, zero_mul, add_zero]
  exact ⟨⟨(AddEquiv.ofBijective toB ⟨htoB_inj, htoB_surj⟩).symm⟩, heQuot⟩

/-- Internal direct sum `c' ℤ_k ⊕ c ℤ_k = ℤ_k` when `c * c' = k` and `Nat.Coprime c c'`. -/
private lemma zmod_internal_direct_sum {c c' k : ℕ} (hc : 2 ≤ c) (hc' : 2 ≤ c')
    (hcop : Nat.Coprime c c') (hprod : c * c' = k) :
    let Γ₁ : AddSubgroup (ZMod k) := AddSubgroup.zmultiples (c' : ZMod k)
    let Γ₂ : AddSubgroup (ZMod k) := AddSubgroup.zmultiples (c : ZMod k)
    Nat.card Γ₁ = c ∧ Nat.card Γ₂ = c' ∧ Γ₁ ⊓ Γ₂ = ⊥ ∧ Γ₁ ⊔ Γ₂ = ⊤ := by
  classical
  intro Γ₁ Γ₂
  have hk_pos : 0 < k := by rw [← hprod]; nlinarith
  haveI : NeZero k := ⟨Nat.ne_of_gt hk_pos⟩
  have hord1 : addOrderOf (c' : ZMod k) = c := by
    rw [ZMod.addOrderOf_coe c' (Nat.ne_of_gt hk_pos)]
    have hgcd : k.gcd c' = c' := Nat.gcd_eq_right ⟨c, by rw [mul_comm, hprod]⟩
    rw [hgcd, ← hprod]
    exact Nat.mul_div_cancel c (by omega)
  have hord2 : addOrderOf (c : ZMod k) = c' := by
    rw [ZMod.addOrderOf_coe c (Nat.ne_of_gt hk_pos)]
    have hgcd : k.gcd c = c := Nat.gcd_eq_right ⟨c', hprod.symm⟩
    rw [hgcd, ← hprod]
    exact Nat.mul_div_cancel_left c' (by omega)
  have hcard1 : Nat.card Γ₁ = c := by rw [Nat.card_zmultiples, hord1]
  have hcard2 : Nat.card Γ₂ = c' := by rw [Nat.card_zmultiples, hord2]
  have hdisj : Γ₁ ⊓ Γ₂ = ⊥ := by
    rw [eq_bot_iff]
    intro x ⟨hx1, hx2⟩
    rcases AddSubgroup.mem_zmultiples_iff.mp hx1 with ⟨m₁, hm₁⟩
    rcases AddSubgroup.mem_zmultiples_iff.mp hx2 with ⟨m₂, hm₂⟩
    have hc_c' : c • (c' : ZMod k) = 0 := hord1 ▸ addOrderOf_nsmul_eq_zero (c' : ZMod k)
    have hc'_c : c' • (c : ZMod k) = 0 := hord2 ▸ addOrderOf_nsmul_eq_zero (c : ZMod k)
    have hc_x : c • x = 0 := by rw [← hm₁, smul_comm, hc_c', smul_zero]
    have hc'_x : c' • x = 0 := by rw [← hm₂, smul_comm, hc'_c, smul_zero]
    have hbez : (1 : ℤ) = (c : ℤ) * Nat.gcdA c c' + (c' : ℤ) * Nat.gcdB c c' := by
      have h := Nat.gcd_eq_gcd_ab c c'
      rw [hcop.gcd_eq_one, Nat.cast_one] at h
      exact h
    have hx0 : x = 0 := by
      calc x = (1 : ℤ) • x := (one_zsmul x).symm
        _ = ((c : ℤ) * Nat.gcdA c c' + (c' : ℤ) * Nat.gcdB c c') • x := by rw [hbez]
        _ = (Nat.gcdA c c' * (c : ℤ)) • x + (Nat.gcdB c c' * (c' : ℤ)) • x := by
            rw [add_zsmul, mul_comm (c : ℤ), mul_comm (c' : ℤ)]
        _ = Nat.gcdA c c' • ((c : ℤ) • x) + Nat.gcdB c c' • ((c' : ℤ) • x) := by
            rw [mul_zsmul, mul_zsmul]
        _ = Nat.gcdA c c' • (c • x) + Nat.gcdB c c' • (c' • x) := by
            rw [natCast_zsmul, natCast_zsmul]
        _ = 0 := by rw [hc_x, hc'_x, smul_zero, smul_zero, add_zero]
    exact hx0
  have hspan : Γ₁ ⊔ Γ₂ = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hbez : (1 : ℤ) = (c : ℤ) * Nat.gcdA c c' + (c' : ℤ) * Nat.gcdB c c' := by
      have h := Nat.gcd_eq_gcd_ab c c'
      rw [hcop.gcd_eq_one, Nat.cast_one] at h
      exact h
    have hsum : ((x.val : ℤ) * Nat.gcdB c c') • (c' : ZMod k) +
                ((x.val : ℤ) * Nat.gcdA c c') • (c : ZMod k) = x := by
      simp only [zsmul_eq_mul, Int.cast_mul, Int.cast_natCast]
      have h1 : ((c : ZMod k) * (Nat.gcdA c c' : ZMod k) +
                 (c' : ZMod k) * (Nat.gcdB c c' : ZMod k)) = 1 := by
        have h := congrArg (fun z : ℤ => (z : ZMod k)) hbez
        push_cast at h
        exact h.symm
      calc (x.val : ZMod k) * (Nat.gcdB c c' : ZMod k) * (c' : ZMod k) +
           (x.val : ZMod k) * (Nat.gcdA c c' : ZMod k) * (c : ZMod k)
          = (x.val : ZMod k) * ((c : ZMod k) * (Nat.gcdA c c' : ZMod k) +
                                (c' : ZMod k) * (Nat.gcdB c c' : ZMod k)) := by ring
        _ = (x.val : ZMod k) * 1 := by rw [h1]
        _ = x := by rw [mul_one, ZMod.natCast_zmod_val]
    rw [← hsum]
    exact AddSubgroup.add_mem_sup
      (AddSubgroup.mem_zmultiples_iff.mpr ⟨(x.val : ℤ) * Nat.gcdB c c', rfl⟩)
      (AddSubgroup.mem_zmultiples_iff.mpr ⟨(x.val : ℤ) * Nat.gcdA c c', rfl⟩)
  exact ⟨hcard1, hcard2, hdisj, hspan⟩

/-- **Theorem 1.1 (Integer and modular flows), parametrized on `HasCycleDecomp`, Master Theorem,
and Corollary 2.8.** -/
theorem thm_1_1_of
    (hCD : HasCycleDecomp)
    {k : ℕ} (hk_pos : 0 < k) (hk_div : 40 ∣ k ∨ 48 ∣ k ∨ 66 ∣ k)
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : Multigraph V E) (_hbr : G.IsBridgeless)
    (hMaster :
      ∀ (B : AddSubgroup (ZMod k)) [Fintype (ZMod k ⧸ B)] [Fintype B]
        [DecidableEq (ZMod k ⧸ B)] [DecidableEq B],
        10 ≤ Fintype.card (ZMod k ⧸ B) → 4 ≤ Fintype.card B →
        ∀ (Sig : StepSystem (ZMod k)),
          CondR1 B Sig → CondR2 B Sig → CondR3 Sig → CondAV B Sig →
          (∀ f g : G.NZFlow (ZMod k), G.SigmaJoined Sig.carrier f g) ∧
          G.FlowGraphConnected (ZMod k))
    (hCor28a : ∀ q : ℕ, 3 ≤ k → 1 ≤ q → q < k → q ∣ k →
      Multigraph.IsLiftable k (q : ZMod k) ∧ Multigraph.IsLiftable k (-(q : ZMod k)))
    (hCor28b : ∀ (Sig : StepSystem (ZMod k)), G.IsLoopless → 3 ≤ k →
      (∀ z ∈ Sig.carrier, Multigraph.IsLiftable k z) →
      (∀ f g : G.NZFlow (ZMod k), G.SigmaJoined Sig.carrier f g) →
      G.IntFlowConnected k) :
    G.ModularFlowConnected k ∧ (G.IsLoopless → G.IntFlowConnected k) := by
  classical
  haveI : NeZero k := ⟨Nat.ne_of_gt hk_pos⟩
  have hparams : ∃ k₀ a b₀ m : ℕ,
      (k₀ = 40 ∧ a = 10 ∧ b₀ = 4 ∨ k₀ = 48 ∧ a = 12 ∧ b₀ = 4 ∨ k₀ = 66 ∧ a = 11 ∧ b₀ = 6) ∧
      1 ≤ m ∧ k = k₀ * m ∧ k₀ = a * b₀ := by
    rcases hk_div with ⟨m, rfl⟩ | ⟨m, rfl⟩ | ⟨m, rfl⟩
    · exact ⟨40, 10, 4, m, Or.inl ⟨rfl, rfl, rfl⟩, by omega, rfl, by norm_num⟩
    · exact ⟨48, 12, 4, m, Or.inr (Or.inl ⟨rfl, rfl, rfl⟩), by omega, rfl, by norm_num⟩
    · exact ⟨66, 11, 6, m, Or.inr (Or.inr ⟨rfl, rfl, rfl⟩), by omega, rfl, by norm_num⟩
  obtain ⟨k₀, a, b₀, m, hcase, hm1, hk_eq, hk0_eq⟩ := hparams
  let b := b₀ * m
  have ha10 : 10 ≤ a := by rcases hcase with ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ | ⟨_, rfl, _⟩ <;> omega
  have hb4 : 4 ≤ b := by
    change 4 ≤ b₀ * m
    rcases hcase with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> nlinarith
  have hb_even : 2 ∣ b := by
    change 2 ∣ b₀ * m
    rcases hcase with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩
    · exact ⟨2 * m, by ring⟩
    · exact ⟨2 * m, by ring⟩
    · exact ⟨3 * m, by ring⟩
  have hkab : a * b = k := by change a * (b₀ * m) = k; rw [hk_eq, hk0_eq]; ring
  have hk3 : 3 ≤ k := by nlinarith
  let B : AddSubgroup (ZMod k) := AddSubgroup.zmultiples (a : ZMod k)
  have hB_and_A : Nonempty (B ≃+ ZMod b) ∧ Nonempty ((ZMod k ⧸ B) ≃+ ZMod a) := by
    have h := zmod_subgroup_mul_card_and_quot (a := a) (b := b) (by omega) (by omega)
    subst hkab
    exact h
  obtain ⟨⟨eB⟩, ⟨eA⟩⟩ := hB_and_A
  haveI : NeZero a := ⟨by omega⟩
  haveI : NeZero b := ⟨by omega⟩
  have hcardA : Fintype.card (ZMod k ⧸ B) = a := by rw [Fintype.card_congr eA.toEquiv, ZMod.card]
  have hcardB : Fintype.card B = b := by rw [Fintype.card_congr eB.toEquiv, ZMod.card]
  let Sig : StepSystem (ZMod k) :=
    { carrier := {z : ZMod k | ∃ q : ℕ, 1 ≤ q ∧ q < k ∧ q ∣ k ∧ (z = (q : ZMod k) ∨ z = -(q : ZMod k))}
      zero_not_mem := by
        rintro ⟨q, hq1, hqk, _, h0 | h0⟩
        · have hdvd : k ∣ q := (ZMod.natCast_eq_zero_iff q k).mp h0.symm
          exact absurd (Nat.le_of_dvd (by omega) hdvd) (by omega)
        · have h0' : (q : ZMod k) = 0 := neg_eq_zero.mp h0.symm
          have hdvd : k ∣ q := (ZMod.natCast_eq_zero_iff q k).mp h0'
          exact absurd (Nat.le_of_dvd (by omega) hdvd) (by omega)
      neg_mem := by
        rintro x ⟨q, hq1, hqk, hqdvd, h | h⟩
        · exact ⟨q, hq1, hqk, hqdvd, Or.inr (by rw [h])⟩
        · exact ⟨q, hq1, hqk, hqdvd, Or.inl (by rw [h, neg_neg])⟩ }
  -- (1) Liftability
  have hlift : ∀ z ∈ Sig.carrier, Multigraph.IsLiftable k z := by
    rintro z ⟨q, hq1, hqk, hqdvd, rfl | rfl⟩
    · exact (hCor28a q hk3 hq1 hqk hqdvd).1
    · exact (hCor28a q hk3 hq1 hqk hqdvd).2
  -- (2) Condition (R1)
  have hR1 : CondR1 B Sig := by
    have hadvd : a ∣ k := ⟨b, hkab.symm⟩
    let proj : ZMod k →+ ZMod a := (ZMod.castHom hadvd (ZMod a)).toAddMonoidHom
    have hproj_surj : Function.Surjective proj := fun x =>
      ⟨(x.val : ZMod k), by
        change ZMod.castHom hadvd (ZMod a) (x.val : ZMod k) = x
        rw [map_natCast, ZMod.natCast_zmod_val]⟩
    have hproj_ker : proj.ker = B := by
      ext x
      simp only [AddMonoidHom.mem_ker, B, AddSubgroup.mem_zmultiples_iff]
      constructor
      · intro h0
        have hx : ((x.val : ℕ) : ZMod a) = 0 := by
          change ZMod.castHom hadvd (ZMod a) x = 0 at h0
          rw [← ZMod.natCast_zmod_val x, map_natCast] at h0
          exact h0
        rcases (ZMod.natCast_eq_zero_iff x.val a).mp hx with ⟨q, hq⟩
        refine ⟨(q : ℤ), ?_⟩
        simp only [zsmul_eq_mul, Int.cast_natCast]
        rw [← Nat.cast_mul, mul_comm q a, ← hq, ZMod.natCast_zmod_val]
      · rintro ⟨t, rfl⟩
        rw [map_zsmul]
        change t • ZMod.castHom hadvd (ZMod a) (a : ZMod k) = 0
        rw [map_natCast, ZMod.natCast_self, smul_zero]
    let eQ : (ZMod k ⧸ B) ≃+ ZMod a :=
      (QuotientAddGroup.quotientAddEquivOfEq hproj_ker.symm).trans
        (QuotientAddGroup.quotientKerEquivOfSurjective proj hproj_surj)
    have heQ_mk : ∀ x : ZMod k, eQ (QuotientAddGroup.mk x) = proj x := fun _ => rfl
    let D : Finset (ZMod a) := Finset.univ.filter (fun z => eQ.symm z ∈ Sig.sigA B)
    have hD_zero : (0 : ZMod a) ∉ D := by
      intro h
      have h' := (Finset.mem_filter.mp h).2
      exact h'.1 (map_zero eQ.symm)
    have hD_sym : ∀ z ∈ D, -z ∈ D := by
      intro z hz
      have hz' := (Finset.mem_filter.mp hz).2
      rcases hz' with ⟨hne0, lam, hlam, hmk⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      refine ⟨by rw [map_neg]; exact neg_ne_zero.mpr hne0, -lam, Sig.neg_mem hlam, ?_⟩
      rw [QuotientAddGroup.mk_neg, hmk, map_neg]
    have hD_cover : ∀ z : ZMod a,
        (∃ q : ℕ, 1 ≤ q ∧ q < k₀ ∧ q ∣ k₀ ∧ (z = (q : ZMod a) ∨ z = -(q : ZMod a))) →
        z ≠ 0 → z ∈ D := by
      rintro z ⟨q, hq1, hqk0, hqdvd0, hzq⟩ hz0
      have hqk : q < k := by nlinarith
      have hqdvd : q ∣ k := hqdvd0.trans ⟨m, hk_eq⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      refine ⟨fun h0 => hz0 (eQ.symm.injective (by simpa using h0)), ?_⟩
      rcases hzq with rfl | rfl
      · refine ⟨(q : ZMod k), ⟨q, hq1, hqk, hqdvd, Or.inl rfl⟩, ?_⟩
        apply eQ.injective
        rw [eQ.apply_symm_apply, heQ_mk]
        change ZMod.castHom hadvd (ZMod a) (q : ZMod k) = (q : ZMod a)
        rw [map_natCast]
      · refine ⟨-(q : ZMod k), ⟨q, hq1, hqk, hqdvd, Or.inr rfl⟩, ?_⟩
        apply eQ.injective
        rw [eQ.apply_symm_apply, heQ_mk]
        change ZMod.castHom hadvd (ZMod a) (-(q : ZMod k)) = -(q : ZMod a)
        rw [map_neg, map_natCast]
    have hD_card : a - 3 ≤ D.card := by
      have htab := sec6_table2_moduli_proved
      rcases hcase with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
      · have hsub : (Finset.univ \ {(0 : ZMod 10), 3, -3}) ⊆ D := by
          intro z hz
          simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
            true_and, not_or] at hz
          exact hD_cover z (htab.1 z hz.1 hz.2.1 hz.2.2) hz.1
        have h1 := zmod10_sdiff_card
        have h2 := Finset.card_le_card hsub
        omega
      · have hsub : (Finset.univ \ {(0 : ZMod 12), 5, -5}) ⊆ D := by
          intro z hz
          simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
            true_and, not_or] at hz
          exact hD_cover z (htab.2.1 z hz.1 hz.2.1 hz.2.2) hz.1
        have h1 := zmod12_sdiff_card
        have h2 := Finset.card_le_card hsub
        omega
      · have hsub : (Finset.univ \ {(0 : ZMod 11), 4, -4}) ⊆ D := by
          intro z hz
          simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
            true_and, not_or] at hz
          exact hD_cover z (htab.2.2 z hz.1 hz.2.1 hz.2.2) hz.1
        have h1 := zmod11_sdiff_card
        have h2 := Finset.card_le_card hsub
        omega
    intro X hX x y hx hy
    let X' : Finset (ZMod a) := X.image eQ
    have hX' : X'.card ≤ 6 := (Finset.card_image_le).trans hX
    have hx' : eQ x ∉ X' := by
      intro h; rcases Finset.mem_image.mp h with ⟨w, hw, heq⟩; exact hx (eQ.injective heq ▸ hw)
    have hy' : eQ y ∉ X' := by
      intro h; rcases Finset.mem_image.mp h with ⟨w, hw, heq⟩; exact hy (eQ.injective heq ▸ hw)
    have hw := lem_6_1_proved ha10 D hD_zero hD_sym hD_card X' hX' (eQ x) (eQ y) hx' hy'
    exact walkIn_of_addEquiv eQ
      (fun u => by
        simp only [Set.mem_ofPred_eq, X', Finset.mem_image]
        constructor
        · rintro hu ⟨w, hw, heq⟩; exact hu (eQ.injective heq ▸ hw)
        · intro h hu; exact h ⟨u, hu, rfl⟩)
      (fun s hs => (Finset.mem_filter.mp hs).2)
      hw
  -- (3) Condition (R2)
  have hR2 : CondR2 B Sig := by
    have hord_a : addOrderOf (a : ZMod k) = b := by
      rw [ZMod.addOrderOf_coe a (Nat.ne_of_gt hk_pos)]
      have hgcd : k.gcd a = a := Nat.gcd_eq_right ⟨b, hkab.symm⟩
      rw [hgcd, ← hkab]
      exact Nat.mul_div_cancel_left b (by omega)
    let toB : ZMod b →+ B :=
      { toFun := fun j => ⟨(j.val : ℤ) • (a : ZMod k), ⟨j.val, rfl⟩⟩
        map_zero' := by ext; simp
        map_add' := fun j₁ j₂ => by
          ext
          simp only [AddSubgroup.coe_add, zsmul_eq_mul, Int.cast_natCast]
          have hba : (b : ZMod k) * (a : ZMod k) = 0 := by
            rw [← Nat.cast_mul, mul_comm b a, hkab]; exact ZMod.natCast_self k
          have hdiv := Nat.div_add_mod (j₁.val + j₂.val) b
          have hval : (j₁ + j₂).val = (j₁.val + j₂.val) % b := ZMod.val_add j₁ j₂
          rw [hval]
          have hcast : ((j₁.val + j₂.val : ℕ) : ZMod k) * (a : ZMod k) =
              ((b * ((j₁.val + j₂.val) / b) + (j₁.val + j₂.val) % b : ℕ) : ZMod k) * (a : ZMod k) := by
            rw [hdiv]
          push_cast at hcast
          calc (((j₁.val + j₂.val) % b : ℕ) : ZMod k) * (a : ZMod k)
              = ((b : ZMod k) * (((j₁.val + j₂.val) / b : ℕ) : ZMod k) +
                 (((j₁.val + j₂.val) % b : ℕ) : ZMod k)) * (a : ZMod k) := by
                rw [add_mul, mul_assoc, mul_comm (((j₁.val + j₂.val) / b : ℕ) : ZMod k), ← mul_assoc,
                    hba, zero_mul, zero_add]
            _ = ((j₁.val : ZMod k) + (j₂.val : ZMod k)) * (a : ZMod k) := hcast.symm
            _ = (j₁.val : ZMod k) * (a : ZMod k) + (j₂.val : ZMod k) * (a : ZMod k) := add_mul _ _ _ }
    have htoB_inj : Function.Injective toB := by
      rw [injective_iff_map_eq_zero]
      intro j hj
      have h0 : (j.val : ℕ) • (a : ZMod k) = 0 := by
        have h' := congrArg Subtype.val hj; simpa [toB] using h'
      have hord_dvd : addOrderOf (a : ZMod k) ∣ j.val := addOrderOf_dvd_of_nsmul_eq_zero h0
      have hdvd : b ∣ j.val := by rcases hord_dvd with ⟨t, ht⟩; exact ⟨t, by rw [ht, hord_a]⟩
      exact (ZMod.val_eq_zero j).mp (Nat.eq_zero_of_dvd_of_lt hdvd j.val_lt)
    have htoB_surj : Function.Surjective toB := by
      have hcard_eq : Fintype.card (ZMod b) = Fintype.card B := by rw [ZMod.card, hcardB]
      exact (Fintype.bijective_iff_injective_and_card toB).mpr ⟨htoB_inj, hcard_eq⟩ |>.2
    let eB' : B ≃+ ZMod b := (AddEquiv.ofBijective toB ⟨htoB_inj, htoB_surj⟩).symm
    have hstep_mem : ∀ s ∈ ({(1 : ZMod b), -1, (2 : ZMod b), -(2 : ZMod b)} : Set (ZMod b)),
        eB'.symm s ∈ Sig.sigB B := by
      have ha_sig : (a : ZMod k) ∈ Sig.carrier := ⟨a, by omega, by nlinarith, ⟨b, hkab.symm⟩, Or.inl rfl⟩
      have h2a_sig : ((2 * a : ℕ) : ZMod k) ∈ Sig.carrier := by
        rcases hb_even with ⟨b', hb'⟩
        exact ⟨2 * a, by omega, by nlinarith, ⟨b', by rw [← hkab, hb']; ring⟩, Or.inl rfl⟩
      have h1_val : (eB'.symm (1 : ZMod b) : ZMod k) = (a : ZMod k) := by
        change ((1 : ZMod b).val : ℤ) • (a : ZMod k) = (a : ZMod k)
        have : Fact (1 < b) := ⟨by omega⟩
        simp [ZMod.val_one b]
      have h2_val : (eB'.symm (2 : ZMod b) : ZMod k) = ((2 * a : ℕ) : ZMod k) := by
        change ((2 : ZMod b).val : ℤ) • (a : ZMod k) = ((2 * a : ℕ) : ZMod k)
        have hv : (2 : ZMod b).val = 2 := by
          change ((2 : ℕ) : ZMod b).val = 2
          rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
        simp [hv]
      intro s hs
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
      change (eB'.symm s : ZMod k) ∈ Sig.carrier
      rcases hs with rfl | rfl | rfl | rfl
      · rw [h1_val]; exact ha_sig
      · rw [map_neg, AddSubgroup.coe_neg, h1_val]; exact Sig.neg_mem ha_sig
      · rw [h2_val]; exact h2a_sig
      · rw [map_neg, AddSubgroup.coe_neg, h2_val]; exact Sig.neg_mem h2a_sig
    intro X hX x y hx hy
    let X' : Finset (ZMod b) := X.image eB'
    have hX' : X'.card ≤ 2 := (Finset.card_image_le).trans hX
    have hx' : eB' x ∉ X' := by
      intro h; rcases Finset.mem_image.mp h with ⟨w, hw, heq⟩; exact hx (eB'.injective heq ▸ hw)
    have hy' : eB' y ∉ X' := by
      intro h; rcases Finset.mem_image.mp h with ⟨w, hw, heq⟩; exact hy (eB'.injective heq ▸ hw)
    have hw := lem_6_2_proved hb4 (by norm_num) (by omega) hb_even X' hX' (eB' x) (eB' y) hx' hy'
    exact walkIn_of_addEquiv eB'
      (fun u => by
        simp only [Set.mem_ofPred_eq, X', Finset.mem_image]
        constructor
        · rintro hu ⟨w, hw, heq⟩; exact hu (eB'.injective heq ▸ hw)
        · intro h hu; exact h ⟨u, hu, rfl⟩)
      hstep_mem hw
  -- (4) Condition (R3)
  have hR3 : CondR3 Sig := by
    have h1_mem : (1 : ZMod k) ∈ Sig.carrier := ⟨1, le_rfl, by omega, one_dvd k, Or.inl (by simp)⟩
    have hup : ∀ (t : ℕ), 1 ≤ t → t ≤ k - 1 →
        WalkIn {g : ZMod k | g ≠ 0} Sig.carrier (1 : ZMod k) (t : ZMod k) := by
      intro t ht1 htk
      induction t with
      | zero => omega
      | succ t ih =>
        by_cases ht0 : t = 0
        · subst ht0
          have h10 : (1 : ZMod k) ≠ 0 := fun h => Sig.zero_not_mem (h ▸ h1_mem)
          exact ⟨h10, by simpa using h10, by simpa using Relation.ReflTransGen.refl⟩
        · have hprev := ih (by omega) (by omega)
          have ht_ne0 : (t : ZMod k) ≠ 0 := by
            intro h
            have hdvd := (ZMod.natCast_eq_zero_iff t k).mp h
            exact absurd (Nat.le_of_dvd (by omega) hdvd) (by omega)
          have ht1_ne0 : ((t + 1 : ℕ) : ZMod k) ≠ 0 := by
            intro h
            have hdvd := (ZMod.natCast_eq_zero_iff (t + 1) k).mp h
            exact absurd (Nat.le_of_dvd (by omega) hdvd) (by omega)
          exact ⟨hprev.1, ht1_ne0, hprev.2.2.tail ⟨ht_ne0, ht1_ne0, 1, h1_mem, by push_cast; rfl⟩⟩
    intro x y hx hy
    have hx1 : 1 ≤ x.val := Nat.pos_of_ne_zero (fun h => hx ((ZMod.val_eq_zero x).mp h))
    have hy1 : 1 ≤ y.val := Nat.pos_of_ne_zero (fun h => hy ((ZMod.val_eq_zero y).mp h))
    have h1x : WalkIn {g : ZMod k | g ≠ 0} Sig.carrier (1 : ZMod k) x := by
      simpa [ZMod.natCast_zmod_val] using hup x.val hx1 (Nat.le_pred_of_lt x.val_lt)
    have h1y : WalkIn {g : ZMod k | g ≠ 0} Sig.carrier (1 : ZMod k) y := by
      simpa [ZMod.natCast_zmod_val] using hup y.val hy1 (Nat.le_pred_of_lt y.val_lt)
    have hx1' : WalkIn {g : ZMod k | g ≠ 0} Sig.carrier x (1 : ZMod k) :=
      walkIn_symm_main (fun _ hs => Sig.neg_mem hs) h1x
    exact ⟨hx1'.1, h1y.2.1, hx1'.2.2.trans h1y.2.2⟩
  -- (5) Condition (AV)
  have hAV : CondAV B Sig := by
    let v2 := k.factorization 2
    let c := 2 ^ v2
    let c' := k / c
    have h2dvd : 2 ∣ k := by
      rcases hcase with ⟨rfl, _, _⟩ | ⟨rfl, _, _⟩ | ⟨rfl, _, _⟩ <;> rw [hk_eq]
      · exact ⟨20 * m, by ring⟩
      · exact ⟨24 * m, by ring⟩
      · exact ⟨33 * m, by ring⟩
    have hv2_pos : 1 ≤ v2 := Nat.Prime.factorization_pos_of_dvd Nat.prime_two (Nat.ne_of_gt hk_pos) h2dvd
    have hc_ge2 : 2 ≤ c := by
      have : 2 ^ 1 ≤ 2 ^ v2 := Nat.pow_le_pow_right (by norm_num) hv2_pos
      simpa using this
    have hc_dvd : c ∣ k := Nat.ordProj_dvd k 2
    have hprod : c * c' = k := Nat.mul_div_cancel' hc_dvd
    have hc'_odd : ¬ 2 ∣ c' := by
      intro h2c'
      have hpow : 2 ^ (v2 + 1) ∣ k := by
        rw [pow_succ, ← hprod]
        exact mul_dvd_mul_left c h2c'
      have hle := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (Nat.ne_of_gt hk_pos)).mp hpow
      omega
    have hcop : Nat.Coprime c c' := by
      apply Nat.Coprime.pow_left
      exact (Nat.prime_two.coprime_iff_not_dvd).mpr hc'_odd
    have hodd_dvd : ∃ q : ℕ, Nat.Prime q ∧ q ≠ 2 ∧ q ∣ k := by
      rcases hcase with ⟨rfl, _, _⟩ | ⟨rfl, _, _⟩ | ⟨rfl, _, _⟩ <;> rw [hk_eq]
      · exact ⟨5, by norm_num, by norm_num, ⟨8 * m, by ring⟩⟩
      · exact ⟨3, by norm_num, by norm_num, ⟨16 * m, by ring⟩⟩
      · exact ⟨3, by norm_num, by norm_num, ⟨22 * m, by ring⟩⟩
    obtain ⟨q, hq, hq2, hqk⟩ := hodd_dvd
    have hqc' : q ∣ c' := by
      have hqcop : Nat.Coprime q c := by
        apply Nat.Coprime.pow_right
        exact (hq.coprime_iff_not_dvd).mpr fun hd =>
          hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hd)
      rw [← hprod] at hqk
      exact hqcop.dvd_of_dvd_mul_left hqk
    have hc'_pos : 0 < c' := Nat.pos_of_ne_zero (fun h0 => by rw [h0, mul_zero] at hprod; omega)
    have hc'_ge2 : 2 ≤ c' := le_trans hq.two_le (Nat.le_of_dvd hc'_pos hqc')
    have hids := zmod_internal_direct_sum hc_ge2 hc'_ge2 hcop hprod
    let Γ₁ : AddSubgroup (ZMod k) := AddSubgroup.zmultiples (c' : ZMod k)
    let Γ₂ : AddSubgroup (ZMod k) := AddSubgroup.zmultiples (c : ZMod k)
    have hcard1 : 2 ≤ Fintype.card Γ₁ := by
      have : Fintype.card Γ₁ = c := by simpa [Nat.card_eq_fintype_card] using hids.1
      omega
    have hcard2 : 2 ≤ Fintype.card Γ₂ := by
      have : Fintype.card Γ₂ = c' := by simpa [Nat.card_eq_fintype_card] using hids.2.1
      omega
    have hc'_mem : (c' : ZMod k) ∈ Sig.carrier :=
      ⟨c', by omega, by nlinarith, ⟨c, by rw [mul_comm, hprod]⟩, Or.inl rfl⟩
    have hc_mem : (c : ZMod k) ∈ Sig.carrier :=
      ⟨c, by omega, by nlinarith, hc_dvd, Or.inl rfl⟩
    have hgen₁ : Γ₁ ≤ AddSubgroup.closure (Sig.carrier ∩ (Γ₁ : Set (ZMod k))) := by
      rw [AddSubgroup.zmultiples_le]
      exact AddSubgroup.subset_closure ⟨hc'_mem, AddSubgroup.mem_zmultiples _⟩
    have hgen₂ : Γ₂ ≤ AddSubgroup.closure (Sig.carrier ∩ (Γ₂ : Set (ZMod k))) := by
      rw [AddSubgroup.zmultiples_le]
      exact AddSubgroup.subset_closure ⟨hc_mem, AddSubgroup.mem_zmultiples _⟩
    exact rem_5_2_internal_direct_sum_of hCD Γ₁ Γ₂ hcard1 hcard2 hids.2.2.1 hids.2.2.2
      B (by omega) Sig hgen₁ hgen₂
  have hm := hMaster B (by omega) (by omega) Sig hR1 hR2 hR3 hAV
  exact ⟨hm.2, fun hll => hCor28b Sig hll hk3 hlift hm.1⟩

end Flow.Proofs
