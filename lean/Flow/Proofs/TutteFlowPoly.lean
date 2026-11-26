-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Flow.Defs.Literature
import Flow.Proofs.Basic
import Flow.Proofs.Liftable
import Mathlib.Tactic

/-!
# Tutte's flow polynomial invariance (1954): `|NZFlow G A|` depends only on `|A|`

Combined with Corollary 2.3 (`cor_2_3`), this reduces `SeymourSixFlow` for all finite abelian
groups of order `≥ 6` to the single group `ZMod 6`.
-/

namespace Flow.Proofs

open Flow

/-- Delete a single edge `e₀` from `G`. -/
def deleteEdge {V E : Type} (G : Multigraph V E) (e₀ : E) : Multigraph V {e : E // e ≠ e₀} where
  tail e := G.tail e.1
  head e := G.head e.1

noncomputable instance instFintypeNZFlow {V E A : Type} [Fintype E] [DecidableEq V] [DecidableEq E]
    [AddCommGroup A] [Fintype A] (G : Multigraph V E) : Fintype (G.NZFlow A) :=
  Fintype.ofInjective (fun f : G.NZFlow A => f.val) (fun _ _ h => Multigraph.NZFlow.ext h)

private lemma nzflow_card_empty {V E A : Type} [Fintype E] [DecidableEq V] [DecidableEq E]
    [AddCommGroup A] [Fintype A] (G : Multigraph V E) (hE : IsEmpty E) :
    Fintype.card (G.NZFlow A) = 1 := by
  have : Unique (G.NZFlow A) :=
    { default :=
        { val := fun e => hE.elim e
          isFlow := fun v => by
            unfold Multigraph.boundary
            have h1 : Finset.univ.filter (fun e : E => G.head e = v) = ∅ := by
              ext e; exact hE.elim e
            have h2 : Finset.univ.filter (fun e : E => G.tail e = v) = ∅ := by
              ext e; exact hE.elim e
            rw [h1, h2]; simp
          nonzero := fun e => hE.elim e }
      uniq := fun f => by ext e; exact hE.elim e }
  exact Fintype.card_unique

private lemma nzflow_card_loop {V E A : Type} [Fintype E] [DecidableEq V] [DecidableEq E]
    [AddCommGroup A] [Fintype A] [DecidableEq A]
    (G : Multigraph V E) (e₀ : E) (hloop : G.tail e₀ = G.head e₀) :
    Fintype.card (G.NZFlow A) =
      (Fintype.card A - 1) * Fintype.card ((deleteEdge G e₀).NZFlow A) := by
  have hbd_eq : ∀ (x : E → A) (v : V),
      G.boundary x v = (deleteEdge G e₀).boundary (fun e => x e.1) v := by
    intro x v
    rw [boundary_eq_sum_ite, boundary_eq_sum_ite]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ e₀)]
    have h0 : ((if G.head e₀ = v then x e₀ else 0) - if G.tail e₀ = v then x e₀ else 0) = 0 := by
      rw [hloop, sub_self]
    rw [h0, zero_add]
    refine Finset.sum_bij (fun e he => ⟨e, Finset.ne_of_mem_erase he⟩)
      (fun _ _ => Finset.mem_univ _)
      (fun _ _ _ _ h => congrArg Subtype.val h)
      (fun e _ => ⟨e.1, Finset.mem_erase.mpr ⟨e.2, Finset.mem_univ _⟩, rfl⟩)
      (fun _ _ => rfl)
  let e_equiv : G.NZFlow A ≃ {a : A // a ≠ 0} × (deleteEdge G e₀).NZFlow A :=
    { toFun := fun f =>
        (⟨f.val e₀, f.nonzero e₀⟩,
         ⟨fun e => f.val e.1, fun v => by rw [← hbd_eq f.val v]; exact f.isFlow v,
          fun e => f.nonzero e.1⟩)
      invFun := fun p =>
        let val : E → A := fun e => if h : e = e₀ then p.1.1 else p.2.val ⟨e, h⟩
        { val := val
          isFlow := fun v => by
            rw [hbd_eq val v]
            have hfun : (fun e : {e : E // e ≠ e₀} => val e.1) = p.2.val := by
              ext e; simp [val, e.2]
            rw [hfun]; exact p.2.isFlow v
          nonzero := fun e => by
            dsimp only [val]
            split_ifs with h
            · exact p.1.2
            · exact p.2.nonzero ⟨e, h⟩ }
      left_inv := fun f => by
        ext e; dsimp only; split_ifs with h
        · rw [h]
        · rfl
      right_inv := fun p => by
        ext
        · simp
        · rename_i e; simp [e.2] }
  rw [Fintype.card_congr e_equiv, Fintype.card_prod]
  congr 1
  rw [Fintype.card_subtype_compl, show Fintype.card {x : A // x = 0} = 1 from Fintype.card_unique]

private lemma nzflow_card_nonloop {V E A : Type} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] [AddCommGroup A] [Fintype A] [DecidableEq A]
    (G : Multigraph V E) (e₀ : E) (hne : G.tail e₀ ≠ G.head e₀) :
    Fintype.card (G.NZFlow A) + Fintype.card ((deleteEdge G e₀).NZFlow A) =
      Fintype.card ((G.contractEdge e₀ hne).NZFlow A) := by
  let Gc := G.contractEdge e₀ hne
  let Gd := deleteEdge G e₀
  -- Given f' : Gd-edge-map with Gc.IsFlow f', extend uniquely to G by setting f(e₀) = -Gd.boundary f' (G.head e₀)
  let extVal (f' : {e : E // e ≠ e₀} → A) (e : E) : A :=
    if h : e = e₀ then -Gd.boundary f' (G.head e₀) else f' ⟨e, h⟩
  have hbd_other : ∀ (f' : {e : E // e ≠ e₀} → A) (v : V) (hvh : v ≠ G.head e₀) (hvt : v ≠ G.tail e₀),
      G.boundary (extVal f') v = Gc.boundary f' ⟨v, hvh⟩ := by
    intro f' v hvh hvt
    rw [boundary_eq_sum_ite, boundary_eq_sum_ite]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ e₀)]
    have h0 : ((if G.head e₀ = v then extVal f' e₀ else 0) - if G.tail e₀ = v then extVal f' e₀ else 0) = 0 := by
      simp [Ne.symm hvh, Ne.symm hvt]
    rw [h0, zero_add]
    refine Finset.sum_bij (fun e he => ⟨e, Finset.ne_of_mem_erase he⟩)
      (fun _ _ => Finset.mem_univ _)
      (fun _ _ _ _ h => congrArg Subtype.val h)
      (fun e _ => ⟨e.1, Finset.mem_erase.mpr ⟨e.2, Finset.mem_univ _⟩, rfl⟩)
      (fun e he => ?_)
    have hne0 : e ≠ e₀ := Finset.ne_of_mem_erase he
    dsimp only [extVal, Gc, Multigraph.contractEdge]
    rw [dif_neg hne0]
    have hh : (if h : G.head e = G.head e₀ then (⟨G.tail e₀, hne⟩ : {u : V // u ≠ G.head e₀}) else ⟨G.head e, h⟩) =
        ⟨v, hvh⟩ ↔ G.head e = v := by
      split_ifs with h
      · constructor
        · intro heq; exact absurd (congrArg Subtype.val heq) (Ne.symm hvt)
        · intro heq; exact absurd (h.symm.trans heq) (Ne.symm hvh)
      · simp [Subtype.ext_iff]
    have ht : (if h : G.tail e = G.head e₀ then (⟨G.tail e₀, hne⟩ : {u : V // u ≠ G.head e₀}) else ⟨G.tail e, h⟩) =
        ⟨v, hvh⟩ ↔ G.tail e = v := by
      split_ifs with h
      · constructor
        · intro heq; exact absurd (congrArg Subtype.val heq) (Ne.symm hvt)
        · intro heq; exact absurd (h.symm.trans heq) (Ne.symm hvh)
      · simp [Subtype.ext_iff]
    rw [if_congr hh.symm rfl rfl, if_congr ht.symm rfl rfl]
    rfl
  have hbd_head : ∀ (f' : {e : E // e ≠ e₀} → A), G.boundary (extVal f') (G.head e₀) = 0 := by
    intro f'
    rw [boundary_eq_sum_ite]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ e₀)]
    have hrest : ∑ e ∈ Finset.univ.erase e₀,
        ((if G.head e = G.head e₀ then extVal f' e else 0) -
         if G.tail e = G.head e₀ then extVal f' e else 0) = Gd.boundary f' (G.head e₀) := by
      rw [boundary_eq_sum_ite]
      refine Finset.sum_bij (fun e he => ⟨e, Finset.ne_of_mem_erase he⟩)
        (fun _ _ => Finset.mem_univ _)
        (fun _ _ _ _ h => congrArg Subtype.val h)
        (fun e _ => ⟨e.1, Finset.mem_erase.mpr ⟨e.2, Finset.mem_univ _⟩, rfl⟩)
        (fun e he => by
          have hne0 := Finset.ne_of_mem_erase he
          dsimp only [extVal, Gd, deleteEdge]; rw [dif_neg hne0]; rfl)
    rw [hrest]
    simp [extVal, hne]
  have hbd_tail_sum : ∀ (f' : {e : E // e ≠ e₀} → A),
      G.boundary (extVal f') (G.tail e₀) + G.boundary (extVal f') (G.head e₀) =
        Gc.boundary f' ⟨G.tail e₀, hne⟩ := by
    intro f'
    rw [boundary_eq_sum_ite, boundary_eq_sum_ite, boundary_eq_sum_ite, ← Finset.sum_add_distrib]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ e₀)]
    have h0 : ((if G.head e₀ = G.tail e₀ then extVal f' e₀ else 0) -
        if G.tail e₀ = G.tail e₀ then extVal f' e₀ else 0) +
       ((if G.head e₀ = G.head e₀ then extVal f' e₀ else 0) -
        if G.tail e₀ = G.head e₀ then extVal f' e₀ else 0) = 0 := by
      simp [hne, Ne.symm hne]
    rw [h0, zero_add]
    refine Finset.sum_bij (fun e he => ⟨e, Finset.ne_of_mem_erase he⟩)
      (fun _ _ => Finset.mem_univ _)
      (fun _ _ _ _ h => congrArg Subtype.val h)
      (fun e _ => ⟨e.1, Finset.mem_erase.mpr ⟨e.2, Finset.mem_univ _⟩, rfl⟩)
      (fun e he => ?_)
    have hne0 := Finset.ne_of_mem_erase he
    dsimp only [extVal, Gc, Multigraph.contractEdge]
    rw [dif_neg hne0]
    have hh : (if h : G.head e = G.head e₀ then (⟨G.tail e₀, hne⟩ : {u : V // u ≠ G.head e₀}) else ⟨G.head e, h⟩) =
        ⟨G.tail e₀, hne⟩ ↔ G.head e = G.tail e₀ ∨ G.head e = G.head e₀ := by
      split_ifs with h
      · simp [h]
      · simp [Subtype.ext_iff, h]
    have ht : (if h : G.tail e = G.head e₀ then (⟨G.tail e₀, hne⟩ : {u : V // u ≠ G.head e₀}) else ⟨G.tail e, h⟩) =
        ⟨G.tail e₀, hne⟩ ↔ G.tail e = G.tail e₀ ∨ G.tail e = G.head e₀ := by
      split_ifs with h
      · simp [h]
      · simp [Subtype.ext_iff, h]
    by_cases h1 : G.head e = G.tail e₀ <;> by_cases h2 : G.head e = G.head e₀ <;>
    by_cases h3 : G.tail e = G.tail e₀ <;> by_cases h4 : G.tail e = G.head e₀
    · exact absurd (h1.symm.trans h2) hne
    · exact absurd (h1.symm.trans h2) hne
    · exact absurd (h1.symm.trans h2) hne
    · exact absurd (h1.symm.trans h2) hne
    · exact absurd (h3.symm.trans h4) hne
    · simp [h1, h2, h3, h4, hne, Ne.symm hne]
    · simp [h1, h2, h3, h4, hne, Ne.symm hne]
    · simp [h1, h2, h3, h4, hne, Ne.symm hne]
    · exact absurd (h3.symm.trans h4) hne
    · simp [h1, h2, h3, h4, hne, Ne.symm hne]
    · simp [h1, h2, h3, h4, hne, Ne.symm hne]
    · simp [h1, h2, h3, h4, hne, Ne.symm hne]
    · exact absurd (h3.symm.trans h4) hne
    · simp [h1, h2, h3, h4, hne, Ne.symm hne]
    · simp [h1, h2, h3, h4, hne, Ne.symm hne]
    · simp [h1, h2, h3, h4, hne, Ne.symm hne]
  have hext_isFlow : ∀ (f' : {e : E // e ≠ e₀} → A), Gc.IsFlow f' → G.IsFlow (extVal f') := by
    intro f' hf' v
    by_cases hvh : v = G.head e₀
    · rw [hvh]; exact hbd_head f'
    · by_cases hvt : v = G.tail e₀
      · rw [hvt]
        have hsum := hbd_tail_sum f'
        rw [hbd_head f', add_zero, hf' ⟨G.tail e₀, hne⟩] at hsum
        exact hsum
      · rw [hbd_other f' v hvh hvt]; exact hf' ⟨v, hvh⟩
  have hres_isFlow : ∀ (f : E → A), G.IsFlow f → Gc.IsFlow (fun e => f e.1) := by
    intro f hf ⟨v, hvh⟩
    have hfun : extVal (fun e => f e.1) = f := by
      ext e
      dsimp only [extVal]
      split_ifs with h
      · rw [h]
        have hb := hf (G.head e₀)
        rw [boundary_eq_sum_ite, ← Finset.add_sum_erase _ _ (Finset.mem_univ e₀)] at hb
        have hrest : ∑ e' ∈ Finset.univ.erase e₀,
            ((if G.head e' = G.head e₀ then f e' else 0) - if G.tail e' = G.head e₀ then f e' else 0) =
            Gd.boundary (fun e' => f e'.1) (G.head e₀) := by
          rw [boundary_eq_sum_ite]
          refine Finset.sum_bij (fun e' he' => ⟨e', Finset.ne_of_mem_erase he'⟩)
            (fun _ _ => Finset.mem_univ _) (fun _ _ _ _ h => congrArg Subtype.val h)
            (fun e' _ => ⟨e'.1, Finset.mem_erase.mpr ⟨e'.2, Finset.mem_univ _⟩, rfl⟩)
            (fun _ _ => rfl)
        rw [hrest] at hb
        simp [hne] at hb
        exact (eq_neg_of_add_eq_zero_left hb).symm
      · rfl
    by_cases hvt : v = G.tail e₀
    · subst hvt
      rw [← hbd_tail_sum (fun e => f e.1), hfun, hf (G.tail e₀), hf (G.head e₀), add_zero]
    · rw [← hbd_other (fun e => f e.1) v hvh hvt, hfun, hf v]
  let eqv : G.NZFlow A ⊕ Gd.NZFlow A ≃ Gc.NZFlow A :=
    { toFun := fun s => match s with
        | Sum.inl f => ⟨fun e => f.val e.1, hres_isFlow f.val f.isFlow, fun e => f.nonzero e.1⟩
        | Sum.inr f =>
          let f0 : E → A := fun e => if h : e = e₀ then 0 else f.val ⟨e, h⟩
          have hf0_fl : G.IsFlow f0 := fun v => by
            trans (Gd.boundary f.val v)
            · rw [boundary_eq_sum_ite, boundary_eq_sum_ite, ← Finset.add_sum_erase _ _ (Finset.mem_univ e₀)]
              simp only [f0, ↓reduceDIte, ite_self, sub_self, zero_add]
              refine Finset.sum_bij (fun e he => ⟨e, Finset.ne_of_mem_erase he⟩)
                (fun _ _ => Finset.mem_univ _) (fun _ _ _ _ h => congrArg Subtype.val h)
                (fun e _ => ⟨e.1, Finset.mem_erase.mpr ⟨e.2, Finset.mem_univ _⟩, rfl⟩)
                (fun e he => by simp [Finset.ne_of_mem_erase he, Gd, deleteEdge])
            · exact f.isFlow v
          ⟨f.val, by
            have hfun : (fun e : {e : E // e ≠ e₀} => f0 e.1) = f.val := by ext e; simp [f0, e.2]
            rw [← hfun]; exact hres_isFlow f0 hf0_fl, f.nonzero⟩
      invFun := fun fc =>
        if h0 : Gd.boundary fc.val (G.head e₀) = 0 then
          Sum.inr ⟨fc.val, fun v => by
            have hfl := hext_isFlow fc.val fc.isFlow v
            have hfun : ∀ e, extVal fc.val e = if h : e = e₀ then 0 else fc.val ⟨e, h⟩ := fun e => by
              dsimp only [extVal]; split_ifs; simp [h0]; rfl
            rw [← hfl, boundary_eq_sum_ite, boundary_eq_sum_ite, ← Finset.add_sum_erase _ _ (Finset.mem_univ e₀)]
            simp only [hfun, ↓reduceDIte, ite_self, sub_self, zero_add]
            symm
            refine Finset.sum_bij (fun e he => ⟨e, Finset.ne_of_mem_erase he⟩)
              (fun _ _ => Finset.mem_univ _) (fun _ _ _ _ h => congrArg Subtype.val h)
              (fun e _ => ⟨e.1, Finset.mem_erase.mpr ⟨e.2, Finset.mem_univ _⟩, rfl⟩)
              (fun e he => by simp [Finset.ne_of_mem_erase he, Gd, deleteEdge]), fc.nonzero⟩
        else
          Sum.inl ⟨extVal fc.val, hext_isFlow fc.val fc.isFlow, fun e => by
            dsimp only [extVal]; split_ifs with h
            · exact neg_ne_zero.mpr h0
            · exact fc.nonzero ⟨e, h⟩⟩
      left_inv := fun s => by
        cases s with
        | inl f =>
          have hbd_ne : Gd.boundary (fun e => f.val e.1) (G.head e₀) ≠ 0 := by
            have hb := f.isFlow (G.head e₀)
            rw [boundary_eq_sum_ite, ← Finset.add_sum_erase _ _ (Finset.mem_univ e₀)] at hb
            have hrest : ∑ e' ∈ Finset.univ.erase e₀,
                ((if G.head e' = G.head e₀ then f.val e' else 0) -
                 if G.tail e' = G.head e₀ then f.val e' else 0) =
                Gd.boundary (fun e' => f.val e'.1) (G.head e₀) := by
              rw [boundary_eq_sum_ite]
              refine Finset.sum_bij (fun e' he' => ⟨e', Finset.ne_of_mem_erase he'⟩)
                (fun _ _ => Finset.mem_univ _) (fun _ _ _ _ h => congrArg Subtype.val h)
                (fun e' _ => ⟨e'.1, Finset.mem_erase.mpr ⟨e'.2, Finset.mem_univ _⟩, rfl⟩)
                (fun _ _ => rfl)
            rw [hrest] at hb; simp [hne] at hb
            intro h0; rw [h0, add_zero] at hb; exact f.nonzero e₀ hb
          dsimp only
          rw [dif_neg hbd_ne]
          congr 1; ext e
          dsimp only [extVal]; split_ifs with h
          · rw [h]
            have hb := f.isFlow (G.head e₀)
            rw [boundary_eq_sum_ite, ← Finset.add_sum_erase _ _ (Finset.mem_univ e₀)] at hb
            have hrest : ∑ e' ∈ Finset.univ.erase e₀,
                ((if G.head e' = G.head e₀ then f.val e' else 0) -
                 if G.tail e' = G.head e₀ then f.val e' else 0) =
                Gd.boundary (fun e' => f.val e'.1) (G.head e₀) := by
              rw [boundary_eq_sum_ite]
              refine Finset.sum_bij (fun e' he' => ⟨e', Finset.ne_of_mem_erase he'⟩)
                (fun _ _ => Finset.mem_univ _) (fun _ _ _ _ h => congrArg Subtype.val h)
                (fun e' _ => ⟨e'.1, Finset.mem_erase.mpr ⟨e'.2, Finset.mem_univ _⟩, rfl⟩)
                (fun _ _ => rfl)
            rw [hrest] at hb; simp [hne] at hb
            exact (eq_neg_of_add_eq_zero_left hb).symm
          · rfl
        | inr f =>
          dsimp only
          rw [dif_pos (f.isFlow (G.head e₀))]
      right_inv := fun fc => by
        dsimp only
        by_cases h0 : Gd.boundary fc.val (G.head e₀) = 0
        · rw [dif_pos h0]
        · rw [dif_neg h0]; dsimp only; ext e; simp [extVal, e.2] }
  rw [← Fintype.card_sum, Fintype.card_congr eqv]

/-- **Tutte (1954):** For any finite multigraph `G`, the number of nowhere-zero `A`-flows
depends only on the order `|A|` of the finite abelian group `A`. -/
theorem tutte_nzflow_card_eq
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : Multigraph V E)
    {A₁ A₂ : Type} [AddCommGroup A₁] [Fintype A₁] [DecidableEq A₁]
    [AddCommGroup A₂] [Fintype A₂] [DecidableEq A₂]
    (hcard : Fintype.card A₁ = Fintype.card A₂) :
    Fintype.card (G.NZFlow A₁) = Fintype.card (G.NZFlow A₂) := by
  have hgen : ∀ m : ℕ,
      ∀ (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
        (G : Multigraph V E), Fintype.card E = m →
        Fintype.card (G.NZFlow A₁) = Fintype.card (G.NZFlow A₂) := by
    intro m
    induction m with
    | zero =>
      intro V E _ _ _ _ G hE
      have : IsEmpty E := Fintype.card_eq_zero_iff.mp hE
      rw [nzflow_card_empty G inferInstance, nzflow_card_empty G inferInstance]
    | succ m ih =>
      intro V E _ _ _ _ G hE
      have hneE : Nonempty E := Fintype.card_pos_iff.mp (by omega)
      obtain ⟨e₀⟩ := hneE
      have hcard_sub : Fintype.card {e : E // e ≠ e₀} = m := by
        rw [Fintype.card_subtype_compl, show Fintype.card {x : E // x = e₀} = 1 from Fintype.card_unique, hE]; omega
      by_cases hloop : G.tail e₀ = G.head e₀
      · rw [nzflow_card_loop G e₀ hloop, nzflow_card_loop G e₀ hloop, hcard,
            ih V _ (deleteEdge G e₀) hcard_sub]
      · have h1 := nzflow_card_nonloop (A := A₁) G e₀ hloop
        have h2 := nzflow_card_nonloop (A := A₂) G e₀ hloop
        have hdel := ih V _ (deleteEdge G e₀) hcard_sub
        have hcon := ih _ _ (G.contractEdge e₀ hloop) hcard_sub
        omega
  exact hgen (Fintype.card E) V E G rfl

/-- Reduction of `SeymourSixFlow` from arbitrary finite abelian groups `|A| ≥ 6` to `ZMod 6`. -/
theorem nzflow_of_zmod6
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : Multigraph V E)
    (A : Type) [AddCommGroup A] [Fintype A] [DecidableEq A]
    (hA : 6 ≤ Fintype.card A)
    (h6 : Nonempty (G.NZFlow (ZMod 6))) :
    Nonempty (G.NZFlow A) := by
  obtain ⟨f6⟩ := h6
  obtain ⟨F, hF_fl, _, hF_bd, hF_nz⟩ := cor_2_3 G (k := 6) (by decide) f6.val f6.isFlow
  let k := Fintype.card A
  have : NeZero k := ⟨by omega⟩
  have hfk_fl : G.IsFlow (fun e => (F e : ZMod k)) := fun v => by
    have hv := hF_fl v
    have hmap : ((G.boundary F v : ℤ) : ZMod k) = G.boundary (fun e => (F e : ZMod k)) v := by
      unfold Multigraph.boundary; push_cast; rfl
    rw [← hmap, hv, Int.cast_zero]
  have hfk_nz : Multigraph.IsNowhereZero (fun e => (F e : ZMod k)) := fun e h0 => by
    have hne0 : F e ≠ 0 := fun h => f6.nonzero e ((hF_nz e).mp h)
    have hbd5 : |F e| ≤ 5 := by simpa using hF_bd e
    have hdvd : (k : ℤ) ∣ F e := (ZMod.intCast_zmod_eq_zero_iff_dvd (F e) k).mp h0
    have hdvd_abs : (k : ℤ) ∣ |F e| := by
      rcases le_total 0 (F e) with h | h
      · rw [abs_of_nonneg h]; exact hdvd
      · rw [abs_of_nonpos h]; exact dvd_neg.mpr hdvd
    have hle : (k : ℤ) ≤ |F e| := Int.le_of_dvd (abs_pos.mpr hne0) hdvd_abs
    omega
  have hpos : 0 < Fintype.card (G.NZFlow (ZMod k)) :=
    Fintype.card_pos_iff.mpr ⟨⟨fun e => (F e : ZMod k), hfk_fl, hfk_nz⟩⟩
  have heq : Fintype.card (G.NZFlow (ZMod k)) = Fintype.card (G.NZFlow A) :=
    tutte_nzflow_card_eq G (by rw [ZMod.card])
  exact Fintype.card_pos_iff.mp (heq ▸ hpos)

end Flow.Proofs
