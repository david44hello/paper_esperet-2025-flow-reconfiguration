module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Flow.Defs.Basic
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.List.Nodup
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Section 2 proofs: flow algebra, reorientation, cycle extraction, and Lemma 2.1

This module establishes core multigraph flow properties, orientation-reversal equivalences,
cycle extraction (from no-degree-1 subgraphs, shortest paths in spanning forests, and
non-negative integer flows), and both parts of Lemma 2.1 (`lem_2_1_a` and `lem_2_1_b`).
-/

namespace Flow.Proofs

open Flow Multigraph

section FlowAlgebra

variable {V E Γ : Type} [Fintype E] [DecidableEq V] [AddCommGroup Γ]

lemma boundary_eq_sum_ite (G : Multigraph V E) (x : E → Γ) (v : V) :
    G.boundary x v =
      ∑ e : E, ((if G.head e = v then x e else 0) - (if G.tail e = v then x e else 0)) := by
  unfold Multigraph.boundary
  rw [Finset.sum_sub_distrib, ← Finset.sum_filter, ← Finset.sum_filter]

lemma boundary_zero (G : Multigraph V E) (v : V) :
    G.boundary (0 : E → Γ) v = 0 := by
  simp [Multigraph.boundary]

lemma boundary_add (G : Multigraph V E) (x y : E → Γ) (v : V) :
    G.boundary (fun e => x e + y e) v = G.boundary x v + G.boundary y v := by
  simp only [Multigraph.boundary, Finset.sum_add_distrib]
  abel

lemma boundary_sub (G : Multigraph V E) (x y : E → Γ) (v : V) :
    G.boundary (fun e => x e - y e) v = G.boundary x v - G.boundary y v := by
  simp only [Multigraph.boundary, Finset.sum_sub_distrib]
  abel

lemma boundary_neg (G : Multigraph V E) (x : E → Γ) (v : V) :
    G.boundary (fun e => -x e) v = -G.boundary x v := by
  simp only [Multigraph.boundary, Finset.sum_neg_distrib]
  abel

lemma boundary_zsmul (G : Multigraph V E) (x : E → ℤ) (lam : Γ) (v : V) :
    G.boundary (fun e => x e • lam) v = G.boundary x v • lam := by
  have hsum : ∀ s : Finset E, ∑ e ∈ s, x e • lam = (∑ e ∈ s, x e) • lam := fun s => by
    induction s using Finset.cons_induction with
    | empty => simp
    | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, ih, add_zsmul]
  unfold Multigraph.boundary
  rw [hsum, hsum, sub_zsmul]
  abel

lemma boundary_finset_sum {ι : Type*} (G : Multigraph V E) (s : Finset ι)
    (f : ι → E → Γ) (v : V) :
    G.boundary (fun e => ∑ i ∈ s, f i e) v = ∑ i ∈ s, G.boundary (f i) v := by
  simp only [Multigraph.boundary, Finset.sum_sub_distrib]
  rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ.filter (fun e => G.tail e = v))]

lemma boundary_list_sum {ι : Type*} (G : Multigraph V E) (l : List ι)
    (f : ι → E → Γ) (v : V) :
    G.boundary (fun e => (l.map (fun i => f i e)).sum) v =
      (l.map (fun i => G.boundary (f i) v)).sum := by
  induction l with
  | nil => simp [Multigraph.boundary]
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [boundary_add, ih]

lemma isFlow_zero (G : Multigraph V E) : G.IsFlow (0 : E → Γ) :=
  fun v => boundary_zero G v

lemma isFlow_add {G : Multigraph V E} {x y : E → Γ} (hx : G.IsFlow x) (hy : G.IsFlow y) :
    G.IsFlow (fun e => x e + y e) := by
  intro v; rw [boundary_add, hx v, hy v, add_zero]

lemma isFlow_sub {G : Multigraph V E} {x y : E → Γ} (hx : G.IsFlow x) (hy : G.IsFlow y) :
    G.IsFlow (fun e => x e - y e) := by
  intro v; rw [boundary_sub, hx v, hy v, sub_zero]

lemma isFlow_neg {G : Multigraph V E} {x : E → Γ} (hx : G.IsFlow x) :
    G.IsFlow (fun e => -x e) := by
  intro v; rw [boundary_neg, hx v, neg_zero]

lemma isFlow_zsmul {G : Multigraph V E} {x : E → ℤ} (hx : G.IsFlow x) (lam : Γ) :
    G.IsFlow (fun e => x e • lam) := by
  intro v; rw [boundary_zsmul, hx v, zero_zsmul]

lemma isFlow_finset_sum {ι : Type*} {G : Multigraph V E} (s : Finset ι) {f : ι → E → Γ}
    (hf : ∀ i ∈ s, G.IsFlow (f i)) :
    G.IsFlow (fun e => ∑ i ∈ s, f i e) := by
  intro v; rw [boundary_finset_sum]; exact Finset.sum_eq_zero (fun i hi => hf i hi v)

lemma isFlow_list_sum {ι : Type*} {G : Multigraph V E} (l : List ι) {f : ι → E → Γ}
    (hf : ∀ i ∈ l, G.IsFlow (f i)) :
    G.IsFlow (fun e => (l.map (fun i => f i e)).sum) := by
  intro v
  rw [boundary_list_sum]
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [hf a (by simp) v, zero_add]
    exact ih (fun i hi => hf i (by simp [hi]))

/-- Summing boundary over a vertex set `S` leaves only edges crossing `(S, V \ S)`. -/
lemma sum_boundary_eq_cut (G : Multigraph V E) (x : E → Γ) (S : Finset V) :
    ∑ v ∈ S, G.boundary x v =
      (∑ e ∈ Finset.univ.filter (fun e => G.head e ∈ S ∧ G.tail e ∉ S), x e) -
      (∑ e ∈ Finset.univ.filter (fun e => G.tail e ∈ S ∧ G.head e ∉ S), x e) := by
  have h1 : ∑ v ∈ S, G.boundary x v =
      ∑ e : E, ((if G.head e ∈ S then x e else 0) - (if G.tail e ∈ S then x e else 0)) := by
    simp_rw [boundary_eq_sum_ite]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq]
  rw [h1, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  by_cases hh : G.head e ∈ S <;> by_cases ht : G.tail e ∈ S <;> simp [hh, ht]

end FlowAlgebra

section Reorientation

variable {V E Γ : Type}

@[simp]
lemma reorient_reorient (G : Multigraph V E) (flip : E → Bool) :
    (G.reorient flip).reorient flip = G := by
  cases G with
  | mk tail head =>
    simp only [Multigraph.reorient]
    congr 1 <;> funext e <;> cases flip e <;> rfl

@[simp]
lemma reorientVal_reorientVal [AddCommGroup Γ] (flip : E → Bool) (x : E → Γ) (e : E) :
    Multigraph.reorientVal flip (Multigraph.reorientVal flip x) e = x e := by
  unfold Multigraph.reorientVal
  cases flip e <;> simp

lemma reorient_boundary [Fintype E] [DecidableEq V] [AddCommGroup Γ]
    (G : Multigraph V E) (flip : E → Bool) (x : E → Γ) (v : V) :
    (G.reorient flip).boundary (Multigraph.reorientVal flip x) v = G.boundary x v := by
  rw [boundary_eq_sum_ite, boundary_eq_sum_ite]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  unfold Multigraph.reorient Multigraph.reorientVal
  cases hfl : flip e
  · simp [hfl]
  · simp only [hfl, ↓reduceIte]
    by_cases h1 : G.tail e = v <;> by_cases h2 : G.head e = v <;> simp [h1, h2] <;> abel

lemma reorient_isFlow_iff [Fintype E] [DecidableEq V] [AddCommGroup Γ]
    (G : Multigraph V E) (flip : E → Bool) (x : E → Γ) :
    (G.reorient flip).IsFlow (Multigraph.reorientVal flip x) ↔ G.IsFlow x := by
  simp only [Multigraph.IsFlow, reorient_boundary]

/-- Transport a subgraph across edge reorientation. -/
def reorientSubgraph (G : Multigraph V E) (flip : E → Bool) (H : G.Subgraph) :
    (G.reorient flip).Subgraph where
  verts := H.verts
  edges := H.edges
  tail_mem {e} he := by
    dsimp only [Multigraph.reorient]
    cases flip e
    · exact H.tail_mem he
    · exact H.head_mem he
  head_mem {e} he := by
    dsimp only [Multigraph.reorient]
    cases flip e
    · exact H.head_mem he
    · exact H.tail_mem he

lemma reorientSubgraph_deg [DecidableEq V] (G : Multigraph V E) (flip : E → Bool)
    (H : G.Subgraph) (v : V) :
    (reorientSubgraph G flip H).deg v = H.deg v := by
  unfold Subgraph.deg reorientSubgraph Multigraph.reorient
  simp only
  have hsum : ∀ (f g : E → ℕ), (∑ e ∈ H.edges, f e) + (∑ e ∈ H.edges, g e) =
      ∑ e ∈ H.edges, (f e + g e) := fun _ _ => (Finset.sum_add_distrib).symm
  simp only [Finset.card_filter]
  rw [hsum, hsum]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  cases flip e <;> simp [Nat.add_comm]

lemma reorientSubgraph_adj (G : Multigraph V E) (flip : E → Bool) (H : G.Subgraph) (u v : V) :
    (reorientSubgraph G flip H).Adj u v ↔ H.Adj u v := by
  unfold Subgraph.Adj reorientSubgraph Multigraph.reorient
  simp only
  constructor <;> rintro ⟨e, he, h⟩ <;> refine ⟨e, he, ?_⟩ <;> cases hfl : flip e <;>
    simp [hfl] at h ⊢ <;> tauto

lemma reorientSubgraph_connected (G : Multigraph V E) (flip : E → Bool) (H : G.Subgraph) :
    (reorientSubgraph G flip H).Connected ↔ H.Connected := by
  unfold Subgraph.Connected
  have hadj : (reorientSubgraph G flip H).Adj = H.Adj := by
    funext u v; exact propext (reorientSubgraph_adj G flip H u v)
  rw [hadj]; rfl

lemma reorientSubgraph_isCycle [DecidableEq V] (G : Multigraph V E) (flip : E → Bool)
    (H : G.Subgraph) :
    (reorientSubgraph G flip H).IsCycle ↔ H.IsCycle := by
  unfold Subgraph.IsCycle
  rw [reorientSubgraph_connected]
  simp only [reorientSubgraph_deg]; rfl

/-- Transport a directed cycle across edge reorientation. -/
def reorientDirectedCycle [Fintype E] [DecidableEq V] (G : Multigraph V E) (flip : E → Bool)
    (C : G.DirectedCycle) : (G.reorient flip).DirectedCycle where
  sub := reorientSubgraph G flip C.sub
  isCycle := (reorientSubgraph_isCycle G flip C.sub).mpr C.isCycle
  sign := Multigraph.reorientVal flip C.sign
  sign_mem {e} he := by
    unfold Multigraph.reorientVal
    rcases C.sign_mem he with h | h <;> cases flip e <;> simp [h]
  sign_zero {e} he := by
    unfold Multigraph.reorientVal
    simp [C.sign_zero he]
  isFlow := (reorient_isFlow_iff G flip C.sign).mpr C.isFlow

end Reorientation

section CycleBuilders

variable {V E : Type} [Fintype E] [DecidableEq V] [DecidableEq E]

/-- Construct a directed 1-cycle from a loop `e`. -/
def directedCycleOfLoop (G : Multigraph V E) (e : E) (hloop : G.tail e = G.head e) :
    G.DirectedCycle where
  sub :=
    { verts := {G.tail e}
      edges := {e}
      tail_mem := fun he => by simp [Finset.mem_singleton.mp he]
      head_mem := fun he => by simp [Finset.mem_singleton.mp he, hloop] }
  isCycle := by
    refine ⟨⟨⟨G.tail e, by simp⟩, fun u hu v hv => ?_⟩, fun v hv => ?_⟩
    · simp only [Finset.mem_singleton] at hu hv; subst hu; subst hv; exact Relation.ReflTransGen.refl
    · simp only [Finset.mem_singleton] at hv; subst hv
      simp [Subgraph.deg, Finset.filter_singleton, hloop.symm]
  sign := fun e' => if e' = e then 1 else 0
  sign_mem := fun he => by simp [Finset.mem_singleton.mp he]
  sign_zero := fun {e'} he => by
    have hne : e' ≠ e := fun h => he (by simp [h])
    simp [hne]
  isFlow := fun v => by
    unfold Multigraph.boundary
    simp [Finset.sum_ite_eq', hloop]

/-- Helper: given a nodup vertex list of length `n ≥ 2` and a nodup edge list of length `n`
forming a simple closed walk `verts[i] --edges[i]--> verts[(i+1)%n]`, build a `DirectedCycle`
whose indicator is `+1` on forward edges and `-1` on backward edges along the walk. -/
def directedCycleOfSimpleClosedWalk (G : Multigraph V E)
    (verts : List V) (edges : List E)
    (hn : 2 ≤ verts.length)
    (hlen : edges.length = verts.length)
    (hv_nodup : verts.Nodup)
    (he_nodup : edges.Nodup)
    (hstep : ∀ (i : ℕ) (hi : i < edges.length),
      let u := verts[i]'(by omega)
      let w := verts[(i + 1) % verts.length]'(Nat.mod_lt _ (by omega))
      let e := edges[i]'hi
      (G.tail e = u ∧ G.head e = w) ∨ (G.tail e = w ∧ G.head e = u)) :
    G.DirectedCycle := by
  let n := verts.length
  have hn_pos : 0 < n := by omega
  -- Helper: orientation sign on edge `e`
  let signFn : E → ℤ := fun e =>
    if h : e ∈ edges then
      let i := edges.idxOf e
      have hi : i < edges.length := List.idxOf_lt_length_of_mem h
      if G.tail e = verts[i]'(by omega) ∧ G.head e = verts[(i + 1) % n]'(Nat.mod_lt _ hn_pos)
      then 1 else -1
    else 0
  have hstep_idx : ∀ (i : ℕ) (hi : i < edges.length),
      let u := verts[i]'(by omega)
      let w := verts[(i + 1) % n]'(Nat.mod_lt _ hn_pos)
      let e := edges[i]'hi
      u ≠ w ∧ ((G.tail e = u ∧ G.head e = w) ∨ (G.tail e = w ∧ G.head e = u)) := by
    intro i hi
    refine ⟨?_, hstep i hi⟩
    intro heq
    have hidx := (List.Nodup.getElem_inj_iff hv_nodup).mp heq
    by_cases hlt : i + 1 < n
    · rw [Nat.mod_eq_of_lt hlt] at hidx; omega
    · have hi1 : i + 1 = n := by omega
      rw [hi1, Nat.mod_self] at hidx; omega
  have hsign_at : ∀ (i : ℕ) (hi : i < edges.length),
      let u := verts[i]'(by omega)
      let w := verts[(i + 1) % n]'(Nat.mod_lt _ hn_pos)
      let e := edges[i]'hi
      (G.tail e = u ∧ G.head e = w ∧ signFn e = 1) ∨
      (G.tail e = w ∧ G.head e = u ∧ signFn e = -1) := by
    intro i hi
    have hmem : edges[i]'hi ∈ edges := List.getElem_mem hi
    have hidx : edges.idxOf (edges[i]'hi) = i := List.Nodup.idxOf_getElem he_nodup i hi
    rcases hstep_idx i hi with ⟨hne, ⟨ht, hh⟩ | ⟨ht, hh⟩⟩
    · left
      refine ⟨ht, hh, ?_⟩
      simp only [signFn, hmem, ↓reduceDIte, hidx, ht, hh, and_self, ↓reduceIte]
    · right
      refine ⟨ht, hh, ?_⟩
      have hnot : ¬ (G.tail (edges[i]'hi) = verts[i]'(by omega) ∧
          G.head (edges[i]'hi) = verts[(i + 1) % n]'(Nat.mod_lt _ hn_pos)) := by
        intro ⟨h1, _⟩; exact hne (ht.symm.trans h1).symm
      simp only [signFn, hmem, ↓reduceDIte, hidx, hnot, ↓reduceIte]
  let subG : G.Subgraph :=
    { verts := verts.toFinset
      edges := edges.toFinset
      tail_mem := fun {e} he => by
        rw [List.mem_toFinset] at he ⊢
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
        rcases hstep i hi with ⟨ht, _⟩ | ⟨ht, _⟩ <;> rw [ht] <;> exact List.getElem_mem _
      head_mem := fun {e} he => by
        rw [List.mem_toFinset] at he ⊢
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
        rcases hstep i hi with ⟨_, hh⟩ | ⟨_, hh⟩ <;> rw [hh] <;> exact List.getElem_mem _ }
  -- Characterize edges incident to `verts[k]`
  have hpred_idx : ∀ (k : ℕ) (hk : k < n),
      let p := (k + n - 1) % n
      p < edges.length ∧ p ≠ k ∧ (p + 1) % verts.length = k := by
    intro k hk
    have hp : (k + n - 1) % n < n := Nat.mod_lt _ hn_pos
    refine ⟨by omega, ?_, ?_⟩
    · by_cases hk0 : k = 0
      · subst hk0; simp only [zero_add]
        rw [Nat.mod_eq_of_lt (by omega)]; omega
      · have hkn : k + n - 1 = (k - 1) + n := by omega
        rw [hkn, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega
    · change (((k + n - 1) % n + 1) % n) = k
      by_cases hk0 : k = 0
      · subst hk0; simp only [zero_add]
        have hlt1 : n - 1 < n := by omega
        rw [Nat.mod_eq_of_lt hlt1]
        have h1 : n - 1 + 1 = n := by omega
        rw [h1, Nat.mod_self]
      · have hkn : k + n - 1 = (k - 1) + n := by omega
        have hlt1 : k - 1 < n := by omega
        rw [hkn, Nat.add_mod_right, Nat.mod_eq_of_lt hlt1]
        have h1 : k - 1 + 1 = k := by omega
        rw [h1, Nat.mod_eq_of_lt hk]
  have hinc_unique : ∀ (k : ℕ) (hk : k < n) (e : E),
      e ∈ edges →
      ((G.tail e = verts[k]'hk ∨ G.head e = verts[k]'hk) ↔
        e = edges[k]'(by omega) ∨ e = edges[(k + n - 1) % n]'(hpred_idx k hk).1) := by
    intro k hk e he
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
    obtain ⟨hp_lt, hp_ne, hp_succ⟩ := hpred_idx k hk
    constructor
    · intro hinc
      have hmem_pair : verts[k]'hk = verts[i]'(by omega) ∨
          verts[k]'hk = verts[(i + 1) % n]'(Nat.mod_lt _ hn_pos) := by
        rcases hstep i hi with ⟨ht, hh⟩ | ⟨ht, hh⟩ <;> rcases hinc with h1 | h1
        · left; exact h1.symm.trans ht
        · right; exact h1.symm.trans hh
        · right; exact h1.symm.trans ht
        · left; exact h1.symm.trans hh
      rcases hmem_pair with heq | heq
      · have hik : k = i := (List.Nodup.getElem_inj_iff hv_nodup).mp heq
        left; congr 1; exact hik.symm
      · have hik : k = (i + 1) % n := (List.Nodup.getElem_inj_iff hv_nodup).mp heq
        right
        have hip : i = (k + n - 1) % n := by
          by_cases hlt : i + 1 < n
          · rw [Nat.mod_eq_of_lt hlt] at hik
            have : k + n - 1 = i + n := by omega
            rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          · have hi1 : i + 1 = n := by omega
            rw [hi1, Nat.mod_self] at hik
            subst hik; simp only [zero_add]
            rw [Nat.mod_eq_of_lt (by omega)]; omega
        congr 1
    · rintro (heq | heq)
      · have hik : i = k := (List.Nodup.getElem_inj_iff he_nodup).mp heq
        subst hik
        rcases hstep i hi with ⟨ht, hh⟩ | ⟨ht, hh⟩
        · left; exact ht
        · right; exact hh
      · have hip : i = (k + n - 1) % n := (List.Nodup.getElem_inj_iff he_nodup).mp heq
        subst hip
        rcases hstep ((k + n - 1) % n) hp_lt with ⟨ht, hh⟩ | ⟨ht, hh⟩
        · right; simpa only [hp_succ] using hh
        · left; simpa only [hp_succ] using ht
  -- Exact degree and boundary contribution of each edge
  refine
    { sub := subG
      isCycle := ?_
      sign := signFn
      sign_mem := fun {e} he => by
        rw [List.mem_toFinset] at he
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
        rcases hsign_at i hi with ⟨_, _, hs⟩ | ⟨_, _, hs⟩
        · left; exact hs
        · right; exact hs
      sign_zero := fun {e} he => by
        rw [List.mem_toFinset] at he
        simp [signFn, he]
      isFlow := ?_ }
  · -- subG.IsCycle
    refine ⟨⟨⟨verts[0]'hn_pos, List.mem_toFinset.mpr (List.getElem_mem hn_pos)⟩, ?_⟩, ?_⟩
    · -- Connected: every verts[k] is reachable from verts[0]
      have hreach : ∀ (k : ℕ) (hk : k < n),
          Relation.ReflTransGen subG.Adj (verts[0]'hn_pos) (verts[k]'hk) := by
        intro k
        induction k with
        | zero => intro _; exact Relation.ReflTransGen.refl
        | succ k ih =>
          intro hk
          have hk' : k < n := by omega
          refine Relation.ReflTransGen.tail (ih hk') ?_
          refine ⟨edges[k]'(by omega), List.mem_toFinset.mpr (List.getElem_mem _), ?_⟩
          have hmod : (k + 1) % verts.length = k + 1 := Nat.mod_eq_of_lt hk
          simpa only [hmod] using hstep k (by omega)
      have hsymm : ∀ {a b : V}, Relation.ReflTransGen subG.Adj a b →
          Relation.ReflTransGen subG.Adj b a := by
        intro a b hab
        induction hab with
        | refl => exact Relation.ReflTransGen.refl
        | tail _ hstep' ih =>
          rcases hstep' with ⟨e, he, h | h⟩
          · exact Relation.ReflTransGen.head ⟨e, he, Or.inr h⟩ ih
          · exact Relation.ReflTransGen.head ⟨e, he, Or.inl h⟩ ih
      intro u hu v hv
      rw [List.mem_toFinset] at hu hv
      obtain ⟨ku, hku, rfl⟩ := List.getElem_of_mem hu
      obtain ⟨kv, hkv, rfl⟩ := List.getElem_of_mem hv
      exact Relation.ReflTransGen.trans (hsymm (hreach ku hku)) (hreach kv hkv)
    · -- 2-regular: deg v = 2 for all v ∈ verts.toFinset
      intro v hv
      rw [List.mem_toFinset] at hv
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hv
      obtain ⟨hp_lt, hp_ne, hp_succ⟩ := hpred_idx k hk
      let ek := edges[k]'(by omega)
      let ep := edges[(k + n - 1) % n]'hp_lt
      have hek_ne_ep : ek ≠ ep := by
        intro h; exact hp_ne ((List.Nodup.getElem_inj_iff he_nodup).mp h).symm
      -- Rewrite deg as sum of (ite (tail e = v) 1 0 + ite (head e = v) 1 0) over edges.toFinset
      unfold Subgraph.deg
      simp only [Finset.card_filter, subG]
      rw [← Finset.sum_add_distrib]
      have hpair : ({ek, ep} : Finset E) ⊆ edges.toFinset := by
        intro e he
        simp only [Finset.mem_insert, Finset.mem_singleton] at he
        rw [List.mem_toFinset]
        rcases he with rfl | rfl <;> exact List.getElem_mem _
      rw [← Finset.sum_subset hpair]
      · rw [Finset.sum_pair hek_ne_ep]
        have h1 : (if G.tail ek = verts[k]'hk then 1 else 0) +
            (if G.head ek = verts[k]'hk then 1 else 0) = 1 := by
          rcases hstep_idx k (by omega) with ⟨hne, ⟨ht, hh⟩ | ⟨ht, hh⟩⟩
          · simp [ek, ht, hh, hne.symm]
          · simp [ek, ht, hh, hne.symm]
        have h2 : (if G.tail ep = verts[k]'hk then 1 else 0) +
            (if G.head ep = verts[k]'hk then 1 else 0) = 1 := by
          rcases hstep_idx ((k + n - 1) % n) hp_lt with ⟨hne, ⟨ht, hh⟩ | ⟨ht, hh⟩⟩
          · dsimp only [ep, n] at hp_succ hne ht hh ⊢; simp only [hp_succ] at hne ht hh
            simp [ht, hh, hne]
          · dsimp only [ep, n] at hp_succ hne ht hh ⊢; simp only [hp_succ] at hne ht hh
            simp [ht, hh, hne]
        omega
      · intro e he hnot
        have hnot' : ¬ (G.tail e = verts[k]'hk ∨ G.head e = verts[k]'hk) := by
          rw [hinc_unique k hk e (List.mem_toFinset.mp he)]
          simpa [Finset.mem_insert, Finset.mem_singleton, ek, ep] using hnot
        push_neg at hnot'
        simp [hnot'.1, hnot'.2]
  · -- G.IsFlow signFn
    intro v
    rw [boundary_eq_sum_ite]
    by_cases hv : v ∈ verts
    · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hv
      obtain ⟨hp_lt, hp_ne, hp_succ⟩ := hpred_idx k hk
      let ek := edges[k]'(by omega)
      let ep := edges[(k + n - 1) % n]'hp_lt
      have hek_ne_ep : ek ≠ ep := by
        intro h; exact hp_ne ((List.Nodup.getElem_inj_iff he_nodup).mp h).symm
      rw [← Finset.sum_subset (Finset.subset_univ ({ek, ep} : Finset E))]
      · rw [Finset.sum_pair hek_ne_ep]
        have h1 : (if G.head ek = verts[k]'hk then signFn ek else 0) -
            (if G.tail ek = verts[k]'hk then signFn ek else 0) = -1 := by
          have hne := (hstep_idx k (by omega)).1
          rcases hsign_at k (by omega) with ⟨ht, hh, hs⟩ | ⟨ht, hh, hs⟩
          · simp [ek, ht, hh, hs, hne.symm]
          · simp [ek, ht, hh, hs, hne.symm]
        have h2 : (if G.head ep = verts[k]'hk then signFn ep else 0) -
            (if G.tail ep = verts[k]'hk then signFn ep else 0) = 1 := by
          have hne := (hstep_idx ((k + n - 1) % n) hp_lt).1
          rcases hsign_at ((k + n - 1) % n) hp_lt with ⟨ht, hh, hs⟩ | ⟨ht, hh, hs⟩
          · dsimp only [ep, n] at hp_succ hne ht hh hs ⊢; simp only [hp_succ] at hne ht hh
            simp [ht, hh, hs, hne]
          · dsimp only [ep, n] at hp_succ hne ht hh hs ⊢; simp only [hp_succ] at hne ht hh
            simp [ht, hh, hs, hne]
        omega
      · intro e _ hnot
        by_cases he : e ∈ edges
        · have hnot' : ¬ (G.tail e = verts[k]'hk ∨ G.head e = verts[k]'hk) := by
            rw [hinc_unique k hk e he]
            simpa [Finset.mem_insert, Finset.mem_singleton, ek, ep] using hnot
          push_neg at hnot'
          simp [hnot'.1, hnot'.2]
        · simp [signFn, he]
    · refine Finset.sum_eq_zero (fun e _ => ?_)
      by_cases he : e ∈ edges
      · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
        have ht : G.tail (edges[i]'hi) ≠ v := by
          intro h
          rcases hstep i hi with ⟨h1, _⟩ | ⟨h1, _⟩ <;> exact hv (h ▸ h1 ▸ List.getElem_mem _)
        have hh : G.head (edges[i]'hi) ≠ v := by
          intro h
          rcases hstep i hi with ⟨_, h1⟩ | ⟨_, h1⟩ <;> exact hv (h ▸ h1 ▸ List.getElem_mem _)
        simp [ht, hh]
      · simp [signFn, he]

/-- Helper: extract a simple path (nodup vertices) from a `ReflTransGen H.Adj u v` walk. -/
lemma exists_simplePath_of_reflTransGen {G : Multigraph V E} {H : G.Subgraph}
    {u v : V} (h : Relation.ReflTransGen H.Adj u v) :
    ∃ (verts : List V) (edges : List E) (_ : verts.length = edges.length + 1),
      verts.Nodup ∧
      verts.head? = some u ∧
      verts.getLast? = some v ∧
      (∀ e ∈ edges, e ∈ H.edges) ∧
      (∀ (i : ℕ) (hi : i < edges.length),
        let a := verts[i]'(by omega)
        let b := verts[i + 1]'(by omega)
        let e := edges[i]'hi
        (G.tail e = a ∧ G.head e = b) ∨ (G.tail e = b ∧ G.head e = a)) := by
  induction h with
  | refl =>
    exact ⟨[u], [], rfl, List.nodup_singleton u, rfl, rfl, by simp, fun i hi => by simp at hi⟩
  | @tail b c _ hbc ih =>
    rcases ih with ⟨verts, edges, hlen, hnodup, hhead, hlast, hedges, hstep⟩
    rcases hbc with ⟨e, heH, hab⟩
    by_cases hc : c ∈ verts
    · -- Short-circuit the path at the first occurrence of `c`
      let idx := verts.idxOf c
      have hidx_lt : idx < verts.length := List.idxOf_lt_length_of_mem hc
      have hvc : verts[idx]'hidx_lt = c := List.getElem_idxOf hidx_lt
      refine ⟨verts.take (idx + 1), edges.take idx, by simp [List.length_take]; omega, ?_, ?_, ?_, ?_, ?_⟩
      · exact hnodup.take
      · cases verts with
        | nil => simp at hhead
        | cons x xs => simpa using hhead
      · rw [List.getLast?_eq_getElem?]
        simp only [List.length_take, Nat.min_eq_left (by omega : idx + 1 ≤ verts.length),
          Nat.add_sub_cancel, List.getElem?_take_of_lt (by omega : idx < idx + 1)]
        rw [List.getElem?_eq_getElem hidx_lt, hvc]
      · intro e' he'; exact hedges e' (List.mem_of_mem_take he')
      · intro i hi
        have hi_lt : i < idx := by rw [List.length_take] at hi; omega
        have hi_e : i < edges.length := by omega
        simp only [List.getElem_take]
        exact hstep i hi_e
    · -- Append `c` and `e`
      refine ⟨verts ++ [c], edges ++ [e], by simp [hlen], ?_, ?_, ?_, ?_, ?_⟩
      · rw [List.nodup_append]
        refine ⟨hnodup, List.nodup_singleton c, fun x hx y hy heq => ?_⟩
        simp only [List.mem_singleton] at hy; subst hy; subst heq; exact hc hx
      · cases verts with
        | nil => simp at hhead
        | cons x xs => simpa using hhead
      · simp
      · intro e' he'
        simp only [List.mem_append, List.mem_singleton] at he'
        rcases he' with h1 | rfl
        · exact hedges e' h1
        · exact heH
      · intro i hi
        simp only [List.length_append, List.length_singleton] at hi
        by_cases hlt : i < edges.length
        · have h1 : (verts ++ [c])[i]'(by simp; omega) = verts[i]'(by omega) :=
            List.getElem_append_left (by omega)
          have h2 : (verts ++ [c])[i + 1]'(by simp; omega) = verts[i + 1]'(by omega) :=
            List.getElem_append_left (by omega)
          have h3 : (edges ++ [e])[i]'(by simp; omega) = edges[i]'hlt :=
            List.getElem_append_left hlt
          simpa only [h1, h2, h3] using hstep i hlt
        · have hi_eq : i = edges.length := by omega
          subst hi_eq
          have hv_pos : 0 < verts.length := by omega
          have hlast_eq : verts[edges.length]'(by omega) = b := by
            rw [List.getLast?_eq_getElem?] at hlast
            have hidx : verts.length - 1 = edges.length := by omega
            rw [hidx, List.getElem?_eq_getElem (by omega)] at hlast
            exact Option.some.inj hlast
          have h1 : (verts ++ [c])[edges.length]'(by simp; omega) = b := by
            rw [List.getElem_append_left (by omega), hlast_eq]
          have h2 : (verts ++ [c])[edges.length + 1]'(by simp; omega) = c := by
            have : edges.length + 1 = verts.length := by omega
            simp [this]
          have h3 : (edges ++ [e])[edges.length]'(by simp) = e := by simp
          simpa only [h1, h2, h3] using hab

/-- In a simple path of a loopless subgraph, all edges are pairwise distinct. -/
lemma simplePath_edges_nodup {G : Multigraph V E} {verts : List V} {edges : List E}
    (hv_nodup : verts.Nodup) (hlen : verts.length = edges.length + 1)
    (hstep : ∀ (i : ℕ) (hi : i < edges.length),
      let a := verts[i]'(by omega)
      let b := verts[i + 1]'(by omega)
      let e := edges[i]'hi
      (G.tail e = a ∧ G.head e = b) ∨ (G.tail e = b ∧ G.head e = a)) :
    edges.Nodup := by
  rw [List.nodup_iff_injective_getElem]
  intro ⟨i, hi⟩ ⟨j, hj⟩ heq
  simp only at heq
  suffices i = j by exact Fin.ext this
  have h1 := hstep i hi
  have h2 := hstep j hj
  rw [← heq] at h2
  -- Endpoints of `edges[i]` are `{verts[i], verts[i+1]}` and `{verts[j], verts[j+1]}`
  have hsets : (verts[i]'(by omega) = verts[j]'(by omega) ∧
      verts[i + 1]'(by omega) = verts[j + 1]'(by omega)) ∨
      (verts[i]'(by omega) = verts[j + 1]'(by omega) ∧
      verts[i + 1]'(by omega) = verts[j]'(by omega)) := by
    rcases h1 with ⟨ht1, hh1⟩ | ⟨ht1, hh1⟩ <;> rcases h2 with ⟨ht2, hh2⟩ | ⟨ht2, hh2⟩
    · left; exact ⟨ht1.symm.trans ht2, hh1.symm.trans hh2⟩
    · right; exact ⟨ht1.symm.trans ht2, hh1.symm.trans hh2⟩
    · right; exact ⟨hh1.symm.trans hh2, ht1.symm.trans ht2⟩
    · left; exact ⟨hh1.symm.trans hh2, ht1.symm.trans ht2⟩
  rcases hsets with ⟨ha, _⟩ | ⟨ha, hb⟩
  · exact (List.Nodup.getElem_inj_iff hv_nodup).mp ha
  · have h1' := (List.Nodup.getElem_inj_iff hv_nodup).mp ha
    have h2' := (List.Nodup.getElem_inj_iff hv_nodup).mp hb
    omega

/-- Any subgraph with at least one edge and no vertex of degree `1` contains a directed cycle. -/
lemma exists_directedCycle_of_no_deg_one [Fintype V] {G : Multigraph V E} (H : G.Subgraph)
    (hne : H.edges.Nonempty) (hdeg : ∀ v ∈ H.verts, H.deg v ≠ 1) :
    ∃ C : G.DirectedCycle, C.sub ≤ H := by
  -- First check if H has a loop
  by_cases hloop : ∃ e ∈ H.edges, G.tail e = G.head e
  · rcases hloop with ⟨e, heH, hl⟩
    refine ⟨directedCycleOfLoop G e hl, ?_⟩
    constructor
    · intro v hv; simp only [directedCycleOfLoop, Finset.mem_singleton] at hv
      subst hv; exact H.tail_mem heH
    · intro e' he'; simp only [directedCycleOfLoop, Finset.mem_singleton] at he'
      subst he'; exact heH
  · push_neg at hloop
    -- No loops in H; define simple paths of length ≥ 1 in H
    let IsPath (k : ℕ) : Prop :=
      1 ≤ k ∧ ∃ (verts : List V) (edges : List E) (_ : verts.length = k + 1) (_ : edges.length = k),
        verts.Nodup ∧
        (∀ e ∈ edges, e ∈ H.edges) ∧
        (∀ (i : ℕ) (hi : i < k),
          let a := verts[i]'(by omega)
          let b := verts[i + 1]'(by omega)
          let e := edges[i]'(by omega)
          (G.tail e = a ∧ G.head e = b) ∨ (G.tail e = b ∧ G.head e = a))
    have hex1 : IsPath 1 := by
      rcases hne with ⟨e₀, he₀⟩
      refine ⟨le_rfl, [G.tail e₀, G.head e₀], [e₀], rfl, rfl, ?_, ?_, ?_⟩
      · simp [hloop e₀ he₀]
      · simp [he₀]
      · intro i hi
        have hi0 : i = 0 := by omega
        subst hi0; left; exact ⟨rfl, rfl⟩
    have hbdd : ∀ k, IsPath k → k ≤ Fintype.card V := by
      intro k ⟨_, verts, _, hlen, _, hnodup, _, _⟩
      have hle := hnodup.length_le_card
      omega
    -- Take maximal k with IsPath k
    classical
    let S := (Finset.range (Fintype.card V + 1)).filter (fun k => IsPath k)
    have hS_ne : S.Nonempty := by
      refine ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hex1⟩⟩
      have := hbdd 1 hex1; omega
    let k := S.max' hS_ne
    have hk_mem : k ∈ S := Finset.max'_mem S hS_ne
    have hk_path : IsPath k := (Finset.mem_filter.mp hk_mem).2
    have hk_max : ∀ k', IsPath k' → k' ≤ k := by
      intro k' hk'
      apply Finset.le_max' S k'
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := hbdd k' hk'; omega), hk'⟩
    rcases hk_path with ⟨hk_pos, verts, edges, hv_len, he_len, hv_nodup, he_sub, hstep⟩
    have he_nodup : edges.Nodup :=
      simplePath_edges_nodup hv_nodup (by omega) (fun i hi => hstep i (by omega))
    -- Look at last vertex `vk = verts[k]` and last edge `elast = edges[k-1]`
    let vk := verts[k]'(by omega)
    let elast := edges[k - 1]'(by omega)
    have helast_mem : elast ∈ H.edges := he_sub elast (List.getElem_mem _)
    have hvk_mem : vk ∈ H.verts := by
      rcases hstep (k - 1) (by omega) with ⟨_, hh⟩ | ⟨ht, _⟩
      · have h1 : k - 1 + 1 = k := by omega
        have hh' : G.head elast = vk := by simpa only [h1] using hh
        rw [← hh']; exact H.head_mem helast_mem
      · have h1 : k - 1 + 1 = k := by omega
        have ht' : G.tail elast = vk := by simpa only [h1] using ht
        rw [← ht']; exact H.tail_mem helast_mem
    -- Show `vk` has another incident edge `e' ≠ elast` in `H.edges`
    have hvk_deg_ge2 : 2 ≤ H.deg vk := by
      have hne1 := hdeg vk hvk_mem
      have hpos : 1 ≤ H.deg vk := by
        unfold Subgraph.deg
        rcases hstep (k - 1) (by omega) with ⟨_, hh⟩ | ⟨ht, _⟩
        · have h1 : k - 1 + 1 = k := by omega
          have hh' : G.head elast = vk := by simpa only [h1] using hh
          have : 1 ≤ (H.edges.filter (fun e => G.head e = vk)).card :=
            Finset.card_pos.mpr ⟨elast, Finset.mem_filter.mpr ⟨helast_mem, hh'⟩⟩
          omega
        · have h1 : k - 1 + 1 = k := by omega
          have ht' : G.tail elast = vk := by simpa only [h1] using ht
          have : 1 ≤ (H.edges.filter (fun e => G.tail e = vk)).card :=
            Finset.card_pos.mpr ⟨elast, Finset.mem_filter.mpr ⟨helast_mem, ht'⟩⟩
          omega
      omega
    have hex_other : ∃ e' ∈ H.edges, e' ≠ elast ∧ (G.tail e' = vk ∨ G.head e' = vk) := by
      by_contra hall
      push_neg at hall
      have hsub_t : H.edges.filter (fun e => G.tail e = vk) ⊆ {elast} := by
        intro e he
        rw [Finset.mem_filter] at he
        by_contra hne'
        exact (hall e he.1 (by simpa using hne')).1 he.2
      have hsub_h : H.edges.filter (fun e => G.head e = vk) ⊆ {elast} := by
        intro e he
        rw [Finset.mem_filter] at he
        by_contra hne'
        exact (hall e he.1 (by simpa using hne')).2 he.2
      -- Since `elast` is not a loop, it cannot be in both filters!
      have hdisj : Disjoint (H.edges.filter (fun e => G.tail e = vk))
          (H.edges.filter (fun e => G.head e = vk)) := by
        rw [Finset.disjoint_left]
        intro e ht hh
        rw [Finset.mem_filter] at ht hh
        exact hloop e ht.1 (ht.2.trans hh.2.symm)
      have hunion : (H.edges.filter (fun e => G.tail e = vk) ∪
          H.edges.filter (fun e => G.head e = vk)) ⊆ {elast} :=
        Finset.union_subset hsub_t hsub_h
      have hcard : H.deg vk ≤ 1 := by
        unfold Subgraph.deg
        rw [← Finset.card_union_of_disjoint hdisj]
        exact le_trans (Finset.card_le_card hunion) (by simp)
      omega
    rcases hex_other with ⟨e', he'_mem, he'_ne, he'_inc⟩
    -- Let `w` be the other endpoint of `e'`
    let w := if G.tail e' = vk then G.head e' else G.tail e'
    have he'_conn : (G.tail e' = vk ∧ G.head e' = w) ∨ (G.tail e' = w ∧ G.head e' = vk) := by
      by_cases ht : G.tail e' = vk
      · left; exact ⟨ht, by simp [w, ht]⟩
      · right
        have hh : G.head e' = vk := he'_inc.resolve_left ht
        exact ⟨by simp [w, ht], hh⟩
    have hw_ne_vk : w ≠ vk := by
      rcases he'_conn with ⟨ht, hh⟩ | ⟨ht, hh⟩
      · intro h; exact hloop e' he'_mem (ht.trans (h ▸ hh).symm)
      · intro h; exact hloop e' he'_mem ((h ▸ ht).trans hh.symm)
    -- By maximality of k, `w ∈ verts`
    have hw_in : w ∈ verts := by
      by_contra hw_not
      have hpath_succ : IsPath (k + 1) := by
        refine ⟨by omega, verts ++ [w], edges ++ [e'], by simp [hv_len], by simp [he_len], ?_, ?_, ?_⟩
        · rw [List.nodup_append]
          refine ⟨hv_nodup, List.nodup_singleton w, fun x hx y hy heq => ?_⟩
          simp only [List.mem_singleton] at hy; subst hy; subst heq; exact hw_not hx
        · intro e he
          simp only [List.mem_append, List.mem_singleton] at he
          rcases he with h1 | rfl
          · exact he_sub e h1
          · exact he'_mem
        · intro i hi
          by_cases hlt : i < k
          · have h1 : (verts ++ [w])[i]'(by simp; omega) = verts[i]'(by omega) :=
              List.getElem_append_left (by omega)
            have h2 : (verts ++ [w])[i + 1]'(by simp; omega) = verts[i + 1]'(by omega) :=
              List.getElem_append_left (by omega)
            have h3 : (edges ++ [e'])[i]'(by simp; omega) = edges[i]'(by omega) :=
              List.getElem_append_left (by omega)
            simpa only [h1, h2, h3] using hstep i hlt
          · have hik : i = k := by omega
            subst hik
            have h1 : (verts ++ [w])[k]'(by simp; omega) = vk :=
              List.getElem_append_left (by omega)
            have h2 : (verts ++ [w])[k + 1]'(by simp; omega) = w := by
              have : k + 1 = verts.length := by omega
              simp [this]
            have h3 : (edges ++ [e'])[k]'(by simp; omega) = e' := by
              have : k = edges.length := by omega
              simp [this]
            simpa only [h1, h2, h3] using he'_conn
      have := hk_max (k + 1) hpath_succ
      omega
    -- Slice from `j = verts.idxOf w` to `k` and close with `e'`
    let j := verts.idxOf w
    have hj_lt_len : j < verts.length := List.idxOf_lt_length_of_mem hw_in
    have hvj : verts[j]'hj_lt_len = w := List.getElem_idxOf hj_lt_len
    have hj_lt_k : j < k := by
      have : j ≠ k := by intro h; exact hw_ne_vk (hvj.symm.trans (by simp [vk, h]))
      omega
    let cVerts := verts.drop j
    let cEdges := edges.drop j ++ [e']
    have hcV_len : cVerts.length = k - j + 1 := by simp [cVerts, hv_len]; omega
    have hcE_len : cEdges.length = cVerts.length := by simp [cEdges, hcV_len, he_len]
    have hcV_nodup : cVerts.Nodup := hv_nodup.drop
    -- `e'` is not in `edges.drop j`
    have he'_not_drop : e' ∉ edges.drop j := by
      intro hmem
      obtain ⟨r, hr, hr_eq⟩ := List.getElem_of_mem hmem
      simp only [List.length_drop, List.getElem_drop] at hr hr_eq
      by_cases hlast : j + r = k - 1
      · apply he'_ne
        have : edges[j + r]'(by omega) = elast := by congr 1
        exact hr_eq.symm.trans this
      · have hjr_lt : j + r + 1 < k := by omega
        -- `edges[j + r]` has endpoints `verts[j+r]` and `verts[j+r+1]`, neither equals `verts[k] = vk`
        have hstep_jr := hstep (j + r) (by omega)
        rw [hr_eq] at hstep_jr
        rcases he'_inc with h1 | h1 <;> rcases hstep_jr with ⟨ht, hh⟩ | ⟨ht, hh⟩
        · have := (List.Nodup.getElem_inj_iff hv_nodup).mp (h1.symm.trans ht); omega
        · have := (List.Nodup.getElem_inj_iff hv_nodup).mp (h1.symm.trans ht); omega
        · have := (List.Nodup.getElem_inj_iff hv_nodup).mp (h1.symm.trans hh); omega
        · have := (List.Nodup.getElem_inj_iff hv_nodup).mp (h1.symm.trans hh); omega
    have hcE_nodup : cEdges.Nodup := by
      rw [List.nodup_append]
      refine ⟨he_nodup.drop, List.nodup_singleton e', fun x hx y hy heq => ?_⟩
      simp only [List.mem_singleton] at hy; subst hy; subst heq; exact he'_not_drop hx
    let C := directedCycleOfSimpleClosedWalk G cVerts cEdges (by omega) hcE_len hcV_nodup hcE_nodup
      (fun i hi => by
        by_cases hlt : i < k - j
        · have hi_drop : i < (edges.drop j).length := by simp [he_len]; omega
          have h1 : cVerts[i]'(by omega) = verts[j + i]'(by omega) := List.getElem_drop
          have hmod : (i + 1) % cVerts.length = i + 1 := Nat.mod_eq_of_lt (by omega)
          have h2 : cVerts[(i + 1) % cVerts.length]'(Nat.mod_lt _ (by omega)) =
              verts[j + i + 1]'(by omega) := by
            simp only [hmod, cVerts, List.getElem_drop, Nat.add_assoc]
          have h3 : cEdges[i]'hi = edges[j + i]'(by omega) := by
            simp only [cEdges, List.getElem_append_left hi_drop, List.getElem_drop]
          simpa only [h1, h2, h3] using hstep (j + i) (by omega)
        · have hi_eq : i = k - j := by omega
          subst hi_eq
          have h1 : cVerts[k - j]'(by omega) = vk := by
            simp only [cVerts, List.getElem_drop, vk]
            congr 1; omega
          have hmod : (k - j + 1) % cVerts.length = 0 := by
            rw [← hcV_len, Nat.mod_self]
          have h2 : cVerts[(k - j + 1) % cVerts.length]'(Nat.mod_lt _ (by omega)) = w := by
            simp only [hmod, cVerts, List.getElem_drop, add_zero, hvj]
          have h3 : cEdges[k - j]'hi = e' := by
            have : (edges.drop j).length = k - j := by simp [he_len]
            simp [cEdges, this]
          simpa only [h1, h2, h3] using he'_conn)
    refine ⟨C, ?_, ?_⟩
    · intro v hv
      have hv_e : ∃ e ∈ C.sub.edges, G.tail e = v ∨ G.head e = v := by
        have hdeg2 := C.isCycle.2 v hv
        unfold Subgraph.deg at hdeg2
        by_cases hpos : 0 < (C.sub.edges.filter (fun e => G.tail e = v)).card
        · rcases Finset.card_pos.mp hpos with ⟨e, he⟩
          exact ⟨e, (Finset.mem_filter.mp he).1, Or.inl (Finset.mem_filter.mp he).2⟩
        · have hpos2 : 0 < (C.sub.edges.filter (fun e => G.head e = v)).card := by omega
          rcases Finset.card_pos.mp hpos2 with ⟨e, he⟩
          exact ⟨e, (Finset.mem_filter.mp he).1, Or.inr (Finset.mem_filter.mp he).2⟩
      rcases hv_e with ⟨e, heC, ht | hh⟩
      · have heH : e ∈ H.edges := by
          simp only [C, directedCycleOfSimpleClosedWalk, List.mem_toFinset, cEdges,
            List.mem_append, List.mem_singleton] at heC
          rcases heC with h1 | rfl
          · exact he_sub e (List.mem_of_mem_drop h1)
          · exact he'_mem
        rw [← ht]; exact H.tail_mem heH
      · have heH : e ∈ H.edges := by
          simp only [C, directedCycleOfSimpleClosedWalk, List.mem_toFinset, cEdges,
            List.mem_append, List.mem_singleton] at heC
          rcases heC with h1 | rfl
          · exact he_sub e (List.mem_of_mem_drop h1)
          · exact he'_mem
        rw [← hh]; exact H.head_mem heH
    · intro e heC
      simp only [C, directedCycleOfSimpleClosedWalk, List.mem_toFinset, cEdges,
        List.mem_append, List.mem_singleton] at heC
      rcases heC with h1 | rfl
      · exact he_sub e (List.mem_of_mem_drop h1)
      · exact he'_mem

/-- Any forest with at least one edge has a vertex of degree `1`. -/
lemma exists_leaf_of_forest [Fintype V] {G : Multigraph V E} {F : G.Subgraph}
    (hF : F.IsForest) (hne : F.edges.Nonempty) :
    ∃ v ∈ F.verts, F.deg v = 1 := by
  by_contra hall
  push_neg at hall
  obtain ⟨C, hCle⟩ := exists_directedCycle_of_no_deg_one F hne hall
  exact hF C.sub hCle C.isCycle

/-- Any flow (in any abelian group) supported on a forest is identically zero. -/
lemma flow_eq_zero_of_supp_subset_forest [Fintype V] {A : Type} [AddCommGroup A]
    {G : Multigraph V E} {T : G.Subgraph} (hT : T.IsForest)
    {h : E → A} (hh : G.IsFlow h) (hsupp : ∀ e, h e ≠ 0 → e ∈ T.edges) :
    ∀ e, h e = 0 := by
  classical
  let E_supp : Finset E := Finset.univ.filter (fun e => h e ≠ 0)
  let F : G.Subgraph :=
    { verts := T.verts
      edges := E_supp
      tail_mem := fun he => T.tail_mem (hsupp _ (Finset.mem_filter.mp he).2)
      head_mem := fun he => T.head_mem (hsupp _ (Finset.mem_filter.mp he).2) }
  have hFle : F ≤ T := ⟨Finset.Subset.refl _, fun e he => hsupp e (Finset.mem_filter.mp he).2⟩
  have hF_forest : F.IsForest := fun C hCF => hT C ⟨hCF.1.trans hFle.1, hCF.2.trans hFle.2⟩
  by_contra hne
  push_neg at hne
  rcases hne with ⟨e₀, he₀⟩
  have hFne : F.edges.Nonempty := ⟨e₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he₀⟩⟩
  obtain ⟨v, _, hdeg1⟩ := exists_leaf_of_forest hF_forest hFne
  -- Exactly one edge of `E_supp` is incident to `v`, contradicting `G.boundary h v = 0`
  have hbd := hh v
  unfold Subgraph.deg at hdeg1
  have hsplit : ((E_supp.filter (fun e => G.head e = v)).card = 1 ∧
      (E_supp.filter (fun e => G.tail e = v)).card = 0) ∨
      ((E_supp.filter (fun e => G.head e = v)).card = 0 ∧
      (E_supp.filter (fun e => G.tail e = v)).card = 1) := by
    simp only [F] at hdeg1; omega
  have hfilter_head : ∑ e ∈ Finset.univ.filter (fun e => G.head e = v), h e =
      ∑ e ∈ E_supp.filter (fun e => G.head e = v), h e := by
    symm
    refine Finset.sum_subset (fun e he => ?_) (fun e he hnot => ?_)
    · rw [Finset.mem_filter] at he ⊢; exact ⟨Finset.mem_univ _, he.2⟩
    · rw [Finset.mem_filter] at he
      by_contra hne0
      exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne0⟩, he.2⟩)
  have hfilter_tail : ∑ e ∈ Finset.univ.filter (fun e => G.tail e = v), h e =
      ∑ e ∈ E_supp.filter (fun e => G.tail e = v), h e := by
    symm
    refine Finset.sum_subset (fun e he => ?_) (fun e he hnot => ?_)
    · rw [Finset.mem_filter] at he ⊢; exact ⟨Finset.mem_univ _, he.2⟩
    · rw [Finset.mem_filter] at he
      by_contra hne0
      exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne0⟩, he.2⟩)
  unfold Multigraph.boundary at hbd
  rw [hfilter_head, hfilter_tail] at hbd
  rcases hsplit with ⟨hh1, ht0⟩ | ⟨hh0, ht1⟩
  · rw [Finset.card_eq_one] at hh1
    rw [Finset.card_eq_zero] at ht0
    rcases hh1 with ⟨e, he⟩
    have he_mem : e ∈ E_supp := (Finset.mem_filter.mp (he ▸ Finset.mem_singleton_self e)).1
    rw [he, ht0] at hbd
    simp only [Finset.sum_singleton, Finset.sum_empty, sub_zero] at hbd
    exact (Finset.mem_filter.mp he_mem).2 hbd
  · rw [Finset.card_eq_zero] at hh0
    rw [Finset.card_eq_one] at ht1
    rcases ht1 with ⟨e, he⟩
    have he_mem : e ∈ E_supp := (Finset.mem_filter.mp (he ▸ Finset.mem_singleton_self e)).1
    rw [hh0, he] at hbd
    simp only [Finset.sum_empty, Finset.sum_singleton, zero_sub, neg_eq_zero] at hbd
    exact (Finset.mem_filter.mp he_mem).2 hbd

end CycleBuilders

section Lemma21

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- Every finite multigraph admits a spanning forest. -/
lemma exists_spanningForest (G : Multigraph V E) :
    ∃ T : G.Subgraph, T.IsSpanningForest := by
  classical
  -- Maximize |T.edges| among acyclic subgraphs with T.verts = univ
  let IsSpanAcyc (k : ℕ) : Prop :=
    ∃ T : G.Subgraph, T.verts = Finset.univ ∧ T.IsForest ∧ T.edges.card = k
  have h0 : IsSpanAcyc 0 :=
    ⟨{ verts := Finset.univ, edges := ∅, tail_mem := by simp, head_mem := by simp },
      rfl,
      fun C hC hcyc => by
        rcases hcyc.1.1 with ⟨v, hv⟩
        have hdeg := hcyc.2 v hv
        have he_empty : C.edges = ∅ := Finset.subset_empty.mp hC.2
        simp [Subgraph.deg, he_empty] at hdeg,
      rfl⟩
  let S := (Finset.range (Fintype.card E + 1)).filter (fun k => IsSpanAcyc k)
  have hS_ne : S.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), h0⟩⟩
  let k := S.max' hS_ne
  have hk_mem := Finset.max'_mem S hS_ne
  rcases (Finset.mem_filter.mp hk_mem).2 with ⟨T, hTv, hTf, hTcard⟩
  refine ⟨T, hTv, hTf, fun u v huv => ?_⟩
  induction huv with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c _ hbc ih =>
    refine Relation.ReflTransGen.trans ih ?_
    rcases hbc with ⟨e, hbc_e⟩
    by_cases heT : e ∈ T.edges
    · exact Relation.ReflTransGen.single ⟨e, heT, hbc_e⟩
    · -- Adding `e` to `T` must create a cycle `C`, which yields a path in `T` between `b` and `c`
      let T' : G.Subgraph :=
        { verts := Finset.univ, edges := insert e T.edges,
          tail_mem := fun _ => Finset.mem_univ _, head_mem := fun _ => Finset.mem_univ _ }
      have hT'_not_forest : ¬ T'.IsForest := by
        intro hT'f
        have hk1 : IsSpanAcyc (k + 1) :=
          ⟨T', rfl, hT'f, by simp only [T', Finset.card_insert_of_notMem heT, hTcard]; rfl⟩
        have hle_card : k + 1 ≤ Fintype.card E := by
          have : T'.edges.card ≤ Fintype.card E := Finset.card_le_univ _
          simp only [T', Finset.card_insert_of_notMem heT, hTcard] at this
          exact this
        have hle := Finset.le_max' S (k + 1)
          (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hk1⟩)
        omega
      unfold Subgraph.IsForest at hT'_not_forest
      push_neg at hT'_not_forest
      rcases hT'_not_forest with ⟨C, hCT', hCcyc⟩
      have heC : e ∈ C.edges := by
        by_contra henot
        apply hTf C ⟨by simp [hTv], fun e' he' => ?_⟩ hCcyc
        have := hCT'.2 he'
        simp only [T', Finset.mem_insert] at this
        exact this.resolve_left (fun heq => henot (heq ▸ he'))
      -- Deleting `e` from cycle `C` still connects `b` and `c` (otherwise C - e separates them,
      -- impossible since every vertex of C has even degree 2!)
      -- Actually prove cleanly: let R = {w | ReflTransGen T.Adj b w}. If c ∉ R, sum deg in C over R ∩ C.verts:
      -- parity argument: every vertex in R ∩ C.verts has degree 2 in C, so cut of C across R is EVEN,
      -- yet `e` is the ONLY edge of C crossing R (since all other edges of C are in T)! Contradiction!
      by_contra hnot_reach
      let R : Finset V := Finset.univ.filter (fun w => Relation.ReflTransGen T.Adj b w)
      have hbR : b ∈ R := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Relation.ReflTransGen.refl⟩
      have hcR : c ∉ R := fun h => hnot_reach (Finset.mem_filter.mp h).2
      -- Every edge `e' ∈ C.edges \ {e}` lies in `T.edges`, so `tail e' ∈ R ↔ head e' ∈ R`
      have hT_closed : ∀ e' ∈ T.edges, G.tail e' ∈ R ↔ G.head e' ∈ R := by
        intro e' he'
        simp only [R, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro h; exact Relation.ReflTransGen.tail h ⟨e', he', Or.inl ⟨rfl, rfl⟩⟩
        · intro h; exact Relation.ReflTransGen.tail h ⟨e', he', Or.inr ⟨rfl, rfl⟩⟩
      -- Sum `C.deg v` over `v ∈ C.verts ∩ R`:
      -- Left side = 2 * |C.verts ∩ R| (even!).
      -- Right side = ∑ e' ∈ C.edges, (ite (tail e' ∈ R) 1 0 + ite (head e' ∈ R) 1 0):
      -- every e' ≠ e contributes 0 or 2 (even!), while e contributes 1 (odd!) -> contradiction!
      have hlhs : ∑ v ∈ C.verts.filter (fun v => v ∈ R), C.deg v =
          2 * (C.verts.filter (fun v => v ∈ R)).card := by
        rw [Finset.sum_congr rfl (fun v hv => hCcyc.2 v (Finset.mem_filter.mp hv).1)]
        simp [Nat.mul_comm]
      have hrhs : ∑ v ∈ C.verts.filter (fun v => v ∈ R), C.deg v =
          ∑ e' ∈ C.edges, ((if G.tail e' ∈ R then 1 else 0) + (if G.head e' ∈ R then 1 else 0)) := by
        unfold Subgraph.deg
        simp only [Finset.card_filter]
        rw [Finset.sum_add_distrib]
        rw [Finset.sum_comm (s := C.verts.filter (fun v => v ∈ R)) (t := C.edges)]
        rw [Finset.sum_comm (s := C.verts.filter (fun v => v ∈ R)) (t := C.edges)]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun e' he' => ?_)
        have htC : G.tail e' ∈ C.verts := C.tail_mem he'
        have hhC : G.head e' ∈ C.verts := C.head_mem he'
        simp [Finset.mem_filter, htC, hhC]
      have he_contrib : (if G.tail e ∈ R then 1 else 0) + (if G.head e ∈ R then 1 else 0) = 1 := by
        rcases hbc_e with ⟨ht, hh⟩ | ⟨ht, hh⟩ <;> simp [ht, hh, hbR, hcR]
      have hrest_even : 2 ∣ ∑ e' ∈ C.edges.erase e,
          ((if G.tail e' ∈ R then 1 else 0) + (if G.head e' ∈ R then 1 else 0)) := by
        apply Finset.dvd_sum
        intro e' he'
        have he'T : e' ∈ T.edges := by
          have := hCT'.2 (Finset.mem_of_mem_erase he')
          simp only [T', Finset.mem_insert] at this
          exact this.resolve_left (Finset.ne_of_mem_erase he')
        have hiff := hT_closed e' he'T
        by_cases ht : G.tail e' ∈ R
        · have hh : G.head e' ∈ R := hiff.mp ht
          simp [ht, hh]
        · have hh : G.head e' ∉ R := fun h => ht (hiff.mpr h)
          simp [ht, hh]
      rw [← Finset.add_sum_erase _ _ heC, he_contrib] at hrhs
      rw [hlhs] at hrhs
      rcases hrest_even with ⟨m, hm⟩
      omega

/-- Existence and uniqueness of the fundamental cycle of `e ∉ T₀.edges` in a spanning forest `T₀`. -/
lemma existsUnique_fundamentalCycle (G : Multigraph V E) (T₀ : G.Subgraph)
    (hT : T₀.IsSpanningForest) (e : E) (he : e ∉ T₀.edges) :
    ∃! C : G.DirectedCycle, G.IsFundamentalCycle T₀ e C := by
  -- Existence
  have hex : ∃ C : G.DirectedCycle, G.IsFundamentalCycle T₀ e C := by
    by_cases hloop : G.tail e = G.head e
    · refine ⟨directedCycleOfLoop G e hloop, ?_, ?_⟩
      · intro e' he'
        simp only [directedCycleOfLoop, Finset.mem_singleton] at he'
        subst he'; exact Finset.mem_insert_self _ _
      · simp [directedCycleOfLoop]
    · have hadj : Relation.ReflTransGen G.Adj (G.head e) (G.tail e) :=
        Relation.ReflTransGen.single ⟨e, Or.inr ⟨rfl, rfl⟩⟩
      have hTwalk := hT.2.2 (G.head e) (G.tail e) hadj
      obtain ⟨verts, edges, hlen, hv_nodup, hhead, hlast, hedges_sub, hstep⟩ :=
        exists_simplePath_of_reflTransGen hTwalk
      have hlen_pos : 1 ≤ edges.length := by
        by_contra h0
        have he0 : edges.length = 0 := by omega
        have hv1 : verts.length = 1 := by omega
        cases verts with
        | nil => simp at hv1
        | cons x xs =>
          cases xs with
          | nil =>
            simp only [List.head?_cons, List.getLast?_singleton, Option.some.injEq] at hhead hlast
            exact hloop (hlast.symm.trans hhead)
          | cons _ _ => simp at hv1
      have he_nodup : edges.Nodup := simplePath_edges_nodup hv_nodup hlen hstep
      have he_not_in : e ∉ edges := fun hm => he (hedges_sub e hm)
      let cEdges := edges ++ [e]
      have hcE_len : cEdges.length = verts.length := by simp [cEdges, hlen]
      have hcE_nodup : cEdges.Nodup := by
        rw [List.nodup_append]
        exact ⟨he_nodup, List.nodup_singleton e, fun x hx y hy h => by
          simp only [List.mem_singleton] at hy; subst hy; subst h; exact he_not_in hx⟩
      have hv0 : verts[0]'(by omega) = G.head e := by
        cases verts with
        | nil => simp at hhead
        | cons x xs => simpa using hhead
      have hvlast : verts[edges.length]'(by omega) = G.tail e := by
        rw [List.getLast?_eq_getElem?] at hlast
        have hidx : verts.length - 1 = edges.length := by omega
        rw [hidx, List.getElem?_eq_getElem (by omega)] at hlast
        exact Option.some.inj hlast
      let C := directedCycleOfSimpleClosedWalk G verts cEdges (by omega) hcE_len hv_nodup hcE_nodup
        (fun i hi => by
          by_cases hlt : i < edges.length
          · have hmod : (i + 1) % verts.length = i + 1 := Nat.mod_eq_of_lt (by omega)
            have h3 : cEdges[i]'hi = edges[i]'hlt := List.getElem_append_left hlt
            simpa only [hmod, h3] using hstep i hlt
          · have hi_eq : i = edges.length := by omega
            subst hi_eq
            have hmod : (edges.length + 1) % verts.length = 0 := by
              rw [← hlen, Nat.mod_self]
            have h3 : cEdges[edges.length]'hi = e := by simp [cEdges]
            left
            simp only [hmod, h3, hv0, hvlast, and_self])
      refine ⟨C, ?_, ?_⟩
      · intro e' he'
        simp only [C, directedCycleOfSimpleClosedWalk, List.mem_toFinset, cEdges,
          List.mem_append, List.mem_singleton] at he'
        rcases he' with h1 | rfl
        · exact Finset.mem_insert_of_mem (hedges_sub e' h1)
        · exact Finset.mem_insert_self _ _
      · -- Show `C.sign e = 1`
        have hmem_e : e ∈ cEdges := by simp [cEdges]
        have hidx_e : cEdges.idxOf e = edges.length := by
          have : cEdges[edges.length]'(by simp [cEdges]) = e := by simp [cEdges]
          simpa only [this] using List.Nodup.idxOf_getElem hcE_nodup edges.length (by simp [cEdges])
        have hmod : (edges.length + 1) % verts.length = 0 := by
          rw [← hlen, Nat.mod_self]
        simp only [C, directedCycleOfSimpleClosedWalk, hmem_e, ↓reduceDIte, hidx_e, hmod,
          hv0, hvlast, and_self, ↓reduceIte]
  rcases hex with ⟨C, hC⟩
  refine ⟨C, hC, fun C' hC' => ?_⟩
  -- Uniqueness: C'.sign - C.sign is a ℤ-flow supported in T₀.edges, hence 0!
  have hdiff_flow : G.IsFlow (fun e' => C'.sign e' - C.sign e') := isFlow_sub C'.isFlow C.isFlow
  have hdiff_supp : ∀ e', C'.sign e' - C.sign e' ≠ 0 → e' ∈ T₀.edges := by
    intro e' hne0
    by_cases heq : e' = e
    · subst heq; exfalso; exact hne0 (by rw [hC'.2, hC.2, sub_self])
    · by_cases hm1 : e' ∈ C'.sub.edges
      · exact (Finset.mem_insert.mp (hC'.1 hm1)).resolve_left heq
      · by_cases hm2 : e' ∈ C.sub.edges
        · exact (Finset.mem_insert.mp (hC.1 hm2)).resolve_left heq
        · exfalso; exact hne0 (by rw [C'.sign_zero hm1, C.sign_zero hm2, sub_self])
  have hzero := flow_eq_zero_of_supp_subset_forest hT.2.1 hdiff_flow hdiff_supp
  have hsign_eq : C'.sign = C.sign := funext (fun e' => sub_eq_zero.mp (hzero e'))
  have hedges_eq : C'.sub.edges = C.sub.edges := by
    ext e'
    constructor
    · intro hm
      by_contra hnot
      have h1 := C'.sign_mem hm
      have h2 := C.sign_zero hnot
      rw [hsign_eq] at h1
      rcases h1 with h1 | h1 <;> omega
    · intro hm
      by_contra hnot
      have h1 := C.sign_mem hm
      have h2 := C'.sign_zero hnot
      rw [hsign_eq] at h2
      rcases h1 with h1 | h1 <;> omega
  have hverts_eq : C'.sub.verts = C.sub.verts := by
    ext v
    have hdeg_pos : ∀ (D : G.DirectedCycle), v ∈ D.sub.verts ↔
        ∃ e' ∈ D.sub.edges, G.tail e' = v ∨ G.head e' = v := by
      intro D
      constructor
      · intro hv
        have hd := D.isCycle.2 v hv
        unfold Subgraph.deg at hd
        by_cases ht : 0 < (D.sub.edges.filter (fun e' => G.tail e' = v)).card
        · rcases Finset.card_pos.mp ht with ⟨e', he'⟩
          exact ⟨e', (Finset.mem_filter.mp he').1, Or.inl (Finset.mem_filter.mp he').2⟩
        · have hh : 0 < (D.sub.edges.filter (fun e' => G.head e' = v)).card := by omega
          rcases Finset.card_pos.mp hh with ⟨e', he'⟩
          exact ⟨e', (Finset.mem_filter.mp he').1, Or.inr (Finset.mem_filter.mp he').2⟩
      · rintro ⟨e', he', rfl | rfl⟩
        · exact D.sub.tail_mem he'
        · exact D.sub.head_mem he'
    rw [hdeg_pos C', hdeg_pos C, hedges_eq]
  cases C' with | mk sub' _ sign' _ _ _ =>
  cases C with | mk sub _ sign _ _ _ =>
  simp only at hsign_eq hedges_eq hverts_eq
  subst hsign_eq
  have : sub' = sub := Subgraph.ext hverts_eq hedges_eq
  subst this
  rfl

/-- **Lemma 2.1(a) (Cycle decomposition — fundamental cycles).** -/
theorem lem_2_1_a
    {A : Type} [AddCommGroup A]
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
        ∀ e, h e = (l.map (fun p => p.2.sign e • p.1)).sum) := by
  have huniq := existsUnique_fundamentalCycle G T₀ hT
  have heval : ∀ (fund : ∀ e : E, e ∉ T₀.edges → G.DirectedCycle),
      (∀ e (he : e ∉ T₀.edges), G.IsFundamentalCycle T₀ e (fund e he)) →
      ∀ (c : E → A) (e₀ : E), e₀ ∉ T₀.edges →
        ∑ e ∈ (Finset.univ \ T₀.edges).attach,
          (fund e.1 (Finset.mem_sdiff.mp e.2).2).sign e₀ • c e.1 = c e₀ := by
    intro fund hfund c e₀ he₀
    have he₀_mem : e₀ ∈ Finset.univ \ T₀.edges := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, he₀⟩
    rw [Finset.sum_eq_single ⟨e₀, he₀_mem⟩]
    · rw [(hfund e₀ he₀).2, one_zsmul]
    · intro ⟨e, he⟩ _ hne
      have he_ne : e₀ ≠ e := fun h => hne (Subtype.ext h.symm)
      have he_not : e₀ ∉ (fund e (Finset.mem_sdiff.mp he).2).sub.edges := by
        intro hm
        have hsub := (hfund e (Finset.mem_sdiff.mp he).2).1 hm
        rw [Finset.mem_insert] at hsub
        exact he₀ (hsub.resolve_left he_ne)
      rw [(fund e (Finset.mem_sdiff.mp he).2).sign_zero he_not, zero_zsmul]
    · intro hnot; exact absurd (Finset.mem_attach _ _) hnot
  have hpart2 : ∀ (fund : ∀ e : E, e ∉ T₀.edges → G.DirectedCycle),
      (∀ e (he : e ∉ T₀.edges), G.IsFundamentalCycle T₀ e (fund e he)) →
      ∀ (h : E → A), G.IsFlow h →
        (∀ e', h e' = ∑ e ∈ (Finset.univ \ T₀.edges).attach,
          (fund e.1 (Finset.mem_sdiff.mp e.2).2).sign e' • h e.1) ∧
        (∀ (c : E → A),
          (∀ e', h e' = ∑ e ∈ (Finset.univ \ T₀.edges).attach,
            (fund e.1 (Finset.mem_sdiff.mp e.2).2).sign e' • c e.1) →
          ∀ e, e ∉ T₀.edges → c e = h e) := by
    intro fund hfund h hh
    refine ⟨?_, ?_⟩
    · let sumF : E → A := fun e' =>
        ∑ e ∈ (Finset.univ \ T₀.edges).attach,
          (fund e.1 (Finset.mem_sdiff.mp e.2).2).sign e' • h e.1
      have hsumF_flow : G.IsFlow sumF :=
        isFlow_finset_sum _ (fun e _ => isFlow_zsmul (fund e.1 _).isFlow (h e.1))
      have hdiff_flow : G.IsFlow (fun e' => h e' - sumF e') := isFlow_sub hh hsumF_flow
      have hdiff_supp : ∀ e', h e' - sumF e' ≠ 0 → e' ∈ T₀.edges := by
        intro e' hne0
        by_contra hnot
        exact hne0 (by simp only [sumF, heval fund hfund h e' hnot, sub_self])
      intro e'
      exact sub_eq_zero.mp (flow_eq_zero_of_supp_subset_forest hT.2.1 hdiff_flow hdiff_supp e')
    · intro c hc e he
      have h1 := hc e
      rw [heval fund hfund c e he] at h1
      exact h1.symm
  refine ⟨huniq, hpart2, ?_⟩
  intro h hh
  classical
  let fund : ∀ e : E, e ∉ T₀.edges → G.DirectedCycle := fun e he => (huniq e he).choose
  have hfund : ∀ e (he : e ∉ T₀.edges), G.IsFundamentalCycle T₀ e (fund e he) :=
    fun e he => (huniq e he).choose_spec.1
  have hrep := (hpart2 fund hfund h hh).1
  let l : List (A × G.DirectedCycle) :=
    ((Finset.univ \ T₀.edges).attach.toList).map
      (fun e => (h e.1, fund e.1 (Finset.mem_sdiff.mp e.2).2))
  refine ⟨l, fun e' => ?_⟩
  rw [hrep e', Finset.sum_eq_multiset_sum, ← Finset.coe_toList, Multiset.map_coe, Multiset.sum_coe]
  simp [l, List.map_map, Function.comp_def]

/-- Extract one forward directed cycle from a non-zero, non-negative integer flow. -/
lemma exists_forward_cycle_of_nonneg_flow (G : Multigraph V E) (h : E → ℤ)
    (hh : G.IsFlow h) (hnn : ∀ e, 0 ≤ h e) (hpos : ∃ e₀, 0 < h e₀) :
    ∃ O : G.DirectedCycle,
      (∀ e ∈ O.sub.edges, O.sign e = 1 ∧ 0 < h e) := by
  by_cases hloop : ∃ e, G.tail e = G.head e ∧ 0 < h e
  · rcases hloop with ⟨e, hl, hpe⟩
    refine ⟨directedCycleOfLoop G e hl, fun e' he' => ?_⟩
    simp only [directedCycleOfLoop, Finset.mem_singleton] at he'
    subst he'
    exact ⟨by simp [directedCycleOfLoop], hpe⟩
  · push_neg at hloop
    -- No positive loop; find a maximal directed simple path of positive edges
    let IsDirPath (k : ℕ) : Prop :=
      1 ≤ k ∧ ∃ (verts : List V) (edges : List E) (_ : verts.length = k + 1) (_ : edges.length = k),
        verts.Nodup ∧
        (∀ e ∈ edges, 0 < h e) ∧
        (∀ (i : ℕ) (hi : i < k),
          G.tail (edges[i]'(by omega)) = verts[i]'(by omega) ∧
          G.head (edges[i]'(by omega)) = verts[i + 1]'(by omega))
    have hex1 : IsDirPath 1 := by
      rcases hpos with ⟨e₀, hpe₀⟩
      have hne : G.tail e₀ ≠ G.head e₀ := fun hl => by have := hloop e₀ hl; omega
      refine ⟨le_rfl, [G.tail e₀, G.head e₀], [e₀], rfl, rfl, by simp [hne], by simp [hpe₀], ?_⟩
      intro i hi
      have : i = 0 := by omega
      subst this; exact ⟨rfl, rfl⟩
    have hbdd : ∀ k, IsDirPath k → k ≤ Fintype.card V := by
      intro k ⟨_, verts, _, hlen, _, hnodup, _, _⟩
      have := hnodup.length_le_card; omega
    classical
    let S := (Finset.range (Fintype.card V + 1)).filter (fun k => IsDirPath k)
    have hS_ne : S.Nonempty := ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := hbdd 1 hex1; omega), hex1⟩⟩
    let k := S.max' hS_ne
    have hk_path : IsDirPath k := (Finset.mem_filter.mp (Finset.max'_mem S hS_ne)).2
    have hk_max : ∀ k', IsDirPath k' → k' ≤ k := fun k' hk' =>
      Finset.le_max' S k' (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := hbdd k' hk'; omega), hk'⟩)
    rcases hk_path with ⟨hk_pos, verts, edges, hv_len, he_len, hv_nodup, he_pos, hstep⟩
    have he_nodup : edges.Nodup :=
      simplePath_edges_nodup hv_nodup (by omega) (fun i hi => Or.inl (hstep i (by omega)))
    let vk := verts[k]'(by omega)
    let elast := edges[k - 1]'(by omega)
    have hhead_last : G.head elast = vk := by
      have h1 := (hstep (k - 1) (by omega)).2
      have hk1 : k - 1 + 1 = k := by omega
      simpa only [hk1] using h1
    have hpos_last : 0 < h elast := he_pos elast (List.getElem_mem _)
    -- Conservation at `vk`: outgoing sum = incoming sum ≥ h elast > 0, so some outgoing edge has `h e' > 0`
    have hout_pos : ∃ e', G.tail e' = vk ∧ 0 < h e' := by
      have hbd := hh vk
      unfold Multigraph.boundary at hbd
      have hsum_eq : ∑ e ∈ Finset.univ.filter (fun e => G.tail e = vk), h e =
          ∑ e ∈ Finset.univ.filter (fun e => G.head e = vk), h e := (sub_eq_zero.mp hbd).symm
      have hin_pos : 0 < ∑ e ∈ Finset.univ.filter (fun e => G.head e = vk), h e := by
        have hmem : elast ∈ Finset.univ.filter (fun e => G.head e = vk) :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hhead_last⟩
        have hle := Finset.single_le_sum (fun e _ => hnn e) hmem
        omega
      rw [← hsum_eq] at hin_pos
      by_contra hall
      push_neg at hall
      have hle0 : ∑ e ∈ Finset.univ.filter (fun e => G.tail e = vk), h e ≤ 0 :=
        Finset.sum_nonpos (fun e he => hall e (Finset.mem_filter.mp he).2)
      omega
    rcases hout_pos with ⟨e', ht', hpe'⟩
    let w := G.head e'
    have hw_ne_vk : w ≠ vk := by
      intro h; have := hloop e' (ht'.trans h.symm); omega
    have hw_in : w ∈ verts := by
      by_contra hw_not
      have hsucc : IsDirPath (k + 1) := by
        refine ⟨by omega, verts ++ [w], edges ++ [e'], by simp [hv_len], by simp [he_len], ?_, ?_, ?_⟩
        · rw [List.nodup_append]
          exact ⟨hv_nodup, List.nodup_singleton w, fun x hx y hy h => by
            simp only [List.mem_singleton] at hy; subst hy; subst h; exact hw_not hx⟩
        · intro e he
          simp only [List.mem_append, List.mem_singleton] at he
          rcases he with h1 | rfl
          · exact he_pos e h1
          · exact hpe'
        · intro i hi
          by_cases hlt : i < k
          · have h1 : (verts ++ [w])[i]'(by simp; omega) = verts[i]'(by omega) :=
              List.getElem_append_left (by omega)
            have h2 : (verts ++ [w])[i + 1]'(by simp; omega) = verts[i + 1]'(by omega) :=
              List.getElem_append_left (by omega)
            have h3 : (edges ++ [e'])[i]'(by simp; omega) = edges[i]'(by omega) :=
              List.getElem_append_left (by omega)
            simpa only [h1, h2, h3] using hstep i hlt
          · have hik : i = k := by omega
            subst hik
            have h1 : (verts ++ [w])[k]'(by simp; omega) = vk := List.getElem_append_left (by omega)
            have h2 : (verts ++ [w])[k + 1]'(by simp; omega) = w := by
              have : k + 1 = verts.length := by omega
              simp [this]
            have h3 : (edges ++ [e'])[k]'(by simp; omega) = e' := by
              have : k = edges.length := by omega
              simp [this]
            exact ⟨by rw [h3, h1]; exact ht', by rw [h3, h2]⟩
      have := hk_max (k + 1) hsucc
      omega
    let j := verts.idxOf w
    have hj_lt_len : j < verts.length := List.idxOf_lt_length_of_mem hw_in
    have hvj : verts[j]'hj_lt_len = w := List.getElem_idxOf hj_lt_len
    have hj_lt_k : j < k := by
      have : j ≠ k := fun h => hw_ne_vk (hvj.symm.trans (by simp [vk, h]))
      omega
    let cVerts := verts.drop j
    let cEdges := edges.drop j ++ [e']
    have hcV_len : cVerts.length = k - j + 1 := by simp [cVerts, hv_len]; omega
    have hcE_len : cEdges.length = cVerts.length := by simp [cEdges, hcV_len, he_len]
    have hcV_nodup : cVerts.Nodup := hv_nodup.drop
    have he'_not_drop : e' ∉ edges.drop j := by
      intro hmem
      obtain ⟨r, hr, hr_eq⟩ := List.getElem_of_mem hmem
      simp only [List.length_drop, List.getElem_drop] at hr hr_eq
      have ht_jr := (hstep (j + r) (by omega)).1
      rw [hr_eq, ht'] at ht_jr
      have := (List.Nodup.getElem_inj_iff hv_nodup).mp ht_jr
      omega
    have hcE_nodup : cEdges.Nodup := by
      rw [List.nodup_append]
      exact ⟨he_nodup.drop, List.nodup_singleton e', fun x hx y hy h => by
        simp only [List.mem_singleton] at hy; subst hy; subst h; exact he'_not_drop hx⟩
    have hc_dir : ∀ (i : ℕ) (hi : i < cEdges.length),
        G.tail (cEdges[i]'hi) = cVerts[i]'(by omega) ∧
        G.head (cEdges[i]'hi) = cVerts[(i + 1) % cVerts.length]'(Nat.mod_lt _ (by omega)) := by
      intro i hi
      by_cases hlt : i < k - j
      · have hi_drop : i < (edges.drop j).length := by simp [he_len]; omega
        have h1 : cVerts[i]'(by omega) = verts[j + i]'(by omega) := List.getElem_drop
        have hmod : (i + 1) % cVerts.length = i + 1 := Nat.mod_eq_of_lt (by omega)
        have h2 : cVerts[(i + 1) % cVerts.length]'(Nat.mod_lt _ (by omega)) =
            verts[j + i + 1]'(by omega) := by
          simp only [hmod, cVerts, List.getElem_drop, Nat.add_assoc]
        have h3 : cEdges[i]'hi = edges[j + i]'(by omega) := by
          simp only [cEdges, List.getElem_append_left hi_drop, List.getElem_drop]
        simpa only [h1, h2, h3] using hstep (j + i) (by omega)
      · have hi_eq : i = k - j := by omega
        subst hi_eq
        have h1 : cVerts[k - j]'(by omega) = vk := by
          simp only [cVerts, List.getElem_drop, vk]; congr 1; omega
        have hmod : (k - j + 1) % cVerts.length = 0 := by rw [← hcV_len, Nat.mod_self]
        have h2 : cVerts[(k - j + 1) % cVerts.length]'(Nat.mod_lt _ (by omega)) = w := by
          simp only [hmod, cVerts, List.getElem_drop, add_zero, hvj]
        have h3 : cEdges[k - j]'hi = e' := by
          have : (edges.drop j).length = k - j := by simp [he_len]
          simp [cEdges, this]
        exact ⟨by rw [h3, h1]; exact ht', by rw [h3, h2]⟩
    let O := directedCycleOfSimpleClosedWalk G cVerts cEdges (by omega) hcE_len hcV_nodup hcE_nodup
      (fun i hi => Or.inl (hc_dir i hi))
    refine ⟨O, fun e heO => ?_⟩
    have hmem : e ∈ cEdges := by
      simpa only [O, directedCycleOfSimpleClosedWalk, List.mem_toFinset] using heO
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hmem
    have hidx : cEdges.idxOf (cEdges[i]'hi) = i := List.Nodup.idxOf_getElem hcE_nodup i hi
    have hsign1 : O.sign (cEdges[i]'hi) = 1 := by
      have hd := hc_dir i hi
      simp only [O, directedCycleOfSimpleClosedWalk, hmem, ↓reduceDIte, hidx, hd.1, hd.2,
        and_self, ↓reduceIte]
    have hpe : 0 < h (cEdges[i]'hi) := by
      simp only [cEdges, List.mem_append, List.mem_singleton] at hmem
      rcases hmem with h1 | h1
      · exact he_pos _ (List.mem_of_mem_drop h1)
      · rw [h1]; exact hpe'
    exact ⟨hsign1, hpe⟩

/-- Signed cycle decomposition core (for arbitrary integer flow `h`). -/
lemma signed_cycle_decomp_core (G : Multigraph V E) :
    ∀ (N : ℕ) (h : E → ℤ),
      G.IsFlow h → (∑ e : E, (h e).natAbs) ≤ N →
      ∃ (cycles : List G.DirectedCycle),
        (∀ e, h e = (cycles.map (fun C => C.sign e)).sum) ∧
        (∀ C ∈ cycles, ∀ e ∈ C.sub.edges, 0 < C.sign e * h e) := by
  intro N
  induction N with
  | zero =>
    intro h _ hN
    have hzero : ∀ e, h e = 0 := by
      intro e
      have hle : (h e).natAbs ≤ 0 :=
        le_trans (Finset.single_le_sum (f := fun e' => (h e').natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ e)) hN
      exact Int.natAbs_eq_zero.mp (Nat.eq_zero_of_le_zero hle)
    exact ⟨[], fun e => by simp [hzero e], by simp⟩
  | succ N ih =>
    intro h hh hN
    by_cases hzero : ∀ e, h e = 0
    · exact ⟨[], fun e => by simp [hzero e], by simp⟩
    · push_neg at hzero
      rcases hzero with ⟨e₀, he₀⟩
      -- Reorient so that `h'` is non-negative everywhere
      let flip : E → Bool := fun e => decide (h e < 0)
      let G' := G.reorient flip
      let h' := Multigraph.reorientVal flip h
      have hh' : G'.IsFlow h' := (reorient_isFlow_iff G flip h).mpr hh
      have hnn' : ∀ e, 0 ≤ h' e := by
        intro e; unfold h' Multigraph.reorientVal flip
        by_cases hlt : h e < 0 <;> simp [hlt] <;> omega
      have hpos' : ∃ e, 0 < h' e := by
        refine ⟨e₀, ?_⟩
        unfold h' Multigraph.reorientVal flip
        by_cases hlt : h e₀ < 0 <;> simp [hlt] <;> omega
      obtain ⟨O', hO'⟩ := exists_forward_cycle_of_nonneg_flow G' h' hh' hnn' hpos'
      -- Transport `O'` back to `G`
      let O : G.DirectedCycle :=
        reorient_reorient G flip ▸ reorientDirectedCycle G' flip O'
      have hO_edges : O.sub.edges = O'.sub.edges := by
        dsimp only [O]
        have hcast : ∀ (G₁ G₂ : Multigraph V E) (heq : G₁ = G₂) (D : G₁.DirectedCycle),
            (heq ▸ D : G₂.DirectedCycle).sub.edges = D.sub.edges := by
          intro G₁ G₂ heq D; subst heq; rfl
        rw [hcast]
        rfl
      have hO_sign : ∀ e, O.sign e = Multigraph.reorientVal flip O'.sign e := by
        intro e
        dsimp only [O]
        have hcast : ∀ (G₁ G₂ : Multigraph V E) (heq : G₁ = G₂) (D : G₁.DirectedCycle),
            (heq ▸ D : G₂.DirectedCycle).sign e = D.sign e := by
          intro G₁ G₂ heq D; subst heq; rfl
        rw [hcast]
        rfl
      have hO_pos : ∀ e ∈ O.sub.edges, 0 < O.sign e * h e := by
        intro e heO
        rw [hO_edges] at heO
        obtain ⟨hs1, hpe⟩ := hO' e heO
        rw [hO_sign e]
        unfold Multigraph.reorientVal flip
        unfold h' Multigraph.reorientVal flip at hpe
        by_cases hlt : h e < 0
        · simp only [hlt, decide_true, ↓reduceIte, hs1] at hpe ⊢; nlinarith
        · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte, hs1] at hpe ⊢; nlinarith
      -- Define residual flow `h_rem = h - O.sign`
      let h_rem : E → ℤ := fun e => h e - O.sign e
      have hrem_flow : G.IsFlow h_rem := isFlow_sub hh O.isFlow
      have hrem_abs : ∀ e, (h_rem e).natAbs =
          if e ∈ O.sub.edges then (h e).natAbs - 1 else (h e).natAbs := by
        intro e
        by_cases heO : e ∈ O.sub.edges
        · simp only [heO, ↓reduceIte, h_rem]
          have hp := hO_pos e heO
          rcases O.sign_mem heO with hs | hs <;> rw [hs] at hp ⊢ <;> omega
        · simp only [heO, ↓reduceIte, h_rem, O.sign_zero heO, sub_zero]
      have hO_ne : O.sub.edges.Nonempty := by
        rcases O.isCycle.1.1 with ⟨v, hv⟩
        have hd := O.isCycle.2 v hv
        unfold Subgraph.deg at hd
        by_cases ht : 0 < (O.sub.edges.filter (fun e => G.tail e = v)).card
        · rcases Finset.card_pos.mp ht with ⟨e, he⟩
          exact ⟨e, (Finset.mem_filter.mp he).1⟩
        · have hh2 : 0 < (O.sub.edges.filter (fun e => G.head e = v)).card := by omega
          rcases Finset.card_pos.mp hh2 with ⟨e, he⟩
          exact ⟨e, (Finset.mem_filter.mp he).1⟩
      have hsum_lt : ∑ e : E, (h_rem e).natAbs < ∑ e : E, (h e).natAbs := by
        apply Finset.sum_lt_sum
        · intro e _
          rw [hrem_abs e]
          split_ifs <;> omega
        · rcases hO_ne with ⟨e₁, he₁⟩
          refine ⟨e₁, Finset.mem_univ _, ?_⟩
          rw [hrem_abs e₁, if_pos he₁]
          have hp := hO_pos e₁ he₁
          rcases O.sign_mem he₁ with hs | hs <;> rw [hs] at hp <;> omega
      obtain ⟨rest, hrest_sum, hrest_pos⟩ := ih h_rem hrem_flow (by omega)
      refine ⟨O :: rest, fun e => ?_, fun C hC e heC => ?_⟩
      · simp only [List.map_cons, List.sum_cons]
        have := hrest_sum e
        simp only [h_rem] at this
        omega
      · simp only [List.mem_cons] at hC
        rcases hC with rfl | hC'
        · exact hO_pos e heC
        · have hp := hrest_pos C hC' e heC
          have hs := C.sign_mem heC
          by_cases heO : e ∈ O.sub.edges
          · have hpo := hO_pos e heO
            have hso := O.sign_mem heO
            simp only [h_rem] at hp
            rcases hs with hs | hs <;> rcases hso with hso | hso <;>
              rw [hs] at hp ⊢ <;> rw [hso] at hpo hp <;> nlinarith
          · simp only [h_rem, O.sign_zero heO, sub_zero] at hp
            exact hp

/-- **Lemma 2.1(b) (Signed cycle decomposition).** -/
theorem lem_2_1_b
    (G : Multigraph V E) (h : E → ℤ) (hh : G.IsFlow h) :
    ∃ (cycles : List G.DirectedCycle),
      (∀ e, h e = (cycles.map (fun C => C.sign e)).sum) ∧
      (∀ C ∈ cycles, ∀ e ∈ C.sub.edges, 0 < C.sign e * h e) ∧
      (∀ e, ((cycles.filter (fun C => e ∈ C.sub.edges)).length : ℤ) = |h e|) ∧
      (∀ C ∈ cycles, ∀ e ∈ C.sub.edges, h e ≠ 0) ∧
      ((∀ e, h e = -1 ∨ h e = 0 ∨ h e = 1) →
        ∀ i j (hi : i < cycles.length) (hj : j < cycles.length), i ≠ j →
          Disjoint (cycles[i]'hi).sub.edges (cycles[j]'hj).sub.edges) := by
  obtain ⟨cycles, hsum, hpos⟩ := signed_cycle_decomp_core G (∑ e : E, (h e).natAbs) h hh le_rfl
  have hcount : ∀ e, ((cycles.filter (fun C => e ∈ C.sub.edges)).length : ℤ) = |h e| := by
    intro e
    -- Every term `C.sign e` is 0 if `e ∉ C.sub.edges`, +1 if `h e > 0`, -1 if `h e < 0`
    have heval := hsum e
    have haux : ∀ (l : List G.DirectedCycle),
        (∀ C ∈ l, e ∈ C.sub.edges → 0 < C.sign e * h e) →
        ((l.filter (fun C => decide (e ∈ C.sub.edges))).length : ℤ) =
          if 0 ≤ h e then (l.map (fun C => C.sign e)).sum else -(l.map (fun C => C.sign e)).sum := by
      intro l
      induction l with
      | nil => intro _; simp
      | cons C t ih =>
        intro hl
        have htail := ih (fun C' hC' => hl C' (by simp [hC']))
        by_cases heC : e ∈ C.sub.edges
        · have hp := hl C (by simp) heC
          have hs := C.sign_mem heC
          simp only [List.filter_cons, decide_eq_true heC, ↓reduceIte, List.length_cons,
            Nat.cast_add, Nat.cast_one, List.map_cons, List.sum_cons, htail]
          split_ifs with hnn
          · rcases hs with hs | hs <;> rw [hs] at hp ⊢ <;> omega
          · rcases hs with hs | hs <;> rw [hs] at hp ⊢ <;> omega
        · simp only [List.filter_cons, decide_eq_false heC, Bool.false_eq_true, ↓reduceIte,
            List.map_cons, List.sum_cons, C.sign_zero heC, zero_add, htail]
    have h1 := haux cycles (fun C hC heC => hpos C hC e heC)
    rw [← heval] at h1
    simpa [abs_eq_self, abs_of_neg, ite_eq_iff] using h1.trans (by
      split_ifs with hnn
      · exact (abs_of_nonneg hnn).symm
      · exact (abs_of_neg (by omega)).symm)
  have hsupp : ∀ C ∈ cycles, ∀ e ∈ C.sub.edges, h e ≠ 0 := by
    intro C hC e heC h0
    have := hpos C hC e heC
    rw [h0, mul_zero] at this
    omega
  refine ⟨cycles, hsum, hpos, hcount, hsupp, ?_⟩
  intro hunit i j hi hj hij
  rw [Finset.disjoint_left]
  intro e hei hej
  have hcnt := hcount e
  have habs_le1 : |h e| ≤ 1 := by
    rcases hunit e with h1 | h1 | h1 <;> simp [h1]
  -- Both index `i` and index `j` survive `cycles.filter (e ∈ ·.sub.edges)`, so length ≥ 2!
  have hge2 : 2 ≤ (cycles.filter (fun C => decide (e ∈ C.sub.edges))).length := by
    have hmap : (cycles.filter (fun C => decide (e ∈ C.sub.edges))).length =
        ((List.finRange cycles.length).filter (fun k => decide (e ∈ (cycles[k.1]'k.2).sub.edges))).length := by
      have : cycles = (List.finRange cycles.length).map (fun k => cycles[k.1]'k.2) := by
        apply List.ext_getElem <;> simp
      conv_lhs => rw [this]
      rw [List.filter_map, List.length_map]
      rfl
    rw [hmap]
    let S := ((List.finRange cycles.length).filter (fun k => decide (e ∈ (cycles[k.1]'k.2).sub.edges))).toFinset
    have hiS : (⟨i, hi⟩ : Fin cycles.length) ∈ S := by
      simp [S, hei]
    have hjS : (⟨j, hj⟩ : Fin cycles.length) ∈ S := by
      simp [S, hej]
    have hne_fin : (⟨i, hi⟩ : Fin cycles.length) ≠ ⟨j, hj⟩ := fun h => hij (Fin.mk.inj h)
    have h2S : 2 ≤ S.card := by
      have hsub : ({⟨i, hi⟩, ⟨j, hj⟩} : Finset (Fin cycles.length)) ⊆ S := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption
      exact le_trans (by rw [Finset.card_pair hne_fin]) (Finset.card_le_card hsub)
    exact le_trans h2S (List.toFinset_card_le _)
  omega

end Lemma21

end Flow.Proofs
