module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Flow.Defs.Literature
public import Flow.Proofs.Elementary
public import Flow.Proofs.Basic
public import Flow.Proofs.MasterHelpers
public import Flow.Proofs.LiftMove
public import Mathlib.Tactic

@[expose] public section

/-!
# Section 4 proofs (Part 3): Lemma 4.7 (`lem_4_7_of`) and Lemma 4.8(SUB) (`lem_4_8_sub_of`)
-/

namespace Flow.Proofs

open Flow

/-! ### Helper: Subpaths of a thread and projecting `Q`-walks to `H` -/

private lemma thread_head_getElem {V E : Type} [DecidableEq V] [DecidableEq E]
    {G : Multigraph V E} {H : G.Subgraph} {src dst : V} (P : ThreadPath G H src dst) :
    P.verts[0]'(by have := P.verts_len; omega) = src := by
  have hh := P.head_eq
  rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by have := P.verts_len; omega),
      Option.some.injEq] at hh
  exact hh

private lemma thread_last_getElem {V E : Type} [DecidableEq V] [DecidableEq E]
    {G : Multigraph V E} {H : G.Subgraph} {src dst : V} (P : ThreadPath G H src dst) :
    P.verts[P.edges.length]'(by have := P.verts_len; omega) = dst := by
  have hl := P.last_eq
  rw [List.getLast?_eq_getElem?] at hl
  have hidx : P.verts.length - 1 = P.edges.length := by have := P.verts_len; omega
  rw [hidx, List.getElem?_eq_getElem (by have := P.verts_len; omega), Option.some.injEq] at hl
  exact hl

/-- Reachability along a thread's prefix `0 .. k` using only `P.edges.take k`. -/
private lemma thread_prefix_reach {V E : Type} [DecidableEq V] [DecidableEq E]
    {G : Multigraph V E} {H : G.Subgraph} {src dst : V} (P : ThreadPath G H src dst)
    (L : G.Subgraph) (k : ℕ) (hk : k ≤ P.edges.length)
    (hsub : ∀ e ∈ P.edges.take k, e ∈ L.edges) :
    Relation.ReflTransGen L.Adj src (P.verts[k]'(by have := P.verts_len; omega)) := by
  induction k with
  | zero => rw [thread_head_getElem P]
  | succ m ih =>
    have hprev := ih (by omega) (fun e he => hsub e (by
      have hsub_take : P.edges.take m = (P.edges.take (m + 1)).take m := by rw [List.take_take]; simp
      rw [hsub_take] at he
      exact List.mem_of_mem_take he))
    have hem : P.edges[m]'(by omega) ∈ L.edges := by
      apply hsub
      have hlt : m < (P.edges.take (m + 1)).length := by rw [List.length_take]; omega
      have hget : (P.edges.take (m + 1))[m]'hlt = P.edges[m]'(by omega) := List.getElem_take
      rw [← hget]; exact List.getElem_mem _
    exact hprev.tail ⟨P.edges[m]'(by omega), hem, P.step_connect m (by omega)⟩

/-- Reachability along a thread's suffix `k .. len` using only `P.edges.drop k`. -/
private lemma thread_suffix_reach {V E : Type} [DecidableEq V] [DecidableEq E]
    {G : Multigraph V E} {H : G.Subgraph} {src dst : V} (P : ThreadPath G H src dst)
    (L : G.Subgraph) (k : ℕ) (hk : k ≤ P.edges.length)
    (hsub : ∀ e ∈ P.edges.drop k, e ∈ L.edges) :
    Relation.ReflTransGen L.Adj (P.verts[k]'(by have := P.verts_len; omega)) dst := by
  have hgo : ∀ m : ℕ, k ≤ m → ∀ (hm : m ≤ P.edges.length),
      Relation.ReflTransGen L.Adj (P.verts[k]'(by have := P.verts_len; omega))
        (P.verts[m]'(by have := P.verts_len; omega)) := by
    intro m
    induction m with
    | zero =>
      intro hkm _
      have hk0 : k = 0 := by omega
      subst hk0; exact .refl
    | succ m ih =>
      intro hkm hm
      by_cases heq : k = m + 1
      · subst heq; exact .refl
      · have hprev := ih (by omega) (by omega)
        have hem : P.edges[m]'(by omega) ∈ L.edges := by
          apply hsub
          have hlt : m - k < (P.edges.drop k).length := by rw [List.length_drop]; omega
          have hget : (P.edges.drop k)[m - k]'hlt = P.edges[m]'(by omega) := by
            rw [List.getElem_drop]; congr 1; omega
          rw [← hget]; exact List.getElem_mem _
        exact hprev.tail ⟨P.edges[m]'(by omega), hem, P.step_connect m (by omega)⟩
  simpa [thread_last_getElem P] using hgo P.edges.length hk le_rfl

private lemma subgraph_adj_symm {V E : Type} {G : Multigraph V E} {L : G.Subgraph}
    {u v : V} (h : Relation.ReflTransGen L.Adj u v) : Relation.ReflTransGen L.Adj v u := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih =>
    rcases hs with ⟨e, he, h1 | h1⟩
    · exact Relation.ReflTransGen.head ⟨e, he, Or.inr h1⟩ ih
    · exact Relation.ReflTransGen.head ⟨e, he, Or.inl h1⟩ ih

/-- Lift a walk in `aux.Q` using edges from `S ⊆ aux.EQ` to a walk in a subgraph `L ≤ H`
containing every thread `sub.thread t` with `aux.origEdge t ∈ S`. -/
private lemma lift_Q_walk_to_H {V E : Type} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    {G : Multigraph V E} {H : G.Subgraph} {sub : SubdivisionData G H}
    {aux : AuxGraphData G H sub}
    (S : Finset aux.EQ) (L : G.Subgraph)
    (hL : ∀ t : sub.E₀, aux.origEdge t ∈ S → ∀ e ∈ (sub.thread t).edges, e ∈ L.edges)
    {x y : aux.VQ}
    (hwalk : Relation.ReflTransGen
      (fun a b => ∃ eq ∈ S, (aux.Q.tail eq = a ∧ aux.Q.head eq = b) ∨
                            (aux.Q.tail eq = b ∧ aux.Q.head eq = a)) x y) :
    Relation.ReflTransGen L.Adj (sub.embedV (aux.contractV x)) (sub.embedV (aux.contractV y)) := by
  induction hwalk with
  | refl => exact .refl
  | @tail a b _ hstep ih =>
    rcases hstep with ⟨eq, heqS, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    · by_cases hex : ∃ t : sub.E₀, aux.origEdge t = eq
      · rcases hex with ⟨t, rfl⟩
        have hta : aux.contractV a = sub.H₀.tail t := h1 ▸ aux.orig_tail t
        have hhb : aux.contractV b = sub.H₀.head t := h2 ▸ aux.orig_head t
        have hth : Relation.ReflTransGen L.Adj (sub.embedV (sub.H₀.tail t)) (sub.embedV (sub.H₀.head t)) := by
          have := thread_suffix_reach (sub.thread t) L 0 (Nat.zero_le _)
            (fun e he => hL t heqS e (by simpa using he))
          simpa [thread_head_getElem (sub.thread t)] using this
        rw [hta] at ih; rw [hhb]
        exact ih.trans hth
      · push Not at hex
        have hce : aux.contractV a = aux.contractV b := by
          rw [← h1, ← h2]; exact aux.exp_same_contractV eq hex
        rw [← hce]; exact ih
    · by_cases hex : ∃ t : sub.E₀, aux.origEdge t = eq
      · rcases hex with ⟨t, rfl⟩
        have htb : aux.contractV b = sub.H₀.tail t := h1 ▸ aux.orig_tail t
        have hha : aux.contractV a = sub.H₀.head t := h2 ▸ aux.orig_head t
        have hth : Relation.ReflTransGen L.Adj (sub.embedV (sub.H₀.tail t)) (sub.embedV (sub.H₀.head t)) := by
          have := thread_suffix_reach (sub.thread t) L 0 (Nat.zero_le _)
            (fun e he => hL t heqS e (by simpa using he))
          simpa [thread_head_getElem (sub.thread t)] using this
        rw [hha] at ih; rw [htb]
        exact ih.trans (subgraph_adj_symm hth)
      · push Not at hex
        have hce : aux.contractV b = aux.contractV a := by
          rw [← h1, ← h2]; exact aux.exp_same_contractV eq hex
        rw [hce]; exact ih

private lemma fNode_ne_eNode_any {V E : Type} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    {G : Multigraph V E} {H : G.Subgraph} {sub : SubdivisionData G H}
    {aux : AuxGraphData G H sub} (fr : Frame G H sub aux)
    (i j : Fin fr.numNodes) : fr.fNode i ≠ fr.eNode j := by
  intro heq
  obtain ⟨k, _, huniq⟩ := fr.blue_unique (fr.fNode i) (fr.f_blue i)
  have hi : i = k := huniq i (Or.inr rfl)
  have hj : j = k := huniq j (Or.inl heq)
  have hij : i = j := hi.trans hj.symm
  subst hij
  exact (fr.e_ne_f i) heq.symm

private lemma eNode_inj {V E : Type} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    {G : Multigraph V E} {H : G.Subgraph} {sub : SubdivisionData G H}
    {aux : AuxGraphData G H sub} (fr : Frame G H sub aux)
    {i j : Fin fr.numNodes} (h : fr.eNode i = fr.eNode j) : i = j := by
  obtain ⟨k, _, huniq⟩ := fr.blue_unique (fr.eNode i) (fr.e_blue i)
  exact (huniq i (Or.inl rfl)).trans (huniq j (Or.inl h)).symm

private lemma fNode_inj {V E : Type} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    {G : Multigraph V E} {H : G.Subgraph} {sub : SubdivisionData G H}
    {aux : AuxGraphData G H sub} (fr : Frame G H sub aux)
    {i j : Fin fr.numNodes} (h : fr.fNode i = fr.fNode j) : i = j := by
  obtain ⟨k, _, huniq⟩ := fr.blue_unique (fr.fNode i) (fr.f_blue i)
  exact (huniq i (Or.inr rfl)).trans (huniq j (Or.inr h)).symm

private lemma H0_connected {V₀ E₀ : Type} [Fintype V₀] [Fintype E₀] [DecidableEq V₀]
    (H₀ : Multigraph V₀ E₀) (h3 : H₀.IsEdgeConnected 3) : H₀.Connected := by
  classical
  intro u v
  let K : Finset V₀ := Finset.univ.filter (fun w => Relation.ReflTransGen H₀.Adj u w)
  have huK : u ∈ K := Finset.mem_filter.mpr ⟨Finset.mem_univ _, .refl⟩
  by_contra hnot
  have hvK : v ∈ Finset.univ \ K := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h => hnot (Finset.mem_filter.mp h).2⟩
  have hcut := h3 K ⟨u, huK⟩ ⟨v, hvK⟩
  have hempty : H₀.cutEdges K = ∅ := by
    ext e
    simp only [Multigraph.cutEdges, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.notMem_empty, iff_false, not_or]
    constructor
    · rintro ⟨ht, hh⟩
      exact hh (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (Finset.mem_filter.mp ht).2.tail ⟨e, Or.inl ⟨rfl, rfl⟩⟩⟩)
    · rintro ⟨ht, hh⟩
      exact ht (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (Finset.mem_filter.mp hh).2.tail ⟨e, Or.inr ⟨rfl, rfl⟩⟩⟩)
  rw [hempty, Finset.card_empty] at hcut
  omega

/-- Extract a simple path inside `L ≤ H` with `verts ⊆ H.verts`. -/
private lemma simplePath_in_sub {V E : Type} [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : Multigraph V E} {H L : G.Subgraph} (hLH : L ≤ H)
    {p p' : V} (hpH : p ∈ H.verts) (hne : p ≠ p')
    (hreach : Relation.ReflTransGen L.Adj p p') :
    ∃ (verts : List V) (edges : List E) (_ : verts.length = edges.length + 1),
      verts.Nodup ∧
      (∀ v ∈ verts, v ∈ H.verts) ∧
      (∀ e ∈ edges, e ∈ L.edges) ∧
      verts.head? = some p ∧
      verts.getLast? = some p' ∧
      (∀ (k : ℕ) (hk : k < edges.length),
        let u := verts[k]'(by omega)
        let w := verts[k + 1]'(by omega)
        let e := edges[k]'hk
        (G.tail e = u ∧ G.head e = w) ∨ (G.tail e = w ∧ G.head e = u)) := by
  obtain ⟨verts, edges, hlen, hnd, hhead, hlast, hedges, hstep⟩ :=
    exists_simplePath_of_reflTransGen hreach
  refine ⟨verts, edges, hlen, hnd, fun v hv => ?_, hedges, hhead, hlast, hstep⟩
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hv
  by_cases hkl : k < edges.length
  · rcases hstep k hkl with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact h1 ▸ H.tail_mem (hLH.2 (hedges _ (List.getElem_mem _)))
    · exact h2 ▸ H.head_mem (hLH.2 (hedges _ (List.getElem_mem _)))
  · by_cases he0 : edges.length = 0
    · have hk0 : k = 0 := by omega
      subst hk0
      have hv0 : verts[0]'hk = p := by
        rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hk, Option.some.injEq] at hhead
        exact hhead
      rw [hv0]; exact hpH
    · have hk_prev : k - 1 < edges.length := by omega
      rcases hstep (k - 1) hk_prev with ⟨_, h2⟩ | ⟨h1, _⟩
      · have hidx : verts[k - 1 + 1]'(by omega) = verts[k]'hk := by congr 1; omega
        rw [hidx] at h2; exact h2 ▸ H.head_mem (hLH.2 (hedges _ (List.getElem_mem _)))
      · have hidx : verts[k - 1 + 1]'(by omega) = verts[k]'hk := by congr 1; omega
        rw [hidx] at h1; exact h1 ▸ H.tail_mem (hLH.2 (hedges _ (List.getElem_mem _)))

/-! ### Lemma 4.7: The path -/

theorem lem_4_7_of
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : Multigraph V E} {H : G.Subgraph} {sub : SubdivisionData G H}
    {aux : AuxGraphData G H sub} (fr : Frame G H sub aux)
    (hO1 : ∀ g : Fin fr.numNodes → aux.EQ, (∀ i, g i = fr.eNode i ∨ g i = fr.fNode i) →
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
          (fun he => (Finset.mem_filter.mp he).2.2)).Connected))
    (p p' : V) (hp : p ∈ H.verts) (hp' : p' ∈ H.verts) (hne : p ≠ p') :
    ∃ (verts : List V) (edges : List E) (hlen : verts.length = edges.length + 1),
      verts.Nodup ∧
      (∀ v ∈ verts, v ∈ H.verts) ∧
      (∀ e ∈ edges, e ∈ H.edges) ∧
      verts.head? = some p ∧
      verts.getLast? = some p' ∧
      (∀ (k : ℕ) (hk : k < edges.length),
        let u := verts[k]'(by omega)
        let w := verts[k + 1]'(by omega)
        let e := edges[k]'hk
        (G.tail e = u ∧ G.head e = w) ∨ (G.tail e = w ∧ G.head e = u)) ∧
      (∀ i : Fin fr.numNodes,
        (edges.toFinset.filter (fun e =>
          (∃ t : sub.E₀, aux.origEdge t = fr.eNode i ∧ e ∈ (sub.thread t).edges) ∨
          (∃ t : sub.E₀, aux.origEdge t = fr.fNode i ∧ e ∈ (sub.thread t).edges))).card ≤ 3) := by
  classical
  let IsInt (v : V) (t : sub.E₀) : Prop :=
    v ∈ (sub.thread t).verts ∧ v ≠ sub.embedV (sub.H₀.tail t) ∧ v ≠ sub.embedV (sub.H₀.head t)
  -- Case 1: p and p' are interior vertices of the same thread t
  by_cases hcase1 : ∃ t : sub.E₀, IsInt p t ∧ IsInt p' t
  · rcases hcase1 with ⟨t, ⟨hpV, hp0, hpl⟩, ⟨hp'V, hp'0, hp'l⟩⟩
    let P := sub.thread t
    obtain ⟨k₁, hk₁, hpk₁⟩ := List.getElem_of_mem hpV
    obtain ⟨k₂, hk₂, hpk₂⟩ := List.getElem_of_mem hp'V
    have hk₁' : k₁ < P.verts.length := hk₁
    have hk₂' : k₂ < P.verts.length := hk₂
    have hlen := P.verts_len
    have hle3 := P.len_le
    have hk₁_pos : 0 < k₁ := by
      by_contra h; have : k₁ = 0 := by omega
      subst this; exact hp0 (hpk₁.symm.trans (thread_head_getElem P))
    have hk₁_lt : k₁ < P.edges.length := by
      by_contra h; have : k₁ = P.edges.length := by omega
      subst this; exact hpl (hpk₁.symm.trans (thread_last_getElem P))
    have hk₂_pos : 0 < k₂ := by
      by_contra h; have : k₂ = 0 := by omega
      subst this; exact hp'0 (hpk₂.symm.trans (thread_head_getElem P))
    have hk₂_lt : k₂ < P.edges.length := by
      by_contra h; have : k₂ = P.edges.length := by omega
      subst this; exact hp'l (hpk₂.symm.trans (thread_last_getElem P))
    have hk_ne : k₁ ≠ k₂ := fun h => hne (by subst h; exact hpk₁.symm.trans hpk₂)
    have hlen3 : P.edges.length = 3 := by omega
    have hstep1 := P.step_connect 1 (by omega)
    refine ⟨[p, p'], [P.edges[1]'(by omega)], rfl, by simp [hne],
      fun v hv => by simp at hv; rcases hv with rfl | rfl; exact hp; exact hp',
      fun e he => by simp at he; subst he; exact P.edges_sub _ (List.getElem_mem _),
      rfl, rfl, fun k hk => ?_, fun i => ?_⟩
    · have hk0 : k = 0 := by simp at hk; omega
      subst hk0
      dsimp only [List.getElem_cons_zero, List.getElem_cons_succ]
      have hcases : (k₁ = 1 ∧ k₂ = 2) ∨ (k₁ = 2 ∧ k₂ = 1) := by omega
      rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [← hpk₁, ← hpk₂]; exact hstep1
      · rw [← hpk₁, ← hpk₂]
        rcases hstep1 with h | h
        · exact Or.inr h
        · exact Or.inl h
    · calc ([P.edges[1]'(by omega)].toFinset.filter _).card
          ≤ [P.edges[1]'(by omega)].toFinset.card := Finset.card_filter_le _ _
        _ ≤ 1 := by simp
        _ ≤ 3 := by decide
  · -- Check Case 3: p and p' are interior vertices of the two threads of some pair N_i
    by_cases hcase3 : ∃ (i : Fin fr.numNodes) (t₁ t₂ : sub.E₀),
        IsInt p t₁ ∧ IsInt p' t₂ ∧
        ((aux.origEdge t₁ = fr.eNode i ∧ aux.origEdge t₂ = fr.fNode i) ∨
         (aux.origEdge t₁ = fr.fNode i ∧ aux.origEdge t₂ = fr.eNode i))
    · -- Case 3: route through op1V i or op2V i inside Te
      rcases hcase3 with ⟨i, t₁, t₂, ⟨hpV, hp0, hpl⟩, ⟨hp'V, hp'0, hp'l⟩, hpair⟩
      have hne_t : t₁ ≠ t₂ := by
        intro h; subst h
        rcases hpair with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact fr.e_ne_f i (h1.symm.trans h2)
        · exact fr.e_ne_f i (h2.symm.trans h1)
      have hcross₁ : (aux.Q.tail (aux.origEdge t₁) ∈ fr.op1V i ∧ aux.Q.head (aux.origEdge t₁) ∈ fr.op2V i) ∨
          (aux.Q.tail (aux.origEdge t₁) ∈ fr.op2V i ∧ aux.Q.head (aux.origEdge t₁) ∈ fr.op1V i) := by
        rcases hpair with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1]
        · exact fr.e_cross i
        · exact fr.f_cross i
      have hcross₂ : (aux.Q.tail (aux.origEdge t₂) ∈ fr.op1V i ∧ aux.Q.head (aux.origEdge t₂) ∈ fr.op2V i) ∨
          (aux.Q.tail (aux.origEdge t₂) ∈ fr.op2V i ∧ aux.Q.head (aux.origEdge t₂) ∈ fr.op1V i) := by
        rcases hpair with ⟨_, h2⟩ | ⟨_, h2⟩ <;> rw [h2]
        · exact fr.f_cross i
        · exact fr.e_cross i
      obtain ⟨k₁, hk₁, hpk₁⟩ := List.getElem_of_mem hpV
      obtain ⟨k₂, hk₂, hpk₂⟩ := List.getElem_of_mem hp'V
      have hk₁_le : k₁ ≤ (sub.thread t₁).edges.length := by have := (sub.thread t₁).verts_len; omega
      have hk₂_le : k₂ ≤ (sub.thread t₂).edges.length := by have := (sub.thread t₂).verts_len; omega
      -- Choose side U ∈ {op1V i, op2V i} with total subpath length ≤ 3
      have hside : ∃ (U : Finset aux.VQ) (x₁ x₂ : aux.VQ) (E₁ E₂ : List E),
          (U = fr.op1V i ∨ U = fr.op2V i) ∧
          x₁ ∈ U ∧ x₂ ∈ U ∧
          E₁.length + E₂.length ≤ 3 ∧
          (∀ e ∈ E₁, e ∈ (sub.thread t₁).edges) ∧
          (∀ e ∈ E₂, e ∈ (sub.thread t₂).edges) ∧
          (∀ L : G.Subgraph, (∀ e ∈ E₁, e ∈ L.edges) →
            Relation.ReflTransGen L.Adj p (sub.embedV (aux.contractV x₁))) ∧
          (∀ L : G.Subgraph, (∀ e ∈ E₂, e ∈ L.edges) →
            Relation.ReflTransGen L.Adj p' (sub.embedV (aux.contractV x₂))) := by
        -- For each t_r, get its op1V-end and op2V-end and corresponding subpath
        have hpick : ∀ (t : sub.E₀) (v : V) (k : ℕ) (hk : k < (sub.thread t).verts.length)
            (hv : (sub.thread t).verts[k]'hk = v)
            (hcr : (aux.Q.tail (aux.origEdge t) ∈ fr.op1V i ∧ aux.Q.head (aux.origEdge t) ∈ fr.op2V i) ∨
                   (aux.Q.tail (aux.origEdge t) ∈ fr.op2V i ∧ aux.Q.head (aux.origEdge t) ∈ fr.op1V i)),
            ∃ (x1 x2 : aux.VQ) (Ea Eb : List E),
              x1 ∈ fr.op1V i ∧ x2 ∈ fr.op2V i ∧
              Ea.length + Eb.length = (sub.thread t).edges.length ∧
              (∀ e ∈ Ea, e ∈ (sub.thread t).edges) ∧
              (∀ e ∈ Eb, e ∈ (sub.thread t).edges) ∧
              (∀ L : G.Subgraph, (∀ e ∈ Ea, e ∈ L.edges) →
                Relation.ReflTransGen L.Adj v (sub.embedV (aux.contractV x1))) ∧
              (∀ L : G.Subgraph, (∀ e ∈ Eb, e ∈ L.edges) →
                Relation.ReflTransGen L.Adj v (sub.embedV (aux.contractV x2))) := by
          intro t v k hk hv hcr
          have hkle : k ≤ (sub.thread t).edges.length := by have := (sub.thread t).verts_len; omega
          have hpre_reach : ∀ L : G.Subgraph, (∀ e ∈ (sub.thread t).edges.take k, e ∈ L.edges) →
              Relation.ReflTransGen L.Adj v (sub.embedV (sub.H₀.tail t)) := fun L hL =>
            subgraph_adj_symm (hv ▸ thread_prefix_reach (sub.thread t) L k hkle hL)
          have hsuf_reach : ∀ L : G.Subgraph, (∀ e ∈ (sub.thread t).edges.drop k, e ∈ L.edges) →
              Relation.ReflTransGen L.Adj v (sub.embedV (sub.H₀.head t)) := fun L hL =>
            hv ▸ thread_suffix_reach (sub.thread t) L k hkle hL
          have hlen_sum : ((sub.thread t).edges.take k).length + ((sub.thread t).edges.drop k).length =
              (sub.thread t).edges.length := by
            rw [List.length_take, List.length_drop]; omega
          rcases hcr with ⟨ht1, hh2⟩ | ⟨ht2, hh1⟩
          · exact ⟨aux.Q.tail (aux.origEdge t), aux.Q.head (aux.origEdge t),
              (sub.thread t).edges.take k, (sub.thread t).edges.drop k,
              ht1, hh2, hlen_sum,
              fun _ he => List.mem_of_mem_take he, fun _ he => List.mem_of_mem_drop he,
              fun L hL => by rw [aux.orig_tail t]; exact hpre_reach L hL,
              fun L hL => by rw [aux.orig_head t]; exact hsuf_reach L hL⟩
          · exact ⟨aux.Q.head (aux.origEdge t), aux.Q.tail (aux.origEdge t),
              (sub.thread t).edges.drop k, (sub.thread t).edges.take k,
              hh1, ht2, by omega,
              fun _ he => List.mem_of_mem_drop he, fun _ he => List.mem_of_mem_take he,
              fun L hL => by rw [aux.orig_head t]; exact hsuf_reach L hL,
              fun L hL => by rw [aux.orig_tail t]; exact hpre_reach L hL⟩
        obtain ⟨x1, y1, Ea1, Eb1, hx1, hy1, hsum1, hEa1, hEb1, hrEa1, hrEb1⟩ :=
          hpick t₁ p k₁ hk₁ hpk₁ hcross₁
        obtain ⟨x2, y2, Ea2, Eb2, hx2, hy2, hsum2, hEa2, hEb2, hrEa2, hrEb2⟩ :=
          hpick t₂ p' k₂ hk₂ hpk₂ hcross₂
        have hlen1 := (sub.thread t₁).len_le
        have hlen2 := (sub.thread t₂).len_le
        by_cases hle : Ea1.length + Ea2.length ≤ 3
        · exact ⟨fr.op1V i, x1, x2, Ea1, Ea2, Or.inl rfl, hx1, hx2, hle, hEa1, hEa2, hrEa1, hrEa2⟩
        · exact ⟨fr.op2V i, y1, y2, Eb1, Eb2, Or.inr rfl, hy1, hy2, by omega, hEb1, hEb2, hrEb1, hrEb2⟩
      obtain ⟨U, x₁, x₂, E₁, E₂, hUside, hx₁U, hx₂U, hE12_le, hE₁_t, hE₂_t, hr₁, hr₂⟩ := hside
      let S : Finset aux.EQ := fr.Te.edges.filter (fun eq => aux.Q.tail eq ∈ U ∧ aux.Q.head eq ∈ U)
      -- S is connected on U by (O1)
      have hS_conn : Relation.ReflTransGen
          (fun a b => ∃ eq ∈ S, (aux.Q.tail eq = a ∧ aux.Q.head eq = b) ∨
                                (aux.Q.tail eq = b ∧ aux.Q.head eq = a)) x₁ x₂ := by
        have hO1_e := (hO1 fr.eNode (fun _ => Or.inl rfl)).2 i
        rcases hUside with rfl | rfl
        · exact hO1_e.1.2 x₁ hx₁U x₂ hx₂U
        · exact hO1_e.2.2 x₁ hx₁U x₂ hx₂U
      -- Neither eNode i nor fNode i lies in S (both cross between disjoint op1V i and op2V i)
      have hnot_ei : fr.eNode i ∉ S := by
        intro hmem
        have ⟨htU, hhU⟩ := (Finset.mem_filter.mp hmem).2
        rcases hUside with rfl | rfl <;> rcases fr.e_cross i with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Finset.disjoint_left.mp (fr.stage_disj i) hhU h2
        · exact Finset.disjoint_left.mp (fr.stage_disj i) htU h1
        · exact Finset.disjoint_left.mp (fr.stage_disj i) h1 htU
        · exact Finset.disjoint_left.mp (fr.stage_disj i) h2 hhU
      have hnot_fi : fr.fNode i ∉ S := by
        intro hmem
        have ⟨htU, hhU⟩ := (Finset.mem_filter.mp hmem).2
        rcases hUside with rfl | rfl <;> rcases fr.f_cross i with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Finset.disjoint_left.mp (fr.stage_disj i) hhU h2
        · exact Finset.disjoint_left.mp (fr.stage_disj i) htU h1
        · exact Finset.disjoint_left.mp (fr.stage_disj i) h1 htU
        · exact Finset.disjoint_left.mp (fr.stage_disj i) h2 hhU
      -- No fNode j lies in S at all (since S ⊆ fr.Te.edges)
      have hnot_fj : ∀ j : Fin fr.numNodes, fr.fNode j ∉ S := by
        intro j hmem
        have hTe := (Finset.mem_filter.mp hmem).1
        simp only [Frame.Te, Frame.Tg, Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ,
          true_and, Finset.mem_image] at hTe
        rcases hTe with hred | ⟨l, heq⟩
        · exact hred (fr.f_blue j)
        · exact fNode_ne_eNode_any fr j l heq.symm
      -- Build subgraph L ≤ H containing threads in S plus E₁ and E₂
      let EL : Finset E :=
        (H.edges.filter (fun e => ∃ t : sub.E₀, aux.origEdge t ∈ S ∧ e ∈ (sub.thread t).edges)) ∪
        E₁.toFinset ∪ E₂.toFinset
      have hEL_sub : EL ⊆ H.edges := by
        intro e he
        simp only [EL, Finset.mem_union, Finset.mem_filter, List.mem_toFinset] at he
        rcases he with (⟨heH, _⟩ | he1) | he2
        · exact heH
        · exact (sub.thread t₁).edges_sub e (hE₁_t e he1)
        · exact (sub.thread t₂).edges_sub e (hE₂_t e he2)
      let L : G.Subgraph :=
        { verts := H.verts
          edges := EL
          tail_mem := fun he => H.tail_mem (hEL_sub he)
          head_mem := fun he => H.head_mem (hEL_sub he) }
      have hreach_x12 : Relation.ReflTransGen L.Adj
          (sub.embedV (aux.contractV x₁)) (sub.embedV (aux.contractV x₂)) :=
        lift_Q_walk_to_H S L (fun t ht e he => Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨(sub.thread t).edges_sub e he, t, ht, he⟩))) hS_conn
      have hreach_pp' : Relation.ReflTransGen L.Adj p p' :=
        ((hr₁ L fun e he => Finset.mem_union_left _ (Finset.mem_union_right _ (List.mem_toFinset.mpr he))).trans
          hreach_x12).trans
          (subgraph_adj_symm (hr₂ L fun e he => Finset.mem_union_right _ (List.mem_toFinset.mpr he)))
      obtain ⟨verts, edges, hlen, hnd, hvH, heL, hhead, hlast, hstep⟩ :=
        simplePath_in_sub (show L ≤ H from ⟨Finset.Subset.refl _, hEL_sub⟩) hp hne hreach_pp'
      refine ⟨verts, edges, hlen, hnd, hvH, fun e he => hEL_sub (heL e he), hhead, hlast, hstep, fun j => ?_⟩
      by_cases hji : j = i
      · subst hji
        -- Every edge of edges on N_i must come from E₁ ∪ E₂
        have hsub_12 : edges.toFinset.filter (fun e =>
            (∃ t : sub.E₀, aux.origEdge t = fr.eNode j ∧ e ∈ (sub.thread t).edges) ∨
            (∃ t : sub.E₀, aux.origEdge t = fr.fNode j ∧ e ∈ (sub.thread t).edges)) ⊆
            E₁.toFinset ∪ E₂.toFinset := by
          intro e he
          rw [Finset.mem_filter] at he
          have hmemL := heL e (List.mem_toFinset.mp he.1)
          simp only [L, EL, Finset.mem_union, Finset.mem_filter] at hmemL
          rcases hmemL with (⟨_, t, htS, het⟩ | he1) | he2
          · exfalso
            rcases he.2 with ⟨t', ht'e, het'⟩ | ⟨t', ht'f, het'⟩
            · have htt : t = t' := by
                by_contra hneq; exact sub.edges_disjoint t t' hneq e het het'
              subst htt; exact hnot_ei (ht'e ▸ htS)
            · have htt : t = t' := by
                by_contra hneq; exact sub.edges_disjoint t t' hneq e het het'
              subst htt; exact hnot_fi (ht'f ▸ htS)
          · exact Finset.mem_union_left _ he1
          · exact Finset.mem_union_right _ he2
        calc (edges.toFinset.filter _).card ≤ (E₁.toFinset ∪ E₂.toFinset).card := Finset.card_le_card hsub_12
          _ ≤ E₁.toFinset.card + E₂.toFinset.card := Finset.card_union_le _ _
          _ ≤ E₁.length + E₂.length := add_le_add (List.toFinset_card_le _) (List.toFinset_card_le _)
          _ ≤ 3 := hE12_le
      · -- j ≠ i: every edge of edges on N_j must come from the unique thread (if any) with origEdge t = eNode j
        by_cases hex_tj : ∃ t : sub.E₀, aux.origEdge t = fr.eNode j
        · rcases hex_tj with ⟨tj, htj⟩
          have hsub_tj : edges.toFinset.filter (fun e =>
              (∃ t : sub.E₀, aux.origEdge t = fr.eNode j ∧ e ∈ (sub.thread t).edges) ∨
              (∃ t : sub.E₀, aux.origEdge t = fr.fNode j ∧ e ∈ (sub.thread t).edges)) ⊆
              (sub.thread tj).edges.toFinset := by
            intro e he
            rw [Finset.mem_filter] at he
            have hmemL := heL e (List.mem_toFinset.mp he.1)
            simp only [L, EL, Finset.mem_union, Finset.mem_filter, List.mem_toFinset] at hmemL
            rcases he.2 with ⟨t', ht'e, het'⟩ | ⟨t', ht'f, het'⟩
            · have hteq : t' = tj := aux.origEdge.injective (ht'e.trans htj.symm)
              subst hteq; exact List.mem_toFinset.mpr het'
            · exfalso
              rcases hmemL with (⟨_, t, htS, het⟩ | he1) | he2
              · have htt : t = t' := by
                  by_contra hneq; exact sub.edges_disjoint t t' hneq e het het'
                subst htt; exact hnot_fj j (ht'f ▸ htS)
              · have htt : t₁ = t' := by
                  by_contra hneq; exact sub.edges_disjoint t₁ t' hneq e (hE₁_t e he1) het'
                subst htt
                rcases hpair with ⟨h1, _⟩ | ⟨h1, _⟩
                · exact fNode_ne_eNode_any fr j i (ht'f.symm.trans h1)
                · exact hji (fNode_inj fr (ht'f.symm.trans h1))
              · have htt : t₂ = t' := by
                  by_contra hneq; exact sub.edges_disjoint t₂ t' hneq e (hE₂_t e he2) het'
                subst htt
                rcases hpair with ⟨_, h2⟩ | ⟨_, h2⟩
                · exact hji (fNode_inj fr (ht'f.symm.trans h2))
                · exact fNode_ne_eNode_any fr j i (ht'f.symm.trans h2)
          exact (Finset.card_le_card hsub_tj).trans
            ((List.toFinset_card_le _).trans (sub.thread tj).len_le)
        · -- No original thread has origEdge t = eNode j, and fNode j is excluded too -> card = 0 ≤ 3
          have hempty : edges.toFinset.filter (fun e =>
              (∃ t : sub.E₀, aux.origEdge t = fr.eNode j ∧ e ∈ (sub.thread t).edges) ∨
              (∃ t : sub.E₀, aux.origEdge t = fr.fNode j ∧ e ∈ (sub.thread t).edges)) = ∅ := by
            ext e
            simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
            intro heM hcond
            rcases hcond with ⟨t', ht'e, _⟩ | ⟨t', ht'f, het'⟩
            · exact hex_tj ⟨t', ht'e⟩
            · have hmemL := heL e (List.mem_toFinset.mp heM)
              simp only [L, EL, Finset.mem_union, Finset.mem_filter, List.mem_toFinset] at hmemL
              rcases hmemL with (⟨_, t, htS, het⟩ | he1) | he2
              · have htt : t = t' := by
                  by_contra hneq; exact sub.edges_disjoint t t' hneq e het het'
                subst htt; exact hnot_fj j (ht'f ▸ htS)
              · have htt : t₁ = t' := by
                  by_contra hneq; exact sub.edges_disjoint t₁ t' hneq e (hE₁_t e he1) het'
                subst htt
                rcases hpair with ⟨h1, _⟩ | ⟨h1, _⟩
                · exact fNode_ne_eNode_any fr j i (ht'f.symm.trans h1)
                · exact hji (fNode_inj fr (ht'f.symm.trans h1))
              · have htt : t₂ = t' := by
                  by_contra hneq; exact sub.edges_disjoint t₂ t' hneq e (hE₂_t e he2) het'
                subst htt
                rcases hpair with ⟨_, h2⟩ | ⟨_, h2⟩
                · exact hji (fNode_inj fr (ht'f.symm.trans h2))
                · exact fNode_ne_eNode_any fr j i (ht'f.symm.trans h2)
          rw [hempty, Finset.card_empty]; omega
    · -- Case 2: pick g i = fNode i if p or p' is interior to fNode i's thread, else eNode i
      let g : Fin fr.numNodes → aux.EQ := fun i =>
        if ∃ t : sub.E₀, aux.origEdge t = fr.fNode i ∧ (IsInt p t ∨ IsInt p' t) then
          fr.fNode i
        else fr.eNode i
      have hg_valid : ∀ i, g i = fr.eNode i ∨ g i = fr.fNode i := fun i => by
        dsimp only [g]; split_ifs
        · exact Or.inr rfl
        · exact Or.inl rfl
      -- Both p and p' lie on threads in (fr.Tg g).edges (or are branch vertices)
      have hInt_in_Tg : ∀ (v : V) (hv_is : v = p ∨ v = p') (t : sub.E₀), IsInt v t →
          aux.origEdge t ∈ (fr.Tg g).edges := by
        intro v hv_is t hvt
        by_cases hbl : aux.origEdge t ∈ fr.blue
        · obtain ⟨i, hi, _⟩ := fr.blue_unique (aux.origEdge t) hbl
          refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, ?_⟩)
          rcases hi with heq | heq
          · -- origEdge t = eNode i: show g i = eNode i (otherwise Case 3 or Case 1!)
            dsimp only [g]
            rw [if_neg]
            · exact heq.symm
            · rintro ⟨t', ht'f, hpt' | hp't'⟩
              · rcases hv_is with rfl | rfl
                · have htt : t = t' := by
                    by_contra hneq; exact sub.interior_disjoint t t' hneq v hvt hpt'
                  subst htt; exact fr.e_ne_f i (heq.symm.trans ht'f)
                · exact hcase3 ⟨i, t', t, hpt', hvt, Or.inr ⟨ht'f, heq⟩⟩
              · rcases hv_is with rfl | rfl
                · exact hcase3 ⟨i, t, t', hvt, hp't', Or.inl ⟨heq, ht'f⟩⟩
                · have htt : t = t' := by
                    by_contra hneq; exact sub.interior_disjoint t t' hneq v hvt hp't'
                  subst htt; exact fr.e_ne_f i (heq.symm.trans ht'f)
          · -- origEdge t = fNode i: then g i = fNode i!
            dsimp only [g]
            rw [if_pos]
            · exact heq.symm
            · exact ⟨t, heq, by rcases hv_is with rfl | rfl; exact Or.inl hvt; exact Or.inr hvt⟩
        · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hbl⟩)
      -- Build subgraph Hg ≤ H from all threads with origEdge t ∈ (fr.Tg g).edges
      let EL : Finset E :=
        H.edges.filter (fun e => ∃ t : sub.E₀, aux.origEdge t ∈ (fr.Tg g).edges ∧ e ∈ (sub.thread t).edges)
      have hEL_sub : EL ⊆ H.edges := Finset.filter_subset _ _
      let Hg : G.Subgraph :=
        { verts := H.verts
          edges := EL
          tail_mem := fun he => H.tail_mem (hEL_sub he)
          head_mem := fun he => H.head_mem (hEL_sub he) }
      -- Show all branch vertices are mutually connected in Hg via (O1) + H0_connected
      have hbranch_conn : ∀ u₀ v₀ : sub.V₀,
          Relation.ReflTransGen Hg.Adj (sub.embedV u₀) (sub.embedV v₀) := by
        intro u₀ v₀
        have hH0 := H0_connected sub.H₀ sub.edgeConn3 u₀ v₀
        induction hH0 with
        | refl => exact .refl
        | @tail a b _ hstep ih =>
          rcases hstep with ⟨t, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
          · let bl := aux.comp (aux.Q.tail (aux.origEdge t))
            have hconn_b := (hO1 g hg_valid).1 bl
            have htVb : aux.Q.tail (aux.origEdge t) ∈ Finset.univ.filter (fun v => aux.comp v = bl) :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
            have hhVb : aux.Q.head (aux.origEdge t) ∈ Finset.univ.filter (fun v => aux.comp v = bl) :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, (aux.edge_same_comp _).symm⟩
            have hQwalk := hconn_b.2 _ htVb _ hhVb
            have hHwalk := lift_Q_walk_to_H
              ((fr.Tg g).edges.filter (fun eq => aux.Q.tail eq ∈ Finset.univ.filter (fun v => aux.comp v = bl) ∧
                aux.Q.head eq ∈ Finset.univ.filter (fun v => aux.comp v = bl)))
              Hg (fun t' ht' e he => Finset.mem_filter.mpr ⟨(sub.thread t').edges_sub e he, t',
                (Finset.mem_filter.mp ht').1, he⟩) hQwalk
            rw [aux.orig_tail t, aux.orig_head t, h1, h2] at hHwalk
            exact ih.trans hHwalk
          · let bl := aux.comp (aux.Q.tail (aux.origEdge t))
            have hconn_b := (hO1 g hg_valid).1 bl
            have htVb : aux.Q.tail (aux.origEdge t) ∈ Finset.univ.filter (fun v => aux.comp v = bl) :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
            have hhVb : aux.Q.head (aux.origEdge t) ∈ Finset.univ.filter (fun v => aux.comp v = bl) :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, (aux.edge_same_comp _).symm⟩
            have hQwalk := hconn_b.2 _ hhVb _ htVb
            have hHwalk := lift_Q_walk_to_H
              ((fr.Tg g).edges.filter (fun eq => aux.Q.tail eq ∈ Finset.univ.filter (fun v => aux.comp v = bl) ∧
                aux.Q.head eq ∈ Finset.univ.filter (fun v => aux.comp v = bl)))
              Hg (fun t' ht' e he => Finset.mem_filter.mpr ⟨(sub.thread t').edges_sub e he, t',
                (Finset.mem_filter.mp ht').1, he⟩) hQwalk
            rw [aux.orig_tail t, aux.orig_head t, h1, h2] at hHwalk
            exact ih.trans hHwalk
      -- Both p and p' reach some branch vertex in Hg
      have hv_to_branch : ∀ v : V, v ∈ H.verts → (v = p ∨ v = p') →
          ∃ v₀ : sub.V₀, Relation.ReflTransGen Hg.Adj v (sub.embedV v₀) := by
        intro v hvH hv_is
        rcases sub.verts_cover v hvH with ⟨v₀, rfl⟩ | ⟨t, hvt⟩
        · exact ⟨v₀, .refl⟩
        · by_cases ht1 : v = sub.embedV (sub.H₀.tail t)
          · exact ⟨sub.H₀.tail t, by rw [ht1]⟩
          · by_cases ht2 : v = sub.embedV (sub.H₀.head t)
            · exact ⟨sub.H₀.head t, by rw [ht2]⟩
            · have hinTg := hInt_in_Tg v hv_is t ⟨hvt, ht1, ht2⟩
              obtain ⟨k, hk, hvk⟩ := List.getElem_of_mem hvt
              have hkle : k ≤ (sub.thread t).edges.length := by have := (sub.thread t).verts_len; omega
              refine ⟨sub.H₀.head t, hvk ▸ thread_suffix_reach (sub.thread t) Hg k hkle fun e he => ?_⟩
              exact Finset.mem_filter.mpr ⟨(sub.thread t).edges_sub e (List.mem_of_mem_drop he),
                t, hinTg, List.mem_of_mem_drop he⟩
      obtain ⟨u₀, hpu₀⟩ := hv_to_branch p hp (Or.inl rfl)
      obtain ⟨v₀, hp'v₀⟩ := hv_to_branch p' hp' (Or.inr rfl)
      have hreach_pp' : Relation.ReflTransGen Hg.Adj p p' :=
        (hpu₀.trans (hbranch_conn u₀ v₀)).trans (subgraph_adj_symm hp'v₀)
      obtain ⟨verts, edges, hlen, hnd, hvH, heL, hhead, hlast, hstep⟩ :=
        simplePath_in_sub (show Hg ≤ H from ⟨Finset.Subset.refl _, hEL_sub⟩) hp hne hreach_pp'
      refine ⟨verts, edges, hlen, hnd, hvH, fun e he => hEL_sub (heL e he), hhead, hlast, hstep, fun j => ?_⟩
      -- Every edge of edges on N_j must come from g j's thread (if any)
      have hgi_only : ∀ eq : aux.EQ, eq ∈ (fr.Tg g).edges → (eq = fr.eNode j ∨ eq = fr.fNode j) → eq = g j := by
        intro eq heqTg hor
        have hbl : eq ∈ fr.blue := by rcases hor with rfl | rfl; exact fr.e_blue j; exact fr.f_blue j
        simp only [Frame.Tg, Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and,
          Finset.mem_image] at heqTg
        rcases heqTg with hred | ⟨l, rfl⟩
        · exact absurd hbl hred
        · obtain ⟨k, _, huniq⟩ := fr.blue_unique (g l) (by rcases hg_valid l with h | h <;> rw [h]; exact fr.e_blue l; exact fr.f_blue l)
          have hjl : j = l := (huniq j hor).trans (huniq l (hg_valid l)).symm
          rw [hjl]
      by_cases hex_tj : ∃ t : sub.E₀, aux.origEdge t = g j
      · rcases hex_tj with ⟨tj, htj⟩
        have hsub_tj : edges.toFinset.filter (fun e =>
            (∃ t : sub.E₀, aux.origEdge t = fr.eNode j ∧ e ∈ (sub.thread t).edges) ∨
            (∃ t : sub.E₀, aux.origEdge t = fr.fNode j ∧ e ∈ (sub.thread t).edges)) ⊆
            (sub.thread tj).edges.toFinset := by
          intro e he
          rw [Finset.mem_filter] at he
          have hmemL := heL e (List.mem_toFinset.mp he.1)
          obtain ⟨t, htTg, het⟩ := (Finset.mem_filter.mp hmemL).2
          have hor : aux.origEdge t = fr.eNode j ∨ aux.origEdge t = fr.fNode j := by
            rcases he.2 with ⟨t', ht'e, het'⟩ | ⟨t', ht'f, het'⟩
            · have htt : t = t' := by by_contra hneq; exact sub.edges_disjoint t t' hneq e het het'
              exact Or.inl (htt ▸ ht'e)
            · have htt : t = t' := by by_contra hneq; exact sub.edges_disjoint t t' hneq e het het'
              exact Or.inr (htt ▸ ht'f)
          have hteq : t = tj := aux.origEdge.injective ((hgi_only _ htTg hor).trans htj.symm)
          subst hteq; exact List.mem_toFinset.mpr het
        exact (Finset.card_le_card hsub_tj).trans
          ((List.toFinset_card_le _).trans (sub.thread tj).len_le)
      · have hempty : edges.toFinset.filter (fun e =>
            (∃ t : sub.E₀, aux.origEdge t = fr.eNode j ∧ e ∈ (sub.thread t).edges) ∨
            (∃ t : sub.E₀, aux.origEdge t = fr.fNode j ∧ e ∈ (sub.thread t).edges)) = ∅ := by
          ext e
          simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
          intro heM hcond
          have hmemL := heL e (List.mem_toFinset.mp heM)
          obtain ⟨t, htTg, het⟩ := (Finset.mem_filter.mp hmemL).2
          have hor : aux.origEdge t = fr.eNode j ∨ aux.origEdge t = fr.fNode j := by
            rcases hcond with ⟨t', ht'e, het'⟩ | ⟨t', ht'f, het'⟩
            · have htt : t = t' := by by_contra hneq; exact sub.edges_disjoint t t' hneq e het het'
              exact Or.inl (htt ▸ ht'e)
            · have htt : t = t' := by by_contra hneq; exact sub.edges_disjoint t t' hneq e het het'
              exact Or.inr (htt ▸ ht'f)
          exact hex_tj ⟨t, hgi_only _ htTg hor⟩
        rw [hempty, Finset.card_empty]; omega

/-! ### Lemma 4.8(SUB): Lifting a contracted move in case `(SUB)` -/

theorem lem_4_8_sub_of
    {Γ : Type} [AddCommGroup Γ] [Fintype Γ] [DecidableEq Γ]
    (B : AddSubgroup Γ) [Fintype (Γ ⧸ B)] [Fintype B] [DecidableEq (Γ ⧸ B)] [DecidableEq B]
    (hA : 10 ≤ Fintype.card (Γ ⧸ B)) (hB : 4 ≤ Fintype.card B)
    (Sig : StepSystem Γ) (hR1 : CondR1 B Sig) (hR2 : CondR2 B Sig)
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : Multigraph V E) (_hbr : G.IsBridgeless)
    (H : G.Subgraph) (sub : SubdivisionData G H)
    (aux : AuxGraphData G H sub) (fr : Frame G H sub aux)
    (C_off : Fin fr.numNodes → aux.Q.DirectedCycle)
    (hO1 : ∀ g : Fin fr.numNodes → aux.EQ, (∀ i, g i = fr.eNode i ∨ g i = fr.fNode i) →
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
          (fun he => (Finset.mem_filter.mp he).2.2)).Connected))
    (hO2 : ∀ i, fr.eNode i ∈ (C_off i).sub.edges ∧ fr.fNode i ∈ (C_off i).sub.edges)
    (hO3 : ∀ l i : Fin fr.numNodes, l < i →
      fr.eNode i ∉ (C_off l).sub.edges ∧ fr.fNode i ∉ (C_off l).sub.edges)
    (hO4 : ∀ l i : Fin fr.numNodes, i < l → fr.fNode i ∉ (C_off l).sub.edges)
    (hO5A : ∀ Y : aux.EQ → Γ ⧸ B, aux.Q.IsFlow Y →
      ∃! x : Fin fr.numNodes → Γ ⧸ B,
        ∀ eq, Y eq = ∑ i : Fin fr.numNodes, (C_off i).sign eq • x i)
    (hO5Z : ∀ Y : aux.EQ → ℤ, aux.Q.IsFlow Y →
      ∃! x : Fin fr.numNodes → ℤ,
        ∀ eq, Y eq = ∑ i : Fin fr.numNodes, (C_off i).sign eq • x i)
    (hO6_HP : fr.HProtected.Connected ∧
      ∀ v ∈ H.verts, (∀ t : sub.E₀, fr.IsFree t →
        ¬ (v ∈ (sub.thread t).verts ∧ v ≠ sub.embedV (sub.H₀.tail t) ∧ v ≠ sub.embedV (sub.H₀.head t))) →
        v ∈ fr.HProtected.verts)
    (hO6_free : ∀ eps : sub.E₀, fr.IsFree eps →
      ∃ D : G.DirectedCycle,
        D.sub ≤ H ∧
        (∀ e ∈ (sub.thread eps).edges, e ∈ D.sub.edges ∧ D.sign e = 1) ∧
        (∀ t : sub.E₀, fr.IsFree t → t ≠ eps →
          ∀ e ∈ (sub.thread t).edges, e ∉ D.sub.edges))
    (h36a_cyc : ∀ (O : H.toMultigraph.DirectedCycle) (t : sub.E₀),
      ∃ s : ℤ, (s = 1 ∨ s = 0 ∨ s = -1) ∧
        ∀ e (he : e ∈ (sub.thread t).edges), O.sign ⟨e, (sub.thread t).edges_sub e he⟩ = s)
    (h36d : ∀ C : aux.Q.DirectedCycle,
      ∃ (cycles : List G.DirectedCycle),
        (∀ O ∈ cycles, O.sub ≤ H) ∧
        (∀ i j (hi : i < cycles.length) (hj : j < cycles.length), i ≠ j →
          Disjoint (cycles[i]'hi).sub.edges (cycles[j]'hj).sub.edges) ∧
        (∀ (x : Γ ⧸ B) (e : E),
          aux.pi (fun eq => C.sign eq • x) e =
            (cycles.map (fun O => O.sign e • x)).sum))
    (hdef312 : ∀ f₀ : G.NZFlow Γ, IsHGoodSub fr B f₀ →
      (∀ t : aux.EQ, ((LamOfFlow B fr f₀).list t).card ≤ 3) ∧
      (0 : aux.EQ → Γ ⧸ B) ∈ PLam (LamOfFlow B fr f₀) ∧
      (∀ Y : aux.EQ → Γ ⧸ B, aux.Q.IsFlow Y →
        (Y ∈ PLam (LamOfFlow B fr f₀) ↔
          ∀ t : sub.E₀, fr.IsProtected t → ∀ e ∈ (sub.thread t).edges,
            quoFlow B f₀.val e + aux.pi Y e ≠ 0)))
    (f : G.NZFlow Γ) (hHgood : IsHGoodSub fr B f)
    (gstar : (G.contractSubgraph H).NZFlow Γ)
    (hmove : ∃ (Cstar : (G.contractSubgraph H).DirectedCycle) (lam : Γ),
      lam ∈ Sig.carrier ∧ ∀ e, gstar.val e = f.val e.1 + Cstar.sign e • lam) :
    ∃ g : G.NZFlow Γ,
      G.SigmaJoined Sig.carrier f g ∧
      (∀ e : {e : E // e ∉ H.edges}, g.val e.1 = gstar.val e) ∧
      IsHGoodSub fr B g := by
  classical
  have hpi_eq : ∀ (Y : aux.EQ → Γ ⧸ B) (t : sub.E₀) (e : E),
      e ∈ (sub.thread t).edges → aux.pi Y e = Y (aux.origEdge t) := by
    intro Y t e het
    have hex : ∃ t' : sub.E₀, e ∈ (sub.thread t').edges := ⟨t, het⟩
    unfold AuxGraphData.pi
    rw [dif_pos hex]
    congr 2
    by_contra hne
    exact sub.edges_disjoint _ t hne e hex.choose_spec het
  have hjoin_of_in : ∀ {S : Set Γ} {f₁ f₂ : G.NZFlow Γ},
      (∀ x ∈ S, x ∈ Sig.carrier) → G.SigmaJoinedIn H S f₁ f₂ → G.SigmaJoined Sig.carrier f₁ f₂ := by
    intro S f₁ f₂ hsub h
    induction h with
    | refl => exact .refl
    | tail _ hs ih =>
      rcases hs with ⟨C, z, _, hz, heq⟩
      exact ih.tail ⟨C, z, hsub z hz, heq⟩
  rcases hmove with ⟨Cstar, lam, hlam, hgstar⟩
  rcases liftContractedCycle G H Cstar with ⟨C, hCdisj, hCsign⟩ | ⟨p, p', hpH, hp'H, hne, hsplice⟩
  · -- Direct lift: C is disjoint from H.edges
    let gVal : E → Γ := fun e => f.val e + C.sign e • lam
    have hg_flow : G.IsFlow gVal := isFlow_add f.isFlow (isFlow_zsmul C.isFlow lam)
    have hg_off : ∀ e : {e : E // e ∉ H.edges}, gVal e.1 = gstar.val e := fun e => by
      dsimp only [gVal]; rw [hCsign e.1 e.2, hgstar e]
    have hg_on : ∀ e ∈ H.edges, gVal e = f.val e := fun e he => by
      have hnot : e ∉ C.sub.edges := Finset.disjoint_right.mp hCdisj he
      dsimp only [gVal]; rw [C.sign_zero hnot, zero_zsmul, add_zero]
    have hg_nz : Multigraph.IsNowhereZero gVal := fun e => by
      by_cases he : e ∈ H.edges
      · rw [hg_on e he]; exact f.nonzero e
      · rw [hg_off ⟨e, he⟩]; exact gstar.nonzero ⟨e, he⟩
    let g : G.NZFlow Γ := ⟨gVal, hg_flow, hg_nz⟩
    refine ⟨g, Relation.ReflTransGen.single ⟨C, lam, hlam, fun _ => rfl⟩, hg_off, fun t ht e het => ?_⟩
    have heH : e ∈ H.edges := (sub.thread t).edges_sub e het
    show quoFlow B gVal e ≠ 0
    rw [show quoFlow B gVal e = quoFlow B f.val e by simp [quoFlow, hg_on e heH]]
    exact hHgood t ht e het
  · -- Splice cases: split on QuotientAddGroup.mk lam = 0
    by_cases hqlam : QuotientAddGroup.mk (s := B) lam = 0
    · -- Case 3: lam ∈ B; build a path J meeting at most 2 free threads, each in 1 edge!
      let IsFreeInt (v : V) (t : sub.E₀) : Prop :=
        fr.IsFree t ∧ v ∈ (sub.thread t).verts ∧
        v ≠ sub.embedV (sub.H₀.tail t) ∧ v ≠ sub.embedV (sub.H₀.head t)
      have hJ3 : ∃ (verts : List V) (edges : List E) (_ : verts.length = edges.length + 1),
          verts.Nodup ∧ (∀ v ∈ verts, v ∈ H.verts) ∧ (∀ e ∈ edges, e ∈ H.edges) ∧
          verts.head? = some p ∧ verts.getLast? = some p' ∧
          (∀ (k : ℕ) (hk : k < edges.length),
            let u := verts[k]'(by omega); let w := verts[k + 1]'(by omega); let e := edges[k]'hk
            (G.tail e = u ∧ G.head e = w) ∨ (G.tail e = w ∧ G.head e = u)) ∧
          ∃ (Efree : Finset E), Efree.card ≤ 2 ∧
            (∀ e ∈ edges, (∃ t : sub.E₀, fr.IsProtected t ∧ e ∈ (sub.thread t).edges) ∨ e ∈ Efree) ∧
            (∀ t : sub.E₀, fr.IsFree t → ∀ e₁ ∈ Efree, ∀ e₂ ∈ Efree,
              e₁ ∈ (sub.thread t).edges → e₂ ∈ (sub.thread t).edges → e₁ = e₂) := by
        by_cases hsame : ∃ t : sub.E₀, IsFreeInt p t ∧ IsFreeInt p' t
        · -- Subcase 3a: same free thread -> 1-edge path
          rcases hsame with ⟨t, ⟨_, hpV, hp0, hpl⟩, ⟨_, hp'V, hp'0, hp'l⟩⟩
          let P := sub.thread t
          obtain ⟨k₁, hk₁, hpk₁⟩ := List.getElem_of_mem hpV
          obtain ⟨k₂, hk₂, hpk₂⟩ := List.getElem_of_mem hp'V
          have hk₁' : k₁ < P.verts.length := hk₁
          have hk₂' : k₂ < P.verts.length := hk₂
          have hlen := P.verts_len; have hle3 := P.len_le
          have hk₁_pos : 0 < k₁ := by
            by_contra h; have : k₁ = 0 := by omega
            subst this; exact hp0 (hpk₁.symm.trans (thread_head_getElem P))
          have hk₁_lt : k₁ < P.edges.length := by
            by_contra h; have : k₁ = P.edges.length := by omega
            subst this; exact hpl (hpk₁.symm.trans (thread_last_getElem P))
          have hk₂_pos : 0 < k₂ := by
            by_contra h; have : k₂ = 0 := by omega
            subst this; exact hp'0 (hpk₂.symm.trans (thread_head_getElem P))
          have hk₂_lt : k₂ < P.edges.length := by
            by_contra h; have : k₂ = P.edges.length := by omega
            subst this; exact hp'l (hpk₂.symm.trans (thread_last_getElem P))
          have hk_ne : k₁ ≠ k₂ := fun h => hne (by subst h; exact hpk₁.symm.trans hpk₂)
          have hlen3 : P.edges.length = 3 := by omega
          have hstep1 := P.step_connect 1 (by omega)
          let emid := P.edges[1]'(by omega)
          refine ⟨[p, p'], [emid], rfl, by simp [hne],
            fun v hv => by simp at hv; rcases hv with rfl | rfl; exact hpH; exact hp'H,
            fun e he => by simp at he; subst he; exact P.edges_sub _ (List.getElem_mem _),
            rfl, rfl, fun k hk => ?_, {emid}, by simp, fun e he => Or.inr (by simpa using he),
            fun _ _ e₁ h1 e₂ h2 _ _ => (Finset.mem_singleton.mp h1).trans (Finset.mem_singleton.mp h2).symm⟩
          have hk0 : k = 0 := by simp at hk; omega
          subst hk0
          dsimp only [List.getElem_cons_zero, List.getElem_cons_succ, emid]
          have hcases : (k₁ = 1 ∧ k₂ = 2) ∨ (k₁ = 2 ∧ k₂ = 1) := by omega
          rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · rw [← hpk₁, ← hpk₂]; exact hstep1
          · rw [← hpk₁, ← hpk₂]
            rcases hstep1 with h | h
            · exact Or.inr h
            · exact Or.inl h
        · -- Subcase 3b: step at most 1 edge from p and p' into fr.HProtected
          have hstep_to_HP : ∀ v ∈ H.verts,
              (v ∈ fr.HProtected.verts) ∨
              (∃ (t : sub.E₀) (e : E) (q : V),
                IsFreeInt v t ∧ e ∈ (sub.thread t).edges ∧ q ∈ fr.HProtected.verts ∧
                ((G.tail e = v ∧ G.head e = q) ∨ (G.tail e = q ∧ G.head e = v))) := by
            intro v hvH
            by_cases hHP : v ∈ fr.HProtected.verts
            · exact Or.inl hHP
            · right
              have hex : ∃ t : sub.E₀, IsFreeInt v t := by
                by_contra hno; push Not at hno
                exact hHP (hO6_HP.2 v hvH fun t ht h => hno t ⟨ht, h⟩)
              rcases hex with ⟨t, hvt⟩
              let P := sub.thread t
              obtain ⟨k, hk, hvk⟩ := List.getElem_of_mem hvt.2.1
              have hk' : k < P.verts.length := hk
              have hlen := P.verts_len; have hle3 := P.len_le
              have hk_pos : 0 < k := by
                by_contra h; have : k = 0 := by omega
                subst this; exact hvt.2.2.1 (hvk.symm.trans (thread_head_getElem P))
              have hk_lt : k < P.edges.length := by
                by_contra h; have : k = P.edges.length := by omega
                subst this; exact hvt.2.2.2 (hvk.symm.trans (thread_last_getElem P))
              -- Either k = 1 (adjacent to tail branch vertex) or k = P.edges.length - 1 (adjacent to head branch vertex)
              have hbr_HP : ∀ v₀ : sub.V₀, sub.embedV v₀ ∈ fr.HProtected.verts := fun v₀ =>
                hO6_HP.2 (sub.embedV v₀) (sub.embedV_mem v₀) fun t' _ ⟨hv', h1, h2⟩ =>
                  sub.interior_disjoint_branch t' _ hv' h1 h2 v₀ rfl
              by_cases hk1 : k = 1
              · subst hk1
                have hs0 := P.step_connect 0 (by omega)
                rw [thread_head_getElem P, hvk] at hs0
                refine ⟨t, P.edges[0]'(by omega), sub.embedV (sub.H₀.tail t), hvt,
                  List.getElem_mem _, hbr_HP _, ?_⟩
                rcases hs0 with h | h
                · exact Or.inr h
                · exact Or.inl h
              · have hk_eq : k + 1 = P.edges.length := by omega
                have hs := P.step_connect k hk_lt
                have hlast_eq : P.verts[k + 1]'(by omega) = sub.embedV (sub.H₀.head t) := by
                  convert thread_last_getElem P using 2
                rw [hvk, hlast_eq] at hs
                exact ⟨t, P.edges[k]'hk_lt, sub.embedV (sub.H₀.head t), hvt,
                  List.getElem_mem _, hbr_HP _, hs⟩
          -- Build Efree (0, 1, or 2 edges) and subgraph L = fr.HProtected ∪ Efree
          have hpick_p : ∃ (Ep : Finset E) (q : V),
              Ep.card ≤ 1 ∧ (∀ e ∈ Ep, e ∈ H.edges) ∧
              (∀ e ∈ Ep, ∃ t : sub.E₀, IsFreeInt p t ∧ e ∈ (sub.thread t).edges) ∧
              q ∈ fr.HProtected.verts ∧
              (∀ L : G.Subgraph, Ep ⊆ L.edges → Relation.ReflTransGen L.Adj p q) := by
            rcases hstep_to_HP p hpH with hHP | ⟨t, e, q, hpt, het, hqHP, hinc⟩
            · exact ⟨∅, p, by simp, fun _ h => absurd h (Finset.notMem_empty _),
                fun _ h => absurd h (Finset.notMem_empty _), hHP, fun _ _ => .refl⟩
            · exact ⟨{e}, q, by simp, fun e' he' => (Finset.mem_singleton.mp he') ▸ (sub.thread t).edges_sub e het,
                fun e' he' => ⟨t, hpt, (Finset.mem_singleton.mp he') ▸ het⟩, hqHP,
                fun L hL => Relation.ReflTransGen.single ⟨e, hL (Finset.mem_singleton_self e), hinc⟩⟩
          have hpick_p' : ∃ (Ep' : Finset E) (q' : V),
              Ep'.card ≤ 1 ∧ (∀ e ∈ Ep', e ∈ H.edges) ∧
              (∀ e ∈ Ep', ∃ t : sub.E₀, IsFreeInt p' t ∧ e ∈ (sub.thread t).edges) ∧
              q' ∈ fr.HProtected.verts ∧
              (∀ L : G.Subgraph, Ep' ⊆ L.edges → Relation.ReflTransGen L.Adj p' q') := by
            rcases hstep_to_HP p' hp'H with hHP | ⟨t, e, q', hp't, het, hq'HP, hinc⟩
            · exact ⟨∅, p', by simp, fun _ h => absurd h (Finset.notMem_empty _),
                fun _ h => absurd h (Finset.notMem_empty _), hHP, fun _ _ => .refl⟩
            · exact ⟨{e}, q', by simp, fun e' he' => (Finset.mem_singleton.mp he') ▸ (sub.thread t).edges_sub e het,
                fun e' he' => ⟨t, hp't, (Finset.mem_singleton.mp he') ▸ het⟩, hq'HP,
                fun L hL => Relation.ReflTransGen.single ⟨e, hL (Finset.mem_singleton_self e), hinc⟩⟩
          obtain ⟨Ep, q, hEp_le, hEp_H, hEp_int, hqHP, hrp⟩ := hpick_p
          obtain ⟨Ep', q', hEp'_le, hEp'_H, hEp'_int, hq'HP, hrp'⟩ := hpick_p'
          let Efree : Finset E := Ep ∪ Ep'
          let EL : Finset E := fr.HProtected.edges ∪ Efree
          have hEL_sub : EL ⊆ H.edges := by
            intro e he
            rw [Finset.mem_union] at he
            rcases he with he | he
            · exact (Finset.mem_filter.mp he).1
            · rw [Finset.mem_union] at he
              rcases he with h | h; exact hEp_H e h; exact hEp'_H e h
          let L : G.Subgraph :=
            { verts := H.verts, edges := EL,
              tail_mem := fun he => H.tail_mem (hEL_sub he),
              head_mem := fun he => H.head_mem (hEL_sub he) }
          have hHP_reach : Relation.ReflTransGen L.Adj q q' := by
            have h := hO6_HP.1.2 q hqHP q' hq'HP
            clear hq'HP hrp'
            induction h with
            | refl => exact .refl
            | tail _ hs ih =>
              rcases hs with ⟨e, heHP, hinc⟩
              exact ih.tail ⟨e, Finset.mem_union_left _ heHP, hinc⟩
          have hreach_pp' : Relation.ReflTransGen L.Adj p p' :=
            ((hrp L (Finset.subset_union_left.trans Finset.subset_union_right)).trans hHP_reach).trans
              (subgraph_adj_symm (hrp' L (Finset.subset_union_right.trans Finset.subset_union_right)))
          obtain ⟨verts, edges, hlen, hnd, hvH, heL, hhead, hlast, hstep⟩ :=
            simplePath_in_sub (show L ≤ H from ⟨Finset.Subset.refl _, hEL_sub⟩) hpH hne hreach_pp'
          refine ⟨verts, edges, hlen, hnd, hvH, fun e he => hEL_sub (heL e he), hhead, hlast, hstep,
            Efree, (Finset.card_union_le _ _).trans (by omega), ?_, ?_⟩
          · intro e he
            have hmem := heL e he
            rw [Finset.mem_union] at hmem
            rcases hmem with hHP | hFr
            · left
              obtain ⟨_, t, htblue, het⟩ := Finset.mem_filter.mp hHP
              exact ⟨t, htblue, het⟩
            · right; exact hFr
          · intro t _ e₁ h1 e₂ h2 he₁t he₂t
            rw [Finset.mem_union] at h1 h2
            rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
            · -- Both in Ep (card ≤ 1)
              have hcard := Finset.card_le_one.mp hEp_le
              exact hcard e₁ h1 e₂ h2
            · -- e₁ ∈ Ep, e₂ ∈ Ep' -> p and p' both interior to t, contradicting hsame!
              exfalso
              obtain ⟨t₁, hpt₁, he₁t₁⟩ := hEp_int e₁ h1
              obtain ⟨t₂, hp't₂, he₂t₂⟩ := hEp'_int e₂ h2
              have ht1 : t₁ = t := by by_contra hneq; exact sub.edges_disjoint t₁ t hneq e₁ he₁t₁ he₁t
              have ht2 : t₂ = t := by by_contra hneq; exact sub.edges_disjoint t₂ t hneq e₂ he₂t₂ he₂t
              exact hsame ⟨t, ht1 ▸ hpt₁, ht2 ▸ hp't₂⟩
            · exfalso
              obtain ⟨t₁, hpt₁, he₂t₁⟩ := hEp_int e₂ h2
              obtain ⟨t₂, hp't₂, he₁t₂⟩ := hEp'_int e₁ h1
              have ht1 : t₁ = t := by by_contra hneq; exact sub.edges_disjoint t₁ t hneq e₂ he₂t₁ he₂t
              have ht2 : t₂ = t := by by_contra hneq; exact sub.edges_disjoint t₂ t hneq e₁ he₁t₂ he₁t
              exact hsame ⟨t, ht1 ▸ hpt₁, ht2 ▸ hp't₂⟩
            · have hcard := Finset.card_le_one.mp hEp'_le
              exact hcard e₁ h1 e₂ h2
      obtain ⟨verts, edges, hlen, hnd, hvH, heH, hhead, hlast, hstep, Efree, hEfree_le2, hJ_cov, hEfree_uniq⟩ := hJ3
      obtain ⟨C, hCsign, hConH⟩ := hsplice verts edges hlen hnd hvH heH hhead hlast hstep
      -- Build E' ⊆ aux.EQ of free original edges met by Efree, with |E'| ≤ 2
      let E' : Finset aux.EQ :=
        Finset.univ.filter (fun eq => ∃ t : sub.E₀, fr.IsFree t ∧ aux.origEdge t = eq ∧
          ∃ e ∈ Efree, e ∈ (sub.thread t).edges)
      have hE'_red : ∀ eq ∈ E', eq ∉ fr.blue := by
        intro eq heq
        obtain ⟨t, htfree, rfl, _⟩ := (Finset.mem_filter.mp heq).2
        exact htfree
      have hE'_le2 : E'.card ≤ 2 := by
        let f_map : E → Finset aux.EQ := fun e =>
          if h : ∃ t : sub.E₀, e ∈ (sub.thread t).edges then {aux.origEdge h.choose} else ∅
        have hsub : E' ⊆ Efree.biUnion f_map := by
          intro eq heq
          obtain ⟨t, _, rfl, e, heFr, het⟩ := (Finset.mem_filter.mp heq).2
          refine Finset.mem_biUnion.mpr ⟨e, heFr, ?_⟩
          have hex : ∃ t' : sub.E₀, e ∈ (sub.thread t').edges := ⟨t, het⟩
          simp only [f_map, hex, ↓reduceDIte, Finset.mem_singleton]
          congr 1
          by_contra hneq; exact sub.edges_disjoint _ t (Ne.symm hneq) e hex.choose_spec het
        calc E'.card ≤ (Efree.biUnion f_map).card := Finset.card_le_card hsub
          _ ≤ ∑ e ∈ Efree, (f_map e).card := Finset.card_biUnion_le
          _ ≤ ∑ _e ∈ Efree, 1 := Finset.sum_le_sum fun e _ => by dsimp [f_map]; split_ifs <;> simp
          _ = Efree.card := by simp
          _ ≤ 2 := hEfree_le2
      let Phi (eq : aux.EQ) : Finset (Γ ⧸ B) :=
        if h : ∃ t : sub.E₀, fr.IsFree t ∧ aux.origEdge t = eq ∧ ∃ e ∈ Efree, e ∈ (sub.thread t).edges then
          {-quoFlow B f.val h.choose_spec.2.2.choose}
        else ∅
      have hPhi_le1 : ∀ eq : aux.EQ, (Phi eq).card ≤ 1 := fun eq => by
        dsimp only [Phi]; split_ifs <;> simp
      have hlem42b := lem_4_2_b_of (A := Γ ⧸ B) fr C_off hO2 hO3 hO5Z
      -- Get Y ∈ PLam (LamOfFlow B fr f) avoiding Phi on E'
      have hex_Y : ∃ Y ∈ PLam (LamOfFlow B fr f), ∀ eq ∈ E', Y eq ∉ Phi eq := by
        by_cases hE'_ne : E'.Nonempty
        · obtain ⟨eq0, heq0⟩ := hE'_ne
          obtain ⟨j0, _⟩ := hlem42b.1 eq0 (hE'_red eq0 heq0)
          let leastIdx (eq : aux.EQ) : Fin fr.numNodes :=
            if h : eq ∉ fr.blue then
              (Finset.univ.filter (fun j : Fin fr.numNodes => eq ∈ (C_off j).sub.edges)).min'
                (by obtain ⟨j, hj⟩ := hlem42b.1 eq h; exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩)
            else j0
          have hleast : ∀ eq ∈ E',
              eq ∈ (C_off (leastIdx eq)).sub.edges ∧
              ∀ j : Fin fr.numNodes, eq ∈ (C_off j).sub.edges → leastIdx eq ≤ j := by
            intro eq heq
            have hred := hE'_red eq heq
            constructor
            · dsimp only [leastIdx]; rw [dif_pos hred]
              have hmin_mem : (Finset.univ.filter (fun j : Fin fr.numNodes => eq ∈ (C_off j).sub.edges)).min'
                  (by obtain ⟨j, hj⟩ := hlem42b.1 eq hred; exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩) ∈
                  Finset.univ.filter (fun j : Fin fr.numNodes => eq ∈ (C_off j).sub.edges) :=
                Finset.min'_mem _ _
              exact (Finset.mem_filter.mp hmin_mem).2
            · intro j hj
              dsimp only [leastIdx]; rw [dif_pos hred]
              exact Finset.min'_le _ j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)
          have hcard_lt : ∀ i : Fin fr.numNodes,
              ((LamOfFlow B fr f).list (fr.eNode i)).card +
              ((LamOfFlow B fr f).list (fr.fNode i)).card +
              ∑ eq ∈ E'.filter (fun eq => leastIdx eq = i), (Phi eq).card < Fintype.card (Γ ⧸ B) := by
            intro i
            have h1 := (hdef312 f hHgood).1 (fr.eNode i)
            have h2 := (hdef312 f hHgood).1 (fr.fNode i)
            have h3 : ∑ eq ∈ E'.filter (fun eq => leastIdx eq = i), (Phi eq).card ≤ 2 := by
              calc ∑ eq ∈ E'.filter (fun eq => leastIdx eq = i), (Phi eq).card
                  ≤ ∑ _eq ∈ E'.filter (fun eq => leastIdx eq = i), 1 := Finset.sum_le_sum fun eq _ => hPhi_le1 eq
                _ = (E'.filter (fun eq => leastIdx eq = i)).card := by simp
                _ ≤ E'.card := Finset.card_filter_le _ _
                _ ≤ 2 := hE'_le2
            omega
          exact hlem42b.2 (LamOfFlow B fr f) E' hE'_red Phi leastIdx hleast hcard_lt
        · rw [Finset.not_nonempty_iff_eq_empty] at hE'_ne
          exact ⟨0, (hdef312 f hHgood).2.1, fun eq heq => absurd (hE'_ne ▸ heq) (Finset.notMem_empty _)⟩
      obtain ⟨Y, hY, hYavoid⟩ := hex_Y
      obtain ⟨f', hjoin_in, hgood', hquo', hout'⟩ :=
        lem_4_6_of B hA hB Sig hR1 hR2 fr C_off hO2 hO3 hO4 hO5A h36a_cyc h36d hO6_free
          f hHgood (hdef312 f hHgood) Y hY
      -- Final move g = f' + lam • χ_C
      have hlamB : lam ∈ B := (QuotientAddGroup.eq_zero_iff lam).mp hqlam
      let gVal : E → Γ := fun e => f'.val e + C.sign e • lam
      have hg_flow : G.IsFlow gVal := isFlow_add f'.isFlow (isFlow_zsmul C.isFlow lam)
      have hg_off : ∀ e : {e : E // e ∉ H.edges}, gVal e.1 = gstar.val e := fun e => by
        dsimp only [gVal]; rw [hout' e.1 e.2, hCsign e.1 e.2, hgstar e]
      have hg_quo : ∀ e, quoFlow B gVal e = quoFlow B f'.val e :=
        fun e => sec4_E2_proved G B f'.val C lam hlamB e
      have hg_nz : Multigraph.IsNowhereZero gVal := fun e => by
        by_cases heH' : e ∈ H.edges
        · by_cases heJ : e ∈ edges
          · -- e ∈ edges: show quoFlow B f'.val e ≠ 0
            apply (sec4_E1_proved (V := V) B gVal e).mpr
            left
            rw [hg_quo e]
            rcases hJ_cov e heJ with ⟨t, htprot, het⟩ | heFr
            · exact hgood' t htprot e het
            · obtain ⟨t, het⟩ := sub.edges_cover e heH'
              by_cases htprot : fr.IsProtected t
              · exact hgood' t htprot e het
              · -- t is free and e ∈ Efree
                have heqE' : aux.origEdge t ∈ E' :=
                  Finset.mem_filter.mpr ⟨Finset.mem_univ _, t, htprot, rfl, e, heFr, het⟩
                have havoid := hYavoid (aux.origEdge t) heqE'
                have hcond : ∃ t' : sub.E₀, fr.IsFree t' ∧ aux.origEdge t' = aux.origEdge t ∧
                    ∃ e' ∈ Efree, e' ∈ (sub.thread t').edges := ⟨t, htprot, rfl, e, heFr, het⟩
                have ht_eq : hcond.choose = t := aux.origEdge.injective hcond.choose_spec.2.1
                have he_eq : hcond.choose_spec.2.2.choose = e := by
                  let e' : E := hcond.choose_spec.2.2.choose
                  have h1 : e' ∈ Efree := hcond.choose_spec.2.2.choose_spec.1
                  have h2 : e' ∈ (sub.thread hcond.choose).edges := hcond.choose_spec.2.2.choose_spec.2
                  rw [ht_eq] at h2
                  exact hEfree_uniq t htprot e' h1 e heFr h2 het
                simp only [Phi, hcond, ↓reduceDIte, he_eq, Finset.mem_singleton] at havoid
                rw [hquo' e, hpi_eq Y t e het]
                intro h0
                exact havoid (eq_neg_of_add_eq_zero_right h0)
          · have hnotC : e ∉ C.sub.edges := fun h => heJ ((hConH e heH').mp h)
            dsimp only [gVal]; rw [C.sign_zero hnotC, zero_zsmul, add_zero]; exact f'.nonzero e
        · rw [hg_off ⟨e, heH'⟩]; exact gstar.nonzero ⟨e, heH'⟩
      let g : G.NZFlow Γ := ⟨gVal, hg_flow, hg_nz⟩
      exact ⟨g, (hjoin_of_in (fun _ h => h) hjoin_in).tail ⟨C, lam, hlam, fun _ => rfl⟩,
        hg_off, fun t ht e het => by rw [hg_quo e]; exact hgood' t ht e het⟩
    · -- Case 2: QuotientAddGroup.mk lam ≠ 0; use Lemma 4.7 path J!
      obtain ⟨verts, edges, hlen, hnd, hvH, heH, hhead, hlast, hstep, hJ_node⟩ :=
        lem_4_7_of fr hO1 p p' hpH hp'H hne
      obtain ⟨C, hCsign, hConH⟩ := hsplice verts edges hlen hnd hvH heH hhead hlast hstep
      -- (2a) Protected threads: augment LamOfFlow with forbidden shifts along J
      let extraLam (eq : aux.EQ) : Finset (Γ ⧸ B) :=
        if h : eq ∈ fr.blue ∧ ∃ t : sub.E₀, aux.origEdge t = eq then
          (edges.toFinset.filter (fun e => e ∈ (sub.thread h.2.choose).edges)).image
            (fun e => -(quoFlow B f.val e + C.sign e • QuotientAddGroup.mk lam))
        else ∅
      let Lam₁ : ListAssignment (A := Γ ⧸ B) fr :=
        { list := fun eq => (LamOfFlow B fr f).list eq ∪ extraLam eq
          empty_on_exp := fun eq hexp => by
            have h1 := (LamOfFlow B fr f).empty_on_exp eq hexp
            have h2 : extraLam eq = ∅ := by
              dsimp only [extraLam]
              have hnot : ¬ (eq ∈ fr.blue ∧ ∃ t : sub.E₀, aux.origEdge t = eq) := fun h => by
                rcases h.2 with ⟨t, ht⟩; exact hexp t ht
              rw [dif_neg hnot]
            rw [h1, h2, Finset.empty_union] }
      have hLam₁_lt : ∀ i : Fin fr.numNodes,
          (Lam₁.list (fr.eNode i)).card + (Lam₁.list (fr.fNode i)).card < Fintype.card (Γ ⧸ B) := by
        intro i
        have h1 := (hdef312 f hHgood).1 (fr.eNode i)
        have h2 := (hdef312 f hHgood).1 (fr.fNode i)
        let S_e : Finset E := edges.toFinset.filter (fun e =>
          ∃ t : sub.E₀, aux.origEdge t = fr.eNode i ∧ e ∈ (sub.thread t).edges)
        let S_f : Finset E := edges.toFinset.filter (fun e =>
          ∃ t : sub.E₀, aux.origEdge t = fr.fNode i ∧ e ∈ (sub.thread t).edges)
        have hdj_ef : Disjoint S_e S_f := by
          rw [Finset.disjoint_left]
          intro e he1 he2
          obtain ⟨t₁, ht₁, het₁⟩ := (Finset.mem_filter.mp he1).2
          obtain ⟨t₂, ht₂, het₂⟩ := (Finset.mem_filter.mp he2).2
          have htt : t₁ = t₂ := by by_contra hneq; exact sub.edges_disjoint t₁ t₂ hneq e het₁ het₂
          subst htt; exact fr.e_ne_f i (ht₁.symm.trans ht₂)
        have hunion_ef : S_e ∪ S_f = edges.toFinset.filter (fun e =>
            (∃ t : sub.E₀, aux.origEdge t = fr.eNode i ∧ e ∈ (sub.thread t).edges) ∨
            (∃ t : sub.E₀, aux.origEdge t = fr.fNode i ∧ e ∈ (sub.thread t).edges)) := by
          ext e; simp only [S_e, S_f, Finset.mem_union, Finset.mem_filter]
          constructor
          · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
            · exact ⟨h1, Or.inl h2⟩
            · exact ⟨h1, Or.inr h2⟩
          · rintro ⟨h1, h2 | h2⟩
            · exact Or.inl ⟨h1, h2⟩
            · exact Or.inr ⟨h1, h2⟩
        have hextra_e : (extraLam (fr.eNode i)).card ≤ S_e.card := by
          dsimp only [extraLam]
          split_ifs with h
          · refine Finset.card_image_le.trans (Finset.card_le_card fun e he => ?_)
            rw [Finset.mem_filter] at he ⊢
            exact ⟨he.1, h.2.choose, h.2.choose_spec, he.2⟩
          · simp
        have hextra_f : (extraLam (fr.fNode i)).card ≤ S_f.card := by
          dsimp only [extraLam]
          split_ifs with h
          · refine Finset.card_image_le.trans (Finset.card_le_card fun e he => ?_)
            rw [Finset.mem_filter] at he ⊢
            exact ⟨he.1, h.2.choose, h.2.choose_spec, he.2⟩
          · simp
        have hsum_ef : S_e.card + S_f.card ≤ 3 := by
          rw [← Finset.card_union_of_disjoint hdj_ef, hunion_ef]
          exact hJ_node i
        have hle_e : (Lam₁.list (fr.eNode i)).card ≤ ((LamOfFlow B fr f).list (fr.eNode i)).card + (extraLam (fr.eNode i)).card :=
          Finset.card_union_le _ _
        have hle_f : (Lam₁.list (fr.fNode i)).card ≤ ((LamOfFlow B fr f).list (fr.fNode i)).card + (extraLam (fr.fNode i)).card :=
          Finset.card_union_le _ _
        omega
      obtain ⟨x, hxLam₁⟩ := lem_4_2_a_of fr C_off hO2 hO3 Lam₁ hLam₁_lt 0 (isFlow_zero aux.Q)
      let Y : aux.EQ → Γ ⧸ B := fun eq => 0 + ∑ i : Fin fr.numNodes, (C_off i).sign eq • x i
      have hY_Lam : Y ∈ PLam (LamOfFlow B fr f) :=
        ⟨hxLam₁.1, fun t ht hmem => hxLam₁.2 t ht (Finset.mem_union_left _ hmem)⟩
      obtain ⟨f₁, hjoin₁, hgood₁, hquo₁, hout₁⟩ :=
        lem_4_6_of B hA hB Sig hR1 hR2 fr C_off hO2 hO3 hO4 hO5A h36a_cyc h36d hO6_free
          f hHgood (hdef312 f hHgood) Y hY_Lam
      -- Verify protected threads stay non-zero after adding lam • χ_C
      have hprot_after : ∀ t : sub.E₀, fr.IsProtected t → ∀ e ∈ (sub.thread t).edges,
          quoFlow B f₁.val e + C.sign e • QuotientAddGroup.mk lam ≠ 0 := by
        intro t htprot e het
        by_cases heJ : e ∈ edges
        · have hcond : aux.origEdge t ∈ fr.blue ∧ ∃ t' : sub.E₀, aux.origEdge t' = aux.origEdge t :=
            ⟨htprot, t, rfl⟩
          have ht_eq : hcond.2.choose = t := aux.origEdge.injective hcond.2.choose_spec
          have havoid := hxLam₁.2 (aux.origEdge t) htprot
          rw [hquo₁ e, hpi_eq Y t e het]
          intro h0
          apply havoid
          refine Finset.mem_union_right _ ?_
          dsimp only [extraLam]
          rw [dif_pos hcond, ht_eq]
          refine Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr heJ, het⟩, ?_⟩
          symm
          apply eq_neg_of_add_eq_zero_right
          have : quoFlow B f.val e + C.sign e • QuotientAddGroup.mk lam +
              ((0 : aux.EQ → Γ ⧸ B) (aux.origEdge t) + ∑ i, (C_off i).sign (aux.origEdge t) • x i) =
              quoFlow B f.val e + Y (aux.origEdge t) + C.sign e • QuotientAddGroup.mk lam := by
            dsimp only [Y, Pi.zero_apply]; abel
          rw [this]; exact h0
        · have hnotC : e ∉ C.sub.edges := fun h => heJ ((hConH e ((sub.thread t).edges_sub e het)).mp h)
          rw [C.sign_zero hnotC, zero_zsmul, add_zero]
          exact hgood₁ t htprot e het
      -- (2b) Free threads: apply Lemma 4.4 to f₁
      let Ecirc : Finset sub.E₀ := Finset.univ.filter (fun eps => fr.IsFree eps)
      let pickB (e : E) : Finset B :=
        if h1 : quoFlow B f₁.val e = 0 then
          {⟨-f₁.val e, B.neg_mem ((QuotientAddGroup.eq_zero_iff (f₁.val e)).mp h1)⟩}
        else if h2 : e ∈ edges ∧ quoFlow B f₁.val e + C.sign e • QuotientAddGroup.mk lam = 0 then
          {⟨-(f₁.val e + C.sign e • lam), B.neg_mem ((QuotientAddGroup.eq_zero_iff (f₁.val e + C.sign e • lam)).mp (by
            change (QuotientAddGroup.mk' B) (f₁.val e + C.sign e • lam) = 0
            rw [map_add, map_zsmul]
            exact h2.2))⟩}
        else ∅
      let T (eps : sub.E₀) : Finset B := (sub.thread eps).edges.toFinset.biUnion pickB
      have hT_sup : ∀ eps ∈ Ecirc, ∀ e ∈ (sub.thread eps).edges,
          quoFlow B f₁.val e = 0 → ∀ (hb : -f₁.val e ∈ B), (⟨-f₁.val e, hb⟩ : B) ∈ T eps := by
        intro eps _ e het hq hb
        refine Finset.mem_biUnion.mpr ⟨e, List.mem_toFinset.mpr het, ?_⟩
        simp [pickB, hq]
      have hT_card : ∀ eps ∈ Ecirc, (T eps).card ≤ (sub.thread eps).edges.length := by
        intro eps _
        calc (T eps).card ≤ ∑ e ∈ (sub.thread eps).edges.toFinset, (pickB e).card := Finset.card_biUnion_le
          _ ≤ ∑ _e ∈ (sub.thread eps).edges.toFinset, 1 := Finset.sum_le_sum fun e _ => by
              dsimp only [pickB]; split_ifs <;> simp
          _ = (sub.thread eps).edges.toFinset.card := by simp
          _ ≤ (sub.thread eps).edges.length := List.toFinset_card_le _
      obtain ⟨f₂, hjoin₂, hgood₂, hquo₂, hout₂, _, hy_eps⟩ :=
        lem_4_4_of B hB Sig hR2 fr hO6_free f₁ hgood₁ Ecirc
          (fun _ h => (Finset.mem_filter.mp h).2) T hT_sup hT_card
      -- (2c) Final move g = f₂ + lam • χ_C
      let gVal : E → Γ := fun e => f₂.val e + C.sign e • lam
      have hg_flow : G.IsFlow gVal := isFlow_add f₂.isFlow (isFlow_zsmul C.isFlow lam)
      have hg_off : ∀ e : {e : E // e ∉ H.edges}, gVal e.1 = gstar.val e := fun e => by
        dsimp only [gVal]; rw [hout₂ e.1 e.2, hout₁ e.1 e.2, hCsign e.1 e.2, hgstar e]
      have hg_quo : ∀ e, quoFlow B gVal e = quoFlow B f₁.val e + C.sign e • QuotientAddGroup.mk lam := by
        intro e
        unfold quoFlow
        change (QuotientAddGroup.mk' B) (f₂.val e + C.sign e • lam) = _
        rw [map_add, map_zsmul]
        have h1 : (QuotientAddGroup.mk' B) (f₂.val e) = quoFlow B f₁.val e := hquo₂ e
        rw [h1]; rfl
      have hg_nz : Multigraph.IsNowhereZero gVal := fun e => by
        by_cases heH' : e ∈ H.edges
        · obtain ⟨t, het⟩ := sub.edges_cover e heH'
          by_cases htprot : fr.IsProtected t
          · exact (sec4_E1_proved (V := V) B gVal e).mpr (Or.inl (by rw [hg_quo e]; exact hprot_after t htprot e het))
          · by_cases heJ : e ∈ edges
            · by_cases hqg : quoFlow B gVal e = 0
              · -- quoFlow B f₁.val e + C.sign e • mk lam = 0, so quoFlow B f₁.val e ≠ 0 (since mk lam ≠ 0 and C.sign e = ±1)
                have hqsum0 : quoFlow B f₁.val e + C.sign e • QuotientAddGroup.mk lam = 0 := by
                  rw [← hg_quo e]; exact hqg
                have heC : e ∈ C.sub.edges := (hConH e heH').mpr heJ
                have hqf₁_ne : quoFlow B f₁.val e ≠ 0 := by
                  intro h0
                  rw [h0, zero_add] at hqsum0
                  rcases C.sign_mem heC with hs | hs
                  · rw [hs, one_zsmul] at hqsum0; exact hqlam hqsum0
                  · rw [hs, neg_one_zsmul, neg_eq_zero] at hqsum0; exact hqlam hqsum0
                obtain ⟨y, hy_notT, hy_eq⟩ := hy_eps t (Finset.mem_filter.mpr ⟨Finset.mem_univ _, htprot⟩)
                dsimp only [gVal]
                rw [hy_eq e het]
                intro h0
                have hb_mem : -(f₁.val e + C.sign e • lam) ∈ B := B.neg_mem ((QuotientAddGroup.eq_zero_iff _).mp (by
                  change (QuotientAddGroup.mk' B) (f₁.val e + C.sign e • lam) = 0
                  rw [map_add, map_zsmul]; exact hqsum0))
                have hmem : (⟨-(f₁.val e + C.sign e • lam), hb_mem⟩ : B) ∈ T t := by
                  refine Finset.mem_biUnion.mpr ⟨e, List.mem_toFinset.mpr het, ?_⟩
                  simp [pickB, hqf₁_ne, heJ, hqsum0]
                have hyval : (y : Γ) = -(f₁.val e + C.sign e • lam) := by
                  apply eq_neg_of_add_eq_zero_right
                  have : f₁.val e + C.sign e • lam + (y : Γ) = f₁.val e + (y : Γ) + C.sign e • lam := by abel
                  rw [this]; exact h0
                have hyeq : y = ⟨-(f₁.val e + C.sign e • lam), hb_mem⟩ := Subtype.ext hyval
                exact hy_notT (hyeq ▸ hmem)
              · exact (sec4_E1_proved (V := V) B gVal e).mpr (Or.inl hqg)
            · have hnotC : e ∉ C.sub.edges := fun h => heJ ((hConH e heH').mp h)
              dsimp only [gVal]; rw [C.sign_zero hnotC, zero_zsmul, add_zero]; exact f₂.nonzero e
        · rw [hg_off ⟨e, heH'⟩]; exact gstar.nonzero ⟨e, heH'⟩
      let g : G.NZFlow Γ := ⟨gVal, hg_flow, hg_nz⟩
      have hjoin_all : G.SigmaJoined Sig.carrier f g :=
        ((hjoin_of_in (fun _ h => h) hjoin₁).trans
          (hjoin_of_in (fun _ h => h.1) hjoin₂)).tail ⟨C, lam, hlam, fun _ => rfl⟩
      exact ⟨g, hjoin_all, hg_off, fun t ht e het => by rw [hg_quo e]; exact hprot_after t ht e het⟩

end Flow.Proofs
