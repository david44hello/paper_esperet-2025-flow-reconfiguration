module

-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
public import Flow.Defs.Literature
public import Flow.Proofs.Elementary
public import Flow.Proofs.Basic
public import Flow.Proofs.SmallClaims
public import Mathlib.Tactic

@[expose] public section

/-!
# Section 4 proofs (Part 2): Lifting contracted cycles (`liftContractedCycle`) and `lem_4_8_cyc`
-/

namespace Flow.Proofs

open Flow

/-! ### Helper: Simple path degree and signed indicator -/

/-- Exact incidence count of a simple path's edges at every vertex `v`. -/
lemma simplePath_deg_eq {V E : Type} [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : Multigraph V E) (verts : List V) (edges : List E)
    (hlen : verts.length = edges.length + 1) (hnodup : verts.Nodup)
    (hstep : ∀ (k : ℕ) (hk : k < edges.length),
      let u := verts[k]'(by omega)
      let w := verts[k + 1]'(by omega)
      let e := edges[k]'hk
      (G.tail e = u ∧ G.head e = w) ∨ (G.tail e = w ∧ G.head e = u))
    (p p' : V) (hp : verts.head? = some p) (hp' : verts.getLast? = some p') (hne : p ≠ p') :
    let P : G.Subgraph :=
      { verts := verts.toFinset
        edges := edges.toFinset
        tail_mem := fun he => by
          rw [List.mem_toFinset] at he
          obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem he
          rcases hstep k hk with ⟨h1, _⟩ | ⟨h1, _⟩
          · rw [h1]; exact List.mem_toFinset.mpr (List.getElem_mem _)
          · rw [h1]; exact List.mem_toFinset.mpr (List.getElem_mem _)
        head_mem := fun he => by
          rw [List.mem_toFinset] at he
          obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem he
          rcases hstep k hk with ⟨_, h2⟩ | ⟨_, h2⟩
          · rw [h2]; exact List.mem_toFinset.mpr (List.getElem_mem _)
          · rw [h2]; exact List.mem_toFinset.mpr (List.getElem_mem _) }
    P.deg p = 1 ∧ P.deg p' = 1 ∧
    (∀ v ∈ verts, v ≠ p → v ≠ p' → P.deg v = 2) ∧
    (∀ v, v ∉ verts → P.deg v = 0) := by
  intro P
  have hedges_nodup : edges.Nodup := simplePath_edges_nodup hnodup hlen hstep
  have hv0 : verts[0]'(by omega) = p := by
    rw [List.head?_eq_getElem?] at hp
    simp only [List.getElem?_eq_getElem (by omega : 0 < verts.length), Option.some.injEq] at hp
    exact hp
  have hvlast : verts[edges.length]'(by omega) = p' := by
    rw [List.getLast?_eq_getElem?] at hp'
    have hidx : verts.length - 1 = edges.length := by omega
    rw [hidx, List.getElem?_eq_getElem (by omega : edges.length < verts.length), Option.some.injEq] at hp'
    exact hp'
  -- Express P.deg v as the number of k < edges.length where v = verts[k] or v = verts[k+1]
  have hdeg_eq : ∀ v : V,
      P.deg v = (Finset.univ.filter (fun k : Fin edges.length =>
        verts[k.1]'(by omega) = v ∨ verts[k.1 + 1]'(by omega) = v)).card := by
    intro v
    have hno_loop : ∀ (k : ℕ) (hk : k < edges.length), G.tail (edges[k]'hk) ≠ G.head (edges[k]'hk) := by
      intro k hk heq
      rcases hstep k hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hveq : verts[k]'(by omega) = verts[k + 1]'(by omega) := h1.symm.trans (heq.trans h2)
        have := (List.Nodup.getElem_inj_iff hnodup).mp hveq; omega
      · have hveq : verts[k + 1]'(by omega) = verts[k]'(by omega) := h1.symm.trans (heq.trans h2)
        have := (List.Nodup.getElem_inj_iff hnodup).mp hveq; omega
    have hdj : Disjoint (P.edges.filter (fun e => G.tail e = v))
        (P.edges.filter (fun e => G.head e = v)) := by
      rw [Finset.disjoint_left]
      intro e h1 h2
      rw [Finset.mem_filter] at h1 h2
      have heL : e ∈ edges := List.mem_toFinset.mp h1.1
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem heL
      exact hno_loop k hk (h1.2.trans h2.2.symm)
    unfold Multigraph.Subgraph.deg
    rw [← Finset.card_union_of_disjoint hdj]
    have hunion : P.edges.filter (fun e => G.tail e = v) ∪ P.edges.filter (fun e => G.head e = v) =
        P.edges.filter (fun e => G.tail e = v ∨ G.head e = v) := by
      ext e; simp only [Finset.mem_union, Finset.mem_filter]; tauto
    rw [hunion]
    symm
    refine Finset.card_bij (fun k _ => edges[k.1]'k.2) (fun k hk => ?_) (fun k₁ _ k₂ _ heq => ?_)
      (fun e he => ?_)
    · rw [Finset.mem_filter] at hk ⊢
      refine ⟨List.mem_toFinset.mpr (List.getElem_mem _), ?_⟩
      rcases hstep k.1 k.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hk.2 with hv | hv
      · exact Or.inl (h1.trans hv)
      · exact Or.inr (h2.trans hv)
      · exact Or.inr (h2.trans hv)
      · exact Or.inl (h1.trans hv)
    · exact Fin.ext ((List.Nodup.getElem_inj_iff hedges_nodup).mp heq)
    · rw [Finset.mem_filter] at he
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem (List.mem_toFinset.mp he.1)
      refine ⟨⟨k, hk⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
      rcases hstep k hk with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases he.2 with hv | hv
      · exact Or.inl (h1.symm.trans hv)
      · exact Or.inr (h2.symm.trans hv)
      · exact Or.inr (h1.symm.trans hv)
      · exact Or.inl (h2.symm.trans hv)
  have hlen_pos : 0 < edges.length := by
    by_contra h0
    have he0 : edges.length = 0 := by omega
    have hpp' : p = p' := by rw [← hv0, ← hvlast]; simp [he0]
    exact hne hpp'
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hdeg_eq p]
    have hf : Finset.univ.filter (fun k : Fin edges.length =>
        verts[k.1]'(by omega) = p ∨ verts[k.1 + 1]'(by omega) = p) = {⟨0, hlen_pos⟩} := by
      ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro (h | h)
        · have := (List.Nodup.getElem_inj_iff hnodup).mp (h.trans hv0.symm); exact Fin.ext this
        · have := (List.Nodup.getElem_inj_iff hnodup).mp (h.trans hv0.symm); omega
      · rintro rfl; exact Or.inl hv0
    rw [hf, Finset.card_singleton]
  · rw [hdeg_eq p']
    have hf : Finset.univ.filter (fun k : Fin edges.length =>
        verts[k.1]'(by omega) = p' ∨ verts[k.1 + 1]'(by omega) = p') =
        {⟨edges.length - 1, by omega⟩} := by
      ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · have hk2 := k.2
        rintro (h | h)
        · have := (List.Nodup.getElem_inj_iff hnodup).mp (h.trans hvlast.symm); omega
        · have := (List.Nodup.getElem_inj_iff hnodup).mp (h.trans hvlast.symm); exact Fin.ext (by dsimp; omega)
      · rintro rfl; right
        have hidx : edges.length - 1 + 1 = edges.length := by omega
        simpa only [hidx] using hvlast
    rw [hf, Finset.card_singleton]
  · intro v hv hvp hvp'
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hv
    have hj0 : 0 < j := by
      by_contra h; have hjz : j = 0 := by omega
      subst hjz; exact hvp hv0
    have hjlt : j < edges.length := by
      by_contra h; have hje : j = edges.length := by omega
      subst hje; exact hvp' hvlast
    rw [hdeg_eq]
    have hf : Finset.univ.filter (fun k : Fin edges.length =>
        verts[k.1]'(by omega) = verts[j]'hj ∨ verts[k.1 + 1]'(by omega) = verts[j]'hj) =
        {⟨j - 1, by omega⟩, ⟨j, hjlt⟩} := by
      ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · have hk2 := k.2
        rintro (h | h)
        · right; exact Fin.ext ((List.Nodup.getElem_inj_iff hnodup).mp h)
        · left; have := (List.Nodup.getElem_inj_iff hnodup).mp h; exact Fin.ext (by dsimp; omega)
      · rintro (rfl | rfl)
        · right
          have hidx : j - 1 + 1 = j := by omega
          simp only [hidx]
        · left; rfl
    rw [hf, Finset.card_pair (by intro h; have := congrArg Fin.val h; dsimp at this; omega)]
  · intro v hv
    rw [hdeg_eq]
    have hf : Finset.univ.filter (fun k : Fin edges.length =>
        verts[k.1]'(by omega) = v ∨ verts[k.1 + 1]'(by omega) = v) = ∅ := by
      ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false, not_or]
      exact ⟨fun h => hv (h ▸ List.getElem_mem _), fun h => hv (h ▸ List.getElem_mem _)⟩
    rw [hf, Finset.card_empty]

/-- Signed indicator of a simple path from `p` to `p'`: `±1` on path edges, `0` elsewhere,
with boundary `-1` at `p`, `+1` at `p'`, and `0` at all other vertices. -/
noncomputable def simplePathSign {V E : Type} [DecidableEq V] [DecidableEq E]
    (G : Multigraph V E) (verts : List V) (edges : List E)
    (hlen : verts.length = edges.length + 1) (e : E) : ℤ :=
  ∑ k : Fin edges.length,
    if edges[k.1]'k.2 = e then
      if G.tail e = verts[k.1]'(by omega) ∧ G.head e = verts[k.1 + 1]'(by omega) then 1 else -1
    else 0

lemma simplePathSign_spec {V E : Type} [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : Multigraph V E) (verts : List V) (edges : List E)
    (hlen : verts.length = edges.length + 1) (hnodup : verts.Nodup)
    (hstep : ∀ (k : ℕ) (hk : k < edges.length),
      let u := verts[k]'(by omega)
      let w := verts[k + 1]'(by omega)
      let e := edges[k]'hk
      (G.tail e = u ∧ G.head e = w) ∨ (G.tail e = w ∧ G.head e = u))
    (p p' : V) (hp : verts.head? = some p) (hp' : verts.getLast? = some p') :
    let σ := simplePathSign G verts edges hlen
    (∀ e ∈ edges, σ e = 1 ∨ σ e = -1) ∧
    (∀ e ∉ edges, σ e = 0) ∧
    (∀ v : V, G.boundary σ v = (if v = p' then 1 else 0) - (if v = p then 1 else 0)) := by
  intro σ
  have hedges_nodup : edges.Nodup := simplePath_edges_nodup hnodup hlen hstep
  have hv0 : verts[0]'(by omega) = p := by
    rw [List.head?_eq_getElem?] at hp
    simp only [List.getElem?_eq_getElem (by omega : 0 < verts.length), Option.some.injEq] at hp
    exact hp
  have hvlast : verts[edges.length]'(by omega) = p' := by
    rw [List.getLast?_eq_getElem?] at hp'
    have hidx : verts.length - 1 = edges.length := by omega
    rw [hidx, List.getElem?_eq_getElem (by omega : edges.length < verts.length), Option.some.injEq] at hp'
    exact hp'
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem he
    dsimp only [σ, simplePathSign]
    rw [Finset.sum_eq_single (⟨k, hk⟩ : Fin edges.length)]
    · simp only [↓reduceIte]
      split_ifs <;> simp
    · intro j _ hj
      have hne : edges[j.1]'j.2 ≠ edges[k]'hk := fun h =>
        hj (Fin.ext ((List.Nodup.getElem_inj_iff hedges_nodup).mp h))
      simp [hne]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro e he
    dsimp only [σ, simplePathSign]
    refine Finset.sum_eq_zero fun k _ => ?_
    have hne : edges[k.1]'k.2 ≠ e := fun h => he (h ▸ List.getElem_mem _)
    simp [hne]
  · intro v
    -- Write σ as sum over k : Fin edges.length of single-edge function
    have hbd_sum : G.boundary σ v =
        ∑ k : Fin edges.length,
          ((if verts[k.1 + 1]'(by omega) = v then (1 : ℤ) else 0) -
           (if verts[k.1]'(by omega) = v then (1 : ℤ) else 0)) := by
      have hfn : σ = fun e => ∑ k : Fin edges.length,
          if edges[k.1]'k.2 = e then
            if G.tail e = verts[k.1]'(by omega) ∧ G.head e = verts[k.1 + 1]'(by omega) then 1 else -1
          else 0 := rfl
      rw [hfn, boundary_finset_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [boundary_eq_sum_ite]
      rw [Finset.sum_eq_single (edges[k.1]'k.2)]
      · simp only [↓reduceIte]
        have hveq_ne : verts[k.1]'(by omega) ≠ verts[k.1 + 1]'(by omega) := fun h => by
          have := (List.Nodup.getElem_inj_iff hnodup).mp h; omega
        rcases hstep k.1 k.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · simp only [h1, h2, and_self, ↓reduceIte]
        · have hnot : ¬ (G.tail (edges[k.1]'k.2) = verts[k.1]'(by omega) ∧
              G.head (edges[k.1]'k.2) = verts[k.1 + 1]'(by omega)) := fun h =>
            hveq_ne (h.1.symm.trans h1)
          simp only [hnot, ↓reduceIte, h1, h2]
          by_cases ha : verts[k.1]'(by omega) = v <;> by_cases hb : verts[k.1 + 1]'(by omega) = v <;>
            simp [ha, hb] <;> ring
      · intro e _ hne; simp [Ne.symm hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hbd_sum]
    -- Telescope ∑_{k < m} (g(k+1) - g(k)) = g(m) - g(0)
    have htelesc : ∀ (m : ℕ) (hm : m ≤ edges.length),
        ∑ k : Fin m, ((if verts[k.1 + 1]'(by omega) = v then (1 : ℤ) else 0) -
                      (if verts[k.1]'(by omega) = v then (1 : ℤ) else 0)) =
        (if verts[m]'(by omega) = v then (1 : ℤ) else 0) -
        (if verts[0]'(by omega) = v then (1 : ℤ) else 0) := by
      intro m
      induction m with
      | zero => intro _; simp
      | succ m ihm =>
        intro hm
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.coe_castSucc, Fin.val_last]
        rw [ihm (by omega)]
        ring
    rw [htelesc edges.length le_rfl, hv0, hvlast]
    by_cases h1 : v = p'
    · subst h1
      by_cases h2 : v = p
      · subst h2; simp
      · simp [h2, Ne.symm h2]
    · by_cases h2 : v = p
      · subst h2; simp [h1, Ne.symm h1]
      · simp [h1, h2, Ne.symm h1, Ne.symm h2]

/-! ### Main helper: `liftContractedCycle` -/

theorem liftContractedCycle
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : Multigraph V E) (H : G.Subgraph)
    (Cstar : (G.contractSubgraph H).DirectedCycle) :
    (∃ C : G.DirectedCycle,
      Disjoint C.sub.edges H.edges ∧
      ∀ e (he : e ∉ H.edges), C.sign e = Cstar.sign ⟨e, he⟩) ∨
    (∃ p p' : V, p ∈ H.verts ∧ p' ∈ H.verts ∧ p ≠ p' ∧
      ∀ (verts : List V) (edges : List E) (hlen : verts.length = edges.length + 1),
        verts.Nodup →
        (∀ v ∈ verts, v ∈ H.verts) →
        (∀ e ∈ edges, e ∈ H.edges) →
        verts.head? = some p →
        verts.getLast? = some p' →
        (∀ (k : ℕ) (hk : k < edges.length),
          let u := verts[k]'(by omega)
          let w := verts[k + 1]'(by omega)
          let e := edges[k]'hk
          (G.tail e = u ∧ G.head e = w) ∨ (G.tail e = w ∧ G.head e = u)) →
        ∃ C : G.DirectedCycle,
          (∀ e (he : e ∉ H.edges), C.sign e = Cstar.sign ⟨e, he⟩) ∧
          (∀ e ∈ H.edges, e ∈ C.sub.edges ↔ e ∈ edges)) := by
  let Gstar := G.contractSubgraph H
  let s : E → ℤ := fun e => if h : e ∈ H.edges then 0 else Cstar.sign ⟨e, h⟩
  let Eout : Finset E := Cstar.sub.edges.map ⟨Subtype.val, Subtype.val_injective⟩
  have hEout_disj : Disjoint Eout H.edges := by
    rw [Finset.disjoint_left]
    intro e he
    rw [Finset.mem_map] at he
    rcases he with ⟨e', _, rfl⟩
    exact e'.2
  have hs_mem : ∀ e ∈ Eout, s e = 1 ∨ s e = -1 := by
    intro e he
    simp only [Eout, Finset.mem_map, Function.Embedding.coeFn_mk] at he
    rcases he with ⟨e', he', rfl⟩
    simp only [s, e'.2, ↓reduceDIte]
    exact Cstar.sign_mem he'
  have hs_zero : ∀ e ∉ Eout, s e = 0 := by
    intro e he
    by_cases hH : e ∈ H.edges
    · simp [s, hH]
    · simp only [s, hH, ↓reduceDIte]
      apply Cstar.sign_zero
      intro hmem; exact he (Finset.mem_map.mpr ⟨⟨e, hH⟩, hmem, rfl⟩)
  -- Vertex set of Eout outside H.verts
  let Vout : Finset V := Finset.univ.filter (fun v => ∃ hv : v ∉ H.verts, some ⟨v, hv⟩ ∈ Cstar.sub.verts)
  -- Boundary of s at vertices outside H.verts is 0
  have hbd_out : ∀ v : V, (hv : v ∉ H.verts) → G.boundary s v = 0 := by
    intro v hv
    have hcs := Cstar.isFlow (some ⟨v, hv⟩)
    trans (Gstar.boundary Cstar.sign (some ⟨v, hv⟩))
    · rw [boundary_eq_sum_ite, boundary_eq_sum_ite]
      rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.filter (fun e : E => e ∉ H.edges)))]
      · refine Finset.sum_bij (fun e he => ⟨e, (Finset.mem_filter.mp he).2⟩)
          (fun _ _ => Finset.mem_univ _)
          (fun _ _ _ _ h => congrArg Subtype.val h)
          (fun e _ => ⟨e.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, e.2⟩, rfl⟩)
          (fun e he => ?_)
        have henot : e ∉ H.edges := (Finset.mem_filter.mp he).2
        simp only [s, henot, ↓reduceDIte, Gstar, Multigraph.contractSubgraph]
        have hhead : (if h : G.head e ∈ H.verts then (none : Option {u : V // u ∉ H.verts}) else some ⟨G.head e, h⟩) =
            some ⟨v, hv⟩ ↔ G.head e = v := by
          split_ifs with h
          · simp only [reduceCtorEq, false_iff]; intro heq; exact hv (heq ▸ h)
          · simp [Subtype.ext_iff]
        have htail : (if h : G.tail e ∈ H.verts then (none : Option {u : V // u ∉ H.verts}) else some ⟨G.tail e, h⟩) =
            some ⟨v, hv⟩ ↔ G.tail e = v := by
          split_ifs with h
          · simp only [reduceCtorEq, false_iff]; intro heq; exact hv (heq ▸ h)
          · simp [Subtype.ext_iff]
        rw [if_congr hhead.symm rfl rfl, if_congr htail.symm rfl rfl]
      · intro e _ hnot
        have heH : e ∈ H.edges := by
          by_contra h; exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
        simp [s, heH]
    · exact hcs
  -- Sum of boundaries of s over H.verts equals Gstar.boundary Cstar.sign none = 0
  have hbd_sumH : ∑ v ∈ H.verts, G.boundary s v = 0 := by
    have hcs := Cstar.isFlow none
    rw [boundary_eq_sum_ite] at hcs
    have hlhs : ∑ v ∈ H.verts, G.boundary s v =
        ∑ e : {e : E // e ∉ H.edges},
          ((if Gstar.head e = none then Cstar.sign e else 0) -
           (if Gstar.tail e = none then Cstar.sign e else 0)) := by
      simp_rw [boundary_eq_sum_ite]
      rw [Finset.sum_comm]
      rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.filter (fun e : E => e ∉ H.edges)))]
      · refine Finset.sum_bij (fun e he => ⟨e, (Finset.mem_filter.mp he).2⟩)
          (fun _ _ => Finset.mem_univ _)
          (fun _ _ _ _ h => congrArg Subtype.val h)
          (fun e _ => ⟨e.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, e.2⟩, rfl⟩)
          (fun e he => ?_)
        have henot : e ∉ H.edges := (Finset.mem_filter.mp he).2
        rw [Finset.sum_sub_distrib]
        have h1 : ∑ v ∈ H.verts, (if G.head e = v then s e else 0) =
            if Gstar.head ⟨e, henot⟩ = none then Cstar.sign ⟨e, henot⟩ else 0 := by
          simp only [s, henot, ↓reduceDIte, Gstar, Multigraph.contractSubgraph]
          by_cases hh : G.head e ∈ H.verts
          · simp [hh, Finset.sum_ite_eq]
          · simp [hh, Finset.sum_ite_eq]
        have h2 : ∑ v ∈ H.verts, (if G.tail e = v then s e else 0) =
            if Gstar.tail ⟨e, henot⟩ = none then Cstar.sign ⟨e, henot⟩ else 0 := by
          simp only [s, henot, ↓reduceDIte, Gstar, Multigraph.contractSubgraph]
          by_cases ht : G.tail e ∈ H.verts
          · simp [ht, Finset.sum_ite_eq]
          · simp [ht, Finset.sum_ite_eq]
        rw [h1, h2]
      · intro e _ hnot
        have heH : e ∈ H.edges := by
          by_contra h; exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
        refine Finset.sum_eq_zero fun v _ => by simp [s, heH]
    rw [hlhs, hcs]
  -- Degree of Eout at any vertex v
  let degE (v : V) : ℕ :=
    (Eout.filter (fun e => G.tail e = v)).card + (Eout.filter (fun e => G.head e = v)).card
  have hdegE_out : ∀ v : V, (hv : v ∉ H.verts) → degE v = Cstar.sub.deg (some ⟨v, hv⟩) := by
    intro v hv
    unfold degE Multigraph.Subgraph.deg
    congr 1
    · refine Finset.card_bij (fun e he => ⟨e, Finset.disjoint_left.mp hEout_disj (Finset.mem_filter.mp he).1⟩)
        (fun e he => ?_) (fun _ _ _ _ h => congrArg Subtype.val h) (fun e' he' => ⟨e'.1, ?_, rfl⟩)
      · rw [Finset.mem_filter] at he ⊢
        simp only [Eout, Finset.mem_map, Function.Embedding.coeFn_mk] at he
        rcases he.1 with ⟨e', he', hval⟩
        have heq : e' = ⟨e, hval ▸ e'.2⟩ := Subtype.ext hval
        refine ⟨heq ▸ he', ?_⟩
        dsimp only [Gstar, Multigraph.contractSubgraph]
        have hnot : G.tail e ∉ H.verts := he.2.symm ▸ hv
        rw [dif_neg hnot]
        exact congrArg some (Subtype.ext he.2)
      · rw [Finset.mem_filter] at he' ⊢
        refine ⟨Finset.mem_map.mpr ⟨e', he'.1, rfl⟩, ?_⟩
        have ht := he'.2
        simp only [Gstar, Multigraph.contractSubgraph] at ht
        by_cases h : G.tail e'.1 ∈ H.verts
        · simp [h] at ht
        · simp only [h, ↓reduceDIte, Option.some.injEq, Subtype.mk.injEq] at ht; exact ht
    · refine Finset.card_bij (fun e he => ⟨e, Finset.disjoint_left.mp hEout_disj (Finset.mem_filter.mp he).1⟩)
        (fun e he => ?_) (fun _ _ _ _ h => congrArg Subtype.val h) (fun e' he' => ⟨e'.1, ?_, rfl⟩)
      · rw [Finset.mem_filter] at he ⊢
        simp only [Eout, Finset.mem_map, Function.Embedding.coeFn_mk] at he
        rcases he.1 with ⟨e', he', hval⟩
        have heq : e' = ⟨e, hval ▸ e'.2⟩ := Subtype.ext hval
        refine ⟨heq ▸ he', ?_⟩
        dsimp only [Gstar, Multigraph.contractSubgraph]
        have hnot : G.head e ∉ H.verts := he.2.symm ▸ hv
        rw [dif_neg hnot]
        exact congrArg some (Subtype.ext he.2)
      · rw [Finset.mem_filter] at he' ⊢
        refine ⟨Finset.mem_map.mpr ⟨e', he'.1, rfl⟩, ?_⟩
        have hh := he'.2
        simp only [Gstar, Multigraph.contractSubgraph] at hh
        by_cases h : G.head e'.1 ∈ H.verts
        · simp [h] at hh
        · simp only [h, ↓reduceDIte, Option.some.injEq, Subtype.mk.injEq] at hh; exact hh
  have hdegE_sumH : ∑ v ∈ H.verts, degE v = Cstar.sub.deg none := by
    unfold degE Multigraph.Subgraph.deg
    rw [Finset.sum_add_distrib]
    have h1 : ∑ v ∈ H.verts, (Eout.filter (fun e => G.tail e = v)).card =
        (Cstar.sub.edges.filter (fun e => Gstar.tail e = none)).card := by
      rw [← Finset.card_biUnion]
      · refine Finset.card_bij (fun e he => ⟨e, Finset.disjoint_left.mp hEout_disj (by
            rw [Finset.mem_biUnion] at he; rcases he with ⟨_, _, h⟩; exact (Finset.mem_filter.mp h).1)⟩)
          (fun e he => ?_) (fun _ _ _ _ h => congrArg Subtype.val h) (fun e' he' => ⟨e'.1, ?_, rfl⟩)
        · rw [Finset.mem_biUnion] at he
          rcases he with ⟨v, hv, hfv⟩
          rw [Finset.mem_filter] at hfv
          simp only [Eout, Finset.mem_map, Function.Embedding.coeFn_mk] at hfv
          rcases hfv.1 with ⟨e', he', hval⟩
          have heq : e' = ⟨e, hval ▸ e'.2⟩ := Subtype.ext hval
          refine Finset.mem_filter.mpr ⟨heq ▸ he', ?_⟩
          simp [Gstar, Multigraph.contractSubgraph, hfv.2.symm ▸ hv]
        · rw [Finset.mem_filter] at he'
          have ht : G.tail e'.1 ∈ H.verts := by
            have h := he'.2; simp only [Gstar, Multigraph.contractSubgraph] at h
            by_cases hm : G.tail e'.1 ∈ H.verts
            · exact hm
            · simp [hm] at h
          exact Finset.mem_biUnion.mpr ⟨G.tail e'.1, ht,
            Finset.mem_filter.mpr ⟨Finset.mem_map.mpr ⟨e', he'.1, rfl⟩, rfl⟩⟩
      · intro u _ v _ huv; dsimp [Function.onFun]; rw [Finset.disjoint_left]
        intro e hu hv
        exact huv ((Finset.mem_filter.mp hu).2.symm.trans (Finset.mem_filter.mp hv).2)
    have h2 : ∑ v ∈ H.verts, (Eout.filter (fun e => G.head e = v)).card =
        (Cstar.sub.edges.filter (fun e => Gstar.head e = none)).card := by
      rw [← Finset.card_biUnion]
      · refine Finset.card_bij (fun e he => ⟨e, Finset.disjoint_left.mp hEout_disj (by
            rw [Finset.mem_biUnion] at he; rcases he with ⟨_, _, h⟩; exact (Finset.mem_filter.mp h).1)⟩)
          (fun e he => ?_) (fun _ _ _ _ h => congrArg Subtype.val h) (fun e' he' => ⟨e'.1, ?_, rfl⟩)
        · rw [Finset.mem_biUnion] at he
          rcases he with ⟨v, hv, hfv⟩
          rw [Finset.mem_filter] at hfv
          simp only [Eout, Finset.mem_map, Function.Embedding.coeFn_mk] at hfv
          rcases hfv.1 with ⟨e', he', hval⟩
          have heq : e' = ⟨e, hval ▸ e'.2⟩ := Subtype.ext hval
          refine Finset.mem_filter.mpr ⟨heq ▸ he', ?_⟩
          simp [Gstar, Multigraph.contractSubgraph, hfv.2.symm ▸ hv]
        · rw [Finset.mem_filter] at he'
          have hh : G.head e'.1 ∈ H.verts := by
            have h := he'.2; simp only [Gstar, Multigraph.contractSubgraph] at h
            by_cases hm : G.head e'.1 ∈ H.verts
            · exact hm
            · simp [hm] at h
          exact Finset.mem_biUnion.mpr ⟨G.head e'.1, hh,
            Finset.mem_filter.mpr ⟨Finset.mem_map.mpr ⟨e', he'.1, rfl⟩, rfl⟩⟩
      · intro u _ v _ huv; dsimp [Function.onFun]; rw [Finset.disjoint_left]
        intro e hu hv
        exact huv ((Finset.mem_filter.mp hu).2.symm.trans (Finset.mem_filter.mp hv).2)
    rw [h1, h2]
  -- Split on none ∈ Cstar.sub.verts
  by_cases hnone : (none : Option {v : V // v ∉ H.verts}) ∈ Cstar.sub.verts
  · have hsum2 : ∑ v ∈ H.verts, degE v = 2 := by rw [hdegE_sumH, Cstar.isCycle.2 none hnone]
    let Att : Finset V := H.verts.filter (fun v => 0 < degE v)
    have hsumAtt : ∑ v ∈ Att, degE v = 2 := by
      rw [← hsum2]
      refine Finset.sum_subset (Finset.filter_subset _ _) fun v hv hnot => ?_
      have : ¬ 0 < degE v := fun h => hnot (Finset.mem_filter.mpr ⟨hv, h⟩)
      omega
    have hAtt_le : Att.card ≤ 2 := by
      have : Att.card ≤ ∑ v ∈ Att, degE v := by
        calc Att.card = ∑ _v ∈ Att, 1 := by simp
          _ ≤ ∑ v ∈ Att, degE v := Finset.sum_le_sum fun v hv => (Finset.mem_filter.mp hv).2
      omega
    have hAtt_ne : Att.Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty] at hempty
      rw [hempty, Finset.sum_empty] at hsumAtt
      omega
    by_cases hAtt1 : Att.card = 1
    · -- Subcase B1: single attachment vertex p ∈ H.verts -> direct lift!
      left
      obtain ⟨p, hpAtt⟩ := Finset.card_eq_one.mp hAtt1
      have hpH : p ∈ H.verts := (Finset.mem_filter.mp (hpAtt ▸ Finset.mem_singleton_self p)).1
      have hdegE_p : degE p = 2 := by rw [hpAtt, Finset.sum_singleton] at hsumAtt; exact hsumAtt
      have hdegE_otherH : ∀ v ∈ H.verts, v ≠ p → degE v = 0 := by
        intro v hv hne
        by_contra hpos
        have hmem : v ∈ Att := Finset.mem_filter.mpr ⟨hv, by omega⟩
        rw [hpAtt, Finset.mem_singleton] at hmem
        exact hne hmem
      have hend_H : ∀ e ∈ Eout, (G.tail e ∈ H.verts → G.tail e = p) ∧ (G.head e ∈ H.verts → G.head e = p) := by
        intro e he
        constructor <;> intro hv <;> by_contra hne
        · have h0 := hdegE_otherH _ hv hne
          have hpos : 0 < (Eout.filter (fun e' => G.tail e' = G.tail e)).card :=
            Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, rfl⟩⟩
          unfold degE at h0; omega
        · have h0 := hdegE_otherH _ hv hne
          have hpos : 0 < (Eout.filter (fun e' => G.head e' = G.head e)).card :=
            Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, rfl⟩⟩
          unfold degE at h0; omega
      let Csub : G.Subgraph :=
        { verts := insert p Vout
          edges := Eout
          tail_mem := fun {e} he => by
            by_cases ht : G.tail e ∈ H.verts
            · rw [(hend_H e he).1 ht]; exact Finset.mem_insert_self _ _
            · refine Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht, ?_⟩)
              simp only [Eout, Finset.mem_map, Function.Embedding.coeFn_mk] at he
              rcases he with ⟨e', he', rfl⟩
              have hmem := Cstar.sub.tail_mem he'
              dsimp only [Gstar, Multigraph.contractSubgraph] at hmem
              rwa [dif_neg ht] at hmem
          head_mem := fun {e} he => by
            by_cases hh : G.head e ∈ H.verts
            · rw [(hend_H e he).2 hh]; exact Finset.mem_insert_self _ _
            · refine Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh, ?_⟩)
              simp only [Eout, Finset.mem_map, Function.Embedding.coeFn_mk] at he
              rcases he with ⟨e', he', rfl⟩
              have hmem := Cstar.sub.head_mem he'
              dsimp only [Gstar, Multigraph.contractSubgraph] at hmem
              rwa [dif_neg hh] at hmem }
      -- Lift walk in Cstar.sub to walk in Csub via φ(none) = p, φ(some v) = v.1
      let phi : Option {v : V // v ∉ H.verts} → V
        | none => p
        | some v => v.1
      have hphi_adj : ∀ a b, Cstar.sub.Adj a b → Csub.Adj (phi a) (phi b) := by
        rintro a b ⟨e', he', ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
        · have heE : e'.1 ∈ Eout := Finset.mem_map.mpr ⟨e', he', rfl⟩
          have ht : G.tail e'.1 = phi a := by
            rw [← h1]; simp only [Gstar, Multigraph.contractSubgraph]
            split_ifs with h
            · exact (hend_H e'.1 heE).1 h
            · rfl
          have hh : G.head e'.1 = phi b := by
            rw [← h2]; simp only [Gstar, Multigraph.contractSubgraph]
            split_ifs with h
            · exact (hend_H e'.1 heE).2 h
            · rfl
          exact ⟨e'.1, heE, Or.inl ⟨ht, hh⟩⟩
        · have heE : e'.1 ∈ Eout := Finset.mem_map.mpr ⟨e', he', rfl⟩
          have ht : G.tail e'.1 = phi b := by
            rw [← h1]; simp only [Gstar, Multigraph.contractSubgraph]
            split_ifs with h
            · exact (hend_H e'.1 heE).1 h
            · rfl
          have hh : G.head e'.1 = phi a := by
            rw [← h2]; simp only [Gstar, Multigraph.contractSubgraph]
            split_ifs with h
            · exact (hend_H e'.1 heE).2 h
            · rfl
          exact ⟨e'.1, heE, Or.inr ⟨ht, hh⟩⟩
      have hCsub_cyc : Csub.IsCycle := by
        refine ⟨⟨⟨p, Finset.mem_insert_self _ _⟩, fun u hu v hv => ?_⟩, fun v hv => ?_⟩
        · have hpre : ∀ x ∈ Csub.verts, ∃ a ∈ Cstar.sub.verts, phi a = x := by
            intro x hx
            rw [Finset.mem_insert] at hx
            rcases hx with rfl | hx
            · exact ⟨none, hnone, rfl⟩
            · rcases (Finset.mem_filter.mp hx).2 with ⟨hxnot, hxmem⟩
              exact ⟨some ⟨x, hxnot⟩, hxmem, rfl⟩
          obtain ⟨a, ha, rfl⟩ := hpre u hu
          obtain ⟨b, hb, rfl⟩ := hpre v hv
          have hrtg := Cstar.isCycle.1.2 a ha b hb
          clear hb hv
          induction hrtg with
          | refl => exact .refl
          | tail _ hs ih => exact ih.tail (hphi_adj _ _ hs)
        · rw [Finset.mem_insert] at hv
          rcases hv with rfl | hv
          · exact hdegE_p
          · rcases (Finset.mem_filter.mp hv).2 with ⟨hvnot, hvmem⟩
            change degE v = 2
            rw [hdegE_out v hvnot]
            exact Cstar.isCycle.2 _ hvmem
      have hs_flow : G.IsFlow s := by
        intro v
        by_cases hv : v ∈ H.verts
        · by_cases hvp : v = p
          · rw [hvp]
            have hoth : ∀ u ∈ H.verts, u ≠ p → G.boundary s u = 0 := by
              intro u hu hne
              have h0 := hdegE_otherH u hu hne
              rw [boundary_eq_sum_ite]
              refine Finset.sum_eq_zero fun e _ => ?_
              by_cases he : e ∈ Eout
              · have ht : G.tail e ≠ u := fun h => by
                  have : 0 < (Eout.filter (fun e' => G.tail e' = u)).card :=
                    Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, h⟩⟩
                  unfold degE at h0; omega
                have hh : G.head e ≠ u := fun h => by
                  have : 0 < (Eout.filter (fun e' => G.head e' = u)).card :=
                    Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, h⟩⟩
                  unfold degE at h0; omega
                simp [ht, hh]
              · simp [hs_zero e he]
            have hsum := hbd_sumH
            rw [← Finset.add_sum_erase _ _ hpH] at hsum
            have hrest : ∑ u ∈ H.verts.erase p, G.boundary s u = 0 :=
              Finset.sum_eq_zero fun u hu => hoth u (Finset.mem_of_mem_erase hu) (Finset.ne_of_mem_erase hu)
            rw [hrest, add_zero] at hsum
            exact hsum
          · have h0 := hdegE_otherH v hv hvp
            rw [boundary_eq_sum_ite]
            refine Finset.sum_eq_zero fun e _ => ?_
            by_cases he : e ∈ Eout
            · have ht : G.tail e ≠ v := fun h => by
                have : 0 < (Eout.filter (fun e' => G.tail e' = v)).card :=
                  Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, h⟩⟩
                unfold degE at h0; omega
              have hh : G.head e ≠ v := fun h => by
                have : 0 < (Eout.filter (fun e' => G.head e' = v)).card :=
                  Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, h⟩⟩
                unfold degE at h0; omega
              simp [ht, hh]
            · simp [hs_zero e he]
        · exact hbd_out v hv
      refine ⟨⟨Csub, hCsub_cyc, s, fun {e} he => hs_mem e he, fun {e} he => hs_zero e he, hs_flow⟩, hEout_disj, fun e he => ?_⟩
      simp [s, he]
    · -- Subcase B2: two distinct attachment vertices p, p' ∈ H.verts!
      right
      have hAtt2 : Att.card = 2 := by
        have hpos : 0 < Att.card := Finset.card_pos.mpr hAtt_ne
        omega
      obtain ⟨p, p', hne, hAtt_eq⟩ := Finset.card_eq_two.mp hAtt2
      have hpAtt : p ∈ Att := by rw [hAtt_eq]; exact Finset.mem_insert_self _ _
      have hp'Att : p' ∈ Att := by rw [hAtt_eq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      have hpH : p ∈ H.verts := (Finset.mem_filter.mp hpAtt).1
      have hp'H : p' ∈ H.verts := (Finset.mem_filter.mp hp'Att).1
      have hdeg_p_pos : 0 < degE p := (Finset.mem_filter.mp hpAtt).2
      have hdeg_p'_pos : 0 < degE p' := (Finset.mem_filter.mp hp'Att).2
      have hsum_pp' : degE p + degE p' = 2 := by
        rw [hAtt_eq, Finset.sum_pair hne] at hsumAtt; exact hsumAtt
      have hdegE_p : degE p = 1 := by omega
      have hdegE_p' : degE p' = 1 := by omega
      have hdegE_otherH : ∀ v ∈ H.verts, v ≠ p → v ≠ p' → degE v = 0 := by
        intro v hv h1 h2
        by_contra hpos
        have hmem : v ∈ Att := Finset.mem_filter.mpr ⟨hv, by omega⟩
        rw [hAtt_eq, Finset.mem_insert, Finset.mem_singleton] at hmem
        rcases hmem with rfl | rfl
        · exact h1 rfl
        · exact h2 rfl
      have hend_H : ∀ e ∈ Eout,
          (G.tail e ∈ H.verts → G.tail e = p ∨ G.tail e = p') ∧
          (G.head e ∈ H.verts → G.head e = p ∨ G.head e = p') := by
        intro e he
        constructor <;> intro hv <;> by_contra hnot
        · push Not at hnot
          have h0 := hdegE_otherH _ hv hnot.1 hnot.2
          have hpos : 0 < (Eout.filter (fun e' => G.tail e' = G.tail e)).card :=
            Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, rfl⟩⟩
          unfold degE at h0; omega
        · push Not at hnot
          have h0 := hdegE_otherH _ hv hnot.1 hnot.2
          have hpos : 0 < (Eout.filter (fun e' => G.head e' = G.head e)).card :=
            Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, rfl⟩⟩
          unfold degE at h0; omega
      have hbd_otherH : ∀ v ∈ H.verts, v ≠ p → v ≠ p' → G.boundary s v = 0 := by
        intro v hv h1 h2
        have h0 := hdegE_otherH v hv h1 h2
        rw [boundary_eq_sum_ite]
        refine Finset.sum_eq_zero fun e _ => ?_
        by_cases he : e ∈ Eout
        · have ht : G.tail e ≠ v := fun h => by
            have : 0 < (Eout.filter (fun e' => G.tail e' = v)).card :=
              Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, h⟩⟩
            unfold degE at h0; omega
          have hh : G.head e ≠ v := fun h => by
            have : 0 < (Eout.filter (fun e' => G.head e' = v)).card :=
              Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, h⟩⟩
            unfold degE at h0; omega
          simp [ht, hh]
        · simp [hs_zero e he]
      have hbd_p_pm : G.boundary s p = 1 ∨ G.boundary s p = -1 := by
        unfold degE at hdegE_p
        have hcase : ((Eout.filter (fun e => G.head e = p)).card = 1 ∧
            (Eout.filter (fun e => G.tail e = p)).card = 0) ∨
            ((Eout.filter (fun e => G.head e = p)).card = 0 ∧
            (Eout.filter (fun e => G.tail e = p)).card = 1) := by omega
        rw [boundary_eq_sum_ite]
        rw [← Finset.sum_subset (Finset.subset_univ Eout) (fun e _ hnot => by simp [hs_zero e hnot])]
        rcases hcase with ⟨hh1, ht0⟩ | ⟨hh0, ht1⟩
        · obtain ⟨e0, he0⟩ := Finset.card_eq_one.mp hh1
          have he0_mem : e0 ∈ Eout ∧ G.head e0 = p := Finset.mem_filter.mp (he0 ▸ Finset.mem_singleton_self e0)
          have hno_t : ∀ e ∈ Eout, G.tail e ≠ p := fun e he ht => by
            have : 0 < (Eout.filter (fun e => G.tail e = p)).card :=
              Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, ht⟩⟩
            omega
          have hsum_eq : ∑ e ∈ Eout, ((if G.head e = p then s e else 0) - (if G.tail e = p then s e else 0)) =
              s e0 := by
            rw [Finset.sum_eq_single e0]
            · simp [he0_mem.2, hno_t e0 he0_mem.1]
            · intro e he hne0
              have hnh : G.head e ≠ p := fun hh => by
                have : e ∈ ({e0} : Finset E) := he0 ▸ Finset.mem_filter.mpr ⟨he, hh⟩
                exact hne0 (Finset.mem_singleton.mp this)
              simp [hnh, hno_t e he]
            · intro h; exact absurd he0_mem.1 h
          rw [hsum_eq]; exact hs_mem e0 he0_mem.1
        · obtain ⟨e0, he0⟩ := Finset.card_eq_one.mp ht1
          have he0_mem : e0 ∈ Eout ∧ G.tail e0 = p := Finset.mem_filter.mp (he0 ▸ Finset.mem_singleton_self e0)
          have hno_h : ∀ e ∈ Eout, G.head e ≠ p := fun e he hh => by
            have : 0 < (Eout.filter (fun e => G.head e = p)).card :=
              Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, hh⟩⟩
            omega
          have hsum_eq : ∑ e ∈ Eout, ((if G.head e = p then s e else 0) - (if G.tail e = p then s e else 0)) =
              -s e0 := by
            rw [Finset.sum_eq_single e0]
            · simp [he0_mem.2, hno_h e0 he0_mem.1]
            · intro e he hne0
              have hnt : G.tail e ≠ p := fun ht => by
                have : e ∈ ({e0} : Finset E) := he0 ▸ Finset.mem_filter.mpr ⟨he, ht⟩
                exact hne0 (Finset.mem_singleton.mp this)
              simp [hnt, hno_h e he]
            · intro h; exact absurd he0_mem.1 h
          rw [hsum_eq]
          rcases hs_mem e0 he0_mem.1 with h | h <;> simp [h]
      have hbd_p'_eq : G.boundary s p' = -G.boundary s p := by
        have hsum := hbd_sumH
        rw [← Finset.sum_subset (show ({p, p'} : Finset V) ⊆ H.verts by
              intro v hv; simp only [Finset.mem_insert, Finset.mem_singleton] at hv
              rcases hv with rfl | rfl; exact hpH; exact hp'H)
            (fun v hv hnot => by
              simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
              exact hbd_otherH v hv hnot.1 hnot.2)] at hsum
        rw [Finset.sum_pair hne] at hsum
        omega
      refine ⟨p, p', hpH, hp'H, hne, ?_⟩
      intro verts edges hlen hnodup hvH heH hhead hlast hstep
      have hP_deg := simplePath_deg_eq G verts edges hlen hnodup hstep p p' hhead hlast hne
      have hP_sig := simplePathSign_spec G verts edges hlen hnodup hstep p p' hhead hlast
      let mult : ℤ := G.boundary s p
      let jSign : E → ℤ := fun e => mult * simplePathSign G verts edges hlen e
      let cSign : E → ℤ := fun e => s e + jSign e
      have hJE_disj : Disjoint Eout edges.toFinset := by
        rw [Finset.disjoint_left]
        intro e he1 he2
        exact Finset.disjoint_left.mp hEout_disj he1 (heH e (List.mem_toFinset.mp he2))
      have hJV_disj : Disjoint Vout verts.toFinset := by
        rw [Finset.disjoint_left]
        intro v hv1 hv2
        exact (Finset.mem_filter.mp hv1).2.1 (hvH v (List.mem_toFinset.mp hv2))
      let Csub : G.Subgraph :=
        { verts := Vout ∪ verts.toFinset
          edges := Eout ∪ edges.toFinset
          tail_mem := fun {e} he => by
            rw [Finset.mem_union] at he ⊢
            rcases he with he | he
            · by_cases ht : G.tail e ∈ H.verts
              · right; rcases (hend_H e he).1 ht with h | h <;> rw [h]
                · exact List.mem_toFinset.mpr (List.mem_of_head? hhead)
                · exact List.mem_toFinset.mpr (List.mem_of_getLast? hlast)
              · left
                refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht, ?_⟩
                simp only [Eout, Finset.mem_map, Function.Embedding.coeFn_mk] at he
                rcases he with ⟨e', he', rfl⟩
                have hmem := Cstar.sub.tail_mem he'
                dsimp only [Gstar, Multigraph.contractSubgraph] at hmem
                rwa [dif_neg ht] at hmem
            · right
              obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem (List.mem_toFinset.mp he)
              rcases hstep k hk with ⟨h1, _⟩ | ⟨h1, _⟩
              · rw [h1]; exact List.mem_toFinset.mpr (List.getElem_mem _)
              · rw [h1]; exact List.mem_toFinset.mpr (List.getElem_mem _)
          head_mem := fun {e} he => by
            rw [Finset.mem_union] at he ⊢
            rcases he with he | he
            · by_cases hh : G.head e ∈ H.verts
              · right; rcases (hend_H e he).2 hh with h | h <;> rw [h]
                · exact List.mem_toFinset.mpr (List.mem_of_head? hhead)
                · exact List.mem_toFinset.mpr (List.mem_of_getLast? hlast)
              · left
                refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh, ?_⟩
                simp only [Eout, Finset.mem_map, Function.Embedding.coeFn_mk] at he
                rcases he with ⟨e', he', rfl⟩
                have hmem := Cstar.sub.head_mem he'
                dsimp only [Gstar, Multigraph.contractSubgraph] at hmem
                rwa [dif_neg hh] at hmem
            · right
              obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem (List.mem_toFinset.mp he)
              rcases hstep k hk with ⟨_, h2⟩ | ⟨_, h2⟩
              · rw [h2]; exact List.mem_toFinset.mpr (List.getElem_mem _)
              · rw [h2]; exact List.mem_toFinset.mpr (List.getElem_mem _) }
      -- Path connectivity inside Csub
      have hp_mem : p ∈ verts := List.mem_of_head? hhead
      have hp'_mem : p' ∈ verts := List.mem_of_getLast? hlast
      have hJ_conn : ∀ u ∈ verts, Relation.ReflTransGen Csub.Adj p u := by
        have hstep_idx : ∀ (k : ℕ) (hk : k < verts.length),
            Relation.ReflTransGen Csub.Adj p (verts[k]'hk) := by
          intro k
          induction k with
          | zero =>
            intro hk
            have hv0 : verts[0]'hk = p := by
              rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hk, Option.some.injEq] at hhead
              exact hhead
            rw [hv0]
          | succ k ih =>
            intro hk
            have hk' : k < edges.length := by omega
            have hprev := ih (by omega)
            have he_mem : edges[k]'hk' ∈ Csub.edges :=
              Finset.mem_union_right _ (List.mem_toFinset.mpr (List.getElem_mem _))
            exact hprev.tail ⟨edges[k]'hk', he_mem, hstep k hk'⟩
        intro u hu
        obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hu
        exact hstep_idx k hk
      have hsym_Csub : ∀ u v, Relation.ReflTransGen Csub.Adj u v → Relation.ReflTransGen Csub.Adj v u := by
        intro u v h
        induction h with
        | refl => exact .refl
        | tail _ hs ih =>
          rcases hs with ⟨e, he, h1 | h1⟩
          · exact Relation.ReflTransGen.head ⟨e, he, Or.inr h1⟩ ih
          · exact Relation.ReflTransGen.head ⟨e, he, Or.inl h1⟩ ih
      have hpp'_conn : Relation.ReflTransGen Csub.Adj p p' := hJ_conn p' hp'_mem
      -- Every vertex of Vout reaches p in Csub (follow Cstar.sub path to none -> hits p or p')
      have hVout_to_p : ∀ u ∈ Vout, Relation.ReflTransGen Csub.Adj u p := by
        intro u hu
        rcases (Finset.mem_filter.mp hu).2 with ⟨hunot, humem⟩
        have hrtg := Cstar.isCycle.1.2 (some ⟨u, hunot⟩) humem none hnone
        -- Induct on path from some u to a: if a = none -> hits p; if a = some w -> reaches w
        have hgo : ∀ a, Relation.ReflTransGen Cstar.sub.Adj (some ⟨u, hunot⟩) a →
            match a with
            | none => Relation.ReflTransGen Csub.Adj u p
            | some w => Relation.ReflTransGen Csub.Adj u w.1 ∨ Relation.ReflTransGen Csub.Adj u p := by
          intro a ha
          induction ha with
          | refl => exact Or.inl .refl
          | @tail b c _ hs ih =>
            rcases hs with ⟨e', he', ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
            · have heC : e'.1 ∈ Csub.edges := Finset.mem_union_left _ (Finset.mem_map.mpr ⟨e', he', rfl⟩)
              cases b with
              | none =>
                cases c with
                | none => exact ih
                | some w => exact Or.inr ih
              | some wb =>
                rcases ih with hreach | hp_done
                · have htb : G.tail e'.1 = wb.1 := by
                    simp only [Gstar, Multigraph.contractSubgraph] at h1
                    by_cases hm : G.tail e'.1 ∈ H.verts
                    · simp [hm] at h1
                    · rw [dif_neg hm] at h1; exact congrArg Subtype.val (Option.some.inj h1)
                  cases c with
                  | none =>
                    have hhH : G.head e'.1 ∈ H.verts := by
                      simp only [Gstar, Multigraph.contractSubgraph] at h2
                      by_cases hm : G.head e'.1 ∈ H.verts
                      · exact hm
                      · simp [hm] at h2
                    rcases (hend_H e'.1 (Finset.mem_map.mpr ⟨e', he', rfl⟩)).2 hhH with h | h
                    · exact hreach.tail ⟨e'.1, heC, Or.inl ⟨htb, h⟩⟩
                    · exact (hreach.tail ⟨e'.1, heC, Or.inl ⟨htb, h⟩⟩).trans (hsym_Csub p p' hpp'_conn)
                  | some wc =>
                    have hhc : G.head e'.1 = wc.1 := by
                      simp only [Gstar, Multigraph.contractSubgraph] at h2
                      by_cases hm : G.head e'.1 ∈ H.verts
                      · simp [hm] at h2
                      · rw [dif_neg hm] at h2; exact congrArg Subtype.val (Option.some.inj h2)
                    exact Or.inl (hreach.tail ⟨e'.1, heC, Or.inl ⟨htb, hhc⟩⟩)
                · cases c with
                  | none => exact hp_done
                  | some _ => exact Or.inr hp_done
            · have heC : e'.1 ∈ Csub.edges := Finset.mem_union_left _ (Finset.mem_map.mpr ⟨e', he', rfl⟩)
              cases b with
              | none =>
                cases c with
                | none => exact ih
                | some _ => exact Or.inr ih
              | some wb =>
                rcases ih with hreach | hp_done
                · have hhb : G.head e'.1 = wb.1 := by
                    simp only [Gstar, Multigraph.contractSubgraph] at h2
                    by_cases hm : G.head e'.1 ∈ H.verts
                    · simp [hm] at h2
                    · rw [dif_neg hm] at h2; exact congrArg Subtype.val (Option.some.inj h2)
                  cases c with
                  | none =>
                    have htH : G.tail e'.1 ∈ H.verts := by
                      simp only [Gstar, Multigraph.contractSubgraph] at h1
                      by_cases hm : G.tail e'.1 ∈ H.verts
                      · exact hm
                      · simp [hm] at h1
                    rcases (hend_H e'.1 (Finset.mem_map.mpr ⟨e', he', rfl⟩)).1 htH with h | h
                    · exact hreach.tail ⟨e'.1, heC, Or.inr ⟨h, hhb⟩⟩
                    · exact (hreach.tail ⟨e'.1, heC, Or.inr ⟨h, hhb⟩⟩).trans (hsym_Csub p p' hpp'_conn)
                  | some wc =>
                    have htc : G.tail e'.1 = wc.1 := by
                      simp only [Gstar, Multigraph.contractSubgraph] at h1
                      by_cases hm : G.tail e'.1 ∈ H.verts
                      · simp [hm] at h1
                      · rw [dif_neg hm] at h1; exact congrArg Subtype.val (Option.some.inj h1)
                    exact Or.inl (hreach.tail ⟨e'.1, heC, Or.inr ⟨htc, hhb⟩⟩)
                · cases c with
                  | none => exact hp_done
                  | some _ => exact Or.inr hp_done
        exact hgo none hrtg
      -- Degree of Csub at every vertex in Csub.verts is 2
      have hCsub_deg : ∀ v ∈ Csub.verts, Csub.deg v = 2 := by
        intro v hv
        -- Split Csub.deg v = degE v + P.deg v
        have hsplit_deg : Csub.deg v = degE v +
            ((edges.toFinset.filter (fun e => G.tail e = v)).card +
             (edges.toFinset.filter (fun e => G.head e = v)).card) := by
          unfold Multigraph.Subgraph.deg degE
          have hdj1 : Disjoint (Eout.filter (fun e => G.tail e = v))
              (edges.toFinset.filter (fun e => G.tail e = v)) :=
            Disjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _) hJE_disj
          have hdj2 : Disjoint (Eout.filter (fun e => G.head e = v))
              (edges.toFinset.filter (fun e => G.head e = v)) :=
            Disjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _) hJE_disj
          simp only [Csub, Finset.filter_union, Finset.card_union_of_disjoint hdj1,
            Finset.card_union_of_disjoint hdj2]
          omega
        rw [hsplit_deg]
        rw [Finset.mem_union] at hv
        rcases hv with hvOut | hvJ
        · rcases (Finset.mem_filter.mp hvOut).2 with ⟨hvnot, hvmem⟩
          have hvnotJ : v ∉ verts := fun h => hvnot (hvH v h)
          have hP0 := hP_deg.2.2.2 v hvnotJ
          unfold Multigraph.Subgraph.deg at hP0
          rw [hdegE_out v hvnot, Cstar.isCycle.2 _ hvmem]
          dsimp only at hP0
          omega
        · have hvL : v ∈ verts := List.mem_toFinset.mp hvJ
          by_cases hvp : v = p
          · subst hvp
            have hP1 := hP_deg.1; unfold Multigraph.Subgraph.deg at hP1
            dsimp only at hP1; omega
          · by_cases hvp' : v = p'
            · subst hvp'
              have hP1 := hP_deg.2.1; unfold Multigraph.Subgraph.deg at hP1
              dsimp only at hP1; omega
            · have hP2 := hP_deg.2.2.1 v hvL hvp hvp'; unfold Multigraph.Subgraph.deg at hP2
              have hE0 := hdegE_otherH v (hvH v hvL) hvp hvp'
              dsimp only at hP2; omega
      have hCsub_cyc : Csub.IsCycle := by
        refine ⟨⟨⟨p, Finset.mem_union_right _ (List.mem_toFinset.mpr hp_mem)⟩, fun u hu v hv => ?_⟩, hCsub_deg⟩
        have hup : Relation.ReflTransGen Csub.Adj u p := by
          rw [Finset.mem_union] at hu
          rcases hu with hu | hu
          · exact hVout_to_p u hu
          · exact hsym_Csub p u (hJ_conn u (List.mem_toFinset.mp hu))
        have hpv : Relation.ReflTransGen Csub.Adj p v := by
          rw [Finset.mem_union] at hv
          rcases hv with hv | hv
          · exact hsym_Csub v p (hVout_to_p v hv)
          · exact hJ_conn v (List.mem_toFinset.mp hv)
        exact hup.trans hpv
      have hcSign_flow : G.IsFlow cSign := by
        intro v
        dsimp only [cSign]
        rw [boundary_add]
        have hjbd : G.boundary jSign v = mult * G.boundary (simplePathSign G verts edges hlen) v := by
          dsimp only [jSign]
          have h := boundary_zsmul G (simplePathSign G verts edges hlen) mult v
          simpa [zsmul_eq_mul, mul_comm] using h
        rw [hjbd, hP_sig.2.2 v]
        by_cases hvp : v = p
        · subst hvp; simp [hne, mult]
        · by_cases hvp' : v = p'
          · subst hvp'; simp [Ne.symm hne, hbd_p'_eq, mult]
          · simp only [hvp, hvp', ↓reduceIte, sub_self, mul_zero, add_zero]
            by_cases hvH' : v ∈ H.verts
            · exact hbd_otherH v hvH' hvp hvp'
            · exact hbd_out v hvH'
      have hcSign_mem : ∀ {e}, e ∈ Csub.edges → cSign e = 1 ∨ cSign e = -1 := by
        intro e he
        rw [Finset.mem_union] at he
        rcases he with heOut | heJ
        · have hnotJ : e ∉ edges := fun h =>
            Finset.disjoint_left.mp hJE_disj heOut (List.mem_toFinset.mpr h)
          dsimp only [cSign, jSign]
          rw [hP_sig.2.1 e hnotJ, mul_zero, add_zero]
          exact hs_mem e heOut
        · have hnotOut : e ∉ Eout := Finset.disjoint_right.mp hJE_disj heJ
          dsimp only [cSign, jSign]
          rw [hs_zero e hnotOut, zero_add]
          rcases hbd_p_pm with hm | hm <;> rcases hP_sig.1 e (List.mem_toFinset.mp heJ) with h1 | h1 <;>
            simp [mult, hm, h1]
      have hcSign_zero : ∀ {e}, e ∉ Csub.edges → cSign e = 0 := by
        intro e he
        rw [Finset.mem_union, not_or] at he
        dsimp only [cSign, jSign]
        rw [hs_zero e he.1, hP_sig.2.1 e (fun h => he.2 (List.mem_toFinset.mpr h)), mul_zero, add_zero]
      refine ⟨⟨Csub, hCsub_cyc, cSign, hcSign_mem, hcSign_zero, hcSign_flow⟩, ?_, ?_⟩
      · intro e henot
        have hnotJ : e ∉ edges := fun h => henot (heH e h)
        dsimp only [cSign, jSign]
        rw [hP_sig.2.1 e hnotJ, mul_zero, add_zero]
        simp [s, henot]
      · intro e heH'
        have hnotOut : e ∉ Eout := Finset.disjoint_right.mp hEout_disj heH'
        simp [Csub, hnotOut]
  · -- Subcase A: none ∉ Cstar.sub.verts -> direct lift!
    left
    have hno_H : ∀ e ∈ Eout, G.tail e ∉ H.verts ∧ G.head e ∉ H.verts := by
      intro e he
      simp only [Eout, Finset.mem_map, Function.Embedding.coeFn_mk] at he
      rcases he with ⟨e', he', rfl⟩
      constructor
      · intro ht
        have hm := Cstar.sub.tail_mem he'
        dsimp only [Gstar, Multigraph.contractSubgraph] at hm
        rw [dif_pos ht] at hm
        exact hnone hm
      · intro hh
        have hm := Cstar.sub.head_mem he'
        dsimp only [Gstar, Multigraph.contractSubgraph] at hm
        rw [dif_pos hh] at hm
        exact hnone hm
    let Csub : G.Subgraph :=
      { verts := Vout
        edges := Eout
        tail_mem := fun {e} he => by
          have ht := (hno_H e he).1
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht, ?_⟩
          simp only [Eout, Finset.mem_map, Function.Embedding.coeFn_mk] at he
          rcases he with ⟨e', he', rfl⟩
          have hm := Cstar.sub.tail_mem he'
          dsimp only [Gstar, Multigraph.contractSubgraph] at hm
          rwa [dif_neg ht] at hm
        head_mem := fun {e} he => by
          have hh := (hno_H e he).2
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh, ?_⟩
          simp only [Eout, Finset.mem_map, Function.Embedding.coeFn_mk] at he
          rcases he with ⟨e', he', rfl⟩
          have hm := Cstar.sub.head_mem he'
          dsimp only [Gstar, Multigraph.contractSubgraph] at hm
          rwa [dif_neg hh] at hm }
    have hCsub_cyc : Csub.IsCycle := by
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · obtain ⟨a, ha⟩ := Cstar.isCycle.1.1
        cases a with
        | none => exact absurd ha hnone
        | some v => exact ⟨v.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, v.2, ha⟩⟩
      · intro u hu v hv
        rcases (Finset.mem_filter.mp hu).2 with ⟨hunot, humem⟩
        rcases (Finset.mem_filter.mp hv).2 with ⟨hvnot, hvmem⟩
        have hrtg := Cstar.isCycle.1.2 (some ⟨u, hunot⟩) humem (some ⟨v, hvnot⟩) hvmem
        have hgo : ∀ a, Relation.ReflTransGen Cstar.sub.Adj (some ⟨u, hunot⟩) a →
            ∀ w (hw : w ∉ H.verts), a = some ⟨w, hw⟩ → Relation.ReflTransGen Csub.Adj u w := by
          intro a ha
          induction ha with
          | refl =>
            intro w hw heq
            have : w = u := (congrArg Subtype.val (Option.some.inj heq)).symm
            subst this; exact .refl
          | @tail b c _ hs ih =>
            intro w hw hc
            subst hc
            rcases hs with ⟨e', he', ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
            · have heE : e'.1 ∈ Eout := Finset.mem_map.mpr ⟨e', he', rfl⟩
              have htnot := (hno_H e'.1 heE).1
              have hhnot := (hno_H e'.1 heE).2
              cases b with
              | none => exact absurd (Cstar.sub.tail_mem he') (by simpa [h1] using hnone)
              | some wb =>
                have htb : G.tail e'.1 = wb.1 := by
                  dsimp only [Gstar, Multigraph.contractSubgraph] at h1
                  rw [dif_neg htnot] at h1; exact congrArg Subtype.val (Option.some.inj h1)
                have hhc : G.head e'.1 = w := by
                  dsimp only [Gstar, Multigraph.contractSubgraph] at h2
                  rw [dif_neg hhnot] at h2; exact congrArg Subtype.val (Option.some.inj h2)
                exact (ih wb.1 wb.2 rfl).tail ⟨e'.1, heE, Or.inl ⟨htb, hhc⟩⟩
            · have heE : e'.1 ∈ Eout := Finset.mem_map.mpr ⟨e', he', rfl⟩
              have htnot := (hno_H e'.1 heE).1
              have hhnot := (hno_H e'.1 heE).2
              cases b with
              | none => exact absurd (Cstar.sub.head_mem he') (by simpa [h2] using hnone)
              | some wb =>
                have hhb : G.head e'.1 = wb.1 := by
                  dsimp only [Gstar, Multigraph.contractSubgraph] at h2
                  rw [dif_neg hhnot] at h2; exact congrArg Subtype.val (Option.some.inj h2)
                have htc : G.tail e'.1 = w := by
                  dsimp only [Gstar, Multigraph.contractSubgraph] at h1
                  rw [dif_neg htnot] at h1; exact congrArg Subtype.val (Option.some.inj h1)
                exact (ih wb.1 wb.2 rfl).tail ⟨e'.1, heE, Or.inr ⟨htc, hhb⟩⟩
        exact hgo (some ⟨v, hvnot⟩) hrtg v hvnot rfl
      · intro v hv
        rcases (Finset.mem_filter.mp hv).2 with ⟨hvnot, hvmem⟩
        change degE v = 2
        rw [hdegE_out v hvnot]
        exact Cstar.isCycle.2 _ hvmem
    have hs_flow : G.IsFlow s := by
      intro v
      by_cases hv : v ∈ H.verts
      · rw [boundary_eq_sum_ite]
        refine Finset.sum_eq_zero fun e _ => ?_
        by_cases he : e ∈ Eout
        · have ht : G.tail e ≠ v := fun h => (hno_H e he).1 (h.symm ▸ hv)
          have hh : G.head e ≠ v := fun h => (hno_H e he).2 (h.symm ▸ hv)
          simp [ht, hh]
        · simp [hs_zero e he]
      · exact hbd_out v hv
    refine ⟨⟨Csub, hCsub_cyc, s, fun {e} he => hs_mem e he, fun {e} he => hs_zero e he, hs_flow⟩, hEout_disj, fun e he => ?_⟩
    simp [s, he]

/-! ### Lemma 4.8(CYC): Lifting a contracted move in case `(CYC)` -/

private lemma exists_short_path_in_cycle {V E : Type} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (G : Multigraph V E) (H : G.Subgraph) (hC : H.IsCycle)
    (p p' : V) (hp : p ∈ H.verts) (hp' : p' ∈ H.verts) (hne : p ≠ p') :
    ∃ (verts : List V) (edges : List E) (_ : verts.length = edges.length + 1),
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
      2 * edges.length ≤ H.edges.card := by
  obtain ⟨v₁, e₁, hlen₁, hnd₁, hhead₁, hlast₁, he₁, hstep₁⟩ :=
    exists_simplePath_of_reflTransGen (hC.1.2 p hp p' hp')
  have hv₁_H : ∀ v ∈ v₁, v ∈ H.verts := by
    intro v hv
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hv
    have he₁_pos : 0 < e₁.length := by
      by_contra h0
      have h0' : e₁.length = 0 := by omega
      have h0v : v₁[0]'(by omega) = p := by
        rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega), Option.some.injEq] at hhead₁
        exact hhead₁
      have hlv : v₁[0]'(by omega) = p' := by
        rw [List.getLast?_eq_getElem?] at hlast₁
        have : v₁.length - 1 = 0 := by omega
        rw [this, List.getElem?_eq_getElem (by omega), Option.some.injEq] at hlast₁
        exact hlast₁
      exact hne (h0v.symm.trans hlv)
    by_cases hkl : k < e₁.length
    · rcases hstep₁ k hkl with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact h1 ▸ H.tail_mem (he₁ _ (List.getElem_mem _))
      · exact h2 ▸ H.head_mem (he₁ _ (List.getElem_mem _))
    · have hk_eq : k = e₁.length := by omega
      have hk_prev : k - 1 < e₁.length := by omega
      rcases hstep₁ (k - 1) hk_prev with ⟨_, h2⟩ | ⟨h1, _⟩
      · have hidx : v₁[k - 1 + 1]'(by omega) = v₁[k]'hk := by congr 1; omega
        rw [hidx] at h2; exact h2 ▸ H.head_mem (he₁ _ (List.getElem_mem _))
      · have hidx : v₁[k - 1 + 1]'(by omega) = v₁[k]'hk := by congr 1; omega
        rw [hidx] at h1; exact h1 ▸ H.tail_mem (he₁ _ (List.getElem_mem _))
  -- Form H₂ = H \ e₁.toFinset; show p and p' are connected in H₂ by handshake parity on component of p
  let H₂ : G.Subgraph :=
    { verts := H.verts
      edges := H.edges \ e₁.toFinset
      tail_mem := fun he => H.tail_mem (Finset.mem_sdiff.mp he).1
      head_mem := fun he => H.head_mem (Finset.mem_sdiff.mp he).1 }
  have hP₁_deg := simplePath_deg_eq G v₁ e₁ hlen₁ hnd₁ hstep₁ p p' hhead₁ hlast₁ hne
  have hdeg_split : ∀ v ∈ H.verts, H₂.deg v +
      ((e₁.toFinset.filter (fun e => G.tail e = v)).card +
       (e₁.toFinset.filter (fun e => G.head e = v)).card) = 2 := by
    intro v hv
    have hsub : e₁.toFinset ⊆ H.edges := fun e he => he₁ e (List.mem_toFinset.mp he)
    have hEq : H.edges = H₂.edges ∪ e₁.toFinset := (Finset.sdiff_union_of_subset hsub).symm
    have hdj : Disjoint H₂.edges e₁.toFinset := Finset.sdiff_disjoint
    have hd := hC.2 v hv
    unfold Multigraph.Subgraph.deg at hd ⊢
    rw [hEq, Finset.filter_union, Finset.filter_union,
        Finset.card_union_of_disjoint (Disjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _) hdj),
        Finset.card_union_of_disjoint (Disjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _) hdj)] at hd
    omega
  have hH₂_deg_p : H₂.deg p = 1 := by
    have h1 := hdeg_split p hp; have h2 := hP₁_deg.1; unfold Multigraph.Subgraph.deg at h2; dsimp at h2; omega
  have hH₂_deg_other : ∀ v ∈ H.verts, v ≠ p → v ≠ p' → H₂.deg v = 0 ∨ H₂.deg v = 2 := by
    intro v hv hvp hvp'
    have h1 := hdeg_split v hv
    by_cases hv1 : v ∈ v₁
    · left; have h2 := hP₁_deg.2.2.1 v hv1 hvp hvp'; unfold Multigraph.Subgraph.deg at h2; dsimp at h2; omega
    · right; have h2 := hP₁_deg.2.2.2 v hv1; unfold Multigraph.Subgraph.deg at h2; dsimp at h2; omega
  -- Connected component K of p in H₂
  have hreach_p' : Relation.ReflTransGen H₂.Adj p p' := by
    classical
    let K : Finset V := H.verts.filter (fun v => Relation.ReflTransGen H₂.Adj p v)
    have hK_closed : ∀ e ∈ H₂.edges, G.tail e ∈ K ↔ G.head e ∈ K := by
      intro e he
      have htH : G.tail e ∈ H.verts := H₂.tail_mem he
      have hhH : G.head e ∈ H.verts := H₂.head_mem he
      simp only [K, Finset.mem_filter, htH, hhH, true_and]
      constructor
      · intro ht; exact ht.tail ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩
      · intro hh; exact hh.tail ⟨e, he, Or.inr ⟨rfl, rfl⟩⟩
    -- Handshake on K: ∑ v ∈ K, H₂.deg v = 2 * |E(K)| is even!
    have hK_even : Even (∑ v ∈ K, H₂.deg v) := by
      let EK := H₂.edges.filter (fun e => G.tail e ∈ K)
      have h1 : ∑ v ∈ K, (H₂.edges.filter (fun e => G.tail e = v)).card = EK.card := by
        rw [← Finset.card_biUnion]
        · congr 1; ext e
          simp only [EK, Finset.mem_biUnion, Finset.mem_filter]
          constructor
          · rintro ⟨v, hvK, he, ht⟩; exact ⟨he, ht.symm ▸ hvK⟩
          · rintro ⟨he, htK⟩; exact ⟨G.tail e, htK, he, rfl⟩
        · intro u _ v _ huv; dsimp [Function.onFun]; rw [Finset.disjoint_left]
          intro e hu hv
          exact huv ((Finset.mem_filter.mp hu).2.symm.trans (Finset.mem_filter.mp hv).2)
      have h2 : ∑ v ∈ K, (H₂.edges.filter (fun e => G.head e = v)).card = EK.card := by
        rw [← Finset.card_biUnion]
        · congr 1; ext e
          simp only [EK, Finset.mem_biUnion, Finset.mem_filter]
          constructor
          · rintro ⟨v, hvK, he, hh⟩
            exact ⟨he, (hK_closed e he).mpr (hh.symm ▸ hvK)⟩
          · rintro ⟨he, htK⟩
            exact ⟨G.head e, (hK_closed e he).mp htK, he, rfl⟩
        · intro u _ v _ huv; dsimp [Function.onFun]; rw [Finset.disjoint_left]
          intro e hu hv
          exact huv ((Finset.mem_filter.mp hu).2.symm.trans (Finset.mem_filter.mp hv).2)
      unfold Multigraph.Subgraph.deg
      rw [Finset.sum_add_distrib, h1, h2]
      exact ⟨EK.card, rfl⟩
    by_contra hnot
    have hpK : p ∈ K := Finset.mem_filter.mpr ⟨hp, .refl⟩
    have hp'notK : p' ∉ K := fun h => hnot (Finset.mem_filter.mp h).2
    rw [← Finset.add_sum_erase _ _ hpK, hH₂_deg_p] at hK_even
    have hrest_even : Even (∑ v ∈ K.erase p, H₂.deg v) := by
      have hall : ∀ v ∈ K.erase p, Even (H₂.deg v) := by
        intro v hv
        have hvH : v ∈ H.verts := (Finset.mem_filter.mp (Finset.mem_of_mem_erase hv)).1
        have hvp : v ≠ p := Finset.ne_of_mem_erase hv
        have hvp' : v ≠ p' := fun h => hp'notK (h ▸ Finset.mem_of_mem_erase hv)
        rcases hH₂_deg_other v hvH hvp hvp' with h | h <;> rw [h]
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
      clear hK_even
      generalize K.erase p = S at hall ⊢
      induction S using Finset.induction_on with
      | empty => exact ⟨0, rfl⟩
      | @insert a s ha ih =>
        rw [Finset.sum_insert ha]
        exact (hall a (Finset.mem_insert_self _ _)).add
          (ih fun v hv => hall v (Finset.mem_insert_of_mem hv))
    rcases hK_even with ⟨m, hm⟩
    rcases hrest_even with ⟨n, hn⟩
    omega
  obtain ⟨v₂, e₂, hlen₂, hnd₂, hhead₂, hlast₂, he₂, hstep₂⟩ :=
    exists_simplePath_of_reflTransGen hreach_p'
  have hv₂_H : ∀ v ∈ v₂, v ∈ H.verts := by
    intro v hv
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hv
    have he₂_pos : 0 < e₂.length := by
      by_contra h0
      have h0' : e₂.length = 0 := by omega
      have h0v : v₂[0]'(by omega) = p := by
        rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega), Option.some.injEq] at hhead₂
        exact hhead₂
      have hlv : v₂[0]'(by omega) = p' := by
        rw [List.getLast?_eq_getElem?] at hlast₂
        have : v₂.length - 1 = 0 := by omega
        rw [this, List.getElem?_eq_getElem (by omega), Option.some.injEq] at hlast₂
        exact hlast₂
      exact hne (h0v.symm.trans hlv)
    by_cases hkl : k < e₂.length
    · rcases hstep₂ k hkl with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact h1 ▸ H₂.tail_mem (he₂ _ (List.getElem_mem _))
      · exact h2 ▸ H₂.head_mem (he₂ _ (List.getElem_mem _))
    · have hk_eq : k = e₂.length := by omega
      have hk_prev : k - 1 < e₂.length := by omega
      rcases hstep₂ (k - 1) hk_prev with ⟨_, h2⟩ | ⟨h1, _⟩
      · have hidx : v₂[k - 1 + 1]'(by omega) = v₂[k]'hk := by congr 1; omega
        rw [hidx] at h2; exact h2 ▸ H₂.head_mem (he₂ _ (List.getElem_mem _))
      · have hidx : v₂[k - 1 + 1]'(by omega) = v₂[k]'hk := by congr 1; omega
        rw [hidx] at h1; exact h1 ▸ H₂.tail_mem (he₂ _ (List.getElem_mem _))
  have hsum_le : e₁.length + e₂.length ≤ H.edges.card := by
    have hnd_e₁ := simplePath_edges_nodup hnd₁ hlen₁ hstep₁
    have hnd_e₂ := simplePath_edges_nodup hnd₂ hlen₂ hstep₂
    have hdj : Disjoint e₁.toFinset e₂.toFinset := by
      rw [Finset.disjoint_left]
      intro e h1 h2
      exact (Finset.mem_sdiff.mp (he₂ e (List.mem_toFinset.mp h2))).2 h1
    have hsub : e₁.toFinset ∪ e₂.toFinset ⊆ H.edges := by
      intro e he
      rw [Finset.mem_union] at he
      rcases he with h | h
      · exact he₁ e (List.mem_toFinset.mp h)
      · exact (Finset.mem_sdiff.mp (he₂ e (List.mem_toFinset.mp h))).1
    calc e₁.length + e₂.length
        = e₁.toFinset.card + e₂.toFinset.card := by
            rw [List.toFinset_card_of_nodup hnd_e₁, List.toFinset_card_of_nodup hnd_e₂]
      _ = (e₁.toFinset ∪ e₂.toFinset).card := (Finset.card_union_of_disjoint hdj).symm
      _ ≤ H.edges.card := Finset.card_le_card hsub
  by_cases hle : e₁.length ≤ e₂.length
  · exact ⟨v₁, e₁, hlen₁, hnd₁, hv₁_H, he₁, hhead₁, hlast₁, hstep₁, by omega⟩
  · exact ⟨v₂, e₂, hlen₂, hnd₂, hv₂_H, fun e he => (Finset.mem_sdiff.mp (he₂ e he)).1,
      hhead₂, hlast₂, hstep₂, by omega⟩

theorem lem_4_8_cyc_proved
    {Γ : Type} [AddCommGroup Γ] [Fintype Γ] [DecidableEq Γ]
    (B : AddSubgroup Γ) [Fintype (Γ ⧸ B)] [Fintype B] [DecidableEq (Γ ⧸ B)] [DecidableEq B]
    (hA : 10 ≤ Fintype.card (Γ ⧸ B)) (_hB : 4 ≤ Fintype.card B)
    (Sig : StepSystem Γ) (hR1 : CondR1 B Sig) (_hR2 : CondR2 B Sig)
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : Multigraph V E) (_hbr : G.IsBridgeless)
    (H : G.Subgraph) (hcyc : IsGoodCyc G H)
    (f : G.NZFlow Γ) (hHgood : IsHGoodCyc G B H f)
    (gstar : (G.contractSubgraph H).NZFlow Γ)
    (hmove : ∃ (Cstar : (G.contractSubgraph H).DirectedCycle) (lam : Γ),
      lam ∈ Sig.carrier ∧ ∀ e, gstar.val e = f.val e.1 + Cstar.sign e • lam) :
    ∃ g : G.NZFlow Γ,
      G.SigmaJoined Sig.carrier f g ∧
      (∀ e : {e : E // e ∉ H.edges}, g.val e.1 = gstar.val e) ∧
      IsHGoodCyc G B H g := by
  rcases hmove with ⟨Cstar, lam, hlam, hgstar⟩
  rcases liftContractedCycle G H Cstar with ⟨C, hCdisj, hCsign⟩ | ⟨p, p', hpH, hp'H, hne, hsplice⟩
  · -- Case 1: Cstar lifts directly to a cycle C disjoint from H.edges
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
    refine ⟨g, Relation.ReflTransGen.single ⟨C, lam, hlam, fun _ => rfl⟩, hg_off, fun e he => ?_⟩
    show quoFlow B gVal e ≠ 0
    rw [show quoFlow B gVal e = quoFlow B f.val e by simp [quoFlow, hg_on e he]]
    exact hHgood e he
  · -- Case 2: Splice with a short simple path J in H of length ≤ 2
    obtain ⟨verts, edges, hlen, hnd, hvH, heH, hhead, hlast, hstep, h2le⟩ :=
      exists_short_path_in_cycle G H hcyc.1 p p' hpH hp'H hne
    have hJlen_le2 : edges.length ≤ 2 := by have := hcyc.2.1; omega
    obtain ⟨C, hCsign, hConH⟩ := hsplice verts edges hlen hnd hvH heH hhead hlast hstep
    by_cases hqlam : QuotientAddGroup.mk (s := B) lam = 0
    · -- lam ∈ B: direct move g = f + lam • χ_C preserves quoFlow everywhere!
      have hlamB : lam ∈ B := (QuotientAddGroup.eq_zero_iff lam).mp hqlam
      let gVal : E → Γ := fun e => f.val e + C.sign e • lam
      have hg_flow : G.IsFlow gVal := isFlow_add f.isFlow (isFlow_zsmul C.isFlow lam)
      have hg_off : ∀ e : {e : E // e ∉ H.edges}, gVal e.1 = gstar.val e := fun e => by
        dsimp only [gVal]; rw [hCsign e.1 e.2, hgstar e]
      have hg_quo : ∀ e, quoFlow B gVal e = quoFlow B f.val e :=
        fun e => sec4_E2_proved G B f.val C lam hlamB e
      have hg_nz : Multigraph.IsNowhereZero gVal := fun e => by
        by_cases he : e ∈ H.edges
        · exact (sec4_E1_proved (V := V) B gVal e).mpr (Or.inl (by rw [hg_quo e]; exact hHgood e he))
        · rw [hg_off ⟨e, he⟩]; exact gstar.nonzero ⟨e, he⟩
      let g : G.NZFlow Γ := ⟨gVal, hg_flow, hg_nz⟩
      exact ⟨g, Relation.ReflTransGen.single ⟨C, lam, hlam, fun _ => rfl⟩, hg_off,
        fun e he => by rw [hg_quo e]; exact hHgood e he⟩
    · -- QuotientAddGroup.mk lam ≠ 0: first shift along directed cycle DH of H
      have hHne_e : H.edges.Nonempty := by
        obtain ⟨v, hv⟩ := hcyc.1.1.1
        have hd := hcyc.1.2 v hv
        by_contra hempty
        rw [Finset.not_nonempty_iff_eq_empty] at hempty
        simp [Multigraph.Subgraph.deg, hempty] at hd
      obtain ⟨DH, hDHle⟩ := exists_directedCycle_of_no_deg_one H hHne_e
        (fun v hv => by rw [hcyc.1.2 v hv]; decide)
      have hDHeq : DH.sub = H := by
        -- Same uniqueness as SmallClaims: cycle ≤ cycle implies equality
        have hverts : DH.sub.verts = H.verts := by
          apply Finset.Subset.antisymm hDHle.1
          intro w hw
          obtain ⟨v₀, hv₀⟩ := DH.isCycle.1.1
          have hpath := hcyc.1.1.2 v₀ (hDHle.1 hv₀) w hw
          clear hw
          induction hpath with
          | refl => exact hv₀
          | @tail u z _ hstep' ih =>
            rcases hstep' with ⟨e, heH', ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
            · have hdeg : DH.sub.deg u = H.deg u := by rw [DH.isCycle.2 u ih, hcyc.1.2 u (hDHle.1 ih)]
              have ht_sub := Finset.filter_subset_filter (fun e => G.tail e = u) hDHle.2
              have hh_sub := Finset.filter_subset_filter (fun e => G.head e = u) hDHle.2
              have ht_le := Finset.card_le_card ht_sub
              have hh_le := Finset.card_le_card hh_sub
              unfold Multigraph.Subgraph.deg at hdeg
              have ht_eq := Finset.eq_of_subset_of_card_le ht_sub (by omega)
              have heD : e ∈ DH.sub.edges := (Finset.mem_filter.mp (ht_eq.symm ▸ Finset.mem_filter.mpr ⟨heH', h1⟩)).1
              simpa [h2] using DH.sub.head_mem heD
            · have hdeg : DH.sub.deg u = H.deg u := by rw [DH.isCycle.2 u ih, hcyc.1.2 u (hDHle.1 ih)]
              have ht_sub := Finset.filter_subset_filter (fun e => G.tail e = u) hDHle.2
              have hh_sub := Finset.filter_subset_filter (fun e => G.head e = u) hDHle.2
              have ht_le := Finset.card_le_card ht_sub
              have hh_le := Finset.card_le_card hh_sub
              unfold Multigraph.Subgraph.deg at hdeg
              have hh_eq := Finset.eq_of_subset_of_card_le hh_sub (by omega)
              have heD : e ∈ DH.sub.edges := (Finset.mem_filter.mp (hh_eq.symm ▸ Finset.mem_filter.mpr ⟨heH', h2⟩)).1
              simpa [h1] using DH.sub.tail_mem heD
        have hedges : DH.sub.edges = H.edges := by
          apply Finset.Subset.antisymm hDHle.2
          intro e heH'
          have huH := H.tail_mem heH'
          have huD : G.tail e ∈ DH.sub.verts := hverts ▸ huH
          have hdeg : DH.sub.deg (G.tail e) = H.deg (G.tail e) := by rw [DH.isCycle.2 _ huD, hcyc.1.2 _ huH]
          have ht_sub := Finset.filter_subset_filter (fun e' => G.tail e' = G.tail e) hDHle.2
          have hh_sub := Finset.filter_subset_filter (fun e' => G.head e' = G.tail e) hDHle.2
          have ht_le := Finset.card_le_card ht_sub
          have hh_le := Finset.card_le_card hh_sub
          unfold Multigraph.Subgraph.deg at hdeg
          have ht_eq := Finset.eq_of_subset_of_card_le ht_sub (by omega)
          have hmem : e ∈ H.edges.filter (fun e' => G.tail e' = G.tail e) := Finset.mem_filter.mpr ⟨heH', rfl⟩
          rw [← ht_eq] at hmem
          exact (Finset.mem_filter.mp hmem).1
        ext x
        · simp [hverts]
        · simp [hedges]
      let X : Finset (Γ ⧸ B) :=
        H.edges.image (fun e => DH.sign e • (-quoFlow B f.val e))
      let X' : Finset (Γ ⧸ B) :=
        edges.toFinset.image (fun e => DH.sign e • (-(quoFlow B f.val e + C.sign e • QuotientAddGroup.mk lam)))
      have hX_le : X.card ≤ 5 := Finset.card_image_le.trans hcyc.2.1
      have hX'_le : X'.card ≤ 2 := Finset.card_image_le.trans ((List.toFinset_card_le _).trans hJlen_le2)
      have hXX'_lt : (X ∪ X').card < Fintype.card (Γ ⧸ B) :=
        (Finset.card_union_le _ _).trans_lt (by omega)
      have hex_c : (Finset.univ \ (X ∪ X')).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro he
        have hsub : (Finset.univ : Finset (Γ ⧸ B)) ⊆ X ∪ X' := Finset.sdiff_eq_empty_iff_subset.mp he
        have := Finset.card_le_card hsub; rw [Finset.card_univ] at this; omega
      obtain ⟨c, hc⟩ := hex_c
      rw [Finset.mem_sdiff, Finset.mem_union, not_or] at hc
      have hcX : c ∉ X := hc.2.1
      have hcX' : c ∉ X' := hc.2.2
      have h0X : (0 : Γ ⧸ B) ∉ X := by
        intro h0
        rw [Finset.mem_image] at h0
        rcases h0 with ⟨e, heH', heq⟩
        have hsm := DH.sign_mem (hDHeq ▸ heH')
        have : -quoFlow B f.val e = 0 := by rcases hsm with hs | hs <;> simp_all
        exact hHgood e heH' (neg_eq_zero.mp this)
      have hnotX_nz : ∀ (u : Γ ⧸ B), u ∉ X → ∀ e ∈ H.edges, quoFlow B f.val e + DH.sign e • u ≠ 0 := by
        intro u hu e heH' h0
        apply hu
        rw [Finset.mem_image]
        refine ⟨e, heH', ?_⟩
        have hsm := DH.sign_mem (hDHeq ▸ heH')
        have h1 : DH.sign e • u = -quoFlow B f.val e := eq_neg_of_add_eq_zero_right h0
        rw [← h1]
        rcases hsm with hs | hs <;> simp [hs]
      obtain ⟨_, _, hrtg⟩ := hR1 X (by omega) 0 c h0X hcX
      -- Walk along DH in (Γ ⧸ B) \ X from 0 to c
      have hwalk_DH : ∀ u : Γ ⧸ B,
          Relation.ReflTransGen (fun a b => a ∈ {x : Γ ⧸ B | x ∉ X} ∧ b ∈ {x : Γ ⧸ B | x ∉ X} ∧
            ∃ σ ∈ Sig.sigA B, b = a + σ) 0 u →
          ∃ f' : G.NZFlow Γ,
            G.SigmaJoined Sig.carrier f f' ∧
            (∀ e, e ∉ H.edges → f'.val e = f.val e) ∧
            (∀ e, quoFlow B f'.val e = quoFlow B f.val e + DH.sign e • u) := by
        intro u hu
        induction hu with
        | refl => exact ⟨f, .refl, fun _ _ => rfl, fun e => by simp⟩
        | @tail a b _ hstep' ih =>
          obtain ⟨fa, hjoin_a, hout_a, hquo_a⟩ := ih
          rcases hstep' with ⟨_, hbX, σ, ⟨_, z, hzSig, hzQuo⟩, rfl⟩
          let fbVal : E → Γ := fun e => fa.val e + DH.sign e • z
          have hfb_flow : G.IsFlow fbVal := isFlow_add fa.isFlow (isFlow_zsmul DH.isFlow z)
          have hfb_quo : ∀ e, quoFlow B fbVal e = quoFlow B f.val e + DH.sign e • (a + σ) := by
            intro e
            unfold quoFlow
            change (QuotientAddGroup.mk' B) (fa.val e + DH.sign e • z) = _
            rw [map_add, map_zsmul]
            have h1 : (QuotientAddGroup.mk' B) (fa.val e) = quoFlow B f.val e + DH.sign e • a := hquo_a e
            have h2 : (QuotientAddGroup.mk' B) z = σ := hzQuo
            rw [h1, h2, smul_add, add_assoc]; rfl
          have hfb_out : ∀ e, e ∉ H.edges → fbVal e = f.val e := fun e he => by
            have hnotD : e ∉ DH.sub.edges := by rw [hDHeq]; exact he
            dsimp only [fbVal]; rw [DH.sign_zero hnotD, zero_zsmul, add_zero, hout_a e he]
          have hfb_nz : Multigraph.IsNowhereZero fbVal := fun e => by
            by_cases he : e ∈ H.edges
            · exact (sec4_E1_proved (V := V) B fbVal e).mpr (Or.inl (by rw [hfb_quo e]; exact hnotX_nz (a + σ) hbX e he))
            · rw [hfb_out e he]; exact f.nonzero e
          let fb : G.NZFlow Γ := ⟨fbVal, hfb_flow, hfb_nz⟩
          exact ⟨fb, hjoin_a.tail ⟨DH, z, hzSig, fun _ => rfl⟩, hfb_out, hfb_quo⟩
      obtain ⟨f', hjoin_f', hout_f', hquo_f'⟩ := hwalk_DH c hrtg
      -- Final move g = f' + lam • χ_C
      let gVal : E → Γ := fun e => f'.val e + C.sign e • lam
      have hg_flow : G.IsFlow gVal := isFlow_add f'.isFlow (isFlow_zsmul C.isFlow lam)
      have hg_off : ∀ e : {e : E // e ∉ H.edges}, gVal e.1 = gstar.val e := fun e => by
        dsimp only [gVal]; rw [hout_f' e.1 e.2, hCsign e.1 e.2, hgstar e]
      have hg_quo_on : ∀ e ∈ H.edges, quoFlow B gVal e ≠ 0 := by
        intro e heH'
        have hqe : quoFlow B gVal e =
            quoFlow B f.val e + DH.sign e • c + C.sign e • QuotientAddGroup.mk lam := by
          unfold quoFlow
          change (QuotientAddGroup.mk' B) (f'.val e + C.sign e • lam) = _
          rw [map_add, map_zsmul]
          have h1 : (QuotientAddGroup.mk' B) (f'.val e) = quoFlow B f.val e + DH.sign e • c := hquo_f' e
          rw [h1]; rfl
        rw [hqe]
        by_cases heJ : e ∈ edges
        · intro h0
          apply hcX'
          rw [Finset.mem_image]
          refine ⟨e, List.mem_toFinset.mpr heJ, ?_⟩
          have hsm := DH.sign_mem (hDHeq ▸ heH')
          have h1 : DH.sign e • c = -(quoFlow B f.val e + C.sign e • QuotientAddGroup.mk lam) := by
            apply eq_neg_of_add_eq_zero_left
            have : quoFlow B f.val e + DH.sign e • c + C.sign e • QuotientAddGroup.mk lam =
                DH.sign e • c + (quoFlow B f.val e + C.sign e • QuotientAddGroup.mk lam) := by abel
            rw [← this]; exact h0
          rw [← h1]
          rcases hsm with hs | hs <;> simp [hs]
        · have hnotC : e ∉ C.sub.edges := fun h => heJ ((hConH e heH').mp h)
          rw [C.sign_zero hnotC, zero_zsmul, add_zero]
          exact hnotX_nz c hcX e heH'
      have hg_nz : Multigraph.IsNowhereZero gVal := fun e => by
        by_cases he : e ∈ H.edges
        · exact (sec4_E1_proved (V := V) B gVal e).mpr (Or.inl (hg_quo_on e he))
        · rw [hg_off ⟨e, he⟩]; exact gstar.nonzero ⟨e, he⟩
      let g : G.NZFlow Γ := ⟨gVal, hg_flow, hg_nz⟩
      exact ⟨g, hjoin_f'.tail ⟨C, lam, hlam, fun _ => rfl⟩, hg_off, hg_quo_on⟩

end Flow.Proofs
