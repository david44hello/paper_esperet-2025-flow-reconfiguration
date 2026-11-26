-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Flow.Defs.Frames
import Flow.Proofs.Blocks

/-!
# Section 3 (Part 3): Flows on `H`, `H₀`, and `Q` (Lemma 3.6(a)–(d))

This module proves Lemma 3.6(a)–(d) (`lem_3_6_a`, `lem_3_6_b`, `lem_3_6_c`, `lem_3_6_d`)
for any abelian group `A` (finite or infinite, including `ℤ`), together with a general
spanning-tree boundary solver (`exists_edge_map_with_boundary`) and directed-cycle lifting
from a subgraph (`liftDirectedCycle`).
-/

namespace Flow.Proofs

open Flow Multigraph

section TreeBoundarySolver

variable {V E A : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] [AddCommGroup A]

/-- On any finite connected multigraph `M`, every vertex-valued function `ν : V → A`
with `∑ v, ν v = 0` is the boundary `M.boundary z` of some `z : E → A`. -/
lemma exists_edge_map_with_boundary :
    ∀ (N : ℕ) (V E : Type) [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
      (M : Multigraph V E) (hconn : M.Connected) (hcard : Fintype.card V ≤ N)
      (ν : V → A) (hsum : ∑ v : V, ν v = 0),
      ∃ z : E → A, ∀ v : V, M.boundary z v = ν v := by
  intro N
  induction N with
  | zero =>
    intro V E _ _ _ _ M _ hcard ν _
    refine ⟨0, fun v => ?_⟩
    have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
    omega
  | succ N ih =>
    intro V E _ _ _ _ M hconn hcard ν hsum
    by_cases h1 : Fintype.card V ≤ 1
    · -- At most 1 vertex: `ν v = ∑ w, ν w = 0`, so `z = 0` works!
      refine ⟨0, fun v => ?_⟩
      rw [boundary_zero]
      have huniv : (Finset.univ : Finset V) = {v} := by
        symm; exact Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by simp; omega)
      rw [huniv, Finset.sum_singleton] at hsum
      exact hsum.symm
    · -- `2 ≤ Fintype.card V`: pick a spanning forest `T` of `M`; it is a spanning tree with a leaf `v₀`!
      obtain ⟨T, hTv, hTf, hTreach⟩ := exists_spanningForest M
      have hTconn : T.Connected := by
        have hVne : (Finset.univ : Finset V).Nonempty :=
          Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp (by omega))
        refine ⟨hTv.symm ▸ hVne, fun u _ v _ => hTreach u v (hconn u v)⟩
      have hTedges_ne : T.edges.Nonempty := by
        have hle := connected_verts_le_edges_succ T hTconn
        rw [hTv, Finset.card_univ] at hle
        exact Finset.card_pos.mp (by omega)
      obtain ⟨v₀, _, hdeg1⟩ := exists_leaf_of_forest hTf hTedges_ne
      -- Find the unique edge `e₀ ∈ T.edges` incident to `v₀`
      have hex_e0 : ∃ e₀ ∈ T.edges, M.tail e₀ = v₀ ∨ M.head e₀ = v₀ := by
        unfold Subgraph.deg at hdeg1
        by_cases ht : 0 < (T.edges.filter (fun e => M.tail e = v₀)).card
        · rcases Finset.card_pos.mp ht with ⟨e, he⟩
          exact ⟨e, (Finset.mem_filter.mp he).1, Or.inl (Finset.mem_filter.mp he).2⟩
        · have hh : 0 < (T.edges.filter (fun e => M.head e = v₀)).card := by omega
          rcases Finset.card_pos.mp hh with ⟨e, he⟩
          exact ⟨e, (Finset.mem_filter.mp he).1, Or.inr (Finset.mem_filter.mp he).2⟩
      rcases hex_e0 with ⟨e₀, he₀T, he₀_inc⟩
      have he₀_noloop : M.tail e₀ ≠ M.head e₀ := isForest_no_loop hTf e₀ he₀T
      -- Every other edge of `T` avoids `v₀`
      have he₀_unique : ∀ e ∈ T.edges, (M.tail e = v₀ ∨ M.head e = v₀) → e = e₀ := by
        intro e heT hinc
        by_contra hne
        have hdisj : Disjoint (T.edges.filter (fun e => M.tail e = v₀))
            (T.edges.filter (fun e => M.head e = v₀)) := by
          rw [Finset.disjoint_left]; intro e' ht hh
          exact isForest_no_loop hTf e' (Finset.mem_filter.mp ht).1
            ((Finset.mem_filter.mp ht).2.trans (Finset.mem_filter.mp hh).2.symm)
        have hsub : ({e, e₀} : Finset E) ⊆
            T.edges.filter (fun e => M.tail e = v₀) ∪ T.edges.filter (fun e => M.head e = v₀) := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · rcases hinc with ht | hh
            · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨heT, ht⟩)
            · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨heT, hh⟩)
          · rcases he₀_inc with ht | hh
            · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨he₀T, ht⟩)
            · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨he₀T, hh⟩)
        have h2 : 2 ≤ T.deg v₀ := by
          unfold Subgraph.deg
          rw [← Finset.card_union_of_disjoint hdisj]
          exact le_trans (by rw [Finset.card_pair hne]) (Finset.card_le_card hsub)
        omega
      -- Let `w₀` be the other endpoint of `e₀` (`w₀ ≠ v₀`)
      let w₀ : V := if M.tail e₀ = v₀ then M.head e₀ else M.tail e₀
      have hw₀_ne : w₀ ≠ v₀ := by
        dsimp only [w₀]; split_ifs with ht
        · exact fun hh => he₀_noloop (ht.trans hh.symm)
        · exact fun ht' => ht ht'
      -- Look at `T' = (T.deleteVertex v₀).toMultigraph` on `{v // v ≠ v₀}`: it is connected!
      let M' := M.deleteVertex v₀
      have hM'_conn : M'.Connected := by
        intro ⟨a, ha⟩ ⟨b, hb⟩
        obtain ⟨verts, edges, hlen, hv_nodup, hhead, hlast, hedgesT, hstep⟩ :=
          exists_simplePath_of_reflTransGen (hTconn.2 a (by simp [hTv]) b (by simp [hTv]))
        -- A simple path in `T` between `a ≠ v₀` and `b ≠ v₀` CANNOT pass through leaf `v₀`!
        have hv₀_not_in : v₀ ∉ verts := by
          intro hmem
          obtain ⟨i, hi, hvi⟩ := List.getElem_of_mem hmem
          have hi_ne0 : i ≠ 0 := fun h0 => by
            subst h0
            cases verts with
            | nil => simp at hi
            | cons x _ =>
              simp only [List.head?_cons, Option.some.injEq] at hhead
              exact ha (hhead.symm.trans hvi)
          have hi_nelast : i ≠ edges.length := fun hlast_i => by
            rw [List.getLast?_eq_getElem?] at hlast
            have hidx : verts.length - 1 = edges.length := by omega
            rw [hidx, List.getElem?_eq_getElem (by omega)] at hlast
            exact hb ((Option.some.inj hlast).symm.trans (hlast_i ▸ hvi))
          -- Both `edges[i - 1]` and `edges[i]` are in `T.edges`, distinct (simple path!), and hit `v₀`!
          have he_nodup := simplePath_edges_nodup hv_nodup hlen hstep
          have he1T : edges[i - 1]'(by omega) ∈ T.edges := hedgesT _ (List.getElem_mem _)
          have he2T : edges[i]'(by omega) ∈ T.edges := hedgesT _ (List.getElem_mem _)
          have h1inc : M.tail (edges[i - 1]'(by omega)) = v₀ ∨ M.head (edges[i - 1]'(by omega)) = v₀ := by
            have hs := hstep (i - 1) (by omega)
            have hi1 : i - 1 + 1 = i := by omega
            simp only [hi1, hvi] at hs
            rcases hs with ⟨_, hh⟩ | ⟨ht, _⟩ <;> [exact Or.inr hh; exact Or.inl ht]
          have h2inc : M.tail (edges[i]'(by omega)) = v₀ ∨ M.head (edges[i]'(by omega)) = v₀ := by
            have hs := hstep i (by omega)
            simp only [hvi] at hs
            rcases hs with ⟨ht, _⟩ | ⟨_, hh⟩ <;> [exact Or.inl ht; exact Or.inr hh]
          have heq12 : edges[i - 1]'(by omega) = edges[i]'(by omega) :=
            (he₀_unique _ he1T h1inc).trans (he₀_unique _ he2T h2inc).symm
          have := (List.Nodup.getElem_inj_iff he_nodup).mp heq12
          omega
        -- Lift the simple path to `M'`!
        have hlift_k : ∀ (k : ℕ) (hk : k < verts.length),
            Relation.ReflTransGen M'.Adj ⟨a, ha⟩ ⟨verts[k]'hk, fun h => hv₀_not_in (h ▸ List.getElem_mem hk)⟩ := by
          intro k
          induction k with
          | zero =>
            intro hk
            have hv0 : verts[0]'hk = a := by
              cases verts with
              | nil => simp at hk
              | cons x _ => simpa using hhead
            have : (⟨verts[0]'hk, fun h => hv₀_not_in (h ▸ List.getElem_mem hk)⟩ : {v // v ≠ v₀}) = ⟨a, ha⟩ :=
              Subtype.ext hv0
            rw [this]
          | succ k ihk =>
            intro hk
            refine Relation.ReflTransGen.tail (ihk (by omega)) ?_
            have hs := hstep k (by omega)
            have htne : M.tail (edges[k]'(by omega)) ≠ v₀ := fun h => by
              rcases hs with ⟨ht, _⟩ | ⟨ht, _⟩ <;> exact hv₀_not_in (h ▸ ht ▸ List.getElem_mem _)
            have hhne : M.head (edges[k]'(by omega)) ≠ v₀ := fun h => by
              rcases hs with ⟨_, hh⟩ | ⟨_, hh⟩ <;> exact hv₀_not_in (h ▸ hh ▸ List.getElem_mem _)
            refine ⟨⟨edges[k]'(by omega), htne, hhne⟩, ?_⟩
            rcases hs with ⟨ht, hh⟩ | ⟨ht, hh⟩
            · left; exact ⟨Subtype.ext ht, Subtype.ext hh⟩
            · right; exact ⟨Subtype.ext ht, Subtype.ext hh⟩
        have hlast_eq : verts[edges.length]'(by omega) = b := by
          rw [List.getLast?_eq_getElem?] at hlast
          have hidx : verts.length - 1 = edges.length := by omega
          rw [hidx, List.getElem?_eq_getElem (by omega)] at hlast
          exact Option.some.inj hlast
        have hres := hlift_k edges.length (by omega)
        have : (⟨verts[edges.length]'(by omega), fun h => hv₀_not_in (h ▸ List.getElem_mem _)⟩ : {v // v ≠ v₀}) = ⟨b, hb⟩ :=
          Subtype.ext hlast_eq
        simpa only [this] using hres
      -- Build reduced target `ν'` on `{v // v ≠ v₀}`: add `ν v₀` to `w₀`!
      let ν' : {v : V // v ≠ v₀} → A := fun v => if v.1 = w₀ then ν v.1 + ν v₀ else ν v.1
      have hcard' : Fintype.card {v : V // v ≠ v₀} ≤ N := by
        rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]; omega
      have hsum' : ∑ v : {v : V // v ≠ v₀}, ν' v = 0 := by
        have h1 : ∑ v : {v : V // v ≠ v₀}, ν' v =
            (∑ v : {v : V // v ≠ v₀}, ν v.1) + ν v₀ := by
          have hsplit : ∀ v : {v : V // v ≠ v₀}, ν' v = ν v.1 + (if v = ⟨w₀, hw₀_ne⟩ then ν v₀ else 0) := by
            intro ⟨v, hv⟩; dsimp only [ν']; by_cases h : v = w₀ <;> simp [h]
          simp_rw [hsplit, Finset.sum_add_distrib]
          simp
        rw [h1]
        have h2 : (∑ v : {v : V // v ≠ v₀}, ν v.1) + ν v₀ = ∑ v : V, ν v := by
          rw [← Finset.add_sum_erase Finset.univ ν (Finset.mem_univ v₀), add_comm]
          congr 1
          refine Finset.sum_bij (fun (x : {v : V // v ≠ v₀}) _ => x.1)
            (fun x _ => Finset.mem_erase.mpr ⟨x.2, Finset.mem_univ _⟩)
            (fun _ _ _ _ h => Subtype.ext h)
            (fun b hb => ⟨⟨b, (Finset.mem_erase.mp hb).1⟩, Finset.mem_univ _, rfl⟩)
            (fun _ _ => rfl)
        rw [h2, hsum]
      obtain ⟨z', hz'⟩ := ih {v : V // v ≠ v₀} {e : E // M.tail e ≠ v₀ ∧ M.head e ≠ v₀}
        M' hM'_conn hcard' ν' hsum'
      -- Extend `z'` to `z : E → A` by setting `z e₀` to match `ν v₀` and `0` on any other edge meeting `v₀`
      let val0 : A := if M.head e₀ = v₀ then ν v₀ else -ν v₀
      let z : E → A := fun e =>
        if h : M.tail e ≠ v₀ ∧ M.head e ≠ v₀ then z' ⟨e, h⟩
        else if e = e₀ then val0 else 0
      refine ⟨z, fun v => ?_⟩
      by_cases hv : v = v₀
      · subst v
        rw [boundary_eq_sum_ite]
        rw [Finset.sum_eq_single e₀]
        · have hnot : ¬ (M.tail e₀ ≠ v₀ ∧ M.head e₀ ≠ v₀) := by
            rcases he₀_inc with ht | hh
            · simp [ht]
            · simp [hh]
          simp only [z, hnot, ↓reduceDIte, ↓reduceIte]
          rcases he₀_inc with ht | hh
          · have hne : M.head e₀ ≠ v₀ := fun h => he₀_noloop (ht.trans h.symm)
            simp [val0, ht, hne]
          · have hne : M.tail e₀ ≠ v₀ := fun h => he₀_noloop (h.trans hh.symm)
            simp [val0, hh, hne]
        · intro e _ hne_e0
          by_cases hgood : M.tail e ≠ v₀ ∧ M.head e ≠ v₀
          · simp [hgood.1, hgood.2]
          · simp [z, hgood, hne_e0]
        · intro hnot; exact absurd (Finset.mem_univ e₀) hnot
      · -- `v ≠ v₀`: `M.boundary z v = M'.boundary z' ⟨v, hv⟩ + contribution of e₀`
        have hbd_split : M.boundary z v =
            M'.boundary z' ⟨v, hv⟩ +
            ((if M.head e₀ = v then val0 else 0) - (if M.tail e₀ = v then val0 else 0)) := by
          rw [boundary_eq_sum_ite, boundary_eq_sum_ite]
          have hsub_sum : ∑ e : {e : E // M.tail e ≠ v₀ ∧ M.head e ≠ v₀},
              ((if M'.head e = ⟨v, hv⟩ then z' e else 0) - (if M'.tail e = ⟨v, hv⟩ then z' e else 0)) =
              ∑ e ∈ Finset.univ.filter (fun e : E => M.tail e ≠ v₀ ∧ M.head e ≠ v₀),
              ((if M.head e = v then z e else 0) - (if M.tail e = v then z e else 0)) := by
            refine Finset.sum_bij (fun e _ => e.1)
              (fun e _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, e.2⟩)
              (fun _ _ _ _ h => Subtype.ext h)
              (fun e he => ⟨⟨e, (Finset.mem_filter.mp he).2⟩, Finset.mem_univ _, rfl⟩)
              (fun e _ => by
                have he2 := e.2
                simp only [z, dif_pos he2, Subtype.coe_eta, M', Multigraph.deleteVertex, Subtype.mk.injEq])
          rw [hsub_sum]
          have hcompl : (∑ e : E, ((if M.head e = v then z e else 0) - (if M.tail e = v then z e else 0))) =
              (∑ e ∈ Finset.univ.filter (fun e : E => M.tail e ≠ v₀ ∧ M.head e ≠ v₀),
                ((if M.head e = v then z e else 0) - (if M.tail e = v then z e else 0))) +
              (∑ e ∈ Finset.univ.filter (fun e : E => ¬ (M.tail e ≠ v₀ ∧ M.head e ≠ v₀)),
                ((if M.head e = v then z e else 0) - (if M.tail e = v then z e else 0))) := by
            exact (Finset.sum_filter_add_sum_filter_not Finset.univ _ _).symm
          rw [hcompl]
          congr 1
          have he₀_bad : ¬ (M.tail e₀ ≠ v₀ ∧ M.head e₀ ≠ v₀) := by
            rcases he₀_inc with ht | hh
            · simp [ht]
            · simp [hh]
          rw [Finset.sum_eq_single e₀]
          · simp only [z, he₀_bad, ↓reduceDIte, ↓reduceIte]
          · intro e he hne_e0
            have hbad := (Finset.mem_filter.mp he).2
            simp [z, hbad, hne_e0]
          · intro hnot
            exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ e₀, he₀_bad⟩) hnot
        rw [hbd_split, hz' ⟨v, hv⟩]
        dsimp only [ν']
        by_cases hvw : v = w₀
        · subst v
          simp only [↓reduceIte]
          rcases he₀_inc with ht | hh
          · have hne : M.head e₀ ≠ v₀ := fun h => he₀_noloop (ht.trans h.symm)
            have hval : val0 = -ν v₀ := by simp [val0, hne]
            have hw_eq : w₀ = M.head e₀ := by simp [w₀, ht]
            have ht_ne : M.tail e₀ ≠ w₀ := ht.symm ▸ hw₀_ne.symm
            rw [hval]
            simp only [← hw_eq, ↓reduceIte, ht_ne, sub_zero]
            abel
          · have hne : M.tail e₀ ≠ v₀ := fun h => he₀_noloop (h.trans hh.symm)
            have hval : val0 = ν v₀ := by simp [val0, hh]
            have hw_eq : w₀ = M.tail e₀ := by simp [w₀, hne]
            have hh_ne : M.head e₀ ≠ w₀ := hh.symm ▸ hw₀_ne.symm
            rw [hval]
            simp only [← hw_eq, ↓reduceIte, hh_ne, zero_sub]
            abel
        · simp only [hvw, ↓reduceIte]
          have ht_ne : M.tail e₀ ≠ v := by
            rcases he₀_inc with ht | hh
            · exact ht.symm ▸ fun h => hv h.symm
            · have htne : M.tail e₀ ≠ v₀ := fun ht => he₀_noloop (ht.trans hh.symm)
              have : w₀ = M.tail e₀ := by simp [w₀, htne]
              exact this ▸ fun h => hvw h.symm
          have hh_ne : M.head e₀ ≠ v := by
            rcases he₀_inc with ht | hh
            · have : w₀ = M.head e₀ := by simp [w₀, ht]
              exact this ▸ fun h => hvw h.symm
            · exact hh.symm ▸ fun h => hv h.symm
          simp [ht_ne, hh_ne]

end TreeBoundarySolver

section Lemma36

variable {V E A : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] [AddCommGroup A]

/-- Lift a directed cycle of `H.toMultigraph` to a directed cycle of `G` with `C.sub ≤ H`. -/
def liftDirectedCycle {G : Multigraph V E} (H : G.Subgraph)
    (O : H.toMultigraph.DirectedCycle) : G.DirectedCycle where
  sub :=
    { verts := O.sub.verts.image Subtype.val
      edges := O.sub.edges.image Subtype.val
      tail_mem := fun {e} he => by
        rcases Finset.mem_image.mp he with ⟨e', he', rfl⟩
        exact Finset.mem_image.mpr ⟨H.toMultigraph.tail e', O.sub.tail_mem he', rfl⟩
      head_mem := fun {e} he => by
        rcases Finset.mem_image.mp he with ⟨e', he', rfl⟩
        exact Finset.mem_image.mpr ⟨H.toMultigraph.head e', O.sub.head_mem he', rfl⟩ }
  isCycle := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rcases O.isCycle.1.1 with ⟨v, hv⟩
      exact ⟨v.1, Finset.mem_image.mpr ⟨v, hv, rfl⟩⟩
    · intro u hu v hv
      rcases Finset.mem_image.mp hu with ⟨u', hu', rfl⟩
      rcases Finset.mem_image.mp hv with ⟨v', hv', rfl⟩
      have hwalk := O.isCycle.1.2 u' hu' v' hv'
      clear hu' hv' hu hv
      induction hwalk with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ hstep ih =>
        rcases hstep with ⟨e', he', hadj⟩
        refine Relation.ReflTransGen.tail ih ⟨e'.1, Finset.mem_image.mpr ⟨e', he', rfl⟩, ?_⟩
        rcases hadj with ⟨ht, hh⟩ | ⟨ht, hh⟩
        · left; exact ⟨congrArg Subtype.val ht, congrArg Subtype.val hh⟩
        · right; exact ⟨congrArg Subtype.val ht, congrArg Subtype.val hh⟩
    · intro v hv
      rcases Finset.mem_image.mp hv with ⟨v', hv', rfl⟩
      have hdeg := O.isCycle.2 v' hv'
      unfold Subgraph.deg at hdeg ⊢
      have ht : (O.sub.edges.image Subtype.val).filter (fun e => G.tail e = v'.1) =
          (O.sub.edges.filter (fun e => H.toMultigraph.tail e = v')).image Subtype.val := by
        ext e; simp only [Finset.mem_filter, Finset.mem_image]
        constructor
        · rintro ⟨⟨e', he', rfl⟩, ht⟩; exact ⟨e', ⟨he', Subtype.ext ht⟩, rfl⟩
        · rintro ⟨e', ⟨he', ht⟩, rfl⟩; exact ⟨⟨e', he', rfl⟩, congrArg Subtype.val ht⟩
      have hh : (O.sub.edges.image Subtype.val).filter (fun e => G.head e = v'.1) =
          (O.sub.edges.filter (fun e => H.toMultigraph.head e = v')).image Subtype.val := by
        ext e; simp only [Finset.mem_filter, Finset.mem_image]
        constructor
        · rintro ⟨⟨e', he', rfl⟩, hh⟩; exact ⟨e', ⟨he', Subtype.ext hh⟩, rfl⟩
        · rintro ⟨e', ⟨he', hh⟩, rfl⟩; exact ⟨⟨e', he', rfl⟩, congrArg Subtype.val hh⟩
      rw [ht, hh, Finset.card_image_of_injective _ Subtype.val_injective,
          Finset.card_image_of_injective _ Subtype.val_injective]
      exact hdeg
  sign := fun e => if h : e ∈ H.edges then O.sign ⟨e, h⟩ else 0
  sign_mem := fun {e} he => by
    rcases Finset.mem_image.mp he with ⟨e', he', rfl⟩
    simp only [e'.2, ↓reduceDIte]
    exact O.sign_mem he'
  sign_zero := fun {e} he => by
    by_cases hH : e ∈ H.edges
    · simp only [hH, ↓reduceDIte]
      apply O.sign_zero
      intro hm; exact he (Finset.mem_image.mpr ⟨⟨e, hH⟩, hm, rfl⟩)
    · simp [hH]
  isFlow := fun v => by
    by_cases hv : v ∈ H.verts
    · have hO := O.isFlow ⟨v, hv⟩
      rw [boundary_eq_sum_ite] at hO ⊢
      have hsum : ∑ e : E, ((if G.head e = v then (if h : e ∈ H.edges then O.sign ⟨e, h⟩ else 0) else 0) -
          (if G.tail e = v then (if h : e ∈ H.edges then O.sign ⟨e, h⟩ else 0) else 0)) =
          ∑ e : {e : E // e ∈ H.edges},
            ((if H.toMultigraph.head e = ⟨v, hv⟩ then O.sign e else 0) -
             (if H.toMultigraph.tail e = ⟨v, hv⟩ then O.sign e else 0)) := by
        rw [← Finset.sum_subset (Finset.subset_univ H.edges)]
        · refine Finset.sum_bij (fun e he => ⟨e, he⟩) (fun _ _ => Finset.mem_univ _)
            (fun _ _ _ _ h => congrArg Subtype.val h)
            (fun e _ => ⟨e.1, e.2, rfl⟩)
            (fun e he => by simp [he, Subgraph.toMultigraph, Subtype.mk.injEq])
        · intro e _ hnot; simp [hnot]
      rw [hsum, hO]
    · rw [boundary_eq_sum_ite]
      refine Finset.sum_eq_zero (fun e _ => ?_)
      by_cases he : e ∈ H.edges
      · have ht : G.tail e ≠ v := fun h => hv (h ▸ H.tail_mem he)
        have hh : G.head e ≠ v := fun h => hv (h ▸ H.head_mem he)
        simp [ht, hh]
      · simp [he]

lemma liftDirectedCycle_le {G : Multigraph V E} (H : G.Subgraph)
    (O : H.toMultigraph.DirectedCycle) : (liftDirectedCycle H O).sub ≤ H := by
  constructor
  · intro v hv; dsimp only [liftDirectedCycle] at hv
    rcases Finset.mem_image.mp hv with ⟨v', _, rfl⟩; exact v'.2
  · intro e he; dsimp only [liftDirectedCycle] at he
    rcases Finset.mem_image.mp he with ⟨e', _, rfl⟩; exact e'.2

/-- Helper: on a thread `sub.thread t` aligned with `G` (`aux.thread_aligned`), the `i`-th edge
and `i+1`-th edge are the ONLY two edges of `H` incident to interior vertex `verts[i+1]`. -/
private lemma thread_interior_edges {G : Multigraph V E} {H : G.Subgraph}
    (sub : SubdivisionData G H) (aux : AuxGraphData G H sub)
    (t : sub.E₀) (i : ℕ) (hi : i + 1 < (sub.thread t).edges.length) :
    let v := (sub.thread t).verts[i + 1]'(by have := (sub.thread t).verts_len; omega)
    let e₁ := (sub.thread t).edges[i]'(by omega)
    let e₂ := (sub.thread t).edges[i + 1]'hi
    (∀ e ∈ H.edges, G.head e = v ↔ e = e₁) ∧
    (∀ e ∈ H.edges, G.tail e = v ↔ e = e₂) := by
  intro v e₁ e₂
  have hv_len := (sub.thread t).verts_len
  have hnodup := (sub.thread t).verts_nodup
  have hhead_v0 : (sub.thread t).verts[0]'(by omega) = sub.embedV (sub.H₀.tail t) := by
    have hh := (sub.thread t).head_eq
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hh
    exact Option.some.inj hh
  have hlast_v : (sub.thread t).verts[(sub.thread t).edges.length]'(by omega) =
      sub.embedV (sub.H₀.head t) := by
    have hl := (sub.thread t).last_eq
    rw [List.getLast?_eq_getElem?] at hl
    have hidx : (sub.thread t).verts.length - 1 = (sub.thread t).edges.length := by omega
    rw [hidx, List.getElem?_eq_getElem (by omega)] at hl
    exact Option.some.inj hl
  have hv_ne_tail : v ≠ sub.embedV (sub.H₀.tail t) := by
    rw [← hhead_v0]; intro h; have := (List.Nodup.getElem_inj_iff hnodup).mp h; omega
  have hv_ne_head : v ≠ sub.embedV (sub.H₀.head t) := by
    rw [← hlast_v]; intro h; have := (List.Nodup.getElem_inj_iff hnodup).mp h; omega
  have hv_int : v ∈ (sub.thread t).verts ∧ v ≠ sub.embedV (sub.H₀.tail t) ∧
      v ≠ sub.embedV (sub.H₀.head t) := ⟨List.getElem_mem _, hv_ne_tail, hv_ne_head⟩
  have he_same_t : ∀ e ∈ H.edges, (G.tail e = v ∨ G.head e = v) → e ∈ (sub.thread t).edges := by
    intro e heH hinc
    obtain ⟨t', het'⟩ := sub.edges_cover e heH
    by_cases ht' : t' = t
    · exact ht' ▸ het'
    · exfalso
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem het'
      have hal := aux.thread_aligned t' j hj
      have hv_in_t' : v ∈ (sub.thread t').verts := by
        rcases hinc with h | h <;> rw [← h] <;> [rw [hal.1]; rw [hal.2]] <;> exact List.getElem_mem _
      have hv_not_branch : ∀ v₀ : sub.V₀, v ≠ sub.embedV v₀ :=
        sub.interior_disjoint_branch t v hv_int.1 hv_int.2.1 hv_int.2.2
      exact sub.interior_disjoint t t' (Ne.symm ht') v hv_int
        ⟨hv_in_t', hv_not_branch _, hv_not_branch _⟩
  constructor
  · intro e heH
    constructor
    · intro hh
      have het := he_same_t e heH (Or.inr hh)
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem het
      have hal := (aux.thread_aligned t j hj).2
      have hidx : j + 1 = i + 1 := (List.Nodup.getElem_inj_iff hnodup).mp (hal.symm.trans hh)
      have hji : j = i := by omega
      subst hji; rfl
    · rintro rfl; exact (aux.thread_aligned t i (by omega)).2
  · intro e heH
    constructor
    · intro ht
      have het := he_same_t e heH (Or.inl ht)
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem het
      have hal := (aux.thread_aligned t j hj).1
      have hidx : j = i + 1 := (List.Nodup.getElem_inj_iff hnodup).mp (hal.symm.trans ht)
      subst hidx; rfl
    · rintro rfl; exact (aux.thread_aligned t (i + 1) hi).1

/-- Helper: boundary of a thread-constant function at a branch vertex `embedV v₀` in `H`
equals the boundary of the corresponding function on `H₀` at `v₀`. -/
private lemma branch_boundary_eq {G : Multigraph V E} {H : G.Subgraph}
    (sub : SubdivisionData G H) (aux : AuxGraphData G H sub)
    (h : {e // e ∈ H.edges} → A) (h₀ : sub.E₀ → A)
    (hconst : ∀ (t : sub.E₀) (e : E) (he : e ∈ (sub.thread t).edges),
      h ⟨e, (sub.thread t).edges_sub e he⟩ = h₀ t)
    (v₀ : sub.V₀) :
    H.toMultigraph.boundary h ⟨sub.embedV v₀, sub.embedV_mem v₀⟩ = sub.H₀.boundary h₀ v₀ := by
  have hhead_v0 : ∀ t : sub.E₀,
      (sub.thread t).verts[0]'(by have := (sub.thread t).verts_len; have := (sub.thread t).len_pos; omega) =
      sub.embedV (sub.H₀.tail t) := by
    intro t; have hh := (sub.thread t).head_eq
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by have := (sub.thread t).verts_len; have := (sub.thread t).len_pos; omega)] at hh
    exact Option.some.inj hh
  have hlast_v : ∀ t : sub.E₀,
      (sub.thread t).verts[(sub.thread t).edges.length]'(by have := (sub.thread t).verts_len; omega) =
      sub.embedV (sub.H₀.head t) := by
    intro t; have hl := (sub.thread t).last_eq
    rw [List.getLast?_eq_getElem?] at hl
    have hidx : (sub.thread t).verts.length - 1 = (sub.thread t).edges.length := by
      have := (sub.thread t).verts_len; omega
    rw [hidx, List.getElem?_eq_getElem (by have := (sub.thread t).verts_len; omega)] at hl
    exact Option.some.inj hl
  unfold Multigraph.boundary
  congr 1
  · -- Incoming edges at `embedV v₀` correspond bijectively to `t` with `H₀.head t = v₀` via last edge of `thread t`!
    refine Finset.sum_bij
      (fun (e : {e // e ∈ H.edges}) he => (sub.edges_cover e.1 e.2).choose)
      (fun e he => ?_) (fun e₁ he₁ e₂ he₂ ht_eq => ?_) (fun t ht => ?_) (fun e _ => ?_)
    · let t := (sub.edges_cover e.1 e.2).choose
      have het : e.1 ∈ (sub.thread t).edges := (sub.edges_cover e.1 e.2).choose_spec
      obtain ⟨j, hj, he_eq⟩ := List.getElem_of_mem het
      have hal := (aux.thread_aligned t j hj).2
      have hhv : G.head e.1 = sub.embedV v₀ := congrArg Subtype.val (Finset.mem_filter.mp he).2
      have hv_eq : (sub.thread t).verts[j + 1]'(by have := (sub.thread t).verts_len; omega) = sub.embedV v₀ := by
        rw [← hal, he_eq, hhv]
      have hj_last : j + 1 = (sub.thread t).edges.length := by
        by_contra hne
        have hj1_lt : j + 1 < (sub.thread t).edges.length := by omega
        have hnot_tail : (sub.thread t).verts[j + 1]'(by have := (sub.thread t).verts_len; omega) ≠
            sub.embedV (sub.H₀.tail t) := by
          intro h
          have h' : (sub.thread t).verts[j + 1]'(by have := (sub.thread t).verts_len; omega) =
              (sub.thread t).verts[0]'(by have := (sub.thread t).verts_len; have := (sub.thread t).len_pos; omega) :=
            h.trans (hhead_v0 t).symm
          have := (List.Nodup.getElem_inj_iff (sub.thread t).verts_nodup).mp h'; omega
        have hnot_head : (sub.thread t).verts[j + 1]'(by have := (sub.thread t).verts_len; omega) ≠
            sub.embedV (sub.H₀.head t) := by
          intro h
          have h' : (sub.thread t).verts[j + 1]'(by have := (sub.thread t).verts_len; omega) =
              (sub.thread t).verts[(sub.thread t).edges.length]'(by have := (sub.thread t).verts_len; omega) :=
            h.trans (hlast_v t).symm
          have := (List.Nodup.getElem_inj_iff (sub.thread t).verts_nodup).mp h'; omega
        exact sub.interior_disjoint_branch t _ (List.getElem_mem _) hnot_tail hnot_head v₀ hv_eq
      have hhead_eq : sub.embedV (sub.H₀.head t) = sub.embedV v₀ :=
        (hlast_v t).symm.trans (by simpa only [hj_last] using hv_eq)
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, sub.embedV.injective hhead_eq⟩
    · let t := (sub.edges_cover e₁.1 e₁.2).choose
      have h1 : e₁.1 ∈ (sub.thread t).edges := (sub.edges_cover e₁.1 e₁.2).choose_spec
      have h2 : e₂.1 ∈ (sub.thread t).edges := by
        change e₂.1 ∈ (sub.thread (sub.edges_cover e₁.1 e₁.2).choose).edges
        rw [ht_eq]; exact (sub.edges_cover e₂.1 e₂.2).choose_spec
      obtain ⟨j₁, hj₁, he₁_eq⟩ := List.getElem_of_mem h1
      obtain ⟨j₂, hj₂, he₂_eq⟩ := List.getElem_of_mem h2
      have hh1 : G.head e₁.1 = sub.embedV v₀ := congrArg Subtype.val (Finset.mem_filter.mp he₁).2
      have hh2 : G.head e₂.1 = sub.embedV v₀ := congrArg Subtype.val (Finset.mem_filter.mp he₂).2
      have hv1 : (sub.thread t).verts[j₁ + 1]'(by have := (sub.thread t).verts_len; omega) = sub.embedV v₀ := by
        rw [← (aux.thread_aligned t j₁ hj₁).2, he₁_eq, hh1]
      have hv2 : (sub.thread t).verts[j₂ + 1]'(by have := (sub.thread t).verts_len; omega) = sub.embedV v₀ := by
        rw [← (aux.thread_aligned t j₂ hj₂).2, he₂_eq, hh2]
      have hj_eq : j₁ + 1 = j₂ + 1 := (List.Nodup.getElem_inj_iff (sub.thread t).verts_nodup).mp (hv1.trans hv2.symm)
      have hj12 : j₁ = j₂ := by omega
      subst hj12
      exact Subtype.ext (he₁_eq.symm.trans he₂_eq)
    · have hht : sub.H₀.head t = v₀ := (Finset.mem_filter.mp ht).2
      have hlen_pos := (sub.thread t).len_pos
      let idx := (sub.thread t).edges.length - 1
      let elast := (sub.thread t).edges[idx]'(by omega)
      have helast_t : elast ∈ (sub.thread t).edges := List.getElem_mem _
      have helast_H : elast ∈ H.edges := (sub.thread t).edges_sub _ helast_t
      refine ⟨⟨elast, helast_H⟩, ?_, ?_⟩
      · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Subtype.ext ?_⟩
        dsimp only [Subgraph.toMultigraph]
        have hal := (aux.thread_aligned t idx (by omega)).2
        have hidx1 : idx + 1 = (sub.thread t).edges.length := by omega
        simp only [elast, hal, hidx1, hlast_v t, hht]
      · by_contra hne
        exact sub.edges_disjoint _ t hne elast (sub.edges_cover elast helast_H).choose_spec helast_t
    · exact hconst _ e.1 (sub.edges_cover e.1 e.2).choose_spec
  · -- Outgoing edges at `embedV v₀` correspond bijectively to `t` with `H₀.tail t = v₀` via first edge of `thread t`!
    refine Finset.sum_bij
      (fun (e : {e // e ∈ H.edges}) he => (sub.edges_cover e.1 e.2).choose)
      (fun e he => ?_) (fun e₁ he₁ e₂ he₂ ht_eq => ?_) (fun t ht => ?_) (fun e _ => ?_)
    · let t := (sub.edges_cover e.1 e.2).choose
      have het : e.1 ∈ (sub.thread t).edges := (sub.edges_cover e.1 e.2).choose_spec
      obtain ⟨j, hj, he_eq⟩ := List.getElem_of_mem het
      have hal := (aux.thread_aligned t j hj).1
      have htv : G.tail e.1 = sub.embedV v₀ := congrArg Subtype.val (Finset.mem_filter.mp he).2
      have hv_eq : (sub.thread t).verts[j]'(by have := (sub.thread t).verts_len; omega) = sub.embedV v₀ := by
        rw [← hal, he_eq, htv]
      have hj0 : j = 0 := by
        by_contra hne
        have hnot_tail : (sub.thread t).verts[j]'(by have := (sub.thread t).verts_len; omega) ≠
            sub.embedV (sub.H₀.tail t) := by
          intro h
          have h' : (sub.thread t).verts[j]'(by have := (sub.thread t).verts_len; omega) =
              (sub.thread t).verts[0]'(by have := (sub.thread t).verts_len; have := (sub.thread t).len_pos; omega) :=
            h.trans (hhead_v0 t).symm
          have := (List.Nodup.getElem_inj_iff (sub.thread t).verts_nodup).mp h'; omega
        have hnot_head : (sub.thread t).verts[j]'(by have := (sub.thread t).verts_len; omega) ≠
            sub.embedV (sub.H₀.head t) := by
          intro h
          have h' : (sub.thread t).verts[j]'(by have := (sub.thread t).verts_len; omega) =
              (sub.thread t).verts[(sub.thread t).edges.length]'(by have := (sub.thread t).verts_len; omega) :=
            h.trans (hlast_v t).symm
          have := (List.Nodup.getElem_inj_iff (sub.thread t).verts_nodup).mp h'; omega
        exact sub.interior_disjoint_branch t _ (List.getElem_mem _) hnot_tail hnot_head v₀ hv_eq
      have htail_eq : sub.embedV (sub.H₀.tail t) = sub.embedV v₀ :=
        (hhead_v0 t).symm.trans (by simpa only [hj0] using hv_eq)
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, sub.embedV.injective htail_eq⟩
    · let t := (sub.edges_cover e₁.1 e₁.2).choose
      have h1 : e₁.1 ∈ (sub.thread t).edges := (sub.edges_cover e₁.1 e₁.2).choose_spec
      have h2 : e₂.1 ∈ (sub.thread t).edges := by
        change e₂.1 ∈ (sub.thread (sub.edges_cover e₁.1 e₁.2).choose).edges
        rw [ht_eq]; exact (sub.edges_cover e₂.1 e₂.2).choose_spec
      obtain ⟨j₁, hj₁, he₁_eq⟩ := List.getElem_of_mem h1
      obtain ⟨j₂, hj₂, he₂_eq⟩ := List.getElem_of_mem h2
      have ht1 : G.tail e₁.1 = sub.embedV v₀ := congrArg Subtype.val (Finset.mem_filter.mp he₁).2
      have ht2 : G.tail e₂.1 = sub.embedV v₀ := congrArg Subtype.val (Finset.mem_filter.mp he₂).2
      have hv1 : (sub.thread t).verts[j₁]'(by have := (sub.thread t).verts_len; omega) = sub.embedV v₀ := by
        rw [← (aux.thread_aligned t j₁ hj₁).1, he₁_eq, ht1]
      have hv2 : (sub.thread t).verts[j₂]'(by have := (sub.thread t).verts_len; omega) = sub.embedV v₀ := by
        rw [← (aux.thread_aligned t j₂ hj₂).1, he₂_eq, ht2]
      have hj12 : j₁ = j₂ := (List.Nodup.getElem_inj_iff (sub.thread t).verts_nodup).mp (hv1.trans hv2.symm)
      subst hj12
      exact Subtype.ext (he₁_eq.symm.trans he₂_eq)
    · have htt : sub.H₀.tail t = v₀ := (Finset.mem_filter.mp ht).2
      have hlen_pos := (sub.thread t).len_pos
      let efirst := (sub.thread t).edges[0]'(by omega)
      have hefirst_t : efirst ∈ (sub.thread t).edges := List.getElem_mem _
      have hefirst_H : efirst ∈ H.edges := (sub.thread t).edges_sub _ hefirst_t
      refine ⟨⟨efirst, hefirst_H⟩, ?_, ?_⟩
      · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Subtype.ext ?_⟩
        dsimp only [Subgraph.toMultigraph]
        have hal := (aux.thread_aligned t 0 (by omega)).1
        simp only [efirst, hal, hhead_v0 t, htt]
      · by_contra hne
        exact sub.edges_disjoint _ t hne efirst (sub.edges_cover efirst hefirst_H).choose_spec hefirst_t
    · exact hconst _ e.1 (sub.edges_cover e.1 e.2).choose_spec

/-- **Lemma 3.6(a) (Flows and cycles of `H` and `H₀`).** -/
theorem lem_3_6_a
    {G : Multigraph V E} {H : G.Subgraph} (sub : SubdivisionData G H)
    (aux : AuxGraphData G H sub) :
    (∀ (O : H.toMultigraph.DirectedCycle) (t : sub.E₀),
      ∃ s : ℤ, (s = 1 ∨ s = 0 ∨ s = -1) ∧
        ∀ e (he : e ∈ (sub.thread t).edges), O.sign ⟨e, (sub.thread t).edges_sub e he⟩ = s) ∧
    (∀ (h : {e // e ∈ H.edges} → A), H.toMultigraph.IsFlow h →
      ∀ t : sub.E₀, ∀ e₁ e₂ (h₁ : e₁ ∈ (sub.thread t).edges) (h₂ : e₂ ∈ (sub.thread t).edges),
        h ⟨e₁, (sub.thread t).edges_sub e₁ h₁⟩ = h ⟨e₂, (sub.thread t).edges_sub e₂ h₂⟩) ∧
    (∃ e : {h : {e // e ∈ H.edges} → A // H.toMultigraph.IsFlow h} ≃
           {h₀ : sub.E₀ → A // sub.H₀.IsFlow h₀},
      ∀ (h : {h : {e // e ∈ H.edges} → A // H.toMultigraph.IsFlow h}) (t : sub.E₀)
        (edge : E) (hedge : edge ∈ (sub.thread t).edges),
        h.1 ⟨edge, (sub.thread t).edges_sub edge hedge⟩ = (e h).1 t) := by
  -- Generic constancy of any `B`-flow of `H` along each thread
  have hconst_any : ∀ {B : Type} [AddCommGroup B] (h : {e // e ∈ H.edges} → B),
      H.toMultigraph.IsFlow h → ∀ (t : sub.E₀) (i : ℕ) (hi : i < (sub.thread t).edges.length),
      h ⟨(sub.thread t).edges[i]'hi, (sub.thread t).edges_sub _ (List.getElem_mem hi)⟩ =
      h ⟨(sub.thread t).edges[0]'(by have := (sub.thread t).len_pos; omega),
         (sub.thread t).edges_sub _ (List.getElem_mem _)⟩ := by
    intro B _ h hh t i
    induction i with
    | zero => intro _; rfl
    | succ i ih =>
      intro hi
      rw [← ih (by omega)]
      obtain ⟨hh_uniq, ht_uniq⟩ := thread_interior_edges sub aux t i hi
      let v := (sub.thread t).verts[i + 1]'(by have := (sub.thread t).verts_len; omega)
      have hvH : v ∈ H.verts := (sub.thread t).verts_sub v (List.getElem_mem _)
      have hbd := hh ⟨v, hvH⟩
      unfold Multigraph.boundary at hbd
      let e₁ : {e // e ∈ H.edges} := ⟨(sub.thread t).edges[i]'(by omega),
        (sub.thread t).edges_sub _ (List.getElem_mem _)⟩
      let e₂ : {e // e ∈ H.edges} := ⟨(sub.thread t).edges[i + 1]'hi,
        (sub.thread t).edges_sub _ (List.getElem_mem _)⟩
      have hf1 : Finset.univ.filter (fun e : {e // e ∈ H.edges} => H.toMultigraph.head e = ⟨v, hvH⟩) = {e₁} := by
        ext e; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
          Subgraph.toMultigraph, Subtype.ext_iff]
        exact hh_uniq e.1 e.2
      have hf2 : Finset.univ.filter (fun e : {e // e ∈ H.edges} => H.toMultigraph.tail e = ⟨v, hvH⟩) = {e₂} := by
        ext e; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
          Subgraph.toMultigraph, Subtype.ext_iff]
        exact ht_uniq e.1 e.2
      rw [hf1, hf2, Finset.sum_singleton, Finset.sum_singleton, sub_eq_zero] at hbd
      exact hbd.symm
  have hconst_A : ∀ (h : {e // e ∈ H.edges} → A), H.toMultigraph.IsFlow h →
      ∀ t : sub.E₀, ∀ e₁ e₂ (h₁ : e₁ ∈ (sub.thread t).edges) (h₂ : e₂ ∈ (sub.thread t).edges),
        h ⟨e₁, (sub.thread t).edges_sub e₁ h₁⟩ = h ⟨e₂, (sub.thread t).edges_sub e₂ h₂⟩ := by
    intro h hh t e₁ e₂ h₁ h₂
    obtain ⟨i₁, hi₁, rfl⟩ := List.getElem_of_mem h₁
    obtain ⟨i₂, hi₂, rfl⟩ := List.getElem_of_mem h₂
    rw [hconst_any h hh t i₁ hi₁, hconst_any h hh t i₂ hi₂]
  refine ⟨?_, hconst_A, ?_⟩
  · -- Part 1: directed cycles constant on threads
    intro O t
    let e0 : {e // e ∈ H.edges} :=
      ⟨(sub.thread t).edges[0]'(by have := (sub.thread t).len_pos; omega),
       (sub.thread t).edges_sub _ (List.getElem_mem _)⟩
    refine ⟨O.sign e0, ?_, fun e he => ?_⟩
    · by_cases hm : e0 ∈ O.sub.edges
      · rcases O.sign_mem hm with hs | hs
        · left; exact hs
        · right; right; exact hs
      · right; left; exact O.sign_zero hm
    · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
      exact hconst_any O.sign O.isFlow t i hi
  · -- Part 3: explicit bijection between `A`-flows of `H` and `A`-flows of `H₀`
    classical
    let toH0 : {h : {e // e ∈ H.edges} → A // H.toMultigraph.IsFlow h} →
        {h₀ : sub.E₀ → A // sub.H₀.IsFlow h₀} := fun ⟨h, hh⟩ =>
      ⟨fun t => h ⟨(sub.thread t).edges[0]'(by have := (sub.thread t).len_pos; omega),
          (sub.thread t).edges_sub _ (List.getElem_mem _)⟩,
       fun v₀ => by
        rw [← branch_boundary_eq sub aux h _ (fun t e he => hconst_A h hh t e _ he (List.getElem_mem _)) v₀]
        exact hh ⟨sub.embedV v₀, sub.embedV_mem v₀⟩⟩
    let ofH0 : {h₀ : sub.E₀ → A // sub.H₀.IsFlow h₀} →
        {h : {e // e ∈ H.edges} → A // H.toMultigraph.IsFlow h} := fun ⟨h₀, hh₀⟩ =>
      ⟨fun e => h₀ (sub.edges_cover e.1 e.2).choose,
       fun ⟨v, hvH⟩ => by
        have hconst_of : ∀ (t : sub.E₀) (e : E) (he : e ∈ (sub.thread t).edges),
            h₀ (sub.edges_cover e ((sub.thread t).edges_sub e he)).choose = h₀ t := by
          intro t e he
          congr 1; by_contra hne
          exact sub.edges_disjoint _ t hne e (sub.edges_cover e ((sub.thread t).edges_sub e he)).choose_spec he
        rcases sub.verts_cover v hvH with ⟨v₀, rfl⟩ | ⟨t, hvt⟩
        · rw [branch_boundary_eq sub aux _ h₀ hconst_of v₀]; exact hh₀ v₀
        · by_cases hbr : ∃ v₀ : sub.V₀, sub.embedV v₀ = v
          · rcases hbr with ⟨v₀, rfl⟩
            rw [branch_boundary_eq sub aux _ h₀ hconst_of v₀]; exact hh₀ v₀
          · push Not at hbr
            obtain ⟨k, hk, hvk⟩ := List.getElem_of_mem hvt
            have hv_len := (sub.thread t).verts_len
            have hk_pos : 1 ≤ k := by
              by_contra h0
              have hk0 : k = 0 := by omega
              subst hk0
              have hh := (sub.thread t).head_eq
              cases hvs : (sub.thread t).verts with
              | nil => simp [hvs] at hk
              | cons x _ =>
                simp only [hvs, List.head?_cons, Option.some.injEq] at hh
                simp only [hvs, List.getElem_cons_zero] at hvk
                exact hbr (sub.H₀.tail t) (hh.symm.trans hvk)
            have hk_lt : k < (sub.thread t).edges.length := by
              by_contra hge
              have hke : k = (sub.thread t).edges.length := by omega
              subst hke
              have hl := (sub.thread t).last_eq
              rw [List.getLast?_eq_getElem?] at hl
              have hidx : (sub.thread t).verts.length - 1 = (sub.thread t).edges.length := by omega
              rw [hidx, List.getElem?_eq_getElem (by omega)] at hl
              exact hbr (sub.H₀.head t) ((Option.some.inj hl).symm.trans hvk)
            have hi : (k - 1) + 1 < (sub.thread t).edges.length := by omega
            obtain ⟨hh_uniq, ht_uniq⟩ := thread_interior_edges sub aux t (k - 1) hi
            have hvk' : (sub.thread t).verts[(k - 1) + 1]'(by omega) = v := by
              have : k - 1 + 1 = k := by omega
              simpa only [this] using hvk
            rw [hvk'] at hh_uniq ht_uniq
            unfold Multigraph.boundary
            let e₁ : {e // e ∈ H.edges} := ⟨(sub.thread t).edges[k - 1]'(by omega),
              (sub.thread t).edges_sub _ (List.getElem_mem _)⟩
            let e₂ : {e // e ∈ H.edges} := ⟨(sub.thread t).edges[(k - 1) + 1]'hi,
              (sub.thread t).edges_sub _ (List.getElem_mem _)⟩
            have hf1 : Finset.univ.filter (fun e : {e // e ∈ H.edges} => H.toMultigraph.head e = ⟨v, hvH⟩) = {e₁} := by
              ext e; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
                Subgraph.toMultigraph, Subtype.ext_iff]; exact hh_uniq e.1 e.2
            have hf2 : Finset.univ.filter (fun e : {e // e ∈ H.edges} => H.toMultigraph.tail e = ⟨v, hvH⟩) = {e₂} := by
              ext e; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
                Subgraph.toMultigraph, Subtype.ext_iff]; exact ht_uniq e.1 e.2
            rw [hf1, hf2, Finset.sum_singleton, Finset.sum_singleton]
            rw [hconst_of t e₁.1 (List.getElem_mem _), hconst_of t e₂.1 (List.getElem_mem _), sub_self]⟩
    refine ⟨
      { toFun := toH0
        invFun := ofH0
        left_inv := fun ⟨h, hh⟩ => by
          apply Subtype.ext; funext ⟨e, heH⟩
          exact hconst_A h hh (sub.edges_cover e heH).choose _ e (List.getElem_mem _) (sub.edges_cover e heH).choose_spec
        right_inv := fun ⟨h₀, hh₀⟩ => by
          apply Subtype.ext; funext t
          dsimp only [toH0, ofH0]
          congr 1; by_contra hne
          exact sub.edges_disjoint _ t hne _
            (sub.edges_cover ((sub.thread t).edges[0]'(by have := (sub.thread t).len_pos; omega))
              ((sub.thread t).edges_sub _ (List.getElem_mem _))).choose_spec
            (List.getElem_mem _) },
      fun ⟨h, hh⟩ t edge hedge => hconst_A h hh t edge _ hedge (List.getElem_mem _)⟩

/-- **Lemma 3.6(b) (Restriction of an `H₀`-flow to any block `K_b` is a flow of `K_b`).** -/
theorem lem_3_6_b
    {G : Multigraph V E} {H : G.Subgraph} (sub : SubdivisionData G H)
    (aux : AuxGraphData G H sub)
    (h₀ : sub.E₀ → A) (hh₀ : sub.H₀.IsFlow h₀) (b : Fin aux.numBlocks) :
    (aux.block_subgraph b).toMultigraph.IsFlow (fun e => h₀ e.1) := by
  classical
  -- Decompose `h₀` as a sum of cycle flows via `lem_2_1_a` + `exists_spanningForest`
  obtain ⟨T₀, hT₀⟩ := exists_spanningForest sub.H₀
  obtain ⟨l, hl⟩ := (lem_2_1_a (A := A) sub.H₀ T₀ hT₀).2.2 h₀ hh₀
  -- Every directed cycle `C` of `sub.H₀` lies either wholly inside `K_b` or edge-disjoint from `K_b`!
  have hcyc_block : ∀ (C : sub.H₀.DirectedCycle),
      C.sub ≤ aux.block_subgraph b ∨ Disjoint C.sub.edges (aux.block_subgraph b).edges := by
    intro C
    by_cases hmeet : ∃ e ∈ C.sub.edges, e ∈ (aux.block_subgraph b).edges
    · rcases hmeet with ⟨e, heC, heK⟩
      exact Or.inl (cycle_subset_block sub.loopless C.isCycle (aux.is_block b) heC heK)
    · push Not at hmeet
      exact Or.inr (Finset.disjoint_left.mpr hmeet)
  have hrestr_cyc : ∀ (p : A × sub.H₀.DirectedCycle),
      (aux.block_subgraph b).toMultigraph.IsFlow (fun e => p.2.sign e.1 • p.1) := by
    rintro ⟨a, C⟩
    apply isFlow_zsmul
    rcases hcyc_block C with hle | hdisj
    · -- `C ≤ block_subgraph b`: boundary inside `block_subgraph b` equals boundary in `H₀` (which is 0)!
      intro ⟨v, hv⟩
      have hC0 := C.isFlow v
      rw [boundary_eq_sum_ite] at hC0 ⊢
      have hsum : ∑ e : {e // e ∈ (aux.block_subgraph b).edges},
          ((if (aux.block_subgraph b).toMultigraph.head e = ⟨v, hv⟩ then C.sign e.1 else 0) -
           (if (aux.block_subgraph b).toMultigraph.tail e = ⟨v, hv⟩ then C.sign e.1 else 0)) =
          ∑ e : sub.E₀,
            ((if sub.H₀.head e = v then C.sign e else 0) - (if sub.H₀.tail e = v then C.sign e else 0)) := by
        rw [← Finset.sum_subset (Finset.subset_univ (aux.block_subgraph b).edges)]
        · refine Finset.sum_bij (fun e _ => e.1) (fun e _ => e.2)
            (fun _ _ _ _ h => Subtype.ext h)
            (fun e he => ⟨⟨e, he⟩, Finset.mem_univ _, rfl⟩)
            (fun e _ => by simp [Subgraph.toMultigraph, Subtype.mk.injEq])
        · intro e _ hnot
          have henotC : e ∉ C.sub.edges := fun hm => hnot (hle.2 hm)
          simp [C.sign_zero henotC]
      rw [hsum, hC0]
    · -- Disjoint from `block_subgraph b`: `C.sign e = 0` on every edge of `block_subgraph b`!
      intro v
      have h0 : (fun e : {e // e ∈ (aux.block_subgraph b).edges} => C.sign e.1) = 0 := by
        funext e; exact C.sign_zero (Finset.disjoint_right.mp hdisj e.2)
      rw [h0]; exact boundary_zero _ v
  have hflow_sum := isFlow_list_sum (G := (aux.block_subgraph b).toMultigraph) l
    (f := fun p e => p.2.sign e.1 • p.1) (fun p _ => hrestr_cyc p)
  have heq : (fun e : {e // e ∈ (aux.block_subgraph b).edges} => h₀ e.1) =
      fun e => (l.map (fun p => p.2.sign e.1 • p.1)).sum := funext (fun e => hl e.1)
  rw [heq]; exact hflow_sum

/-- **Lemma 3.6(c) (Projection `π` preserves flows, and every flow of `H` lifts to `Q`).** -/
theorem lem_3_6_c
    {G : Multigraph V E} {H : G.Subgraph} (sub : SubdivisionData G H)
    (aux : AuxGraphData G H sub) :
    (∀ Y : aux.EQ → A, aux.Q.IsFlow Y →
      sub.H₀.IsFlow (fun t => Y (aux.origEdge t)) ∧
      H.toMultigraph.IsFlow (fun e => aux.pi Y e.1)) ∧
    (∀ h : {e // e ∈ H.edges} → A, H.toMultigraph.IsFlow h →
      ∃ Y : aux.EQ → A, aux.Q.IsFlow Y ∧ ∀ e : {e // e ∈ H.edges}, aux.pi Y e.1 = h e) := by
  classical
  have hpi_eq : ∀ (Y : aux.EQ → A) (t : sub.E₀) (e : E) (he : e ∈ (sub.thread t).edges),
      aux.pi Y e = Y (aux.origEdge t) := by
    intro Y t e he
    have hex : ∃ t' : sub.E₀, e ∈ (sub.thread t').edges := ⟨t, he⟩
    simp only [AuxGraphData.pi, hex, ↓reduceDIte]
    congr 2
    by_contra hne
    exact sub.edges_disjoint _ t hne e hex.choose_spec he
  obtain ⟨_, _, eqv, heqv⟩ := lem_3_6_a (A := A) sub aux
  constructor
  · -- Forward direction
    intro Y hY
    have hH0_flow : sub.H₀.IsFlow (fun t => Y (aux.origEdge t)) := by
      intro v₀
      let S : Finset aux.VQ := Finset.univ.filter (fun u => aux.contractV u = v₀)
      have hsum0 : ∑ u ∈ S, aux.Q.boundary Y u = 0 := Finset.sum_eq_zero (fun u _ => hY u)
      rw [sum_boundary_eq_cut] at hsum0
      -- Only original edges can cross `S` (expansion edges stay inside one fiber `contractV⁻¹(v₀)`)!
      have hhead_eq : ∑ eq ∈ Finset.univ.filter (fun eq => aux.Q.head eq ∈ S ∧ aux.Q.tail eq ∉ S), Y eq =
          ∑ t ∈ Finset.univ.filter (fun t : sub.E₀ => sub.H₀.head t = v₀), Y (aux.origEdge t) := by
        refine Finset.sum_bij (fun t _ => aux.origEdge t) (fun t ht => ?_)
          (fun _ _ _ _ h => aux.origEdge.injective h) (fun eq heq => ?_) (fun _ _ => rfl) |>.symm
        · have hht := (Finset.mem_filter.mp ht).2
          have htt_ne : sub.H₀.tail t ≠ v₀ := fun h => sub.loopless t (h.trans hht.symm)
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, (aux.orig_head t).trans hht⟩,
            fun hm => htt_ne ((aux.orig_tail t).symm.trans (Finset.mem_filter.mp hm).2)⟩
        · have ⟨hhS, htnotS⟩ := (Finset.mem_filter.mp heq).2
          have hex_t : ∃ t : sub.E₀, aux.origEdge t = eq := by
            by_contra hall; push Not at hall
            have hsame := aux.exp_same_contractV eq hall
            exact htnotS (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsame.trans (Finset.mem_filter.mp hhS).2⟩)
          rcases hex_t with ⟨t, rfl⟩
          refine ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
          rw [← aux.orig_head t]; exact (Finset.mem_filter.mp hhS).2
      have htail_eq : ∑ eq ∈ Finset.univ.filter (fun eq => aux.Q.tail eq ∈ S ∧ aux.Q.head eq ∉ S), Y eq =
          ∑ t ∈ Finset.univ.filter (fun t : sub.E₀ => sub.H₀.tail t = v₀), Y (aux.origEdge t) := by
        refine Finset.sum_bij (fun t _ => aux.origEdge t) (fun t ht => ?_)
          (fun _ _ _ _ h => aux.origEdge.injective h) (fun eq heq => ?_) (fun _ _ => rfl) |>.symm
        · have htt := (Finset.mem_filter.mp ht).2
          have hht_ne : sub.H₀.head t ≠ v₀ := fun h => sub.loopless t (htt.trans h.symm)
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, (aux.orig_tail t).trans htt⟩,
            fun hm => hht_ne ((aux.orig_head t).symm.trans (Finset.mem_filter.mp hm).2)⟩
        · have ⟨htS, hhnotS⟩ := (Finset.mem_filter.mp heq).2
          have hex_t : ∃ t : sub.E₀, aux.origEdge t = eq := by
            by_contra hall; push Not at hall
            have hsame := aux.exp_same_contractV eq hall
            exact hhnotS (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsame.symm.trans (Finset.mem_filter.mp htS).2⟩)
          rcases hex_t with ⟨t, rfl⟩
          refine ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
          rw [← aux.orig_tail t]; exact (Finset.mem_filter.mp htS).2
      rw [hhead_eq, htail_eq] at hsum0
      exact hsum0
    refine ⟨hH0_flow, ?_⟩
    -- Use `eqv.symm` on `⟨fun t => Y (aux.origEdge t), hH0_flow⟩`!
    let hLift := eqv.symm ⟨fun t => Y (aux.origEdge t), hH0_flow⟩
    have hEq : (fun e : {e // e ∈ H.edges} => aux.pi Y e.1) = hLift.1 := by
      funext ⟨e, heH⟩
      obtain ⟨t, het⟩ := sub.edges_cover e heH
      rw [hpi_eq Y t e het]
      have h1 := heqv hLift t e het
      rw [Equiv.apply_symm_apply] at h1
      exact h1.symm
    rw [hEq]; exact hLift.2
  · -- Backward direction: lift `h` on `H` to `Y` on `Q`
    intro h hh
    let h₀ := (eqv ⟨h, hh⟩).1
    have hh₀ : sub.H₀.IsFlow h₀ := (eqv ⟨h, hh⟩).2
    -- Start with `Y₀`: equals `h₀ t` on `origEdge t` and `0` on expansion edges
    let Y₀ : aux.EQ → A := fun eq =>
      if hex : ∃ t : sub.E₀, aux.origEdge t = eq then h₀ hex.choose else 0
    have hY₀_orig : ∀ t : sub.E₀, Y₀ (aux.origEdge t) = h₀ t := fun t => by
      have hex : ∃ t' : sub.E₀, aux.origEdge t' = aux.origEdge t := ⟨t, rfl⟩
      simp only [Y₀, hex, ↓reduceDIte]
      congr 1; exact aux.origEdge.injective hex.choose_spec
    have hY₀_exp : ∀ eq : aux.EQ, (∀ t : sub.E₀, aux.origEdge t ≠ eq) → Y₀ eq = 0 := fun eq hexp => by
      simp [Y₀, hexp]
    -- On each fiber `V_{b, x} = {u : VQ | comp u = b ∧ contractV u = x}`, sum of `aux.Q.boundary Y₀` is 0!
    -- Build expansion-edge subgraphs `F_{b, x}` on each fiber and solve `-boundary Y₀` via `exists_edge_map_with_boundary`!
    let fibV (b : Fin aux.numBlocks) (x : sub.V₀) := {u : aux.VQ // aux.comp u = b ∧ aux.contractV u = x}
    let fibE (b : Fin aux.numBlocks) (x : sub.V₀) :=
      {eq : aux.EQ // (∀ t : sub.E₀, aux.origEdge t ≠ eq) ∧
        aux.comp (aux.Q.tail eq) = b ∧ aux.contractV (aux.Q.tail eq) = x}
    let fibG (b : Fin aux.numBlocks) (x : sub.V₀) : Multigraph (fibV b x) (fibE b x) :=
      { tail := fun eq => ⟨aux.Q.tail eq.1, eq.2.2⟩
        head := fun eq => ⟨aux.Q.head eq.1,
          (aux.edge_same_comp eq.1).symm.trans eq.2.2.1,
          (aux.exp_same_contractV eq.1 eq.2.1).symm.trans eq.2.2.2⟩ }
    have hfib_conn : ∀ b x, (fibG b x).Connected := by
      intro b x ⟨u, hu1, hu2⟩ ⟨v, hv1, hv2⟩
      have hw := aux.fiber_connected b u v hu1 hv1 (hu2.trans hv2.symm)
      -- Every vertex along `hw` stays in `fibV b x`!
      have hstay : ∀ {p q : aux.VQ} (hp1 : aux.comp p = b) (hp2 : aux.contractV p = x),
          Relation.ReflTransGen
            (fun a c => ∃ eq : aux.EQ, (∀ t : sub.E₀, aux.origEdge t ≠ eq) ∧
              ((aux.Q.tail eq = a ∧ aux.Q.head eq = c) ∨ (aux.Q.tail eq = c ∧ aux.Q.head eq = a))) p q →
          ∃ (hq : aux.comp q = b ∧ aux.contractV q = x),
            Relation.ReflTransGen (fibG b x).Adj ⟨p, hp1, hp2⟩ ⟨q, hq⟩ := by
        intro p q hp1 hp2 hw'
        induction hw' with
        | refl => exact ⟨⟨hp1, hp2⟩, Relation.ReflTransGen.refl⟩
        | @tail r s _ hrs ih =>
          rcases ih with ⟨⟨hr1, hr2⟩, hwalk⟩
          rcases hrs with ⟨eq, hexp, ⟨ht, hh⟩ | ⟨ht, hh⟩⟩
          · have hs1 : aux.comp s = b := hh ▸ (aux.edge_same_comp eq).symm.trans (ht.symm ▸ hr1)
            have hs2 : aux.contractV s = x := hh ▸ (aux.exp_same_contractV eq hexp).symm.trans (ht.symm ▸ hr2)
            refine ⟨⟨hs1, hs2⟩, Relation.ReflTransGen.tail hwalk ?_⟩
            refine ⟨⟨eq, hexp, ht.symm ▸ hr1, ht.symm ▸ hr2⟩, Or.inl ⟨Subtype.ext ht, Subtype.ext hh⟩⟩
          · have hs1 : aux.comp s = b := ht ▸ (aux.edge_same_comp eq).trans (hh.symm ▸ hr1)
            have hs2 : aux.contractV s = x := ht ▸ (aux.exp_same_contractV eq hexp).trans (hh.symm ▸ hr2)
            refine ⟨⟨hs1, hs2⟩, Relation.ReflTransGen.tail hwalk ?_⟩
            refine ⟨⟨eq, hexp, (congrArg aux.comp ht).trans hs1,
              (congrArg aux.contractV ht).trans hs2⟩, Or.inr ⟨Subtype.ext ht, Subtype.ext hh⟩⟩
      exact (hstay hu1 hu2 hw).2
    have hfib_sum0 : ∀ b x, ∑ u : fibV b x, (-aux.Q.boundary Y₀ u.1) = 0 := by
      intro b x
      rw [Finset.sum_neg_distrib, neg_eq_zero]
      let S : Finset aux.VQ := Finset.univ.filter (fun u => aux.comp u = b ∧ aux.contractV u = x)
      have h1 : ∑ u : fibV b x, aux.Q.boundary Y₀ u.1 = ∑ u ∈ S, aux.Q.boundary Y₀ u := by
        refine Finset.sum_bij (fun u _ => u.1) (fun u _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, u.2⟩)
          (fun _ _ _ _ h => Subtype.ext h)
          (fun u hu => ⟨⟨u, (Finset.mem_filter.mp hu).2⟩, Finset.mem_univ _, rfl⟩)
          (fun _ _ => rfl)
      rw [h1, sum_boundary_eq_cut]
      -- If `x ∈ (block_subgraph b).verts`, this cut sum equals `(block_subgraph b).toMultigraph.boundary h₀ x = 0`!
      -- If `x ∉ (block_subgraph b).verts`, NO original edge in block `b` hits `x`, so both sums are 0!
      by_cases hxK : x ∈ (aux.block_subgraph b).verts
      · have hKb_flow := lem_3_6_b sub aux h₀ hh₀ b ⟨x, hxK⟩
        unfold Multigraph.boundary at hKb_flow
        have hhead_eq : ∑ eq ∈ Finset.univ.filter (fun eq => aux.Q.head eq ∈ S ∧ aux.Q.tail eq ∉ S), Y₀ eq =
            ∑ e ∈ Finset.univ.filter (fun e : {e // e ∈ (aux.block_subgraph b).edges} =>
              (aux.block_subgraph b).toMultigraph.head e = ⟨x, hxK⟩), h₀ e.1 := by
          refine Finset.sum_bij (fun e _ => aux.origEdge e.1) (fun e he => ?_)
            (fun _ _ _ _ h => Subtype.ext (aux.origEdge.injective h)) (fun eq heq => ?_) (fun e _ => (hY₀_orig e.1).symm) |>.symm
          · have hhe : sub.H₀.head e.1 = x := congrArg Subtype.val (Finset.mem_filter.mp he).2
            have hcb : aux.comp (aux.Q.tail (aux.origEdge e.1)) = b := (aux.orig_in_block e.1 b).mp e.2
            have hcb_h : aux.comp (aux.Q.head (aux.origEdge e.1)) = b := (aux.edge_same_comp _).symm.trans hcb
            have hte_ne : sub.H₀.tail e.1 ≠ x := fun h => sub.loopless e.1 (h.trans hhe.symm)
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcb_h, (aux.orig_head e.1).trans hhe⟩,
              fun hm => hte_ne ((aux.orig_tail e.1).symm.trans (Finset.mem_filter.mp hm).2.2)⟩
          · have ⟨hhS, htnotS⟩ := (Finset.mem_filter.mp heq).2
            have hex_t : ∃ t : sub.E₀, aux.origEdge t = eq := by
              by_contra hall; push Not at hall
              have hsc := aux.edge_same_comp eq
              have hsv := aux.exp_same_contractV eq hall
              have ⟨hc, hv⟩ := (Finset.mem_filter.mp hhS).2
              exact htnotS (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsc.trans hc, hsv.trans hv⟩)
            rcases hex_t with ⟨t, rfl⟩
            have ⟨hc_h, hv_h⟩ := (Finset.mem_filter.mp hhS).2
            have htK : t ∈ (aux.block_subgraph b).edges :=
              (aux.orig_in_block t b).mpr ((aux.edge_same_comp _).trans hc_h)
            refine ⟨⟨t, htK⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Subtype.ext ?_⟩, rfl⟩
            dsimp only [Subgraph.toMultigraph]; rw [← aux.orig_head t]; exact hv_h
        have htail_eq : ∑ eq ∈ Finset.univ.filter (fun eq => aux.Q.tail eq ∈ S ∧ aux.Q.head eq ∉ S), Y₀ eq =
            ∑ e ∈ Finset.univ.filter (fun e : {e // e ∈ (aux.block_subgraph b).edges} =>
              (aux.block_subgraph b).toMultigraph.tail e = ⟨x, hxK⟩), h₀ e.1 := by
          refine Finset.sum_bij (fun e _ => aux.origEdge e.1) (fun e he => ?_)
            (fun _ _ _ _ h => Subtype.ext (aux.origEdge.injective h)) (fun eq heq => ?_) (fun e _ => (hY₀_orig e.1).symm) |>.symm
          · have hte : sub.H₀.tail e.1 = x := congrArg Subtype.val (Finset.mem_filter.mp he).2
            have hcb : aux.comp (aux.Q.tail (aux.origEdge e.1)) = b := (aux.orig_in_block e.1 b).mp e.2
            have hhe_ne : sub.H₀.head e.1 ≠ x := fun h => sub.loopless e.1 (hte.trans h.symm)
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcb, (aux.orig_tail e.1).trans hte⟩,
              fun hm => hhe_ne ((aux.orig_head e.1).symm.trans (Finset.mem_filter.mp hm).2.2)⟩
          · have ⟨htS, hhnotS⟩ := (Finset.mem_filter.mp heq).2
            have hex_t : ∃ t : sub.E₀, aux.origEdge t = eq := by
              by_contra hall; push Not at hall
              have hsc := aux.edge_same_comp eq
              have hsv := aux.exp_same_contractV eq hall
              have ⟨hc, hv⟩ := (Finset.mem_filter.mp htS).2
              exact hhnotS (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsc.symm.trans hc, hsv.symm.trans hv⟩)
            rcases hex_t with ⟨t, rfl⟩
            have ⟨hc_t, hv_t⟩ := (Finset.mem_filter.mp htS).2
            have htK : t ∈ (aux.block_subgraph b).edges := (aux.orig_in_block t b).mpr hc_t
            refine ⟨⟨t, htK⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Subtype.ext ?_⟩, rfl⟩
            dsimp only [Subgraph.toMultigraph]; rw [← aux.orig_tail t]; exact hv_t
        rw [hhead_eq, htail_eq, hKb_flow]
      · -- `x ∉ (block_subgraph b).verts`: no edge with `Y₀ eq ≠ 0` can touch `S`!
        have hzero_touch : ∀ eq : aux.EQ, (aux.Q.head eq ∈ S ∨ aux.Q.tail eq ∈ S) → Y₀ eq = 0 := by
          intro eq htouch
          by_cases hex : ∃ t : sub.E₀, aux.origEdge t = eq
          · rcases hex with ⟨t, rfl⟩
            exfalso
            rcases htouch with hh | ht
            · have ⟨hc, hv⟩ := (Finset.mem_filter.mp hh).2
              have htK : t ∈ (aux.block_subgraph b).edges :=
                (aux.orig_in_block t b).mpr ((aux.edge_same_comp _).trans hc)
              exact hxK (hv ▸ (aux.orig_head t) ▸ (aux.block_subgraph b).head_mem htK)
            · have ⟨hc, hv⟩ := (Finset.mem_filter.mp ht).2
              have htK : t ∈ (aux.block_subgraph b).edges := (aux.orig_in_block t b).mpr hc
              exact hxK (hv ▸ (aux.orig_tail t) ▸ (aux.block_subgraph b).tail_mem htK)
          · push Not at hex; exact hY₀_exp eq hex
        rw [Finset.sum_eq_zero (fun eq heq => hzero_touch eq (Or.inl (Finset.mem_filter.mp heq).2.1)),
            Finset.sum_eq_zero (fun eq heq => hzero_touch eq (Or.inr (Finset.mem_filter.mp heq).2.1)),
            sub_self]
    -- Solve on each fiber `(b, x)`!
    let sol (b : Fin aux.numBlocks) (x : sub.V₀) : fibE b x → A :=
      (exists_edge_map_with_boundary (A := A) (Fintype.card (fibV b x))
        (fibV b x) (fibE b x) (fibG b x) (hfib_conn b x) le_rfl
        (fun u => -aux.Q.boundary Y₀ u.1) (hfib_sum0 b x)).choose
    have hsol_spec : ∀ b x (u : fibV b x), (fibG b x).boundary (sol b x) u = -aux.Q.boundary Y₀ u.1 :=
      fun b x => (exists_edge_map_with_boundary (A := A) (Fintype.card (fibV b x))
        (fibV b x) (fibE b x) (fibG b x) (hfib_conn b x) le_rfl
        (fun u => -aux.Q.boundary Y₀ u.1) (hfib_sum0 b x)).choose_spec
    let Z : aux.EQ → A := fun eq =>
      if h : ∀ t : sub.E₀, aux.origEdge t ≠ eq then
        sol (aux.comp (aux.Q.tail eq)) (aux.contractV (aux.Q.tail eq)) ⟨eq, h, rfl, rfl⟩
      else 0
    let Y : aux.EQ → A := fun eq => Y₀ eq + Z eq
    refine ⟨Y, fun u => ?_, fun ⟨e, heH⟩ => ?_⟩
    · rw [boundary_add]
      -- Show `aux.Q.boundary Z u = (fibG (aux.comp u) (aux.contractV u)).boundary (sol ...) ⟨u, rfl, rfl⟩`
      let b := aux.comp u
      let x := aux.contractV u
      have hsol_congr : ∀ {b₁ b₂ : Fin aux.numBlocks} {x₁ x₂ : sub.V₀}
          (hb : b₁ = b₂) (hx : x₁ = x₂) (eq : aux.EQ) (hexp : ∀ t : sub.E₀, aux.origEdge t ≠ eq)
          (h1 : aux.comp (aux.Q.tail eq) = b₁) (h2 : aux.contractV (aux.Q.tail eq) = x₁),
          sol b₁ x₁ ⟨eq, hexp, h1, h2⟩ = sol b₂ x₂ ⟨eq, hexp, h1.trans hb, h2.trans hx⟩ := by
        intro b₁ b₂ x₁ x₂ hb hx
        subst hb; subst hx; intro _ _ _ _; rfl
      have hZ_bd : aux.Q.boundary Z u = (fibG b x).boundary (sol b x) ⟨u, rfl, rfl⟩ := by
        rw [boundary_eq_sum_ite, boundary_eq_sum_ite]
        symm
        rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.filter (fun eq : aux.EQ =>
            (∀ t : sub.E₀, aux.origEdge t ≠ eq) ∧ aux.comp (aux.Q.tail eq) = b ∧ aux.contractV (aux.Q.tail eq) = x)))]
        · refine Finset.sum_bij (fun eq _ => eq.1)
            (fun eq _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, eq.2⟩)
            (fun _ _ _ _ h => Subtype.ext h)
            (fun eq heq => ⟨⟨eq, (Finset.mem_filter.mp heq).2⟩, Finset.mem_univ _, rfl⟩)
            (fun eq _ => ?_)
          rcases eq with ⟨eq, hexp, hb, hx⟩
          have hZeq : Z eq = sol b x ⟨eq, hexp, hb, hx⟩ := by
            dsimp only [Z]
            split_ifs
            exact hsol_congr hb hx eq hexp rfl rfl
          rw [hZeq]
          dsimp only [fibG, fibV]
          by_cases h1 : aux.Q.head eq = u <;> by_cases h2 : aux.Q.tail eq = u <;>
            simp [h1, h2]
        · intro eq _ hnot
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hnot
          by_cases hexp : ∀ t : sub.E₀, aux.origEdge t ≠ eq
          · have hne_t : aux.Q.tail eq ≠ u := fun ht => by
              exact hnot ⟨hexp, ht.symm ▸ rfl, ht.symm ▸ rfl⟩
            have hne_h : aux.Q.head eq ≠ u := fun hh => by
              exact hnot ⟨hexp, (aux.edge_same_comp eq).trans (hh.symm ▸ rfl),
                (aux.exp_same_contractV eq hexp).trans (hh.symm ▸ rfl)⟩
            simp [hne_t, hne_h]
          · simp [Z, hexp]
      rw [hZ_bd, hsol_spec b x ⟨u, rfl, rfl⟩, add_neg_cancel]
    · obtain ⟨t, het⟩ := sub.edges_cover e heH
      rw [hpi_eq Y t e het]
      have hZ0 : Z (aux.origEdge t) = 0 := by
        simp only [Z]
        have hnot : ¬ ∀ t' : sub.E₀, aux.origEdge t' ≠ aux.origEdge t := fun hall => hall t rfl
        simp [hnot]
      simp only [Y, hY₀_orig t, hZ0, add_zero]
      exact (heqv ⟨h, hh⟩ t e het).symm

/-- **Lemma 3.6(d) (Projection of a cycle flow `x • χ_C` of `Q` decomposes into pairwise
edge-disjoint cycles of `H`).** -/
theorem lem_3_6_d
    {G : Multigraph V E} {H : G.Subgraph} (sub : SubdivisionData G H)
    (aux : AuxGraphData G H sub)
    (C : aux.Q.DirectedCycle) :
    ∃ (cycles : List G.DirectedCycle),
      (∀ O ∈ cycles, O.sub ≤ H) ∧
      (∀ i j (hi : i < cycles.length) (hj : j < cycles.length), i ≠ j →
        Disjoint (cycles[i]'hi).sub.edges (cycles[j]'hj).sub.edges) ∧
      (∀ (x : A) (e : E),
        aux.pi (fun eq => C.sign eq • x) e =
          (cycles.map (fun O => O.sign e • x)).sum) := by
  classical
  have hpiZ_flow : H.toMultigraph.IsFlow (fun e => aux.pi C.sign e.1) :=
    ((lem_3_6_c (A := ℤ) sub aux).1 C.sign C.isFlow).2
  have hunit : ∀ e : {e // e ∈ H.edges},
      aux.pi C.sign e.1 = -1 ∨ aux.pi C.sign e.1 = 0 ∨ aux.pi C.sign e.1 = 1 := by
    intro ⟨e, heH⟩
    have hex : ∃ t : sub.E₀, e ∈ (sub.thread t).edges := sub.edges_cover e heH
    simp only [AuxGraphData.pi, hex, ↓reduceDIte]
    by_cases hm : aux.origEdge hex.choose ∈ C.sub.edges
    · rcases C.sign_mem hm with h1 | h1
      · right; right; exact h1
      · left; exact h1
    · right; left; exact C.sign_zero hm
  obtain ⟨hcycles, hsum, _, _, _, hdisj⟩ := lem_2_1_b H.toMultigraph (fun e => aux.pi C.sign e.1) hpiZ_flow
  have hdisj' := hdisj hunit
  let cycles : List G.DirectedCycle := hcycles.map (liftDirectedCycle H)
  refine ⟨cycles, ?_, ?_, ?_⟩
  · intro O hO
    rcases List.mem_map.mp hO with ⟨O', _, rfl⟩
    exact liftDirectedCycle_le H O'
  · intro i j hi hj hij
    simp only [cycles, List.length_map] at hi hj
    simp only [cycles, List.getElem_map, liftDirectedCycle]
    rw [Finset.disjoint_left]
    intro e hei hej
    rcases Finset.mem_image.mp hei with ⟨e₁, he₁, rfl⟩
    rcases Finset.mem_image.mp hej with ⟨e₂, he₂, heq⟩
    have h12 : e₁ = e₂ := Subtype.ext heq.symm
    subst h12
    exact Finset.disjoint_left.mp (hdisj' i j hi hj hij) he₁ he₂
  · intro x e
    have hlist_zsmul : ∀ (l : List G.DirectedCycle),
        (l.map (fun O => O.sign e • x)).sum = (l.map (fun O => O.sign e)).sum • x := by
      intro l
      induction l with
      | nil => simp
      | cons a t ih => simp only [List.map_cons, List.sum_cons, ih, add_zsmul]
    rw [hlist_zsmul]
    by_cases heH : e ∈ H.edges
    · have hex : ∃ t : sub.E₀, e ∈ (sub.thread t).edges := sub.edges_cover e heH
      have hpi_scale : aux.pi (fun eq => C.sign eq • x) e = aux.pi C.sign e • x := by
        simp only [AuxGraphData.pi, hex, ↓reduceDIte]
      rw [hpi_scale]
      congr 1
      have h1 := hsum ⟨e, heH⟩
      rw [h1]
      simp only [cycles, List.map_map, Function.comp_def, liftDirectedCycle, heH, ↓reduceDIte]
    · have hnot_t : ¬ ∃ t : sub.E₀, e ∈ (sub.thread t).edges := by
        rintro ⟨t, het⟩; exact heH ((sub.thread t).edges_sub e het)
      simp only [AuxGraphData.pi, hnot_t, ↓reduceDIte]
      have h0 : (cycles.map (fun O => O.sign e)).sum = 0 := by
        apply List.sum_eq_zero
        intro z hz
        rcases List.mem_map.mp hz with ⟨O, hO, rfl⟩
        rcases List.mem_map.mp hO with ⟨O', _, rfl⟩
        simp [liftDirectedCycle, heH]
      rw [h0, zero_zsmul]

end Lemma36

end Flow.Proofs
