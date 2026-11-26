-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Flow.Defs.Literature
import Flow.Proofs.Elementary
import Flow.Proofs.Basic
import Flow.Proofs.Extraction
import Mathlib.Tactic

/-!
# Section 4 proofs (Part 1): Lemmas 4.1 through 4.6
-/

namespace Flow.Proofs

open Flow

/-! ### Lemma 4.1: Sparse zeros yield a good subgraph -/

private lemma multigraph_handshake {V E : Type} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (G : Multigraph V E) :
    ∑ v : V, G.deg v = 2 * Fintype.card E := by
  unfold Multigraph.deg
  rw [Finset.sum_add_distrib]
  have h1 : ∑ v : V, (Finset.univ.filter (fun e : E => G.tail e = v)).card = Fintype.card E := by
    rw [← Finset.card_biUnion]
    · convert Finset.card_univ (α := E); ext e; simp
    · intro u _ v _ huv; dsimp [Function.onFun]; rw [Finset.disjoint_left]
      intro e hu hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
      exact huv (hu.symm.trans hv)
  have h2 : ∑ v : V, (Finset.univ.filter (fun e : E => G.head e = v)).card = Fintype.card E := by
    rw [← Finset.card_biUnion]
    · convert Finset.card_univ (α := E); ext e; simp
    · intro u _ v _ huv; dsimp [Function.onFun]; rw [Finset.disjoint_left]
      intro e hu hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
      exact huv (hu.symm.trans hv)
  rw [h1, h2]; omega

private lemma deg_ge_three_of_edgeConn3 {V E : Type} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (G : Multigraph V E) (hll : G.IsLoopless) (h3 : G.IsEdgeConnected 3)
    (hn : 2 ≤ Fintype.card V) (v : V) : 3 ≤ G.deg v := by
  have hcomp_ne : (Finset.univ \ ({v} : Finset V)).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have hsub : (Finset.univ : Finset V) ⊆ {v} := Finset.sdiff_eq_empty_iff_subset.mp hempty
    have hcard : Fintype.card V ≤ 1 := by
      simpa using Finset.card_le_card hsub
    omega
  have hcut := h3 {v} (Finset.singleton_nonempty v) hcomp_ne
  have heq : G.cutEdges {v} =
      (Finset.univ.filter (fun e => G.tail e = v)) ∪
      (Finset.univ.filter (fun e => G.head e = v)) := by
    ext e
    simp only [Multigraph.cutEdges, Finset.mem_filter, Finset.mem_univ, Finset.mem_union,
      Finset.mem_singleton, true_and]
    have hne := hll e
    constructor
    · rintro (⟨h1, _⟩ | ⟨_, h2⟩)
      · exact Or.inl h1
      · exact Or.inr h2
    · rintro (h1 | h2)
      · exact Or.inl ⟨h1, fun h2 => hne (h1.trans h2.symm)⟩
      · exact Or.inr ⟨fun h1 => hne (h1.trans h2.symm), h2⟩
  have hdj : Disjoint (Finset.univ.filter (fun e => G.tail e = v))
      (Finset.univ.filter (fun e => G.head e = v)) := by
    rw [Finset.disjoint_left]
    intro e ht hh
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht hh
    exact hll e (ht.trans hh.symm)
  unfold Multigraph.deg
  rw [← Finset.card_union_of_disjoint hdj, ← heq]
  exact hcut

theorem lem_4_1_proved
    {Γ : Type} [AddCommGroup Γ] [Fintype Γ] [DecidableEq Γ]
    (B : AddSubgroup Γ) [DecidableEq (Γ ⧸ B)]
    (Sig : StepSystem Γ) (hAV : CondAV B Sig)
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : Multigraph V E) (hll : G.IsLoopless) (h3 : G.IsEdgeConnected 3)
    (hn : 2 ≤ Fintype.card V) (f : G.NZFlow Γ) :
    ∃ (f' : G.NZFlow Γ) (H : G.Subgraph),
      G.SigmaJoined Sig.carrier f f' ∧
      IsGoodSubgraph G H ∧
      ∀ e ∈ H.edges, quoFlow B f'.val e ≠ 0 := by
  obtain ⟨f', hjoin, hzeros⟩ := hAV V E G hll h3 hn f
  let S : Finset E := Finset.univ.filter (fun e => quoFlow B f'.val e ≠ 0)
  let Z : Finset E := Finset.univ.filter (fun e => quoFlow B f'.val e = 0)
  have hSZ : S.card + Z.card = Fintype.card E := by
    have hdj : Disjoint S Z := Finset.disjoint_left.mpr fun e h1 h2 =>
      (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2
    rw [← Finset.card_union_of_disjoint hdj]
    convert Finset.card_univ (α := E)
    ext e; simp only [S, Z, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  have hdeg_sum : 3 * Fintype.card V ≤ 2 * Fintype.card E := by
    rw [← multigraph_handshake G]
    calc 3 * Fintype.card V = ∑ _v : V, 3 := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
      _ ≤ ∑ v : V, G.deg v := Finset.sum_le_sum fun v _ => deg_ge_three_of_edgeConn3 G hll h3 hn v
  have hZ9 : 9 * Z.card ≤ Fintype.card E := hzeros
  have hS_bound : 4 * Fintype.card V ≤ 3 * S.card := by omega
  by_cases hn3 : 3 ≤ Fintype.card V
  · -- Restrict to G' = (V, S) and apply Lemma 3.2
    let G' : Multigraph V {e : E // e ∈ S} := ⟨fun e => G.tail e.1, fun e => G.head e.1⟩
    have hll' : G'.IsLoopless := fun e => hll e.1
    have hcardE' : Fintype.card {e : E // e ∈ S} = S.card := Fintype.card_coe S
    have hm' : 4 * Fintype.card V < 3 * Fintype.card {e : E // e ∈ S} + 6 := by omega
    obtain ⟨H', hH'good⟩ := lem_3_2 G' hll' hn3 hm'
    let H : G.Subgraph :=
      { verts := H'.verts
        edges := H'.edges.map ⟨Subtype.val, Subtype.val_injective⟩
        tail_mem := fun he => by
          rw [Finset.mem_map] at he; rcases he with ⟨e', he', rfl⟩
          exact H'.tail_mem he'
        head_mem := fun he => by
          rw [Finset.mem_map] at he; rcases he with ⟨e', he', rfl⟩
          exact H'.head_mem he' }
    refine ⟨f', H, hjoin, ?_, ?_⟩
    · rcases hH'good with ⟨hcyc, hle5, hv2⟩ | hsub'
      · left
        refine ⟨⟨⟨hcyc.1.1, fun u hu v hv => ?_⟩, fun v hv => ?_⟩, ?_, hv2⟩
        · have hpath := hcyc.1.2 u hu v hv
          clear hv
          induction hpath with
          | refl => exact .refl
          | tail _ hs ih =>
            rcases hs with ⟨e', he', h1 | h1⟩
            · exact ih.tail ⟨e'.1, Finset.mem_map.mpr ⟨e', he', rfl⟩, Or.inl h1⟩
            · exact ih.tail ⟨e'.1, Finset.mem_map.mpr ⟨e', he', rfl⟩, Or.inr h1⟩
        · have hd := hcyc.2 v hv
          unfold Multigraph.Subgraph.deg at hd ⊢
          have ht : (H.edges.filter (fun e => G.tail e = v)).card =
              (H'.edges.filter (fun e => G'.tail e = v)).card := by
            refine Finset.card_bij (fun e he => ⟨e, ?_⟩) (fun e he => ?_)
              (fun _ _ _ _ h => congrArg Subtype.val h) (fun e' he' => ⟨e'.1, ?_, rfl⟩)
            · have hm := (Finset.mem_filter.mp he).1
              rw [Finset.mem_map] at hm; rcases hm with ⟨e', _, rfl⟩; exact e'.2
            · rw [Finset.mem_filter] at he ⊢
              rw [Finset.mem_map] at he
              rcases he.1 with ⟨e', he', hval⟩
              have heq : e' = ⟨e, hval ▸ e'.2⟩ := Subtype.ext hval
              exact ⟨heq ▸ he', he.2⟩
            · rw [Finset.mem_filter] at he' ⊢
              exact ⟨Finset.mem_map.mpr ⟨e', he'.1, rfl⟩, he'.2⟩
          have hh : (H.edges.filter (fun e => G.head e = v)).card =
              (H'.edges.filter (fun e => G'.head e = v)).card := by
            refine Finset.card_bij (fun e he => ⟨e, ?_⟩) (fun e he => ?_)
              (fun _ _ _ _ h => congrArg Subtype.val h) (fun e' he' => ⟨e'.1, ?_, rfl⟩)
            · have hm := (Finset.mem_filter.mp he).1
              rw [Finset.mem_map] at hm; rcases hm with ⟨e', _, rfl⟩; exact e'.2
            · rw [Finset.mem_filter] at he ⊢
              rw [Finset.mem_map] at he
              rcases he.1 with ⟨e', he', hval⟩
              have heq : e' = ⟨e, hval ▸ e'.2⟩ := Subtype.ext hval
              exact ⟨heq ▸ he', he.2⟩
            · rw [Finset.mem_filter] at he' ⊢
              exact ⟨Finset.mem_map.mpr ⟨e', he'.1, rfl⟩, he'.2⟩
          rw [ht, hh]; exact hd
        · simpa [H] using hle5
      · right
        rcases hsub' with ⟨sub'⟩
        refine ⟨{
          V₀ := sub'.V₀
          E₀ := sub'.E₀
          H₀ := sub'.H₀
          loopless := sub'.loopless
          edgeConn3 := sub'.edgeConn3
          card_ge_two := sub'.card_ge_two
          embedV := sub'.embedV
          embedV_mem := sub'.embedV_mem
          thread := fun t =>
            { verts := (sub'.thread t).verts
              edges := (sub'.thread t).edges.map Subtype.val
              len_pos := by simpa using (sub'.thread t).len_pos
              len_le := by simpa using (sub'.thread t).len_le
              verts_len := by simpa using (sub'.thread t).verts_len
              verts_nodup := (sub'.thread t).verts_nodup
              verts_sub := (sub'.thread t).verts_sub
              edges_sub := fun e he => by
                rw [List.mem_map] at he; rcases he with ⟨e', he', rfl⟩
                exact Finset.mem_map.mpr ⟨e', (sub'.thread t).edges_sub e' he', rfl⟩
              head_eq := (sub'.thread t).head_eq
              last_eq := (sub'.thread t).last_eq
              step_connect := fun i hi => by
                have hi' : i < (sub'.thread t).edges.length := by simpa using hi
                simpa using (sub'.thread t).step_connect i hi' }
          edges_disjoint := fun t₁ t₂ hne e he₁ he₂ => by
            rw [List.mem_map] at he₁ he₂
            rcases he₁ with ⟨e₁, he₁, rfl⟩
            rcases he₂ with ⟨e₂, he₂, heq⟩
            have : e₁ = e₂ := Subtype.ext heq.symm
            subst this
            exact sub'.edges_disjoint t₁ t₂ hne e₁ he₁ he₂
          edges_cover := fun e heH => by
            rw [Finset.mem_map] at heH; rcases heH with ⟨e', he', rfl⟩
            obtain ⟨t, ht⟩ := sub'.edges_cover e' he'
            exact ⟨t, List.mem_map.mpr ⟨e', ht, rfl⟩⟩
          interior_disjoint_branch := sub'.interior_disjoint_branch
          interior_disjoint := sub'.interior_disjoint
          verts_cover := sub'.verts_cover }⟩
    · intro e heH
      rw [Finset.mem_map] at heH; rcases heH with ⟨e', _, rfl⟩
      exact (Finset.mem_filter.mp e'.2).2
  · -- Case |V| = 2: S.card ≥ 3 ≥ 2, two parallel edges form a 2-cycle
    have hn2 : Fintype.card V = 2 := by omega
    have hS2 : 2 ≤ S.card := by omega
    obtain ⟨e₁, he₁, e₂, he₂, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
    have hV_two : ∀ v : V, v = G.tail e₁ ∨ v = G.head e₁ := by
      intro v
      have hpair : ({G.tail e₁, G.head e₁} : Finset V).card = 2 := Finset.card_pair (hll e₁)
      have huniv : ({G.tail e₁, G.head e₁} : Finset V) = Finset.univ :=
        Finset.eq_univ_of_card _ (by rw [hpair, hn2])
      have hv : v ∈ ({G.tail e₁, G.head e₁} : Finset V) := by rw [huniv]; exact Finset.mem_univ v
      simpa using hv
    have he₂_ends : (G.tail e₂ = G.tail e₁ ∧ G.head e₂ = G.head e₁) ∨
        (G.tail e₂ = G.head e₁ ∧ G.head e₂ = G.tail e₁) := by
      rcases hV_two (G.tail e₂) with ht | ht <;> rcases hV_two (G.head e₂) with hh | hh
      · exact absurd (ht.trans hh.symm) (hll e₂)
      · exact Or.inl ⟨ht, hh⟩
      · exact Or.inr ⟨ht, hh⟩
      · exact absurd (ht.trans hh.symm) (hll e₂)
    let H : G.Subgraph :=
      { verts := {G.tail e₁, G.head e₁}
        edges := {e₁, e₂}
        tail_mem := fun he => by
          simp only [Finset.mem_insert, Finset.mem_singleton] at he ⊢
          rcases he with heq | heq
          · rw [heq]; exact Or.inl rfl
          · rw [heq]; exact hV_two (G.tail e₂)
        head_mem := fun he => by
          simp only [Finset.mem_insert, Finset.mem_singleton] at he ⊢
          rcases he with heq | heq
          · rw [heq]; exact Or.inr rfl
          · rw [heq]; exact hV_two (G.head e₂) }
    refine ⟨f', H, hjoin, Or.inl ⟨?_, ?_, ?_⟩, ?_⟩
    · refine ⟨⟨⟨G.tail e₁, Finset.mem_insert_self _ _⟩, fun u hu v hv => ?_⟩, fun v hv => ?_⟩
      · simp only [H, Finset.mem_insert, Finset.mem_singleton] at hu hv
        rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
        · exact .refl
        · exact Relation.ReflTransGen.single ⟨e₁, Finset.mem_insert_self _ _, Or.inl ⟨rfl, rfl⟩⟩
        · exact Relation.ReflTransGen.single ⟨e₁, Finset.mem_insert_self _ _, Or.inr ⟨rfl, rfl⟩⟩
        · exact .refl
      · simp only [H, Finset.mem_insert, Finset.mem_singleton] at hv
        unfold Multigraph.Subgraph.deg
        have hth := hll e₁
        rcases hv with rfl | rfl
        · rcases he₂_ends with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · have hf1 : ({e₁, e₂} : Finset E).filter (fun e => G.tail e = G.tail e₁) = {e₁, e₂} := by
              ext e; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
              constructor
              · exact fun h => h.1
              · rintro (rfl | rfl) <;> simp [h1]
            have hf2 : ({e₁, e₂} : Finset E).filter (fun e => G.head e = G.tail e₁) = ∅ := by
              ext e; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
                Finset.notMem_empty, iff_false, not_and]
              rintro (rfl | rfl) h
              · exact hth h.symm
              · exact hth (h2.symm.trans h).symm
            simp only [H, hf1, hf2, Finset.card_pair hne, Finset.card_empty]
          · have hf1 : ({e₁, e₂} : Finset E).filter (fun e => G.tail e = G.tail e₁) = {e₁} := by
              ext e; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
              constructor
              · rintro ⟨rfl | rfl, h⟩
                · rfl
                · exact absurd (h.symm.trans h1) hth
              · rintro rfl; exact ⟨Or.inl rfl, rfl⟩
            have hf2 : ({e₁, e₂} : Finset E).filter (fun e => G.head e = G.tail e₁) = {e₂} := by
              ext e; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
              constructor
              · rintro ⟨rfl | rfl, h⟩
                · exact absurd h.symm hth
                · rfl
              · rintro rfl; exact ⟨Or.inr rfl, h2⟩
            simp only [H, hf1, hf2, Finset.card_singleton]
        · rcases he₂_ends with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · have hf1 : ({e₁, e₂} : Finset E).filter (fun e => G.tail e = G.head e₁) = ∅ := by
              ext e; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
                Finset.notMem_empty, iff_false, not_and]
              rintro (rfl | rfl) h
              · exact hth h
              · exact hth (h1.symm.trans h)
            have hf2 : ({e₁, e₂} : Finset E).filter (fun e => G.head e = G.head e₁) = {e₁, e₂} := by
              ext e; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
              constructor
              · exact fun h => h.1
              · rintro (rfl | rfl) <;> simp [h2]
            simp only [H, hf1, hf2, Finset.card_pair hne, Finset.card_empty]
          · have hf1 : ({e₁, e₂} : Finset E).filter (fun e => G.tail e = G.head e₁) = {e₂} := by
              ext e; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
              constructor
              · rintro ⟨rfl | rfl, h⟩
                · exact absurd h hth
                · rfl
              · rintro rfl; exact ⟨Or.inr rfl, h1⟩
            have hf2 : ({e₁, e₂} : Finset E).filter (fun e => G.head e = G.head e₁) = {e₁} := by
              ext e; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
              constructor
              · rintro ⟨rfl | rfl, h⟩
                · rfl
                · exact absurd (h2.symm.trans h) hth
              · rintro rfl; exact ⟨Or.inl rfl, rfl⟩
            simp only [H, hf1, hf2, Finset.card_singleton]
    · simp only [H, Finset.card_pair hne]; decide
    · simp only [H, Finset.card_pair (hll e₁)]; decide
    · intro e heH
      simp only [H, Finset.mem_insert, Finset.mem_singleton] at heH
      rcases heH with rfl | rfl
      · exact (Finset.mem_filter.mp he₁).2
      · exact (Finset.mem_filter.mp he₂).2

/-! ### Lemma 4.2(a) & 4.2(b): Reverse choice -/

private lemma zsmul_pm_one_cancel {A : Type} [AddCommGroup A] {s : ℤ}
    (hs : s = 1 ∨ s = -1) (x : A) : s • (s • x) = x := by
  rcases hs with rfl | rfl <;> simp

private lemma avoid_finset_card {A : Type} [AddCommGroup A] [Fintype A] [DecidableEq A]
    (s : ℤ) (hs : s = 1 ∨ s = -1) (z : A) (L : Finset A) :
    (Finset.univ.filter (fun c : A => z + s • c ∈ L)).card ≤ L.card := by
  have hsub : Finset.univ.filter (fun c : A => z + s • c ∈ L) ⊆
      L.image (fun a => s • (a - z)) := by
    intro c hc
    rw [Finset.mem_filter] at hc
    rw [Finset.mem_image]
    refine ⟨z + s • c, hc.2, ?_⟩
    rw [add_sub_cancel_left, zsmul_pm_one_cancel hs]
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

theorem lem_4_2_a_of
    {V E A : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    [AddCommGroup A] [Fintype A] [DecidableEq A]
    {G : Multigraph V E} {H : G.Subgraph} {sub : SubdivisionData G H}
    {aux : AuxGraphData G H sub} (fr : Frame G H sub aux)
    (C : Fin fr.numNodes → aux.Q.DirectedCycle)
    (hO2 : ∀ i, fr.eNode i ∈ (C i).sub.edges ∧ fr.fNode i ∈ (C i).sub.edges)
    (hO3 : ∀ l i : Fin fr.numNodes, l < i →
      fr.eNode i ∉ (C l).sub.edges ∧ fr.fNode i ∉ (C l).sub.edges)
    (Lam : ListAssignment (A := A) fr)
    (hcard : ∀ i : Fin fr.numNodes,
      (Lam.list (fr.eNode i)).card + (Lam.list (fr.fNode i)).card < Fintype.card A)
    (Y₀ : aux.EQ → A) (hY₀ : aux.Q.IsFlow Y₀) :
    ∃ x : Fin fr.numNodes → A,
      (fun eq => Y₀ eq + ∑ i : Fin fr.numNodes, (C i).sign eq • x i) ∈ PLam Lam := by
  let s := fr.numNodes
  let evalY (x : Fin s → A) (eq : aux.EQ) : A := Y₀ eq + ∑ j : Fin s, (C j).sign eq • x j
  have hstep : ∀ k : ℕ, k ≤ s →
      ∃ x : Fin s → A,
        (∀ j : Fin s, j.1 < s - k → x j = 0) ∧
        (∀ i : Fin s, s - k ≤ i.1 →
          evalY x (fr.eNode i) ∉ Lam.list (fr.eNode i) ∧
          evalY x (fr.fNode i) ∉ Lam.list (fr.fNode i)) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨fun _ => 0, fun _ _ => rfl, fun i hi => by omega⟩
    | succ k ih =>
      intro hk
      obtain ⟨x, hx0, hxok⟩ := ih (by omega)
      let i₀ : Fin s := ⟨s - (k + 1), by omega⟩
      have hxi₀ : x i₀ = 0 := hx0 i₀ (by dsimp [i₀]; omega)
      let badE : Finset A := Finset.univ.filter (fun c : A =>
        evalY x (fr.eNode i₀) + (C i₀).sign (fr.eNode i₀) • c ∈ Lam.list (fr.eNode i₀))
      let badF : Finset A := Finset.univ.filter (fun c : A =>
        evalY x (fr.fNode i₀) + (C i₀).sign (fr.fNode i₀) • c ∈ Lam.list (fr.fNode i₀))
      have hbadE : badE.card ≤ (Lam.list (fr.eNode i₀)).card :=
        avoid_finset_card _ ((C i₀).sign_mem (hO2 i₀).1) _ _
      have hbadF : badF.card ≤ (Lam.list (fr.fNode i₀)).card :=
        avoid_finset_card _ ((C i₀).sign_mem (hO2 i₀).2) _ _
      have hbad_lt : (badE ∪ badF).card < Fintype.card A := by
        calc (badE ∪ badF).card ≤ badE.card + badF.card := Finset.card_union_le _ _
          _ ≤ (Lam.list (fr.eNode i₀)).card + (Lam.list (fr.fNode i₀)).card := add_le_add hbadE hbadF
          _ < Fintype.card A := hcard i₀
      have hex : (Finset.univ \ (badE ∪ badF)).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro he
        have hsub : (Finset.univ : Finset A) ⊆ badE ∪ badF := Finset.sdiff_eq_empty_iff_subset.mp he
        have := Finset.card_le_card hsub
        rw [Finset.card_univ] at this
        omega
      obtain ⟨c, hc⟩ := hex
      rw [Finset.mem_sdiff, Finset.mem_union, not_or] at hc
      have hcE : c ∉ badE := hc.2.1
      have hcF : c ∉ badF := hc.2.2
      let x' : Fin s → A := Function.update x i₀ c
      have heval_x' : ∀ eq : aux.EQ, evalY x' eq = evalY x eq + (C i₀).sign eq • c := by
        intro eq
        dsimp only [evalY, x']
        have hsum : ∑ j : Fin s, (C j).sign eq • Function.update x i₀ c j =
            (∑ j : Fin s, (C j).sign eq • x j) + (C i₀).sign eq • c := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀),
              ← Finset.add_sum_erase _ (fun j => (C j).sign eq • x j) (Finset.mem_univ i₀)]
          simp only [Function.update_self, hxi₀, smul_zero, zero_add]
          have heq : ∑ j ∈ Finset.univ.erase i₀, (C j).sign eq • Function.update x i₀ c j =
              ∑ j ∈ Finset.univ.erase i₀, (C j).sign eq • x j := by
            refine Finset.sum_congr rfl fun j hj => ?_
            rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
          rw [heq, add_comm]
        rw [hsum, add_assoc]
      refine ⟨x', fun j hj => ?_, fun i hi => ?_⟩
      · have hne : j ≠ i₀ := fun h => by subst h; dsimp [i₀] at hj; omega
        dsimp only [x']
        rw [Function.update_of_ne hne]
        exact hx0 j (by omega)
      · by_cases hi_eq : i = i₀
        · subst hi_eq
          rw [heval_x', heval_x']
          exact ⟨fun h => hcE (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩),
                 fun h => hcF (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)⟩
        · have hlt : i₀ < i := by
            show i₀.1 < i.1; dsimp [i₀]
            have : i.1 ≠ s - (k + 1) := fun h => hi_eq (Fin.ext h)
            omega
          have hno := hO3 i₀ i hlt
          rw [heval_x', heval_x', (C i₀).sign_zero hno.1, (C i₀).sign_zero hno.2,
              zero_zsmul, add_zero, add_zero]
          have hlt' : s - (k + 1) < i.1 := hlt
          exact hxok i (by omega)
  obtain ⟨x, _, hok⟩ := hstep s le_rfl
  refine ⟨x, ?_, ?_⟩
  · refine isFlow_add hY₀ (isFlow_finset_sum Finset.univ fun i _ => isFlow_zsmul (C i).isFlow (x i))
  · intro t ht
    obtain ⟨i, hi, _⟩ := fr.blue_unique t ht
    have hok_i := hok i (by omega)
    rcases hi with rfl | rfl
    · exact hok_i.1
    · exact hok_i.2

theorem lem_4_2_b_of
    {V E A : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    [AddCommGroup A] [Fintype A] [DecidableEq A]
    {G : Multigraph V E} {H : G.Subgraph} {sub : SubdivisionData G H}
    {aux : AuxGraphData G H sub} (fr : Frame G H sub aux)
    (C : Fin fr.numNodes → aux.Q.DirectedCycle)
    (hO2 : ∀ i, fr.eNode i ∈ (C i).sub.edges ∧ fr.fNode i ∈ (C i).sub.edges)
    (hO3 : ∀ l i : Fin fr.numNodes, l < i →
      fr.eNode i ∉ (C l).sub.edges ∧ fr.fNode i ∉ (C l).sub.edges)
    (hO5Z : ∀ Y : aux.EQ → ℤ, aux.Q.IsFlow Y →
      ∃! x : Fin fr.numNodes → ℤ, ∀ eq, Y eq = ∑ i : Fin fr.numNodes, (C i).sign eq • x i) :
    (∀ eps : aux.EQ, eps ∉ fr.blue → ∃ i : Fin fr.numNodes, eps ∈ (C i).sub.edges) ∧
    (∀ (Lam : ListAssignment (A := A) fr) (E' : Finset aux.EQ)
      (hE' : ∀ eps ∈ E', eps ∉ fr.blue)
      (Phi : aux.EQ → Finset A)
      (leastIdx : aux.EQ → Fin fr.numNodes)
      (hleast : ∀ eps ∈ E',
        eps ∈ (C (leastIdx eps)).sub.edges ∧
        ∀ j : Fin fr.numNodes, eps ∈ (C j).sub.edges → leastIdx eps ≤ j),
      (∀ i : Fin fr.numNodes,
        (Lam.list (fr.eNode i)).card + (Lam.list (fr.fNode i)).card +
        ∑ eps ∈ E'.filter (fun eps => leastIdx eps = i), (Phi eps).card < Fintype.card A) →
      ∃ Y ∈ PLam Lam, ∀ eps ∈ E', Y eps ∉ Phi eps) := by
  constructor
  · -- Part 1: Every red edge lies on at least one official cycle
    intro eps heps_red
    let b := aux.comp (aux.Q.tail eps)
    let Vb := Finset.univ.filter (fun v => aux.comp v = b)
    let Hb := Multigraph.Subgraph.induced aux.Q Vb
    let Qb := Hb.toMultigraph
    obtain ⟨wc, hwc⟩ := fr.comp_wc b
    have heps_Hb : eps ∈ Hb.edges := by
      simp only [Hb, Multigraph.Subgraph.induced, Finset.mem_filter, Finset.mem_univ, true_and, Vb]
      exact ⟨rfl, (aux.edge_same_comp eps).symm⟩
    let epsQb : {e : aux.EQ // e ∈ Hb.edges} := ⟨eps, heps_Hb⟩
    let Tb := Multigraph.Subgraph.ofEdges Qb Finset.univ wc.blue
      (fun _ => Finset.mem_univ _) (fun _ => Finset.mem_univ _)
    have hTb_sf : Tb.IsSpanningForest :=
      ⟨wc.blue_tree.1, wc.blue_tree.2.2, fun u v _ =>
        wc.blue_tree.2.1.2 u (Finset.mem_univ _) v (Finset.mem_univ _)⟩
    have heps_not_Tb : epsQb ∉ Tb.edges := by
      intro hmem
      exact heps_red ((hwc epsQb).mp hmem)
    obtain ⟨FQb, hFQb, _⟩ := existsUnique_fundamentalCycle Qb Tb hTb_sf epsQb heps_not_Tb
    let Fval : aux.EQ → ℤ := fun eq => if h : eq ∈ Hb.edges then FQb.sign ⟨eq, h⟩ else 0
    have hF_flow : aux.Q.IsFlow Fval := by
      intro u
      by_cases hu : u ∈ Hb.verts
      · have hbd := FQb.isFlow ⟨u, hu⟩
        trans (Qb.boundary FQb.sign ⟨u, hu⟩)
        · rw [boundary_eq_sum_ite, boundary_eq_sum_ite]
          rw [← Finset.sum_subset (Finset.subset_univ Hb.edges)]
          · refine Finset.sum_bij (fun eq heq => ⟨eq, heq⟩) (fun _ _ => Finset.mem_univ _)
              (fun _ _ _ _ h => congrArg Subtype.val h) (fun eq _ => ⟨eq.1, eq.2, rfl⟩) (fun eq heq => ?_)
            dsimp only [Fval, Qb, Multigraph.Subgraph.toMultigraph]
            rw [dif_pos heq]
            by_cases h1 : aux.Q.head eq = u <;> by_cases h2 : aux.Q.tail eq = u <;>
              simp [Subtype.ext_iff, h1, h2]
          · intro eq _ hnot
            dsimp only [Fval]
            rw [dif_neg hnot]
            simp
        · exact hbd
      · rw [boundary_eq_sum_ite]
        refine Finset.sum_eq_zero fun eq _ => ?_
        by_cases heq : eq ∈ Hb.edges
        · have ht : aux.Q.tail eq ≠ u := fun h => hu (h ▸ Hb.tail_mem heq)
          have hh : aux.Q.head eq ≠ u := fun h => hu (h ▸ Hb.head_mem heq)
          simp [ht, hh]
        · simp [Fval, heq]
    obtain ⟨x, hx, _⟩ := hO5Z Fval hF_flow
    have hFeps : Fval eps = 1 := by
      simp only [Fval, heps_Hb, ↓reduceDIte]
      exact hFQb.2
    have hsum1 : ∑ i : Fin fr.numNodes, (C i).sign eps • x i = 1 := by
      rw [← hx eps, hFeps]
    by_contra hall
    push Not at hall
    have hsum0 : ∑ i : Fin fr.numNodes, (C i).sign eps • x i = 0 :=
      Finset.sum_eq_zero fun i _ => by rw [(C i).sign_zero (hall i), zero_zsmul]
    omega
  · -- Part 2: Reverse choice avoiding Lam on blue edges and Phi on E'
    intro Lam E' _ Phi leastIdx hleast hcard
    let s := fr.numNodes
    let evalY (x : Fin s → A) (eq : aux.EQ) : A := ∑ j : Fin s, (C j).sign eq • x j
    have hstep : ∀ k : ℕ, k ≤ s →
        ∃ x : Fin s → A,
          (∀ j : Fin s, j.1 < s - k → x j = 0) ∧
          (∀ i : Fin s, s - k ≤ i.1 →
            evalY x (fr.eNode i) ∉ Lam.list (fr.eNode i) ∧
            evalY x (fr.fNode i) ∉ Lam.list (fr.fNode i)) ∧
          (∀ eps ∈ E', s - k ≤ (leastIdx eps).1 → evalY x eps ∉ Phi eps) := by
      intro k
      induction k with
      | zero =>
        intro _
        refine ⟨fun _ => 0, fun _ _ => rfl, fun i hi => by omega, fun eps _ hi => by omega⟩
      | succ k ih =>
        intro hk
        obtain ⟨x, hx0, hxok, hxE'⟩ := ih (by omega)
        let i₀ : Fin s := ⟨s - (k + 1), by omega⟩
        have hxi₀ : x i₀ = 0 := hx0 i₀ (by dsimp [i₀]; omega)
        let badE : Finset A := Finset.univ.filter (fun c : A =>
          evalY x (fr.eNode i₀) + (C i₀).sign (fr.eNode i₀) • c ∈ Lam.list (fr.eNode i₀))
        let badF : Finset A := Finset.univ.filter (fun c : A =>
          evalY x (fr.fNode i₀) + (C i₀).sign (fr.fNode i₀) • c ∈ Lam.list (fr.fNode i₀))
        let E'i := E'.filter (fun eps => leastIdx eps = i₀)
        let badPhi (eps : aux.EQ) : Finset A := Finset.univ.filter (fun c : A =>
          evalY x eps + (C i₀).sign eps • c ∈ Phi eps)
        let badAll : Finset A := badE ∪ badF ∪ E'i.biUnion badPhi
        have hbadE : badE.card ≤ (Lam.list (fr.eNode i₀)).card :=
          avoid_finset_card _ ((C i₀).sign_mem (hO2 i₀).1) _ _
        have hbadF : badF.card ≤ (Lam.list (fr.fNode i₀)).card :=
          avoid_finset_card _ ((C i₀).sign_mem (hO2 i₀).2) _ _
        have hbadPhi : (E'i.biUnion badPhi).card ≤ ∑ eps ∈ E'i, (Phi eps).card := by
          refine (Finset.card_biUnion_le).trans (Finset.sum_le_sum fun eps heps => ?_)
          rw [Finset.mem_filter] at heps
          have hmem : eps ∈ (C i₀).sub.edges := heps.2 ▸ (hleast eps heps.1).1
          exact avoid_finset_card _ ((C i₀).sign_mem hmem) _ _
        have hbad_lt : badAll.card < Fintype.card A := by
          calc badAll.card ≤ (badE ∪ badF).card + (E'i.biUnion badPhi).card := Finset.card_union_le _ _
            _ ≤ badE.card + badF.card + (E'i.biUnion badPhi).card :=
                add_le_add (Finset.card_union_le _ _) le_rfl
            _ ≤ (Lam.list (fr.eNode i₀)).card + (Lam.list (fr.fNode i₀)).card +
                ∑ eps ∈ E'i, (Phi eps).card :=
                add_le_add (add_le_add hbadE hbadF) hbadPhi
            _ < Fintype.card A := hcard i₀
        have hex : (Finset.univ \ badAll).Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]
          intro he
          have hsub : (Finset.univ : Finset A) ⊆ badAll := Finset.sdiff_eq_empty_iff_subset.mp he
          have := Finset.card_le_card hsub
          rw [Finset.card_univ] at this
          omega
        obtain ⟨c, hc⟩ := hex
        rw [Finset.mem_sdiff] at hc
        have hcnot : c ∉ badAll := hc.2
        have hcE : c ∉ badE := fun h => hcnot (Finset.mem_union_left _ (Finset.mem_union_left _ h))
        have hcF : c ∉ badF := fun h => hcnot (Finset.mem_union_left _ (Finset.mem_union_right _ h))
        have hcPhi : ∀ eps ∈ E'i, c ∉ badPhi eps := fun eps heps h =>
          hcnot (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨eps, heps, h⟩))
        let x' : Fin s → A := Function.update x i₀ c
        have heval_x' : ∀ eq : aux.EQ, evalY x' eq = evalY x eq + (C i₀).sign eq • c := by
          intro eq
          dsimp only [evalY, x']
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀),
              ← Finset.add_sum_erase _ (fun j => (C j).sign eq • x j) (Finset.mem_univ i₀)]
          simp only [Function.update_self, hxi₀, smul_zero, zero_add]
          have heq : ∑ j ∈ Finset.univ.erase i₀, (C j).sign eq • Function.update x i₀ c j =
              ∑ j ∈ Finset.univ.erase i₀, (C j).sign eq • x j :=
            Finset.sum_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
          rw [heq, add_comm]
        refine ⟨x', fun j hj => ?_, fun i hi => ?_, fun eps heps hi => ?_⟩
        · have hne : j ≠ i₀ := fun h => by subst h; dsimp [i₀] at hj; omega
          dsimp only [x']
          rw [Function.update_of_ne hne]
          exact hx0 j (by omega)
        · by_cases hi_eq : i = i₀
          · subst hi_eq
            rw [heval_x', heval_x']
            exact ⟨fun h => hcE (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩),
                   fun h => hcF (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)⟩
          · have hlt : i₀ < i := by
              show i₀.1 < i.1; dsimp [i₀]
              have : i.1 ≠ s - (k + 1) := fun h => hi_eq (Fin.ext h)
              omega
            have hno := hO3 i₀ i hlt
            rw [heval_x', heval_x', (C i₀).sign_zero hno.1, (C i₀).sign_zero hno.2,
                zero_zsmul, add_zero, add_zero]
            have hlt' : s - (k + 1) < i.1 := hlt
            exact hxok i (by omega)
        · by_cases hi_eq : leastIdx eps = i₀
          · rw [heval_x']
            intro hmem
            exact hcPhi eps (Finset.mem_filter.mpr ⟨heps, hi_eq⟩)
              (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem⟩)
          · have hlt : i₀ < leastIdx eps := by
              show i₀.1 < (leastIdx eps).1; dsimp [i₀]
              have : (leastIdx eps).1 ≠ s - (k + 1) := fun h => hi_eq (Fin.ext h)
              omega
            have hnot_in : eps ∉ (C i₀).sub.edges := fun hmem =>
              not_lt_of_ge ((hleast eps heps).2 i₀ hmem) hlt
            rw [heval_x', (C i₀).sign_zero hnot_in, zero_zsmul, add_zero]
            have hlt' : s - (k + 1) < (leastIdx eps).1 := hlt
            exact hxE' eps heps (by omega)
    obtain ⟨x, _, hok, hE'ok⟩ := hstep s le_rfl
    refine ⟨evalY x, ⟨?_, ?_⟩, fun eps heps => hE'ok eps heps (by omega)⟩
    · exact isFlow_finset_sum Finset.univ fun i _ => isFlow_zsmul (C i).isFlow (x i)
    · intro t ht
      obtain ⟨i, hi, _⟩ := fr.blue_unique t ht
      have hok_i := hok i (by omega)
      rcases hi with rfl | rfl
      · exact hok_i.1
      · exact hok_i.2

/-! ### Lemma 4.3: Walk lemma -/

theorem lem_4_3_of
    {V E Γ : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    [AddCommGroup Γ] [Fintype Γ] [DecidableEq Γ]
    (B : AddSubgroup Γ) [Fintype (Γ ⧸ B)] [DecidableEq (Γ ⧸ B)]
    (hA : 10 ≤ Fintype.card (Γ ⧸ B))
    (Sig : StepSystem Γ) (hR1 : CondR1 B Sig)
    {G : Multigraph V E} {H : G.Subgraph} {sub : SubdivisionData G H}
    {aux : AuxGraphData G H sub} (fr : Frame G H sub aux)
    (C : Fin fr.numNodes → aux.Q.DirectedCycle)
    (hO2 : ∀ i, fr.eNode i ∈ (C i).sub.edges ∧ fr.fNode i ∈ (C i).sub.edges)
    (hO3 : ∀ l i : Fin fr.numNodes, l < i →
      fr.eNode i ∉ (C l).sub.edges ∧ fr.fNode i ∉ (C l).sub.edges)
    (hO4 : ∀ l i : Fin fr.numNodes, i < l → fr.fNode i ∉ (C l).sub.edges)
    (hO5 : ∀ Y : aux.EQ → Γ ⧸ B, aux.Q.IsFlow Y →
      ∃! x : Fin fr.numNodes → Γ ⧸ B,
        ∀ eq, Y eq = ∑ i : Fin fr.numNodes, (C i).sign eq • x i)
    (Lam : ListAssignment (A := Γ ⧸ B) fr)
    (hLam : ∀ t ∈ fr.blue, (Lam.list t).card ≤ 3)
    (Y Y' : aux.EQ → Γ ⧸ B) (hY : Y ∈ PLam Lam) (hY' : Y' ∈ PLam Lam) :
    Relation.ReflTransGen
      (fun Z Z' => Z ∈ PLam Lam ∧ Z' ∈ PLam Lam ∧
        ∃ (σ : Γ ⧸ B) (l : Fin fr.numNodes), σ ∈ Sig.sigA B ∧
          ∀ eq, Z' eq = Z eq + (C l).sign eq • σ) Y Y' := by
  let s := fr.numNodes
  -- Define truncated list assignment LamAt k: active on nodes j with k ≤ j.1
  let LamAt (k : ℕ) : ListAssignment (A := Γ ⧸ B) fr :=
    { list := fun e =>
        if h : ∃ j : Fin s, k ≤ j.1 ∧ (e = fr.eNode j ∨ e = fr.fNode j) then Lam.list e else ∅
      empty_on_exp := fun e hexp => by
        split_ifs
        · exact Lam.empty_on_exp e hexp
        · rfl }
  let GoodStep (k : ℕ) (Z Z' : aux.EQ → Γ ⧸ B) : Prop :=
    Z ∈ PLam (LamAt k) ∧ Z' ∈ PLam (LamAt k) ∧
    ∃ (σ : Γ ⧸ B) (l : Fin s), σ ∈ Sig.sigA B ∧ ∀ eq, Z' eq = Z eq + (C l).sign eq • σ
  have hPLam_at_zero : ∀ Z, Z ∈ PLam (LamAt 0) ↔ Z ∈ PLam Lam := by
    intro Z
    constructor <;> rintro ⟨hfl, hbl⟩ <;> refine ⟨hfl, fun t ht => ?_⟩
    · obtain ⟨j, hj, _⟩ := fr.blue_unique t ht
      have hex : ∃ j : Fin s, 0 ≤ j.1 ∧ (t = fr.eNode j ∨ t = fr.fNode j) := ⟨j, Nat.zero_le _, hj⟩
      have h := hbl t ht
      dsimp only [LamAt] at h
      rw [dif_pos hex] at h
      exact h
    · have h := hbl t ht
      dsimp only [LamAt]
      split_ifs
      · exact h
      · exact Finset.notMem_empty _
  -- Downward induction on k from s down to 0 (formalized by induction on d = s - k)
  have hdown : ∀ d : ℕ, d ≤ s →
      ∀ Z₁ Z₂ : aux.EQ → Γ ⧸ B, Z₁ ∈ PLam (LamAt (s - d)) → Z₂ ∈ PLam (LamAt (s - d)) →
        Relation.ReflTransGen (GoodStep (s - d)) Z₁ Z₂ := by
    intro d
    induction d with
    | zero =>
      intro _ Z₁ Z₂ hZ₁ hZ₂
      have hPLam_s : ∀ Z, aux.Q.IsFlow Z → Z ∈ PLam (LamAt s) := by
        intro Z hfl
        refine ⟨hfl, fun t _ => ?_⟩
        have hno : ¬ ∃ j : Fin s, s ≤ j.1 ∧ (t = fr.eNode j ∨ t = fr.fNode j) := by
          rintro ⟨j, hj, _⟩; exact not_le_of_gt j.2 hj
        simp [LamAt, hno]
      obtain ⟨x, hx, _⟩ := hO5 (fun eq => Z₂ eq - Z₁ eq) (isFlow_sub hZ₂.1 hZ₁.1)
      -- Walk along each coordinate l ∈ Fin s one by one
      have hwalk_one : ∀ (Z : aux.EQ → Γ ⧸ B) (hZ : aux.Q.IsFlow Z) (l : Fin s) (a : Γ ⧸ B),
          Relation.ReflTransGen (GoodStep (s - 0)) Z (fun eq => Z eq + (C l).sign eq • a) := by
        intro Z hZ l a
        have hW := hR1 ∅ (by simp) 0 a (Finset.notMem_empty _) (Finset.notMem_empty _)
        rcases hW with ⟨_, _, hrtg⟩
        have hgen : ∀ u : Γ ⧸ B,
            Relation.ReflTransGen (fun x y => x ∈ {b : Γ ⧸ B | b ∉ (∅ : Finset _)} ∧
              y ∈ {b : Γ ⧸ B | b ∉ (∅ : Finset _)} ∧ ∃ σ ∈ Sig.sigA B, y = x + σ) 0 u →
            Relation.ReflTransGen (GoodStep (s - 0)) Z (fun eq => Z eq + (C l).sign eq • u) := by
          intro u hu
          induction hu with
          | refl =>
            have : (fun eq => Z eq + (C l).sign eq • (0 : Γ ⧸ B)) = Z := by
              ext eq; simp
            rw [this]
          | @tail u v _ hstep ih =>
            rcases hstep with ⟨_, _, σ, hσ, rfl⟩
            have hfl_u : aux.Q.IsFlow (fun eq => Z eq + (C l).sign eq • u) :=
              isFlow_add hZ (isFlow_zsmul (C l).isFlow u)
            have hfl_v : aux.Q.IsFlow (fun eq => Z eq + (C l).sign eq • (u + σ)) :=
              isFlow_add hZ (isFlow_zsmul (C l).isFlow (u + σ))
            refine ih.tail ⟨hPLam_s _ hfl_u, hPLam_s _ hfl_v, σ, l, hσ, fun eq => ?_⟩
            dsimp only
            rw [smul_add, add_assoc]
        exact hgen a hrtg
      -- Induct over Finset of coordinates
      have hwalk_set : ∀ (S : Finset (Fin s)),
          Relation.ReflTransGen (GoodStep (s - 0)) Z₁
            (fun eq => Z₁ eq + ∑ l ∈ S, (C l).sign eq • x l) := by
        intro S
        induction S using Finset.induction_on with
        | empty =>
          have : (fun eq => Z₁ eq + ∑ l ∈ (∅ : Finset (Fin s)), (C l).sign eq • x l) = Z₁ := by
            ext eq; simp
          rw [this]
        | @insert l S' hl ih =>
          have hfl : aux.Q.IsFlow (fun eq => Z₁ eq + ∑ j ∈ S', (C j).sign eq • x j) :=
            isFlow_add hZ₁.1 (isFlow_finset_sum S' fun j _ => isFlow_zsmul (C j).isFlow (x j))
          have hstep_l := hwalk_one _ hfl l (x l)
          have heq : (fun eq => (Z₁ eq + ∑ j ∈ S', (C j).sign eq • x j) + (C l).sign eq • x l) =
              (fun eq => Z₁ eq + ∑ j ∈ insert l S', (C j).sign eq • x j) := by
            ext eq
            rw [Finset.sum_insert hl]
            abel
          rw [heq] at hstep_l
          exact ih.trans hstep_l
      have hfin : (fun eq => Z₁ eq + ∑ l : Fin s, (C l).sign eq • x l) = Z₂ := by
        ext eq; rw [← hx eq]; abel
      rw [← hfin]
      exact hwalk_set Finset.univ
    | succ d ih =>
      intro hd Z₁ Z₂ hZ₁ hZ₂
      let i : ℕ := s - (d + 1)
      have hi_lt : i < s := by omega
      have hi_succ : i + 1 = s - d := by omega
      let i₀ : Fin s := ⟨i, hi_lt⟩
      have hsub_PLam : ∀ Z, Z ∈ PLam (LamAt i) → Z ∈ PLam (LamAt (i + 1)) := by
        rintro Z ⟨hfl, hbl⟩
        refine ⟨hfl, fun t ht => ?_⟩
        have h := hbl t ht
        dsimp only [LamAt] at h ⊢
        split_ifs with h1
        · rcases h1 with ⟨j, hj, hteq⟩
          have h2 : ∃ j : Fin s, i ≤ j.1 ∧ (t = fr.eNode j ∨ t = fr.fNode j) := ⟨j, by omega, hteq⟩
          rw [dif_pos h2] at h
          exact h
        · exact Finset.notMem_empty _
      let Xe (Z : aux.EQ → Γ ⧸ B) : Finset (Γ ⧸ B) :=
        Finset.univ.filter (fun c => Z (fr.eNode i₀) + (C i₀).sign (fr.eNode i₀) • c ∈ Lam.list (fr.eNode i₀))
      let Xf (Z : aux.EQ → Γ ⧸ B) : Finset (Γ ⧸ B) :=
        Finset.univ.filter (fun c => Z (fr.fNode i₀) + (C i₀).sign (fr.fNode i₀) • c ∈ Lam.list (fr.fNode i₀))
      let X (Z : aux.EQ → Γ ⧸ B) : Finset (Γ ⧸ B) := Xe Z ∪ Xf Z
      have hXe_le : ∀ Z, (Xe Z).card ≤ 3 := fun Z =>
        (avoid_finset_card _ ((C i₀).sign_mem (hO2 i₀).1) _ _).trans (hLam _ (fr.e_blue i₀))
      have hXf_le : ∀ Z, (Xf Z).card ≤ 3 := fun Z =>
        (avoid_finset_card _ ((C i₀).sign_mem (hO2 i₀).2) _ _).trans (hLam _ (fr.f_blue i₀))
      have hX_le : ∀ Z, (X Z).card ≤ 6 := fun Z =>
        (Finset.card_union_le _ _).trans (by have := hXe_le Z; have := hXf_le Z; omega)
      -- Key equivalence (*)
      have hstar : ∀ Z, Z ∈ PLam (LamAt (i + 1)) → ∀ c : Γ ⧸ B,
          (fun eq => Z eq + (C i₀).sign eq • c) ∈ PLam (LamAt i) ↔ c ∉ X Z := by
        intro Z hZ c
        have hfl_c : aux.Q.IsFlow (fun eq => Z eq + (C i₀).sign eq • c) :=
          isFlow_add hZ.1 (isFlow_zsmul (C i₀).isFlow c)
        constructor
        · intro hZc hc
          rw [Finset.mem_union] at hc
          rcases hc with hcE | hcF
          · rw [Finset.mem_filter] at hcE
            have hmem := hZc.2 (fr.eNode i₀) (fr.e_blue i₀)
            have hex : ∃ j : Fin s, i ≤ j.1 ∧ (fr.eNode i₀ = fr.eNode j ∨ fr.eNode i₀ = fr.fNode j) :=
              ⟨i₀, le_rfl, Or.inl rfl⟩
            simp only [LamAt, hex, ↓reduceDIte] at hmem
            exact hmem hcE.2
          · rw [Finset.mem_filter] at hcF
            have hmem := hZc.2 (fr.fNode i₀) (fr.f_blue i₀)
            have hex : ∃ j : Fin s, i ≤ j.1 ∧ (fr.fNode i₀ = fr.eNode j ∨ fr.fNode i₀ = fr.fNode j) :=
              ⟨i₀, le_rfl, Or.inr rfl⟩
            simp only [LamAt, hex, ↓reduceDIte] at hmem
            exact hmem hcF.2
        · intro hc
          refine ⟨hfl_c, fun t ht => ?_⟩
          dsimp only [LamAt]
          split_ifs with hex
          · rcases hex with ⟨j, hj, hteq⟩
            by_cases hj_eq : j = i₀
            · subst hj_eq
              rcases hteq with rfl | rfl
              · intro hmem
                exact hc (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem⟩))
              · intro hmem
                exact hc (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem⟩))
            · have hlt : i₀ < j := by
                show i₀.1 < j.1; dsimp [i₀]
                have : j.1 ≠ i := fun h => hj_eq (Fin.ext h)
                omega
              have hno := hO3 i₀ j hlt
              have hsign0 : (C i₀).sign t = 0 := by
                rcases hteq with rfl | rfl
                · exact (C i₀).sign_zero hno.1
                · exact (C i₀).sign_zero hno.2
              rw [hsign0, zero_zsmul, add_zero]
              have hlt' : i < j.1 := hlt
              have hex' : ∃ j' : Fin s, i + 1 ≤ j'.1 ∧ (t = fr.eNode j' ∨ t = fr.fNode j') :=
                ⟨j, by omega, hteq⟩
              have hmem := hZ.2 t ht
              dsimp only [LamAt] at hmem
              rw [dif_pos hex'] at hmem
              exact hmem
          · exact Finset.notMem_empty _
      -- Lift a WalkIn outside X Z to a GoodStep i walk along C i₀
      have hwalk_Ci : ∀ (Z : aux.EQ → Γ ⧸ B) (hZ : Z ∈ PLam (LamAt (i + 1))) (c₁ c₂ : Γ ⧸ B),
          c₁ ∉ X Z → c₂ ∉ X Z →
          Relation.ReflTransGen (GoodStep i)
            (fun eq => Z eq + (C i₀).sign eq • c₁)
            (fun eq => Z eq + (C i₀).sign eq • c₂) := by
        intro Z hZ c₁ c₂ hc₁ hc₂
        obtain ⟨_, h2, hrtg⟩ := hR1 (X Z) (hX_le Z) c₁ c₂ hc₁ hc₂
        clear h2 hc₂
        induction hrtg with
        | refl => exact .refl
        | @tail u v _ hstep ih' =>
          rcases hstep with ⟨hu, hv, σ, hσ, rfl⟩
          refine ih'.tail ⟨(hstar Z hZ u).mpr hu, (hstar Z hZ (u + σ)).mpr hv, σ, i₀, hσ, fun eq => ?_⟩
          dsimp only
          rw [smul_add, add_assoc]
      -- Get walk in PLam (LamAt (i + 1)) from IH
      have hwalk_up : Relation.ReflTransGen (GoodStep (i + 1)) Z₁ Z₂ := by
        rw [hi_succ]
        exact ih (by omega) Z₁ Z₂ (hi_succ ▸ hsub_PLam Z₁ hZ₁) (hi_succ ▸ hsub_PLam Z₂ hZ₂)
      have htrack : ∀ Z, Relation.ReflTransGen (GoodStep (i + 1)) Z₁ Z →
          ∃ c : Γ ⧸ B, c ∉ X Z ∧
            Relation.ReflTransGen (GoodStep i) Z₁ (fun eq => Z eq + (C i₀).sign eq • c) := by
        intro Z hrtg
        induction hrtg with
        | refl =>
          have h0 : (0 : Γ ⧸ B) ∉ X Z₁ := by
            have h0eq : (fun eq => Z₁ eq + (C i₀).sign eq • (0 : Γ ⧸ B)) = Z₁ := by ext eq; simp
            exact (hstar Z₁ (hsub_PLam Z₁ hZ₁) 0).mp (h0eq.symm ▸ hZ₁)
          refine ⟨0, h0, ?_⟩
          have h0eq : (fun eq => Z₁ eq + (C i₀).sign eq • (0 : Γ ⧸ B)) = Z₁ := by ext eq; simp
          rw [h0eq]
        | @tail Z Z' _ hstep ih' =>
          obtain ⟨c, hc, hpath⟩ := ih'
          rcases hstep with ⟨hZ, hZ', σ, l, hσ, hZ'eq⟩
          by_cases hl_eq : l = i₀
          · -- Case (i): l = i₀, set c' = c - σ
            subst hl_eq
            have hsame : (fun eq => Z' eq + (C i₀).sign eq • (c - σ)) =
                (fun eq => Z eq + (C i₀).sign eq • c) := by
              ext eq; rw [hZ'eq eq, smul_sub]; abel
            have hc' : c - σ ∉ X Z' :=
              (hstar Z' hZ' (c - σ)).mp (hsame.symm ▸ (hstar Z hZ c).mpr hc)
            exact ⟨c - σ, hc', hsame.symm ▸ hpath⟩
          · by_cases hl_lt : l < i₀
            · -- Case (ii): l < i₀, C l avoids eNode i₀ and fNode i₀
              have hno := hO3 l i₀ hl_lt
              have hZ'e : Z' (fr.eNode i₀) = Z (fr.eNode i₀) := by
                rw [hZ'eq, (C l).sign_zero hno.1, zero_zsmul, add_zero]
              have hZ'f : Z' (fr.fNode i₀) = Z (fr.fNode i₀) := by
                rw [hZ'eq, (C l).sign_zero hno.2, zero_zsmul, add_zero]
              have hXeq : X Z' = X Z := by
                simp only [X, Xe, Xf, hZ'e, hZ'f]
              have hc' : c ∉ X Z' := hXeq ▸ hc
              refine ⟨c, hc', hpath.tail ⟨(hstar Z hZ c).mpr hc, (hstar Z' hZ' c).mpr hc',
                σ, l, hσ, fun eq => ?_⟩⟩
              dsimp only
              rw [hZ'eq eq]; abel
            · -- Case (iii): i₀ < l, C l avoids fNode i₀
              have hl_gt : i₀ < l := lt_of_le_of_ne (not_lt.mp hl_lt) (Ne.symm hl_eq)
              have hnof := hO4 l i₀ hl_gt
              have hZ'f : Z' (fr.fNode i₀) = Z (fr.fNode i₀) := by
                rw [hZ'eq, (C l).sign_zero hnof, zero_zsmul, add_zero]
              have hXfeq : Xf Z' = Xf Z := by simp only [Xf, hZ'f]
              have hunion : X Z ∪ X Z' = Xe Z ∪ Xe Z' ∪ Xf Z := by
                ext a; simp only [X, hXfeq, Finset.mem_union]; tauto
              have hcard_lt : (X Z ∪ X Z').card < Fintype.card (Γ ⧸ B) := by
                rw [hunion]
                calc (Xe Z ∪ Xe Z' ∪ Xf Z).card
                    ≤ (Xe Z ∪ Xe Z').card + (Xf Z).card := Finset.card_union_le _ _
                  _ ≤ (Xe Z).card + (Xe Z').card + (Xf Z).card :=
                      add_le_add (Finset.card_union_le _ _) le_rfl
                  _ ≤ 3 + 3 + 3 := add_le_add (add_le_add (hXe_le Z) (hXe_le Z')) (hXf_le Z)
                  _ < Fintype.card (Γ ⧸ B) := by omega
              have hex : (Finset.univ \ (X Z ∪ X Z')).Nonempty := by
                rw [Finset.nonempty_iff_ne_empty]
                intro he
                have hsub : (Finset.univ : Finset (Γ ⧸ B)) ⊆ X Z ∪ X Z' :=
                  Finset.sdiff_eq_empty_iff_subset.mp he
                have := Finset.card_le_card hsub
                rw [Finset.card_univ] at this
                omega
              obtain ⟨c', hc'⟩ := hex
              rw [Finset.mem_sdiff, Finset.mem_union, not_or] at hc'
              have h1 := hwalk_Ci Z hZ c c' hc hc'.2.1
              have hstep_l : GoodStep i
                  (fun eq => Z eq + (C i₀).sign eq • c')
                  (fun eq => Z' eq + (C i₀).sign eq • c') :=
                ⟨(hstar Z hZ c').mpr hc'.2.1, (hstar Z' hZ' c').mpr hc'.2.2, σ, l, hσ, fun eq => by
                  dsimp only; rw [hZ'eq eq]; abel⟩
              exact ⟨c', hc'.2.2, (hpath.trans h1).tail hstep_l⟩
      obtain ⟨cn, hcn, hpath⟩ := htrack Z₂ hwalk_up
      have h0 : (0 : Γ ⧸ B) ∉ X Z₂ := by
        have h0eq : (fun eq => Z₂ eq + (C i₀).sign eq • (0 : Γ ⧸ B)) = Z₂ := by ext eq; simp
        exact (hstar Z₂ (hsub_PLam Z₂ hZ₂) 0).mp (h0eq.symm ▸ hZ₂)
      have hback := hwalk_Ci Z₂ (hsub_PLam Z₂ hZ₂) cn 0 hcn h0
      have h0eq : (fun eq => Z₂ eq + (C i₀).sign eq • (0 : Γ ⧸ B)) = Z₂ := by ext eq; simp
      rw [h0eq] at hback
      exact hpath.trans hback
  have hres : Relation.ReflTransGen (GoodStep 0) Y Y' := by
    have h := hdown s le_rfl Y Y'
      (by rw [Nat.sub_self]; exact (hPLam_at_zero Y).mpr hY)
      (by rw [Nat.sub_self]; exact (hPLam_at_zero Y').mpr hY')
    rwa [Nat.sub_self] at h
  clear hY'
  induction hres with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail ⟨(hPLam_at_zero _).mp hs.1, (hPLam_at_zero _).mp hs.2.1, hs.2.2⟩

/-! ### Lemma 4.4: Preparation in `B` -/

theorem lem_4_4_of
    {V E Γ : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    [AddCommGroup Γ] [Fintype Γ] [DecidableEq Γ]
    (B : AddSubgroup Γ) [Fintype B] [DecidableEq B] [DecidableEq (Γ ⧸ B)]
    (hB : 4 ≤ Fintype.card B) (Sig : StepSystem Γ) (hR2 : CondR2 B Sig)
    {G : Multigraph V E} {H : G.Subgraph} {sub : SubdivisionData G H}
    {aux : AuxGraphData G H sub} (fr : Frame G H sub aux)
    (hO6_free : ∀ eps : sub.E₀, fr.IsFree eps →
      ∃ D : G.DirectedCycle,
        D.sub ≤ H ∧
        (∀ e ∈ (sub.thread eps).edges, e ∈ D.sub.edges ∧ D.sign e = 1) ∧
        (∀ t : sub.E₀, fr.IsFree t → t ≠ eps →
          ∀ e ∈ (sub.thread t).edges, e ∉ D.sub.edges))
    (f : G.NZFlow Γ) (hgood : IsHGoodSub fr B f)
    (Ecirc : Finset sub.E₀) (hEcirc : ∀ eps ∈ Ecirc, fr.IsFree eps)
    (T : sub.E₀ → Finset B)
    (hT_sup : ∀ eps ∈ Ecirc, ∀ e ∈ (sub.thread eps).edges,
      quoFlow B f.val e = 0 →
      ∀ (hb : -f.val e ∈ B), (⟨-f.val e, hb⟩ : B) ∈ T eps)
    (hT_card : ∀ eps ∈ Ecirc, (T eps).card ≤ (sub.thread eps).edges.length) :
    ∃ fcirc : G.NZFlow Γ,
      G.SigmaJoinedIn H {lam | lam ∈ Sig.carrier ∧ lam ∈ B} f fcirc ∧
      IsHGoodSub fr B fcirc ∧
      (∀ e, quoFlow B fcirc.val e = quoFlow B f.val e) ∧
      (∀ e, e ∉ H.edges → fcirc.val e = f.val e) ∧
      (∀ t : sub.E₀, fr.IsFree t → t ∉ Ecirc → ∀ e ∈ (sub.thread t).edges, fcirc.val e = f.val e) ∧
      (∀ eps ∈ Ecirc, ∃ y : B, y ∉ T eps ∧
        ∀ e ∈ (sub.thread eps).edges, fcirc.val e = f.val e + (y : Γ)) := by
  induction Ecirc using Finset.induction_on with
  | empty =>
    exact ⟨f, .refl, hgood, fun _ => rfl, fun _ _ => rfl, fun _ _ _ _ _ => rfl,
      fun eps heps => absurd heps (Finset.notMem_empty _)⟩
  | @insert eps E' heps_not ih =>
    have hE'_free : ∀ t ∈ E', fr.IsFree t := fun t ht => hEcirc t (Finset.mem_insert_of_mem ht)
    have hT_sup' : ∀ t ∈ E', ∀ e ∈ (sub.thread t).edges, quoFlow B f.val e = 0 →
        ∀ (hb : -f.val e ∈ B), (⟨-f.val e, hb⟩ : B) ∈ T t :=
      fun t ht => hT_sup t (Finset.mem_insert_of_mem ht)
    have hT_card' : ∀ t ∈ E', (T t).card ≤ (sub.thread t).edges.length :=
      fun t ht => hT_card t (Finset.mem_insert_of_mem ht)
    obtain ⟨f₁, hjoin₁, hgood₁, hquo₁, hout₁, hfree₁, hdone₁⟩ := ih hE'_free hT_sup' hT_card'
    have heps_free : fr.IsFree eps := hEcirc eps (Finset.mem_insert_self _ _)
    have hf₁_eps : ∀ e ∈ (sub.thread eps).edges, f₁.val e = f.val e :=
      hfree₁ eps heps_free heps_not
    by_cases h0T : (0 : B) ∉ T eps
    · -- No move needed for eps; take y = 0
      refine ⟨f₁, hjoin₁, hgood₁, hquo₁, hout₁, ?_, ?_⟩
      · intro t ht hnot
        exact hfree₁ t ht (fun hmem => hnot (Finset.mem_insert_of_mem hmem))
      · intro t ht
        rw [Finset.mem_insert] at ht
        rcases ht with rfl | ht'
        · exact ⟨0, h0T, fun e he => by rw [hf₁_eps e he]; simp⟩
        · exact hdone₁ t ht'
    · push Not at h0T
      -- Build W_eps ⊆ (T eps).erase 0, so |W_eps| ≤ 2, and pick y ∈ B \ T eps
      let W : Finset B := (T eps).erase 0
      have hW_card : W.card ≤ 2 := by
        have hlen := (sub.thread eps).len_le
        have hTc := hT_card eps (Finset.mem_insert_self _ _)
        have hcard_er : W.card = (T eps).card - 1 := Finset.card_erase_of_mem h0T
        omega
      have hT_lt : (T eps).card < Fintype.card B := by
        have hlen := (sub.thread eps).len_le
        have hTc := hT_card eps (Finset.mem_insert_self _ _)
        omega
      have hex_y : (Finset.univ \ T eps).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro he
        have hsub : (Finset.univ : Finset B) ⊆ T eps := Finset.sdiff_eq_empty_iff_subset.mp he
        have := Finset.card_le_card hsub
        rw [Finset.card_univ] at this
        omega
      obtain ⟨y, hy⟩ := hex_y
      rw [Finset.mem_sdiff] at hy
      have hy_notT : y ∉ T eps := hy.2
      have h0_notW : (0 : B) ∉ W := Finset.notMem_erase 0 (T eps)
      have hy_notW : y ∉ W := fun h => hy_notT (Finset.mem_of_mem_erase h)
      obtain ⟨D, hDH, hDeps, hDother⟩ := hO6_free eps heps_free
      obtain ⟨_, _, hrtg⟩ := hR2 W hW_card 0 y h0_notW hy_notW
      -- Helper: for any z ∉ W, f₁ + z • χ_D is a valid NZFlow agreeing on all other edges
      have mkNZ : ∀ z : B, z ∉ W →
          ∃ fz : G.NZFlow Γ,
            (∀ e, fz.val e = f₁.val e + D.sign e • (z : Γ)) ∧
            IsHGoodSub fr B fz ∧
            (∀ e, quoFlow B fz.val e = quoFlow B f.val e) := by
        intro z hzW
        let val : E → Γ := fun e => f₁.val e + D.sign e • (z : Γ)
        have hfl : G.IsFlow val := isFlow_add f₁.isFlow (isFlow_zsmul D.isFlow (z : Γ))
        have hquo : ∀ e, quoFlow B val e = quoFlow B f.val e := fun e => by
          rw [sec4_E2_proved G B f₁.val D (z : Γ) z.2 e, hquo₁ e]
        have hnz : Multigraph.IsNowhereZero val := by
          intro e
          by_cases heH : e ∈ H.edges
          · obtain ⟨t, het⟩ := sub.edges_cover e heH
            by_cases hprot : fr.IsProtected t
            · exact (sec4_E1_proved (V := V) B val e).mpr (Or.inl (by rw [hquo e]; exact hgood t hprot e het))
            · have htfree : fr.IsFree t := hprot
              by_cases hteq : t = eps
              · by_cases hqu : quoFlow B f.val e = 0
                · have hfeB : f.val e ∈ B := (QuotientAddGroup.eq_zero_iff (f.val e)).mp hqu
                  have hnegB : -f.val e ∈ B := B.neg_mem hfeB
                  have hneg_inT : (⟨-f.val e, hnegB⟩ : B) ∈ T eps :=
                    hT_sup eps (Finset.mem_insert_self _ _) e (hteq ▸ het) hqu hnegB
                  have hneg_ne0 : (⟨-f.val e, hnegB⟩ : B) ≠ 0 := by
                    intro h0
                    have hval0 : -f.val e = 0 := congrArg Subtype.val h0
                    exact f.nonzero e (neg_eq_zero.mp hval0)
                  have hneg_inW : (⟨-f.val e, hnegB⟩ : B) ∈ W :=
                    Finset.mem_erase.mpr ⟨hneg_ne0, hneg_inT⟩
                  have hzne : (z : Γ) ≠ -f.val e := fun h => by
                    have hzeq : z = ⟨-f.val e, hnegB⟩ := Subtype.ext h
                    exact hzW (hzeq ▸ hneg_inW)
                  have hds := (hDeps e (hteq ▸ het)).2
                  dsimp only [val]
                  rw [hf₁_eps e (hteq ▸ het), hds, one_zsmul]
                  intro h0
                  exact hzne (eq_neg_of_add_eq_zero_right h0)
                · exact (sec4_E1_proved (V := V) B val e).mpr (Or.inl (by rw [hquo e]; exact hqu))
              · have hnotD : e ∉ D.sub.edges := hDother t htfree hteq e het
                dsimp only [val]
                rw [D.sign_zero hnotD, zero_zsmul, add_zero]
                exact f₁.nonzero e
          · have hnotD : e ∉ D.sub.edges := fun h => heH (hDH.2 h)
            dsimp only [val]
            rw [D.sign_zero hnotD, zero_zsmul, add_zero]
            exact f₁.nonzero e
        exact ⟨⟨val, hfl, hnz⟩, fun _ => rfl, fun t ht e he => by rw [hquo e]; exact hgood t ht e he, hquo⟩
      -- Induct on the WalkIn from 0 to y in B \ W
      have hwalk : ∀ z : B,
          Relation.ReflTransGen (fun u v => u ∈ {b : B | b ∉ W} ∧ v ∈ {b : B | b ∉ W} ∧
            ∃ s ∈ Sig.sigB B, v = u + s) 0 z →
          z ∉ W →
          ∃ fz : G.NZFlow Γ,
            (∀ e, fz.val e = f₁.val e + D.sign e • (z : Γ)) ∧
            G.SigmaJoinedIn H {lam | lam ∈ Sig.carrier ∧ lam ∈ B} f₁ fz := by
        intro z hz
        induction hz with
        | refl =>
          intro _
          exact ⟨f₁, fun e => by simp, .refl⟩
        | @tail u v _ hstep ih' =>
          intro hvW
          rcases hstep with ⟨huW, _, s, hs, rfl⟩
          obtain ⟨fu, hfu_eq, hfu_join⟩ := ih' huW
          obtain ⟨fv, hfv_eq, _, _⟩ := mkNZ (u + s) hvW
          have hmove : G.SigmaMoveIn H {lam | lam ∈ Sig.carrier ∧ lam ∈ B} fu fv := by
            refine ⟨D, (s : Γ), hDH, ⟨hs, s.2⟩, fun e => ?_⟩
            rw [hfv_eq e, hfu_eq e]
            push_cast
            rw [smul_add, add_assoc]
          exact ⟨fv, hfv_eq, hfu_join.tail hmove⟩
      obtain ⟨f₂, hf₂_eq, hf₂_join⟩ := hwalk y hrtg hy_notW
      have hquo₂ : ∀ e, quoFlow B f₂.val e = quoFlow B f.val e := fun e => by
        have hfun : f₂.val = fun e' => f₁.val e' + D.sign e' • (y : Γ) := funext hf₂_eq
        rw [hfun, sec4_E2_proved G B f₁.val D (y : Γ) y.2 e, hquo₁ e]
      refine ⟨f₂, hjoin₁.trans hf₂_join, fun t ht e he => by rw [hquo₂ e]; exact hgood t ht e he,
        hquo₂, ?_, ?_, ?_⟩
      · intro e heH
        have hnotD : e ∉ D.sub.edges := fun h => heH (hDH.2 h)
        rw [hf₂_eq e, D.sign_zero hnotD, zero_zsmul, add_zero, hout₁ e heH]
      · intro t htfree htnot e het
        have hne : t ≠ eps := fun h => htnot (h ▸ Finset.mem_insert_self _ _)
        have hnotE' : t ∉ E' := fun h => htnot (Finset.mem_insert_of_mem h)
        have hnotD : e ∉ D.sub.edges := hDother t htfree hne e het
        rw [hf₂_eq e, D.sign_zero hnotD, zero_zsmul, add_zero, hfree₁ t htfree hnotE' e het]
      · intro t ht
        rw [Finset.mem_insert] at ht
        rcases ht with rfl | ht'
        · refine ⟨y, hy_notT, fun e het => ?_⟩
          rw [hf₂_eq e, hf₁_eps e het, (hDeps e het).2, one_zsmul]
        · obtain ⟨yt, hyt_notT, hyt_eq⟩ := hdone₁ t ht'
          refine ⟨yt, hyt_notT, fun e het => ?_⟩
          have hne : t ≠ eps := fun h => heps_not (h ▸ ht')
          have hnotD : e ∉ D.sub.edges := hDother t (hE'_free t ht') hne e het
          rw [hf₂_eq e, D.sign_zero hnotD, zero_zsmul, add_zero, hyt_eq e het]

/-! ### Lemma 4.5: One step inside `H` -/

private lemma restrictDirectedCycle_const_on_thread
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    {G : Multigraph V E} {H : G.Subgraph} (sub : SubdivisionData G H)
    (aux : AuxGraphData G H sub)
    (h36a_cyc : ∀ (O : H.toMultigraph.DirectedCycle) (t : sub.E₀),
      ∃ s : ℤ, (s = 1 ∨ s = 0 ∨ s = -1) ∧
        ∀ e (he : e ∈ (sub.thread t).edges), O.sign ⟨e, (sub.thread t).edges_sub e he⟩ = s)
    (O : G.DirectedCycle) (hOH : O.sub ≤ H) (t : sub.E₀) :
    ∃ s : ℤ, (s = 1 ∨ s = 0 ∨ s = -1) ∧
      ∀ e ∈ (sub.thread t).edges, O.sign e = s := by
  let OH : H.toMultigraph.DirectedCycle :=
    { sub :=
        { verts := Finset.univ.filter (fun v : {v // v ∈ H.verts} => v.1 ∈ O.sub.verts)
          edges := Finset.univ.filter (fun e : {e // e ∈ H.edges} => e.1 ∈ O.sub.edges)
          tail_mem := fun he => by
            rw [Finset.mem_filter] at he ⊢
            exact ⟨Finset.mem_univ _, O.sub.tail_mem he.2⟩
          head_mem := fun he => by
            rw [Finset.mem_filter] at he ⊢
            exact ⟨Finset.mem_univ _, O.sub.head_mem he.2⟩ }
      isCycle := by
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · obtain ⟨v, hv⟩ := O.isCycle.1.1
          exact ⟨⟨v, hOH.1 hv⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩⟩
        · intro u hu v hv
          have hrtg := O.isCycle.1.2 u.1 (Finset.mem_filter.mp hu).2 v.1 (Finset.mem_filter.mp hv).2
          have hgo : ∀ a b, Relation.ReflTransGen O.sub.Adj a b →
              ∀ (ha : a ∈ H.verts) (hb : b ∈ H.verts),
              Relation.ReflTransGen
                (Multigraph.Subgraph.Adj (G := H.toMultigraph)
                  { verts := Finset.univ.filter (fun v : {v // v ∈ H.verts} => v.1 ∈ O.sub.verts)
                    edges := Finset.univ.filter (fun e : {e // e ∈ H.edges} => e.1 ∈ O.sub.edges)
                    tail_mem := fun he => Finset.mem_filter.mpr ⟨Finset.mem_univ _, O.sub.tail_mem (Finset.mem_filter.mp he).2⟩
                    head_mem := fun he => Finset.mem_filter.mpr ⟨Finset.mem_univ _, O.sub.head_mem (Finset.mem_filter.mp he).2⟩ })
                ⟨a, ha⟩ ⟨b, hb⟩ := by
            intro a b hab
            induction hab with
            | refl => intro ha hb; exact .refl
            | @tail x y _ hs ih =>
              intro ha hy
              rcases hs with ⟨e, heO, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
              · have hxH : x ∈ H.verts := h1 ▸ H.tail_mem (hOH.2 heO)
                exact (ih ha hxH).tail ⟨⟨e, hOH.2 heO⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, heO⟩,
                  Or.inl ⟨Subtype.ext h1, Subtype.ext h2⟩⟩
              · have hxH : x ∈ H.verts := h2 ▸ H.head_mem (hOH.2 heO)
                exact (ih ha hxH).tail ⟨⟨e, hOH.2 heO⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, heO⟩,
                  Or.inr ⟨Subtype.ext h1, Subtype.ext h2⟩⟩
          exact hgo u.1 v.1 hrtg u.2 v.2
        · intro v hv
          have hd := O.isCycle.2 v.1 (Finset.mem_filter.mp hv).2
          unfold Multigraph.Subgraph.deg at hd ⊢
          have h1 : ((Finset.univ.filter (fun e : {e // e ∈ H.edges} => e.1 ∈ O.sub.edges)).filter
              (fun e => H.toMultigraph.tail e = v)).card =
              (O.sub.edges.filter (fun e => G.tail e = v.1)).card := by
            refine Finset.card_bij (fun e _ => e.1) (fun e he => ?_) (fun _ _ _ _ h => Subtype.ext h)
              (fun e he => ⟨⟨e, hOH.2 (Finset.mem_filter.mp he).1⟩, ?_, rfl⟩)
            · rw [Finset.mem_filter, Finset.mem_filter] at he
              exact Finset.mem_filter.mpr ⟨he.1.2, congrArg Subtype.val he.2⟩
            · rw [Finset.mem_filter] at he
              exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, he.1⟩, Subtype.ext he.2⟩
          have h2 : ((Finset.univ.filter (fun e : {e // e ∈ H.edges} => e.1 ∈ O.sub.edges)).filter
              (fun e => H.toMultigraph.head e = v)).card =
              (O.sub.edges.filter (fun e => G.head e = v.1)).card := by
            refine Finset.card_bij (fun e _ => e.1) (fun e he => ?_) (fun _ _ _ _ h => Subtype.ext h)
              (fun e he => ⟨⟨e, hOH.2 (Finset.mem_filter.mp he).1⟩, ?_, rfl⟩)
            · rw [Finset.mem_filter, Finset.mem_filter] at he
              exact Finset.mem_filter.mpr ⟨he.1.2, congrArg Subtype.val he.2⟩
            · rw [Finset.mem_filter] at he
              exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, he.1⟩, Subtype.ext he.2⟩
          rw [h1, h2]; exact hd
      sign := fun e => O.sign e.1
      sign_mem := fun he => O.sign_mem (Finset.mem_filter.mp he).2
      sign_zero := fun he => O.sign_zero fun h => he (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      isFlow := fun v => by
        have hbd := O.isFlow v.1
        trans (G.boundary O.sign v.1)
        · rw [boundary_eq_sum_ite, boundary_eq_sum_ite]
          symm
          rw [← Finset.sum_subset (Finset.subset_univ H.edges)]
          · refine Finset.sum_bij (fun e he => ⟨e, he⟩) (fun _ _ => Finset.mem_univ _)
              (fun _ _ _ _ h => congrArg Subtype.val h) (fun e _ => ⟨e.1, e.2, rfl⟩) (fun e _ => ?_)
            by_cases h1 : G.head e = v.1 <;> by_cases h2 : G.tail e = v.1 <;>
              simp [Multigraph.Subgraph.toMultigraph, Subtype.ext_iff, h1, h2]
          · intro e _ hnot
            have h0 : O.sign e = 0 := O.sign_zero fun h => hnot (hOH.2 h)
            simp [h0]
        · exact hbd }
  obtain ⟨s, hs, hconst⟩ := h36a_cyc OH t
  exact ⟨s, hs, fun e he => hconst e he⟩

theorem lem_4_5_of
    {V E Γ : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    [AddCommGroup Γ] [Fintype Γ] [DecidableEq Γ]
    (B : AddSubgroup Γ) [Fintype B] [DecidableEq B] [DecidableEq (Γ ⧸ B)]
    (hB : 4 ≤ Fintype.card B) (Sig : StepSystem Γ) (hR2 : CondR2 B Sig)
    {G : Multigraph V E} {H : G.Subgraph} {sub : SubdivisionData G H}
    {aux : AuxGraphData G H sub} (fr : Frame G H sub aux)
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
    (hO6_free : ∀ eps : sub.E₀, fr.IsFree eps →
      ∃ D : G.DirectedCycle,
        D.sub ≤ H ∧
        (∀ e ∈ (sub.thread eps).edges, e ∈ D.sub.edges ∧ D.sign e = 1) ∧
        (∀ t : sub.E₀, fr.IsFree t → t ≠ eps →
          ∀ e ∈ (sub.thread t).edges, e ∉ D.sub.edges))
    (f : G.NZFlow Γ) (hgood : IsHGoodSub fr B f)
    (C : aux.Q.DirectedCycle) (σ : Γ ⧸ B) (hσ : σ ∈ Sig.sigA B)
    (hu' : ∀ t : sub.E₀, fr.IsProtected t → ∀ e ∈ (sub.thread t).edges,
      quoFlow B f.val e + aux.pi (fun eq => C.sign eq • σ) e ≠ 0) :
    ∃ f' : G.NZFlow Γ,
      G.SigmaJoinedIn H Sig.carrier f f' ∧
      IsHGoodSub fr B f' ∧
      (∀ e, quoFlow B f'.val e = quoFlow B f.val e + aux.pi (fun eq => C.sign eq • σ) e) ∧
      (∀ e, e ∉ H.edges → f'.val e = f.val e) := by
  classical
  rcases hσ with ⟨hσ_ne0, lam, hlam_mem, hlam_quo⟩
  obtain ⟨cycles, hcycles_H, hcycles_disj, hcycles_pi⟩ := h36d C
  -- Delta on every edge e from cycles
  let deltaE (e : E) : Γ := (cycles.map (fun O => O.sign e • lam)).sum
  have hdeltaE_quo : ∀ e : E, QuotientAddGroup.mk (deltaE e) = aux.pi (fun eq => C.sign eq • σ) e := by
    intro e
    rw [hcycles_pi σ e]
    dsimp only [deltaE]
    have hmap : ∀ (l : List G.DirectedCycle),
        (QuotientAddGroup.mk' B) ((l.map (fun O => O.sign e • lam)).sum) =
        (l.map (fun O => O.sign e • σ)).sum := by
      intro l
      induction l with
      | nil => simp
      | cons O tl ih =>
        simp only [List.map_cons, List.sum_cons, map_add, map_zsmul, ih]
        congr 2
    exact hmap cycles
  -- deltaE is constant along every thread
  have hdelta_const : ∀ (t : sub.E₀) (e₁ e₂ : E),
      e₁ ∈ (sub.thread t).edges → e₂ ∈ (sub.thread t).edges → deltaE e₁ = deltaE e₂ := by
    intro t e₁ e₂ h1 h2
    dsimp only [deltaE]
    congr 1
    refine List.map_congr_left fun O hO => ?_
    obtain ⟨s, _, hcs⟩ := restrictDirectedCycle_const_on_thread sub aux h36a_cyc O (hcycles_H O hO) t
    rw [hcs e₁ h1, hcs e₂ h2]
  -- If aux.pi (C.sign • σ) e = 0, then deltaE e = 0 (since cycles are pairwise edge-disjoint and σ ≠ 0)
  have hdelta_zero_of_pi_zero : ∀ e : E, aux.pi (fun eq => C.sign eq • σ) e = 0 → deltaE e = 0 := by
    intro e hpi0
    by_cases hex : ∃ O ∈ cycles, e ∈ O.sub.edges
    · exfalso
      rcases hex with ⟨O, hO, heO⟩
      obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem hO
      have hother : ∀ j (hj : j < cycles.length), j ≠ idx → (cycles[j]'hj).sign e = 0 := by
        intro j hj hne
        have hdj := hcycles_disj idx j hidx hj hne.symm
        exact (cycles[j]'hj).sign_zero (Finset.disjoint_left.mp hdj heO)
      have hsum_eq : (cycles.map (fun D => D.sign e • σ)).sum = (cycles[idx]'hidx).sign e • σ := by
        have hlist : ∀ (l : List G.DirectedCycle) (i : ℕ) (hi : i < l.length),
            (∀ j (hj : j < l.length), j ≠ i → (l[j]'hj).sign e = 0) →
            (l.map (fun D => D.sign e • σ)).sum = (l[i]'hi).sign e • σ := by
          intro l
          induction l with
          | nil => intro _ hi; simp at hi
          | cons hd tl ihl =>
            intro i hi hoth
            cases i with
            | zero =>
              simp only [List.map_cons, List.sum_cons, List.getElem_cons_zero]
              have htl0 : (tl.map (fun D => D.sign e • σ)).sum = 0 := by
                apply List.sum_eq_zero
                intro x hx; rw [List.mem_map] at hx; rcases hx with ⟨D, hD, rfl⟩
                obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hD
                have h0 := hoth (j + 1) (by simp; omega) (by omega)
                simp only [List.getElem_cons_succ] at h0
                rw [h0, zero_zsmul]
              rw [htl0, add_zero]
            | succ i' =>
              simp only [List.map_cons, List.sum_cons, List.getElem_cons_succ]
              have hhd0 := hoth 0 (by simp) (by omega)
              simp only [List.getElem_cons_zero] at hhd0
              rw [hhd0, zero_zsmul, zero_add]
              exact ihl i' (by simp at hi; omega) fun j hj hne => by
                have := hoth (j + 1) (by simp; omega) (by omega)
                simpa using this
        exact hlist cycles idx hidx hother
      rw [hcycles_pi σ e, hsum_eq] at hpi0
      rcases (cycles[idx]'hidx).sign_mem heO with hs | hs
      · rw [hs, one_zsmul] at hpi0; exact hσ_ne0 hpi0
      · rw [hs, neg_one_zsmul, neg_eq_zero] at hpi0; exact hσ_ne0 hpi0
    · push Not at hex
      dsimp only [deltaE]
      apply List.sum_eq_zero
      intro x hx; rw [List.mem_map] at hx; rcases hx with ⟨O, hO, rfl⟩
      rw [O.sign_zero (hex O hO), zero_zsmul]
  -- Prepare B via Lemma 4.4 on all free edges
  let Ecirc : Finset sub.E₀ := Finset.univ.filter (fun eps => fr.IsFree eps)
  let pickB (e : E) : Finset B :=
    if h1 : quoFlow B f.val e = 0 then
      {⟨-f.val e, B.neg_mem ((QuotientAddGroup.eq_zero_iff (f.val e)).mp h1)⟩}
    else if h2 : quoFlow B f.val e + aux.pi (fun eq => C.sign eq • σ) e = 0 then
      {⟨-(f.val e + deltaE e), B.neg_mem ((QuotientAddGroup.eq_zero_iff (f.val e + deltaE e)).mp (by
        change (QuotientAddGroup.mk' B) (f.val e + deltaE e) = 0
        rw [map_add]
        exact (by simpa [quoFlow, hdeltaE_quo e] using h2)) )⟩}
    else ∅
  let T (eps : sub.E₀) : Finset B := (sub.thread eps).edges.toFinset.biUnion pickB
  have hT_sup : ∀ eps ∈ Ecirc, ∀ e ∈ (sub.thread eps).edges,
      quoFlow B f.val e = 0 → ∀ (hb : -f.val e ∈ B), (⟨-f.val e, hb⟩ : B) ∈ T eps := by
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
  obtain ⟨fcirc, hjoin_B, hgood_c, hquo_c, hout_c, hfree_c, hy_eps⟩ :=
    lem_4_4_of B hB Sig hR2 fr hO6_free f hgood Ecirc (fun _ h => (Finset.mem_filter.mp h).2) T hT_sup hT_card
  have hjoin_c : G.SigmaJoinedIn H Sig.carrier f fcirc := by
    clear hgood_c hquo_c hout_c hfree_c hy_eps
    induction hjoin_B with
    | refl => exact .refl
    | tail _ hs ih =>
      rcases hs with ⟨O, z, hOH, hz, heq⟩
      exact ih.tail ⟨O, z, hOH, hz.1, heq⟩
  -- Verify that fcirc + deltaE is nowhere zero on every edge of H
  have hfinal_nz : ∀ e ∈ H.edges, fcirc.val e + deltaE e ≠ 0 := by
    intro e heH
    obtain ⟨t, het⟩ := sub.edges_cover e heH
    have hq_new : quoFlow B (fun e' => fcirc.val e' + deltaE e') e =
        quoFlow B f.val e + aux.pi (fun eq => C.sign eq • σ) e := by
      unfold quoFlow
      change (QuotientAddGroup.mk' B) (fcirc.val e + deltaE e) = _
      rw [map_add]
      have h1 : (QuotientAddGroup.mk' B) (fcirc.val e) = quoFlow B f.val e := hquo_c e
      have h2 : (QuotientAddGroup.mk' B) (deltaE e) = aux.pi (fun eq => C.sign eq • σ) e := hdeltaE_quo e
      rw [h1, h2]; rfl
    by_cases hprot : fr.IsProtected t
    · exact (sec4_E1_proved (V := V) B (fun e' => fcirc.val e' + deltaE e') e).mpr
        (Or.inl (by rw [hq_new]; exact hu' t hprot e het))
    · by_cases hqu' : quoFlow B f.val e + aux.pi (fun eq => C.sign eq • σ) e = 0
      · obtain ⟨y, hy_notT, hy_eq⟩ := hy_eps t (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hprot⟩)
        rw [hy_eq e het]
        by_cases hqu : quoFlow B f.val e = 0
        · have hpi0 : aux.pi (fun eq => C.sign eq • σ) e = 0 := by simpa [hqu] using hqu'
          rw [hdelta_zero_of_pi_zero e hpi0, add_zero]
          intro h0
          have hmem : (⟨-f.val e, B.neg_mem ((QuotientAddGroup.eq_zero_iff (f.val e)).mp hqu)⟩ : B) ∈ T t :=
            hT_sup t (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hprot⟩) e het hqu _
          have hyval : y = ⟨-f.val e, B.neg_mem ((QuotientAddGroup.eq_zero_iff (f.val e)).mp hqu)⟩ :=
            Subtype.ext (eq_neg_of_add_eq_zero_right h0)
          exact hy_notT (hyval ▸ hmem)
        · intro h0
          have hb_mem : -(f.val e + deltaE e) ∈ B := B.neg_mem ((QuotientAddGroup.eq_zero_iff (f.val e + deltaE e)).mp (by
            change (QuotientAddGroup.mk' B) (f.val e + deltaE e) = 0
            rw [map_add]
            simpa [quoFlow, hdeltaE_quo e] using hqu'))
          have hmem : (⟨-(f.val e + deltaE e), hb_mem⟩ : B) ∈ T t := by
            refine Finset.mem_biUnion.mpr ⟨e, List.mem_toFinset.mpr het, ?_⟩
            simp [pickB, hqu, hqu']
          have hyval : (y : Γ) = -(f.val e + deltaE e) := by
            apply eq_neg_of_add_eq_zero_right
            have : f.val e + deltaE e + (y : Γ) = f.val e + (y : Γ) + deltaE e := by abel
            rw [this]; exact h0
          have hyeq : y = ⟨-(f.val e + deltaE e), hb_mem⟩ := Subtype.ext hyval
          exact hy_notT (hyeq ▸ hmem)
      · exact (sec4_E1_proved (V := V) B (fun e' => fcirc.val e' + deltaE e') e).mpr
          (Or.inl (by rw [hq_new]; exact hqu'))
  -- Apply cycles one by one using pairwise edge-disjointness
  have happly_cycles : ∀ (l : List G.DirectedCycle),
      (∀ O ∈ l, O.sub ≤ H) →
      (∀ i j (hi : i < l.length) (hj : j < l.length), i ≠ j →
        Disjoint (l[i]'hi).sub.edges (l[j]'hj).sub.edges) →
      ∀ (cur : G.NZFlow Γ),
      (∀ e, cur.val e = fcirc.val e ∨ cur.val e = fcirc.val e + deltaE e) →
      (∀ O ∈ l, ∀ e ∈ O.sub.edges, cur.val e = fcirc.val e ∧
        cur.val e + O.sign e • lam = fcirc.val e + deltaE e) →
      ∃ fin : G.NZFlow Γ,
        G.SigmaJoinedIn H Sig.carrier cur fin ∧
        ∀ e, fin.val e = cur.val e + (l.map (fun O => O.sign e • lam)).sum := by
    intro l
    induction l with
    | nil =>
      intro _ _ cur _ _
      exact ⟨cur, .refl, fun e => by simp⟩
    | cons O rest ih =>
      intro hlH hldisj cur hcur_vals hcur_on
      let nxtVal : E → Γ := fun e => cur.val e + O.sign e • lam
      have hnxt_flow : G.IsFlow nxtVal := isFlow_add cur.isFlow (isFlow_zsmul O.isFlow lam)
      have hnxt_nz : Multigraph.IsNowhereZero nxtVal := by
        intro e
        by_cases heO : e ∈ O.sub.edges
        · have heH : e ∈ H.edges := (hlH O (List.mem_cons_self ..)).2 heO
          dsimp only [nxtVal]
          rw [(hcur_on O (List.mem_cons_self ..) e heO).2]
          exact hfinal_nz e heH
        · dsimp only [nxtVal]
          rw [O.sign_zero heO, zero_zsmul, add_zero]
          exact cur.nonzero e
      let nxt : G.NZFlow Γ := ⟨nxtVal, hnxt_flow, hnxt_nz⟩
      have hmove : G.SigmaMoveIn H Sig.carrier cur nxt :=
        ⟨O, lam, hlH O (List.mem_cons_self ..), hlam_mem, fun _ => rfl⟩
      have hrest_H : ∀ D ∈ rest, D.sub ≤ H := fun D hD => hlH D (List.mem_cons_of_mem O hD)
      have hrest_disj : ∀ i j (hi : i < rest.length) (hj : j < rest.length), i ≠ j →
          Disjoint (rest[i]'hi).sub.edges (rest[j]'hj).sub.edges := fun i j hi hj hne =>
        hldisj (i + 1) (j + 1) (by simp; omega) (by simp; omega) (by omega)
      have hnxt_vals : ∀ e, nxt.val e = fcirc.val e ∨ nxt.val e = fcirc.val e + deltaE e := by
        intro e
        by_cases heO : e ∈ O.sub.edges
        · right; exact (hcur_on O (List.mem_cons_self ..) e heO).2
        · dsimp only [nxt, nxtVal]
          rw [O.sign_zero heO, zero_zsmul, add_zero]
          exact hcur_vals e
      have hnxt_on : ∀ D ∈ rest, ∀ e ∈ D.sub.edges, nxt.val e = fcirc.val e ∧
          nxt.val e + D.sign e • lam = fcirc.val e + deltaE e := by
        intro D hD e heD
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hD
        have hdj : Disjoint O.sub.edges (rest[j]'hj).sub.edges :=
          hldisj 0 (j + 1) (by simp) (by simp; omega) (by omega)
        have hnotO : e ∉ O.sub.edges := Finset.disjoint_right.mp hdj heD
        have hne : nxt.val e = cur.val e := by
          dsimp only [nxt, nxtVal]; rw [O.sign_zero hnotO, zero_zsmul, add_zero]
        rw [hne]
        exact hcur_on _ (List.mem_cons_of_mem O hD) e heD
      obtain ⟨fin, hjoin_r, hfin_eq⟩ := ih hrest_H hrest_disj nxt hnxt_vals hnxt_on
      refine ⟨fin, Relation.ReflTransGen.head hmove hjoin_r, fun e => ?_⟩
      rw [hfin_eq e]
      simp only [nxt, nxtVal, List.map_cons, List.sum_cons, add_assoc]
  have hcur_on_init : ∀ O ∈ cycles, ∀ e ∈ O.sub.edges, fcirc.val e = fcirc.val e ∧
      fcirc.val e + O.sign e • lam = fcirc.val e + deltaE e := by
    intro O hO e heO
    refine ⟨rfl, ?_⟩
    congr 1
    obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem hO
    have hother : ∀ j (hj : j < cycles.length), j ≠ idx → (cycles[j]'hj).sign e = 0 := by
      intro j hj hne
      have hdj := hcycles_disj idx j hidx hj hne.symm
      exact (cycles[j]'hj).sign_zero (Finset.disjoint_left.mp hdj heO)
    have hlist : ∀ (l : List G.DirectedCycle) (i : ℕ) (hi : i < l.length),
        (∀ j (hj : j < l.length), j ≠ i → (l[j]'hj).sign e = 0) →
        (l.map (fun D => D.sign e • lam)).sum = (l[i]'hi).sign e • lam := by
      intro l
      induction l with
      | nil => intro _ hi; simp at hi
      | cons hd tl ihl =>
        intro i hi hoth
        cases i with
        | zero =>
          simp only [List.map_cons, List.sum_cons, List.getElem_cons_zero]
          have htl0 : (tl.map (fun D => D.sign e • lam)).sum = 0 := by
            apply List.sum_eq_zero
            intro x hx; rw [List.mem_map] at hx; rcases hx with ⟨D, hD, rfl⟩
            obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hD
            have h0 := hoth (j + 1) (by simp; omega) (by omega)
            simp only [List.getElem_cons_succ] at h0
            rw [h0, zero_zsmul]
          rw [htl0, add_zero]
        | succ i' =>
          simp only [List.map_cons, List.sum_cons, List.getElem_cons_succ]
          have hhd0 := hoth 0 (by simp) (by omega)
          simp only [List.getElem_cons_zero] at hhd0
          rw [hhd0, zero_zsmul, zero_add]
          exact ihl i' (by simp at hi; omega) fun j hj hne => by
            have := hoth (j + 1) (by simp; omega) (by omega)
            simpa using this
    exact (hlist cycles idx hidx hother).symm
  obtain ⟨f', hjoin_cycs, hf'_eq⟩ :=
    happly_cycles cycles hcycles_H hcycles_disj fcirc (fun _ => Or.inl rfl) hcur_on_init
  have hquo_f' : ∀ e, quoFlow B f'.val e = quoFlow B f.val e + aux.pi (fun eq => C.sign eq • σ) e := by
    intro e
    unfold quoFlow
    change (QuotientAddGroup.mk' B) (f'.val e) = _
    rw [hf'_eq e, map_add]
    have h1 : (QuotientAddGroup.mk' B) (fcirc.val e) = quoFlow B f.val e := hquo_c e
    have h2 : (QuotientAddGroup.mk' B) (deltaE e) = aux.pi (fun eq => C.sign eq • σ) e := hdeltaE_quo e
    exact by rw [h1]; exact congrArg (quoFlow B f.val e + ·) h2
  refine ⟨f', hjoin_c.trans hjoin_cycs, fun t ht e het => by rw [hquo_f' e]; exact hu' t ht e het,
    hquo_f', ?_⟩
  intro e heH
  have h0 : deltaE e = 0 := by
    dsimp only [deltaE]
    apply List.sum_eq_zero
    intro x hx; rw [List.mem_map] at hx; rcases hx with ⟨O, hO, rfl⟩
    rw [O.sign_zero (fun h => heH ((hcycles_H O hO).2 h)), zero_zsmul]
  rw [hf'_eq e, show (cycles.map (fun O => O.sign e • lam)).sum = 0 from h0, add_zero, hout_c e heH]

/-! ### Lemma 4.6: Changing the `A`-coordinate inside `H` -/

theorem lem_4_6_of
    {V E Γ : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    [AddCommGroup Γ] [Fintype Γ] [DecidableEq Γ]
    (B : AddSubgroup Γ) [Fintype (Γ ⧸ B)] [Fintype B] [DecidableEq (Γ ⧸ B)] [DecidableEq B]
    (hA : 10 ≤ Fintype.card (Γ ⧸ B)) (hB : 4 ≤ Fintype.card B)
    (Sig : StepSystem Γ) (hR1 : CondR1 B Sig) (hR2 : CondR2 B Sig)
    {G : Multigraph V E} {H : G.Subgraph} {sub : SubdivisionData G H}
    {aux : AuxGraphData G H sub} (fr : Frame G H sub aux)
    (C : Fin fr.numNodes → aux.Q.DirectedCycle)
    (hO2 : ∀ i, fr.eNode i ∈ (C i).sub.edges ∧ fr.fNode i ∈ (C i).sub.edges)
    (hO3 : ∀ l i : Fin fr.numNodes, l < i →
      fr.eNode i ∉ (C l).sub.edges ∧ fr.fNode i ∉ (C l).sub.edges)
    (hO4 : ∀ l i : Fin fr.numNodes, i < l → fr.fNode i ∉ (C l).sub.edges)
    (hO5 : ∀ Y : aux.EQ → Γ ⧸ B, aux.Q.IsFlow Y →
      ∃! x : Fin fr.numNodes → Γ ⧸ B,
        ∀ eq, Y eq = ∑ i : Fin fr.numNodes, (C i).sign eq • x i)
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
    (hO6_free : ∀ eps : sub.E₀, fr.IsFree eps →
      ∃ D : G.DirectedCycle,
        D.sub ≤ H ∧
        (∀ e ∈ (sub.thread eps).edges, e ∈ D.sub.edges ∧ D.sign e = 1) ∧
        (∀ t : sub.E₀, fr.IsFree t → t ≠ eps →
          ∀ e ∈ (sub.thread t).edges, e ∉ D.sub.edges))
    (f : G.NZFlow Γ) (hgood : IsHGoodSub fr B f)
    (hdef312 :
      (∀ t : aux.EQ, ((LamOfFlow B fr f).list t).card ≤ 3) ∧
      (0 : aux.EQ → Γ ⧸ B) ∈ PLam (LamOfFlow B fr f) ∧
      (∀ Y : aux.EQ → Γ ⧸ B, aux.Q.IsFlow Y →
        (Y ∈ PLam (LamOfFlow B fr f) ↔
          ∀ t : sub.E₀, fr.IsProtected t → ∀ e ∈ (sub.thread t).edges,
            quoFlow B f.val e + aux.pi Y e ≠ 0)))
    (Y : aux.EQ → Γ ⧸ B) (hY : Y ∈ PLam (LamOfFlow B fr f)) :
    ∃ f' : G.NZFlow Γ,
      G.SigmaJoinedIn H Sig.carrier f f' ∧
      IsHGoodSub fr B f' ∧
      (∀ e, quoFlow B f'.val e = quoFlow B f.val e + aux.pi Y e) ∧
      (∀ e, e ∉ H.edges → f'.val e = f.val e) := by
  have hpi_zero : ∀ e, aux.pi (A := Γ ⧸ B) 0 e = 0 := by
    intro e; classical unfold AuxGraphData.pi; split_ifs <;> rfl
  have hpi_add : ∀ (Z₁ Z₂ : aux.EQ → Γ ⧸ B) (e : E),
      aux.pi (fun eq => Z₁ eq + Z₂ eq) e = aux.pi Z₁ e + aux.pi Z₂ e := by
    intro Z₁ Z₂ e; classical unfold AuxGraphData.pi; split_ifs <;> simp
  have hwalk := lem_4_3_of B hA Sig hR1 fr C hO2 hO3 hO4 hO5
    (LamOfFlow B fr f) (fun t _ => hdef312.1 t) 0 Y hdef312.2.1 hY
  have htrack : ∀ Z,
      Relation.ReflTransGen
        (fun Z₁ Z₂ => Z₁ ∈ PLam (LamOfFlow B fr f) ∧ Z₂ ∈ PLam (LamOfFlow B fr f) ∧
          ∃ (σ : Γ ⧸ B) (l : Fin fr.numNodes), σ ∈ Sig.sigA B ∧
            ∀ eq, Z₂ eq = Z₁ eq + (C l).sign eq • σ) 0 Z →
      ∃ f' : G.NZFlow Γ,
        G.SigmaJoinedIn H Sig.carrier f f' ∧
        IsHGoodSub fr B f' ∧
        (∀ e, quoFlow B f'.val e = quoFlow B f.val e + aux.pi Z e) ∧
        (∀ e, e ∉ H.edges → f'.val e = f.val e) := by
    intro Z hrtg
    induction hrtg with
    | refl =>
      exact ⟨f, .refl, hgood, fun e => by rw [hpi_zero e, add_zero], fun _ _ => rfl⟩
    | @tail Z₁ Z₂ _ hstep ih =>
      obtain ⟨f₁, hjoin₁, hgood₁, hquo₁, hout₁⟩ := ih
      rcases hstep with ⟨_, hZ₂, σ, l, hσ, hZ₂eq⟩
      have hZ₂_fun : Z₂ = fun eq => Z₁ eq + (C l).sign eq • σ := funext hZ₂eq
      have hu' : ∀ t : sub.E₀, fr.IsProtected t → ∀ e ∈ (sub.thread t).edges,
          quoFlow B f₁.val e + aux.pi (fun eq => (C l).sign eq • σ) e ≠ 0 := by
        intro t ht e het
        rw [hquo₁ e, add_assoc, ← hpi_add, ← hZ₂_fun]
        exact (hdef312.2.2 Z₂ hZ₂.1).mp hZ₂ t ht e het
      obtain ⟨f₂, hjoin₂, hgood₂, hquo₂, hout₂⟩ :=
        lem_4_5_of B hB Sig hR2 fr h36a_cyc h36d hO6_free f₁ hgood₁ (C l) σ hσ hu'
      refine ⟨f₂, hjoin₁.trans hjoin₂, hgood₂, fun e => ?_, fun e he => (hout₂ e he).trans (hout₁ e he)⟩
      rw [hquo₂ e, hquo₁ e, add_assoc, ← hpi_add, ← hZ₂_fun]
  exact htrack Y hwalk

end Flow.Proofs
