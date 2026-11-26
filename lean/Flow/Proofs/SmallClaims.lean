-- Copyright (C) Dave Goel 2026--now. Licensed under the Apache License 2.0; see LICENSE.
import Flow.Defs.Literature
import Flow.Proofs.Basic
import Mathlib.Tactic

/-!
# Small standalone claims: `sec1_trivial_int_k2` and `sec2_move_iff_supp_cycle`
-/

namespace Flow.Proofs

open Flow

/-! ### Section 1: `I_2(G)` is connected for every finite multigraph `G` -/

private lemma int_k2_val_eq_pm_one {V E : Type} [Fintype E] [DecidableEq V]
    {G : Multigraph V E} (F : G.IntKFlow 2) (e : E) :
    F.val e = 1 ∨ F.val e = -1 := by
  have hne := F.nonzero e
  have hbd := F.bound e
  have hle : |F.val e| ≤ 1 := by simpa using hbd
  rcases abs_le.mp hle with ⟨h1, h2⟩
  omega

private lemma int_k2_step_list {V E : Type} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E]
    (G : Multigraph V E) :
    ∀ (cycles : List G.DirectedCycle) (F F' : G.IntKFlow 2),
      (∀ e, F'.val e - F.val e = 2 * (cycles.map (fun C => C.sign e)).sum) →
      (∀ i j (hi : i < cycles.length) (hj : j < cycles.length), i ≠ j →
        Disjoint (cycles[i]'hi).sub.edges (cycles[j]'hj).sub.edges) →
      Relation.ReflTransGen G.IntKFlowMove F F' := by
  intro cycles
  induction cycles with
  | nil =>
    intro F F' hdiff _
    have hEq : F = F' := by
      ext e
      have h := hdiff e
      simp only [List.map_nil, List.sum_nil, mul_zero, sub_eq_zero] at h
      exact h.symm
    rw [hEq]
  | cons C rest ih =>
    intro F F' hdiff hdisj
    have hrest_zero : ∀ e ∈ C.sub.edges, (rest.map (fun D => D.sign e)).sum = 0 := by
      intro e heC
      apply List.sum_eq_zero
      intro x hx
      rw [List.mem_map] at hx
      rcases hx with ⟨D, hD, rfl⟩
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hD
      have hdj : Disjoint C.sub.edges (rest[j]'hj).sub.edges :=
        hdisj 0 (j + 1) (by simp) (by simp; omega) (by omega)
      have hnot : e ∉ (rest[j]'hj).sub.edges := Finset.disjoint_left.mp hdj heC
      exact (rest[j]'hj).sign_zero hnot
    let val₁ : E → ℤ := fun e => F.val e + C.sign e * 2
    have hflow₁ : G.IsFlow val₁ := by
      intro v
      have h1 := F.isFlow v
      have h2 := C.isFlow v
      have h3 : G.IsFlow (fun e => C.sign e • (2 : ℤ)) := isFlow_zsmul C.isFlow (2 : ℤ)
      have h4 := isFlow_add F.isFlow h3 v
      simpa [val₁, zsmul_eq_mul] using h4
    have hval₁_eq : ∀ e, val₁ e = F.val e ∨ val₁ e = F'.val e := by
      intro e
      by_cases he : e ∈ C.sub.edges
      · right
        have hd := hdiff e
        simp only [List.map_cons, List.sum_cons, hrest_zero e he, add_zero] at hd
        dsimp [val₁]
        linarith
      · left
        simp [val₁, C.sign_zero he]
    let F₁ : G.IntKFlow 2 :=
      { val := val₁
        isFlow := hflow₁
        nonzero := fun e => by
          rcases hval₁_eq e with h | h <;> rw [h]
          · exact F.nonzero e
          · exact F'.nonzero e
        bound := fun e => by
          rcases hval₁_eq e with h | h <;> rw [h]
          · exact F.bound e
          · exact F'.bound e }
    have hmove : G.IntKFlowMove F F₁ := ⟨C, 2, by decide, fun _ => rfl⟩
    have hdiff₁ : ∀ e, F'.val e - F₁.val e = 2 * (rest.map (fun D => D.sign e)).sum := by
      intro e
      have hd := hdiff e
      simp only [List.map_cons, List.sum_cons] at hd
      dsimp [F₁, val₁]
      linarith
    have hdisj₁ : ∀ i j (hi : i < rest.length) (hj : j < rest.length), i ≠ j →
        Disjoint (rest[i]'hi).sub.edges (rest[j]'hj).sub.edges := by
      intro i j hi hj hne
      exact hdisj (i + 1) (j + 1) (by simp; omega) (by simp; omega) (by omega)
    exact Relation.ReflTransGen.head hmove (ih F₁ F' hdiff₁ hdisj₁)

theorem sec1_trivial_int_k2_proved
    {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : Multigraph V E) :
    G.IntFlowConnected 2 := by
  intro F F'
  let h : E → ℤ := fun e => (F'.val e - F.val e) / 2
  have h2 : ∀ e, 2 * h e = F'.val e - F.val e := by
    intro e
    dsimp [h]
    rcases int_k2_val_eq_pm_one F e with hF | hF <;>
    rcases int_k2_val_eq_pm_one F' e with hF' | hF' <;>
    omega
  have hpm : ∀ e, h e = -1 ∨ h e = 0 ∨ h e = 1 := by
    intro e
    dsimp [h]
    rcases int_k2_val_eq_pm_one F e with hF | hF <;>
    rcases int_k2_val_eq_pm_one F' e with hF' | hF' <;>
    omega
  have hh : G.IsFlow h := by
    intro v
    have hdiff_flow : G.IsFlow (fun e => F'.val e - F.val e) := isFlow_sub F'.isFlow F.isFlow
    have hbv : G.boundary (fun e => 2 * h e) v = 0 := by
      have hfun : (fun e => 2 * h e) = (fun e => F'.val e - F.val e) := funext h2
      rw [hfun]
      exact hdiff_flow v
    have hsmul : G.boundary (fun e => 2 * h e) v = 2 * G.boundary h v := by
      unfold Multigraph.boundary
      simp only [← Finset.mul_sum, mul_sub]
    rw [hsmul] at hbv
    omega
  obtain ⟨cycles, hsum, _, _, _, hdisj⟩ := lem_2_1_b G h hh
  refine int_k2_step_list G cycles F F' (fun e => ?_) (hdisj hpm)
  rw [← hsum e, h2 e]

/-! ### Section 2: `FlowMove f g ↔ ∃ cycle C, C.edges = supp (g - f)` -/

private lemma subgraph_deg_eq_implies_edges_at {V E : Type} [DecidableEq V]
    {G : Multigraph V E} {C D : G.Subgraph} (hDC : D ≤ C)
    (v : V) (hdeg : D.deg v = C.deg v) :
    ∀ e ∈ C.edges, G.tail e = v ∨ G.head e = v → e ∈ D.edges := by
  have ht_sub : D.edges.filter (fun e => G.tail e = v) ⊆ C.edges.filter (fun e => G.tail e = v) :=
    Finset.filter_subset_filter _ hDC.2
  have hh_sub : D.edges.filter (fun e => G.head e = v) ⊆ C.edges.filter (fun e => G.head e = v) :=
    Finset.filter_subset_filter _ hDC.2
  have ht_le : (D.edges.filter (fun e => G.tail e = v)).card ≤
      (C.edges.filter (fun e => G.tail e = v)).card := Finset.card_le_card ht_sub
  have hh_le : (D.edges.filter (fun e => G.head e = v)).card ≤
      (C.edges.filter (fun e => G.head e = v)).card := Finset.card_le_card hh_sub
  unfold Multigraph.Subgraph.deg at hdeg
  have ht_eq : D.edges.filter (fun e => G.tail e = v) = C.edges.filter (fun e => G.tail e = v) :=
    Finset.eq_of_subset_of_card_le ht_sub (by omega)
  have hh_eq : D.edges.filter (fun e => G.head e = v) = C.edges.filter (fun e => G.head e = v) :=
    Finset.eq_of_subset_of_card_le hh_sub (by omega)
  intro e he hinc
  rcases hinc with ht | hh
  · have hmem : e ∈ C.edges.filter (fun e => G.tail e = v) := Finset.mem_filter.mpr ⟨he, ht⟩
    rw [← ht_eq] at hmem
    exact (Finset.mem_filter.mp hmem).1
  · have hmem : e ∈ C.edges.filter (fun e => G.head e = v) := Finset.mem_filter.mpr ⟨he, hh⟩
    rw [← hh_eq] at hmem
    exact (Finset.mem_filter.mp hmem).1

private lemma cycle_eq_of_le {V E : Type} [DecidableEq V]
    {G : Multigraph V E} {C D : G.Subgraph} (hC : C.IsCycle) (hD : D.IsCycle) (hDC : D ≤ C) :
    D = C := by
  have hverts : D.verts = C.verts := by
    apply Finset.Subset.antisymm hDC.1
    intro w hwC
    obtain ⟨v₀, hv₀D⟩ := hD.1.1
    have hpath := hC.1.2 v₀ (hDC.1 hv₀D) w hwC
    clear hwC
    induction hpath with
    | refl => exact hv₀D
    | @tail u z _ hstep ih =>
      rcases hstep with ⟨e, heC, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
      · have hdeg : D.deg u = C.deg u := by rw [hD.2 u ih, hC.2 u (hDC.1 ih)]
        have heD : e ∈ D.edges := subgraph_deg_eq_implies_edges_at hDC u hdeg e heC (Or.inl h1)
        simpa [h2] using D.head_mem heD
      · have hdeg : D.deg u = C.deg u := by rw [hD.2 u ih, hC.2 u (hDC.1 ih)]
        have heD : e ∈ D.edges := subgraph_deg_eq_implies_edges_at hDC u hdeg e heC (Or.inr h2)
        simpa [h1] using D.tail_mem heD
  have hedges : D.edges = C.edges := by
    apply Finset.Subset.antisymm hDC.2
    intro e heC
    have huC : G.tail e ∈ C.verts := C.tail_mem heC
    have huD : G.tail e ∈ D.verts := hverts ▸ huC
    have hdeg : D.deg (G.tail e) = C.deg (G.tail e) := by rw [hD.2 _ huD, hC.2 _ huC]
    exact subgraph_deg_eq_implies_edges_at hDC (G.tail e) hdeg e heC (Or.inl rfl)
  ext x
  · simp [hverts]
  · simp [hedges]

theorem sec2_move_iff_supp_cycle_proved
    {V E Γ : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    [AddCommGroup Γ] [DecidableEq Γ]
    (G : Multigraph V E) (f g : G.NZFlow Γ) :
    G.FlowMove f g ↔
      ∃ C : G.Subgraph, C.IsCycle ∧ C.edges = Multigraph.supp (fun e => g.val e - f.val e) := by
  constructor
  · rintro ⟨C, lam, hlam, heq⟩
    refine ⟨C.sub, C.isCycle, ?_⟩
    ext e
    simp only [Multigraph.supp, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [heq e, add_sub_cancel_left]
    constructor
    · intro he
      rcases C.sign_mem he with hs | hs
      · simpa [hs] using hlam
      · simpa [hs] using neg_ne_zero.mpr hlam
    · intro hne
      by_contra hnot
      rw [C.sign_zero hnot, zero_zsmul] at hne
      exact hne rfl
  · rintro ⟨C, hC, hsupp⟩
    have hne_e : C.edges.Nonempty := by
      obtain ⟨v, hv⟩ := hC.1.1
      have hdeg := hC.2 v hv
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty] at hempty
      simp [Multigraph.Subgraph.deg, hempty] at hdeg
    have hnodeg1 : ∀ v ∈ C.verts, C.deg v ≠ 1 := fun v hv => by rw [hC.2 v hv]; decide
    obtain ⟨D, hDC⟩ := exists_directedCycle_of_no_deg_one C hne_e hnodeg1
    have hDeq : D.sub = C := cycle_eq_of_le hC D.isCycle hDC
    obtain ⟨e₀, he₀C⟩ := hne_e
    have he₀D : e₀ ∈ D.sub.edges := hDeq ▸ he₀C
    let d : E → Γ := fun e => g.val e - f.val e
    have hd_flow : G.IsFlow d := isFlow_sub g.isFlow f.isFlow
    have hd_supp : ∀ e, d e ≠ 0 ↔ e ∈ C.edges := by
      intro e
      have hmem : e ∈ C.edges ↔ e ∈ Multigraph.supp d := by rw [hsupp]
      simpa [Multigraph.supp] using hmem.symm
    let lam : Γ := D.sign e₀ • d e₀
    have hlam_ne : lam ≠ 0 := by
      have hd₀ : d e₀ ≠ 0 := (hd_supp e₀).mpr he₀C
      rcases D.sign_mem he₀D with hs | hs
      · simpa [lam, hs] using hd₀
      · simpa [lam, hs] using neg_ne_zero.mpr hd₀
    have hsign_sq : D.sign e₀ • lam = d e₀ := by
      dsimp [lam]
      rcases D.sign_mem he₀D with hs | hs <;> simp [hs]
    let r : E → Γ := fun e => d e - D.sign e • lam
    have hr_flow : G.IsFlow r := isFlow_sub hd_flow (isFlow_zsmul D.isFlow lam)
    let T : G.Subgraph :=
      { verts := C.verts
        edges := C.edges.erase e₀
        tail_mem := fun he => C.tail_mem (Finset.mem_of_mem_erase he)
        head_mem := fun he => C.head_mem (Finset.mem_of_mem_erase he) }
    have hT_forest : T.IsForest := by
      intro K hKT hKcyc
      have hKC : K ≤ C := ⟨hKT.1, hKT.2.trans (Finset.erase_subset e₀ C.edges)⟩
      have hKeq : K = C := cycle_eq_of_le hC hKcyc hKC
      have he₀K : e₀ ∈ K.edges := hKeq ▸ he₀C
      exact (Finset.mem_erase.mp (hKT.2 he₀K)).1 rfl
    have hr_supp : ∀ e, r e ≠ 0 → e ∈ T.edges := by
      intro e hne
      by_cases heC : e ∈ C.edges
      · refine Finset.mem_erase.mpr ⟨?_, heC⟩
        rintro rfl
        exact hne (by simp [r, hsign_sq])
      · exfalso
        have hd0 : d e = 0 := by
          by_contra h
          exact heC ((hd_supp e).mp h)
        have hD0 : D.sign e = 0 := D.sign_zero (by rw [hDeq]; exact heC)
        exact hne (by simp [r, hd0, hD0])
    have hr_zero := flow_eq_zero_of_supp_subset_forest hT_forest hr_flow hr_supp
    refine ⟨D, lam, hlam_ne, fun e => ?_⟩
    have hre := hr_zero e
    dsimp [r, d] at hre
    exact eq_add_of_sub_eq' (sub_eq_zero.mp hre)

end Flow.Proofs
