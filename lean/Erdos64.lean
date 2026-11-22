import Mathlib

/-!
# Projeto Erdős #64 — Formalização em Lean 4 (`Checkpoint v1.4`)

Sincronizado com `README.md` e `Erdos64_lean.md` (Pós-Rodada 9, Progresso `24% / 100%`).
Lean `v4.36.0` / Mathlib `v4.36.0`: 0 erros, 0 avisos de linter e 9 avisos de `sorry`.

16 teoremas públicos verificados sem dependência de `sorry`:
- `HasPow2Cycle.map`, `HasPow2Cycle.mono`, `HasPow2Cycle.of_induce`
- `no_two_common_neighbors`, `common_neighbors_le_one`, `triangles_edge_disjoint`
- `minimal_connected`, `high_degree_independent`, `no_L3_vertices`
- `fullerene_euler_inequality`, `planar_girth5_no_C8_card_ge_60`
- `minimal_bridgeless`
- `bipartite_three_terminals_same_color`, `even_closed_walk_same_color_edges`,
  `two_join_edges_dyadic_residues` (lemas auxiliares do Teorema 19)
- `hex_has_cycle16_of_no_close_collision`

Em `hex_covering_has_cycle_4_8_16`, apenas o raio de colisão 6 mantém `sorry`.
-/

open SimpleGraph

namespace Erdos64

/-! ### Definições Fundamentais -/

/-- Um grafo `G` contém um ciclo simples de comprimento `2^k` para algum `k ≥ 2`. -/
def HasPow2Cycle {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ (v : V) (p : G.Walk v v) (k : ℕ), 2 ≤ k ∧ p.IsCycle ∧ p.length = 2 ^ k

/-- Enunciado oficial do Problema #64 de Erdős (Conjectura de Erdős–Gyárfás). -/
def ErdosGyarfasConjecture : Prop :=
  ∀ (V : Type) [Fintype V] [Nonempty V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj],
    (∀ v : V, 3 ≤ G.degree v) → HasPow2Cycle G

/-- Um grafo finito simples é um contraexemplo se possui δ(G) ≥ 3 e é livre de C_{2^k}. -/
def IsCounterexample {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  (∀ v : V, 3 ≤ G.degree v) ∧ ¬ HasPow2Cycle G

/-- Contraexemplo mínimo: menor número de vértices e, no empate, menor número de arestas. -/
def IsMinimalCounterexample {V : Type} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  IsCounterexample G ∧
  ∀ (W : Type) [Fintype W] [Nonempty W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj],
    IsCounterexample H →
      Fintype.card V < Fintype.card W ∨
      (Fintype.card V = Fintype.card W ∧ G.edgeFinset.card ≤ H.edgeFinset.card)

/-! ### Infraestrutura Formal: Transporte de Ciclos C_{2^k} — TODOS `VERIFIED` -/

/-- Qualquer homomorfismo injetivo de grafos preserva a existência de um ciclo C_{2^k}. -/
theorem HasPow2Cycle.map {V W : Type*} {H : SimpleGraph V} {G : SimpleGraph W}
    (f : H →g G) (hf : Function.Injective f) (h : HasPow2Cycle H) : HasPow2Cycle G := by
  rcases h with ⟨v, p, k, hk, hp, hlen⟩
  have hSym2 : Function.Injective (Sym2.map f) := by
    intro a b hab
    induction a using Sym2.ind with | _ a₁ a₂ =>
    induction b using Sym2.ind with | _ b₁ b₂ =>
    change s(f a₁, f a₂) = s(f b₁, f b₂) at hab
    rw [Sym2.eq_iff] at hab ⊢
    rcases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨hf h1, hf h2⟩
    · exact Or.inr ⟨hf h1, hf h2⟩
  refine ⟨f v, p.map f, k, hk, ?_, ?_⟩
  · cases p with
    | nil => exact absurd rfl hp.ne_nil
    | cons hstep q =>
      refine
        { edges_nodup := by
             rw [Walk.edges_map]
             exact hp.edges_nodup.map hSym2
          ne_nil := by simp
          support_nodup := by
            have hsup : q.support.Nodup := by
              simpa [Walk.support_cons] using hp.support_nodup
            simpa [Walk.map_cons, Walk.support_cons, Walk.support_map] using hsup.map hf }
  · rw [Walk.length_map, hlen]

/-- Subgrafos geradores (H ≤ G) preservam `HasPow2Cycle`. -/
theorem HasPow2Cycle.mono {V : Type*} {H G : SimpleGraph V} (hle : H ≤ G)
    (h : HasPow2Cycle H) : HasPow2Cycle G :=
  HasPow2Cycle.map (SimpleGraph.Hom.ofLE hle) Function.injective_id h

/-- Subgrafos induzidos preservam `HasPow2Cycle`. -/
theorem HasPow2Cycle.of_induce {V : Type*} {G : SimpleGraph V} {s : Set V}
    (h : HasPow2Cycle (G.induce s)) : HasPow2Cycle G :=
  HasPow2Cycle.map (SimpleGraph.Embedding.induce s).toHom Subtype.val_injective h

/-! ### Rodada 1: Propriedades Básicas (Lemas 1–4) — TODOS `VERIFIED` -/

/-- Lema 2 (versão estrutural): Em qualquer grafo livre de C_{2^k}, dois vértices distintos
têm no máximo um vizinho em comum (caso contrário formam um C_4). -/
theorem no_two_common_neighbors {V : Type*} (G : SimpleGraph V)
    (hfree : ¬ HasPow2Cycle G) {u v w₁ w₂ : V}
    (huv : u ≠ v)
    (huw₁ : G.Adj u w₁) (hvw₁ : G.Adj v w₁)
    (huw₂ : G.Adj u w₂) (hvw₂ : G.Adj v w₂) :
    w₁ = w₂ := by
  by_contra hw
  have hne_uw₁ : u ≠ w₁ := G.ne_of_adj huw₁
  have hne_uw₂ : u ≠ w₂ := G.ne_of_adj huw₂
  have hne_vw₁ : v ≠ w₁ := G.ne_of_adj hvw₁
  have hne_vw₂ : v ≠ w₂ := G.ne_of_adj hvw₂
  let p : G.Walk u u :=
    Walk.cons huw₁ (Walk.cons hvw₁.symm (Walk.cons hvw₂ (Walk.cons huw₂.symm Walk.nil)))
  have hp_cycle : p.IsCycle := by
    refine
      { edges_nodup := ?_
        ne_nil := by simp [p]
        support_nodup := ?_ }
    · simp only [p, Walk.edges_cons, Walk.edges_nil, List.nodup_cons, List.mem_cons,
        List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true, Sym2.eq_iff]
      refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;> tauto
    · simp only [p, Walk.support_cons, Walk.support_nil, List.tail_cons, List.nodup_cons,
        List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true]
      exact ⟨⟨hne_vw₁.symm, hw, hne_uw₁.symm⟩, ⟨hne_vw₂, huv.symm⟩, ⟨hne_uw₂.symm, not_false⟩⟩
  exact hfree ⟨u, p, 2, le_rfl, hp_cycle, rfl⟩

/-- Lema 2 (versão cardinalidade): O conjunto de vizinhos comuns de dois vértices distintos
tem cardinalidade no máximo 1. -/
theorem common_neighbors_le_one {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ HasPow2Cycle G) {u v : V} (huv : u ≠ v) :
    (G.commonNeighbors u v).toFinset.card ≤ 1 := by
  refine Finset.card_le_one.mpr ?_
  intro w₁ hw₁ w₂ hw₂
  simp only [Set.mem_toFinset, mem_commonNeighbors] at hw₁ hw₂
  exact no_two_common_neighbors G hfree huv hw₁.1 hw₁.2 hw₂.1 hw₂.2

/-- Lema 3: Em qualquer grafo livre de C_{2^k}, dois triângulos nunca compartilham uma aresta. -/
theorem triangles_edge_disjoint {V : Type*} (G : SimpleGraph V)
    (hfree : ¬ HasPow2Cycle G) {u v w₁ w₂ : V}
    (huv : G.Adj u v)
    (huw₁ : G.Adj u w₁) (hvw₁ : G.Adj v w₁)
    (huw₂ : G.Adj u w₂) (hvw₂ : G.Adj v w₂) :
    w₁ = w₂ :=
  no_two_common_neighbors G hfree (G.ne_of_adj huv) huw₁ hvw₁ huw₂ hvw₂

/-- Lema 1: Todo contraexemplo mínimo é conexo. -/
theorem minimal_connected {V : Type} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmin : IsMinimalCounterexample G) : G.Connected := by
  classical
  refine ⟨fun u₀ v₀ => ?_⟩
  by_contra hnr
  let S : Set V := {x : V | G.Reachable u₀ x}
  let W : Type := {x : V // x ∈ S}
  have : Nonempty W := ⟨⟨u₀, SimpleGraph.Reachable.refl u₀⟩⟩
  let H : SimpleGraph W := G.induce S
  have hfreeH : ¬ HasPow2Cycle H := fun h => hmin.1.2 (HasPow2Cycle.of_induce h)
  have hdegH : ∀ x : W, 3 ≤ H.degree x := by
    intro x
    have himg : (H.neighborFinset x).image Subtype.val = G.neighborFinset x.1 := by
      ext y
      simp only [Finset.mem_image, SimpleGraph.mem_neighborFinset, Subtype.exists]
      constructor
      · rintro ⟨w, _, hxw, rfl⟩
        exact hxw
      · intro hxy
        exact ⟨y, x.2.trans hxy.reachable, hxy, rfl⟩
    have hcard : H.degree x = G.degree x.1 := by
      rw [SimpleGraph.degree, SimpleGraph.degree, ← himg,
        Finset.card_image_of_injective _ Subtype.val_injective]
    rw [hcard]
    exact hmin.1.1 x.1
  have hlt : Fintype.card W < Fintype.card V := by
    have hss : Finset.univ.image (Subtype.val : W → V) ⊂ Finset.univ := by
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨Finset.subset_univ _, fun heq => ?_⟩
      have hv0 : v₀ ∈ Finset.univ.image (Subtype.val : W → V) := by
        rw [heq]; exact Finset.mem_univ v₀
      rcases Finset.mem_image.mp hv0 with ⟨w, _, rfl⟩
      exact hnr w.2
    have hcard := Finset.card_lt_card hss
    rw [Finset.card_image_of_injective _ Subtype.val_injective,
      Finset.card_univ, Finset.card_univ] at hcard
    exact hcard
  have hcmp := hmin.2 W H ⟨hdegH, hfreeH⟩
  omega

/-- Lema 4: Em um contraexemplo mínimo, os vértices de grau ≥ 4 formam conjunto independente. -/
theorem high_degree_independent {V : Type} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmin : IsMinimalCounterexample G) {u v : V}
    (hu : 4 ≤ G.degree u) (hv : 4 ≤ G.degree v) : ¬ G.Adj u v := by
  classical
  intro huv
  have huv_ne : u ≠ v := G.ne_of_adj huv
  let H : SimpleGraph V := G.deleteEdges {s(u, v)}
  have hHG : H ≤ G := G.deleteEdges_le _
  have hfreeH : ¬ HasPow2Cycle H := fun h => hmin.1.2 (HasPow2Cycle.mono hHG h)
  have hdegH : ∀ x : V, 3 ≤ H.degree x := by
    intro x
    by_cases hxu : x = u
    · subst hxu
      have hnb : H.neighborFinset x = (G.neighborFinset x).erase v := by
        ext y
        simp [H, SimpleGraph.mem_neighborFinset, SimpleGraph.deleteEdges_adj,
          Set.mem_singleton_iff, Finset.mem_erase, huv_ne]; tauto
      have hv_mem : v ∈ G.neighborFinset x := by
        simpa [SimpleGraph.mem_neighborFinset] using huv
      rw [SimpleGraph.degree, hnb, Finset.card_erase_of_mem hv_mem]
      change 3 ≤ G.degree x - 1
      omega
    · by_cases hxv : x = v
      · subst hxv
        have hnb : H.neighborFinset x = (G.neighborFinset x).erase u := by
          ext y
          simp [H, SimpleGraph.mem_neighborFinset, SimpleGraph.deleteEdges_adj,
            Set.mem_singleton_iff, Finset.mem_erase, huv_ne.symm]; tauto
        have hu_mem : u ∈ G.neighborFinset x := by
          simpa [SimpleGraph.mem_neighborFinset] using huv.symm
        rw [SimpleGraph.degree, hnb, Finset.card_erase_of_mem hu_mem]
        change 3 ≤ G.degree x - 1
        omega
      · have hnb : H.neighborFinset x = G.neighborFinset x := by
          ext y
          simp [H, SimpleGraph.mem_neighborFinset, SimpleGraph.deleteEdges_adj,
            Set.mem_singleton_iff, hxu, hxv]
        rw [SimpleGraph.degree, hnb]
        exact hmin.1.1 x
  have hedge_lt : H.edgeFinset.card < G.edgeFinset.card := by
    refine Finset.card_lt_card ?_
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨?_, ?_⟩
    · intro e he
      induction e using Sym2.ind with | _ a b =>
      simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he ⊢
      exact hHG he
    · intro heq
      have hmemG : s(u, v) ∈ G.edgeFinset := SimpleGraph.mem_edgeFinset.mpr huv
      rw [← heq] at hmemG
      have hmemH : H.Adj u v := SimpleGraph.mem_edgeFinset.mp hmemG
      simp [H, SimpleGraph.deleteEdges_adj] at hmemH
  have hcmp := hmin.2 V H ⟨hdegH, hfreeH⟩
  omega

/-! ### Rodada 2: Conectividade (Lema 5) -/

/-- Duas cópias do conjunto de vértices com uma única cópia da raiz. -/
private abbrev RootDouble {W : Type} (r : W) :=
  {p : W × Bool // p.1 = r → p.2 = false}

private def doubleRoot {W : Type} (r : W) : RootDouble r :=
  ⟨(r, false), fun _ => rfl⟩

private theorem double_eq_root {W : Type} {r : W} (x : RootDouble r)
    (hx : x.val.1 = r) : x = doubleRoot r :=
  Subtype.ext (Prod.ext hx (x.property hx))

private def doubleGraph {W : Type} (A : SimpleGraph W) (r : W) :
    SimpleGraph (RootDouble r) where
  Adj x y := A.Adj x.val.1 y.val.1 ∧
    (x.val.2 = y.val.2 ∨ x = doubleRoot r ∨ y = doubleRoot r)
  symm := ⟨by
    intro x y h
    exact ⟨h.1.symm, by tauto⟩⟩
  loopless := ⟨fun _ h => A.ne_of_adj h.1 rfl⟩

private theorem double_walk_side {W : Type} {r : W} {A : SimpleGraph W}
    {x y : RootDouble r} (p : (doubleGraph A r).Walk x y)
    (hr : doubleRoot r ∉ p.support.dropLast) :
    ∀ z ∈ p.support, z ≠ doubleRoot r → z.val.2 = x.val.2 := by
  induction p with
  | nil => simp
  | @cons x a y hxa q ih =>
    rw [Walk.support_cons, List.dropLast_cons_of_ne_nil q.support_ne_nil,
      List.mem_cons, not_or] at hr
    intro z hz hzr
    rw [Walk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · rfl
    · have har : a ≠ doubleRoot r := by
        intro ha
        subst a
        cases q with
        | nil => exact hzr (by simpa using hz)
        | cons h q =>
          exact hr.2 (by
            rw [Walk.support_cons, List.dropLast_cons_of_ne_nil q.support_ne_nil]
            exact List.mem_cons_self)
      have hbit := hxa.2.resolve_right (fun h => h.elim (Ne.symm hr.1) har)
      exact (ih hr.2 z hz hzr).trans hbit.symm

private theorem double_cycle_fold {W : Type} {r : W} {A : SimpleGraph W}
    {x : RootDouble r} (p : (doubleGraph A r).Walk x x) (hp : p.IsCycle)
    (hr : doubleRoot r ∉ p.tail.support.dropLast) :
    let f : doubleGraph A r →g A := ⟨fun z => z.val.1, fun h => h.1⟩
    (p.map f).IsCycle := by
  intro f
  refine Walk.isCycle_iff_isPath_tail_and_le_length.mpr ⟨?_, by simpa using hp.three_le_length⟩
  rw [Walk.isPath_def, (p.map f).support_tail_of_not_nil (by simpa using hp.not_nil),
    Walk.support_map, ← List.map_tail, ← p.support_tail_of_not_nil hp.not_nil]
  apply hp.isPath_tail.support_nodup.map_on
  intro a ha b hb hab
  change a.val.1 = b.val.1 at hab
  by_cases ha' : a.val.1 = r
  · exact (double_eq_root a ha').trans (double_eq_root b (hab.symm.trans ha')).symm
  · have hne (z : RootDouble r) (hz : z.val.1 ≠ r) : z ≠ doubleRoot r :=
      fun h => hz (congrArg (fun t : RootDouble r => t.val.1) h)
    have hbitA := double_walk_side p.tail hr a ha (hne a ha')
    have hbitB := double_walk_side p.tail hr b hb (hne b (fun hb' => ha' (hab.trans hb')))
    exact Subtype.ext (Prod.ext hab (hbitA.trans hbitB.symm))

private theorem double_hasPow2Cycle {W : Type} {A : SimpleGraph W} (r : W)
    (h : HasPow2Cycle (doubleGraph A r)) : HasPow2Cycle A := by
  classical
  rcases h with ⟨x, p, k, hk, hp, hlen⟩
  let f : doubleGraph A r →g A := ⟨fun z => z.val.1, fun h => h.1⟩
  suffices ∀ {y : RootDouble r} (q : (doubleGraph A r).Walk y y),
      q.IsCycle → q.length = 2 ^ k → doubleRoot r ∉ q.tail.support.dropLast →
      HasPow2Cycle A by
    by_cases hr : doubleRoot r ∈ p.support
    · let q := p.rotate (doubleRoot r) hr
      have hq : q.IsCycle := hp.rotate hr
      apply this q hq (by simpa [q] using hlen)
      have hn := hq.isPath_tail.support_nodup
      rw [← q.tail.dropLast_support_concat] at hn
      intro hm
      exact List.disjoint_of_nodup_append hn hm (by simp)
    · apply this p hp hlen
      intro hm
      apply hr
      rw [← p.cons_support_tail hp.not_nil]
      exact List.mem_cons_of_mem _ (List.mem_of_mem_dropLast hm)
  intro y q hq hqLen hr
  exact ⟨f y, q.map f, k, hk, double_cycle_fold q hq hr, by simpa using hqLen⟩

private theorem double_minDegree {W : Type} [Fintype W] [DecidableEq W]
    (A : SimpleGraph W) [DecidableRel A.Adj] (r : W)
    [Fintype (RootDouble r)] [DecidableRel (doubleGraph A r).Adj]
    (hr : 2 ≤ A.degree r) (hdeg : ∀ x ≠ r, 3 ≤ A.degree x)
    (x : RootDouble r) : 3 ≤ (doubleGraph A r).degree x := by
  classical
  let D := doubleGraph A r
  change 3 ≤ D.degree x
  by_cases hx : x = doubleRoot r
  · subst x
    let f : A.neighborSet r × Bool → D.neighborSet (doubleRoot r) :=
      fun ⟨y, b⟩ => ⟨⟨(y, b), fun hy => (A.ne_of_adj y.property hy.symm).elim⟩,
        y.property, Or.inr (Or.inl rfl)⟩
    have hf : Function.Injective f := by
      intro ⟨y, b⟩ ⟨z, c⟩ h
      have he : (y.val, b) = (z.val, c) :=
        congrArg (fun w : D.neighborSet (doubleRoot r) => w.val.val) h
      exact Prod.ext (Subtype.ext (congrArg Prod.fst he))
        (congrArg (fun w : W × Bool => w.2) he)
    have hc := Fintype.card_le_of_injective f hf
    rw [Fintype.card_prod, A.card_neighborSet_eq_degree, D.card_neighborSet_eq_degree] at hc
    simp only [Fintype.card_bool] at hc
    omega
  · let b := x.val.2
    let f : A.neighborSet x.val.1 → D.neighborSet x := fun y =>
      ⟨⟨(y, if y.val = r then false else b), fun h => by
          change y.val = r at h
          simp [h]⟩, y.property, by
        by_cases hy : y.val = r
        · right
          exact Or.inr (double_eq_root _ hy)
        · left
          simp [hy, b]⟩
    have hf : Function.Injective f := by
      intro y z h
      exact Subtype.ext (congrArg (fun w : D.neighborSet x => w.val.val.1) h)
    have hc := Fintype.card_le_of_injective f hf
    rw [A.card_neighborSet_eq_degree, D.card_neighborSet_eq_degree] at hc
    exact (hdeg _ (fun he => hx (double_eq_root x he))).trans hc

private theorem bridge_side_too_small {V : Type} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hmin : IsMinimalCounterexample G)
    {u v : V} (hb : G.IsBridge s(u, v))
    (hsmall : 2 * Fintype.card {x : V // (G.deleteEdges {s(u, v)}).Reachable u x} ≤
      Fintype.card V) : False := by
  classical
  let D := G.deleteEdges {s(u, v)}
  let S : Set V := {x | D.Reachable u x}
  let W := {x : V // x ∈ S}
  let r : W := ⟨u, Reachable.refl u⟩
  let A := G.induce S
  have hv : v ∉ S := hb
  have hfree : ¬ HasPow2Cycle A := fun h => hmin.1.2 (HasPow2Cycle.of_induce h)
  have hcard (x : W) : A.degree x = ((G.neighborFinset x.val).erase v).card := by
    have hnb : (A.neighborFinset x).image Subtype.val = (G.neighborFinset x.val).erase v := by
      ext y
      simp only [Finset.mem_image, SimpleGraph.mem_neighborFinset, Finset.mem_erase, Subtype.exists]
      constructor
      · rintro ⟨z, hz, hxz, rfl⟩
        exact ⟨fun h => hv (h ▸ hz), hxz⟩
      · rintro ⟨hyv, hxy⟩
        have hD : D.Adj x.val y := by
          refine SimpleGraph.deleteEdges_adj.mpr ⟨hxy, ?_⟩
          simp only [Set.mem_singleton_iff, Sym2.eq_iff]
          exact fun h => h.elim (fun h => hyv h.2) (fun h => hv (h.1 ▸ x.property))
        exact ⟨y, x.property.trans hD.reachable, hxy, rfl⟩
    rw [SimpleGraph.degree, ← hnb, Finset.card_image_of_injective _ Subtype.val_injective]
  have hcross (x : W) (hx : G.Adj x.val v) : x = r := by
    by_contra hne
    have hD : D.Adj x.val v := by
      refine SimpleGraph.deleteEdges_adj.mpr ⟨hx, ?_⟩
      simp only [Set.mem_singleton_iff, Sym2.eq_iff]
      exact fun h => h.elim (fun h => hne (Subtype.ext h.1)) (fun h => hv (h.1 ▸ x.property))
    exact hv (x.property.trans hD.reachable)
  have hr : 2 ≤ A.degree r := by
    have ha := hb.reachable_iff_adj.mp ((minimal_connected G hmin).preconnected u v)
    have hm : v ∈ G.neighborFinset r.val := by
      simpa [SimpleGraph.mem_neighborFinset] using ha
    rw [hcard, Finset.card_erase_of_mem hm]
    have hd := hmin.1.1 r.val
    change 2 ≤ G.degree r.val - 1
    omega
  have hdeg (x : W) (hx : x ≠ r) : 3 ≤ A.degree x := by
    have hm : v ∉ G.neighborFinset x.val :=
      fun h => hx (hcross x (by simpa [SimpleGraph.mem_neighborFinset] using h))
    rw [hcard, Finset.erase_eq_of_notMem hm]
    exact hmin.1.1 x.val
  let T := RootDouble r
  have : Nonempty T := ⟨doubleRoot r⟩
  have hlt : Fintype.card T < Fintype.card V := by
    have ht : Fintype.card T < Fintype.card (W × Bool) := by
      refine Fintype.card_lt_of_injective_not_surjective Subtype.val Subtype.val_injective ?_
      intro hs
      obtain ⟨z, hz⟩ := hs (r, true)
      have hfalse : true = false :=
        (hz ▸ z.property : (r, true).1 = r → (r, true).2 = false) rfl
      cases hfalse
    apply lt_of_lt_of_le ht
    rw [Fintype.card_prod, Fintype.card_bool, Nat.mul_comm]
    exact hsmall
  have hce : IsCounterexample (doubleGraph A r) :=
    ⟨double_minDegree A r hr hdeg, fun h => hfree (double_hasPow2Cycle r h)⟩
  have hcmp := hmin.2 T (doubleGraph A r) hce
  omega

/-- Lema 5: Todo contraexemplo mínimo não possui pontes (é 2-aresta-conexo). -/
theorem minimal_bridgeless {V : Type} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmin : IsMinimalCounterexample G) (e : Sym2 V) : ¬ G.IsBridge e := by
  classical
  induction e using Sym2.ind with | _ u v =>
  intro hb
  let D := G.deleteEdges {s(u, v)}
  let U := {x : V // D.Reachable u x}
  let W := {x : V // D.Reachable v x}
  let f : U ⊕ W → V := Sum.elim Subtype.val Subtype.val
  have hf : Function.Injective f := by
    intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (Subtype.ext h)
      | inr b =>
        change a.val = b.val at h
        exact (hb (a.property.trans (h.symm ▸ b.property).symm)).elim
    | inr a =>
      cases b with
      | inl b =>
        change a.val = b.val at h
        exact (hb (b.property.trans (h ▸ a.property).symm)).elim
      | inr b => exact congrArg Sum.inr (Subtype.ext h)
  have hcard := Fintype.card_le_of_injective f hf
  rw [Fintype.card_sum] at hcard
  by_cases hs : 2 * Fintype.card U ≤ Fintype.card V
  · exact bridge_side_too_small G hmin hb hs
  · have ht : 2 * Fintype.card W ≤ Fintype.card V := by omega
    rw [Sym2.eq_swap (a := u) (b := v)] at hb
    exact bridge_side_too_small G hmin hb (by simpa [W, D, Sym2.eq_swap (a := v) (b := u)] using ht)

/-! ### Rodada 3: Teorema do Cacto de Triângulos (Teorema 7) -/

/-- Subgrafo `G_Δ` das arestas que pertencem a pelo menos um triângulo em `G`. -/
def triangleSubgraph {V : Type*} (G : SimpleGraph V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ ∃ w : V, G.Adj u w ∧ G.Adj v w
  symm := ⟨by
    rintro u v ⟨huv, w, huw, hvw⟩
    exact ⟨huv.symm, w, hvw, huw⟩⟩
  loopless := ⟨by
    rintro v ⟨hvv, _⟩
    exact G.ne_of_adj hvv rfl⟩


/-! ### Lemas auxiliares do Teorema 7 (Quest, ramo `quest-provas`) -/

theorem triangleSubgraph_le {V : Type*} (G : SimpleGraph V) : triangleSubgraph G ≤ G :=
  fun _ _ h => h.1

/-- Um ciclo de comprimento 4 já é um `C_{2^2}`. -/
theorem hasPow2Cycle_of_cycle_four {V : Type*} {G : SimpleGraph V} {v : V}
    (p : G.Walk v v) (hp : p.IsCycle) (h4 : p.length = 4) : HasPow2Cycle G :=
  ⟨v, p, 2, le_rfl, hp, by simpa using h4⟩

/-- Desvio por um ápice: trocar a primeira aresta `v a` de um ciclo por `v w a`, com `w` fora do
ciclo, gera um ciclo de comprimento uma unidade maior. -/
theorem cycle_detour_cons {V : Type*} {G : SimpleGraph V} {v a w : V}
    (h : G.Adj v a) (q : G.Walk a v) (hc : (Walk.cons h q).IsCycle)
    (hvw : G.Adj v w) (hwa : G.Adj w a) (hw : w ∉ (Walk.cons h q).support) :
    (Walk.cons hvw (Walk.cons hwa q)).IsCycle ∧
      (Walk.cons hvw (Walk.cons hwa q)).length = (Walk.cons h q).length + 1 := by
  rw [Walk.cons_isCycle_iff] at hc
  have hwq : w ∉ q.support := fun hm => hw (by simp [hm])
  have hwv : w ≠ v := fun e => hw (by simp [e])
  refine ⟨?_, by simp⟩
  rw [Walk.cons_isCycle_iff, Walk.cons_isPath_iff]
  refine ⟨⟨hc.1, hwq⟩, ?_⟩
  intro hm
  rw [Walk.edges_cons, List.mem_cons] at hm
  rcases hm with he | he
  · rw [Sym2.eq_iff] at he
    rcases he with ⟨h1, _⟩ | ⟨h1, h2⟩
    · exact hwv h1.symm
    · exact G.ne_of_adj h h1
  · exact hwq (Walk.snd_mem_support_of_mem_edges q he)

/-- Teorema 7: Em qualquer grafo livre de C_{2^k}, `G_Δ` não possui ciclos de comprimento ≥ 4. -/
theorem triangle_cactus_no_long_cycle {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hfree : ¬ HasPow2Cycle G) :
    ∀ (v : V) (p : (triangleSubgraph G).Walk v v), p.IsCycle → p.length = 3 := by
  sorry

/-! ### Rodada 4: Componentes de V_3 e Pisos de Cubicidade (Teoremas 8–10) -/

/-- Corolário 8.1 (`VERIFIED`): Em um contraexemplo mínimo, todo vértice de grau 3 tem pelo
menos um vizinho de grau 3 (ou seja, L_3 = ∅). -/
theorem no_L3_vertices {V : Type} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmin : IsMinimalCounterexample G) {v : V} (hv : G.degree v = 3) :
    ∃ u : V, G.Adj v u ∧ G.degree u = 3 := by
  classical
  by_contra hno
  push Not at hno
  have hnb_ge4 : ∀ u : V, G.Adj v u → 4 ≤ G.degree u := by
    intro u hvu
    have h3 : 3 ≤ G.degree u := hmin.1.1 u
    have hne : G.degree u ≠ 3 := hno u hvu
    omega
  have hne_nb : (G.neighborFinset v).Nonempty := by
    rw [← Finset.card_pos]
    change 0 < G.degree v
    omega
  rcases hne_nb with ⟨u₀, hu₀⟩
  have hvu₀ : G.Adj v u₀ := by
    simpa [SimpleGraph.mem_neighborFinset] using hu₀
  have hu₀_ne : u₀ ≠ v := (G.ne_of_adj hvu₀).symm
  let S : Set V := {x : V | x ≠ v}
  let W : Type := {x : V // x ∈ S}
  have : Nonempty W := ⟨⟨u₀, hu₀_ne⟩⟩
  let H : SimpleGraph W := G.induce S
  have hfreeH : ¬ HasPow2Cycle H := fun h => hmin.1.2 (HasPow2Cycle.of_induce h)
  have hdegH : ∀ x : W, 3 ≤ H.degree x := by
    intro x
    have himg : (H.neighborFinset x).image Subtype.val = (G.neighborFinset x.1).erase v := by
      ext y
      simp only [Finset.mem_image, SimpleGraph.mem_neighborFinset, Finset.mem_erase, Subtype.exists]
      constructor
      · rintro ⟨w, hw, hxw, rfl⟩
        exact ⟨hw, hxw⟩
      · rintro ⟨hyv, hxy⟩
        exact ⟨y, hyv, hxy, rfl⟩
    have hcard : H.degree x = ((G.neighborFinset x.1).erase v).card := by
      rw [SimpleGraph.degree, ← himg, Finset.card_image_of_injective _ Subtype.val_injective]
    rw [hcard]
    by_cases hxv : G.Adj x.1 v
    · have hv_mem : v ∈ G.neighborFinset x.1 := by
        simpa [SimpleGraph.mem_neighborFinset] using hxv
      rw [Finset.card_erase_of_mem hv_mem]
      have h4 := hnb_ge4 x.1 hxv.symm
      change 3 ≤ G.degree x.1 - 1
      omega
    · have herase : (G.neighborFinset x.1).erase v = G.neighborFinset x.1 := by
        ext y
        simp only [Finset.mem_erase, SimpleGraph.mem_neighborFinset]
        exact ⟨fun h => h.2, fun hxy => ⟨fun hyv => hxv (hyv ▸ hxy), hxy⟩⟩
      rw [herase]
      exact hmin.1.1 x.1
  have hlt : Fintype.card W < Fintype.card V := by
    have hss : Finset.univ.image (Subtype.val : W → V) ⊂ Finset.univ := by
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨Finset.subset_univ _, fun heq => ?_⟩
      have hv_mem : v ∈ Finset.univ.image (Subtype.val : W → V) := by
        rw [heq]; exact Finset.mem_univ v
      rcases Finset.mem_image.mp hv_mem with ⟨w, _, hwv⟩
      exact w.2 hwv
    have hcard := Finset.card_lt_card hss
    rw [Finset.card_image_of_injective _ Subtype.val_injective,
      Finset.card_univ, Finset.card_univ] at hcard
    exact hcard
  have hcmp := hmin.2 W H ⟨hdegH, hfreeH⟩
  omega

/-- Teorema 10a: Todo contraexemplo mínimo sem triângulos satisfaz |V_3| ≥ (8/11) |V|. -/
theorem minimal_triangle_free_cubicity {V : Type} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmin : IsMinimalCounterexample G)
    (htf : G.CliqueFree 3) :
    8 * Fintype.card V ≤ 11 * (Finset.univ.filter (fun v : V => G.degree v = 3)).card := by
  sorry

/-- Teorema 10b: Todo contraexemplo mínimo bipartido satisfaz |V_3| ≥ (20/27) |V|. -/
theorem minimal_bipartite_cubicity {V : Type} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmin : IsMinimalCounterexample G)
    (hbip : ∃ c : V → Bool, ∀ u v : V, G.Adj u v → c u ≠ c v) :
    20 * Fintype.card V ≤ 27 * (Finset.univ.filter (fun v : V => G.degree v = 3)).card := by
  sorry

/-! ### Rodada 5: Autorredução de K_3-fatores e C_5-fatores (Teoremas 11–12) -/

/-- Partição de `V` em ciclos disjuntos de comprimento `d` (d-fator puro). -/
def HasPureCycleFactor {V : Type*} [Fintype V] (G : SimpleGraph V) (d : ℕ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (f : ι → Fin d → V),
    Function.Bijective (fun p : ι × Fin d => f p.1 p.2) ∧
    ∀ (i : ι) (j : Fin d),
      G.Adj (f i j) (f i ⟨(j.val + 1) % d, Nat.mod_lt _ (by have := j.isLt; omega)⟩)

/-- Teorema 11: Nenhum contraexemplo mínimo é cúbico com um K_3-fator. -/
theorem minimal_no_K3_factor {V : Type} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmin : IsMinimalCounterexample G)
    (hcubic : G.IsRegularOfDegree 3) :
    ¬ HasPureCycleFactor G 3 := by
  sorry

/-- Teorema 12: Nenhum contraexemplo mínimo é cúbico com um C_5-fator. -/
theorem minimal_no_C5_factor {V : Type} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmin : IsMinimalCounterexample G)
    (hcubic : G.IsRegularOfDegree 3) :
    ¬ HasPureCycleFactor G 5 := by
  sorry

/-! ### Rodada 6: Redução à Metade em Bipartidos Não-3-Conexos (Teorema 13) -/
/-- Um grafo possui um corte de vértices de tamanho ≤ 2 se remover um conjunto `S` de tamanho ≤ 2
torna o subgrafo induzido em `Sᶜ` desconexo. -/
def HasSmallVertexCut {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∃ S : Finset V, S.card ≤ 2 ∧ ¬ (G.induce (S : Set V)ᶜ).Connected

/-- Teorema 13 (versão de redução de ordem): Todo contraexemplo bipartido com corte de ≤ 2 vértices
produz um contraexemplo simples de ordem no máximo ⌊(|V| + 2) / 2⌋. -/
theorem bipartite_not_3connected_halving {V : Type} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hce : IsCounterexample G)
    (hbip : ∃ c : V → Bool, ∀ u v : V, G.Adj u v → c u ≠ c v)
    (hcut : HasSmallVertexCut G) :
    ∃ (W : Type) (_ : Fintype W) (_ : Nonempty W) (_ : DecidableEq W)
      (H : SimpleGraph W) (_ : DecidableRel H.Adj),
      IsCounterexample H ∧ 2 * Fintype.card W ≤ Fintype.card V + 2 := by
  sorry

/-! ### Rodada 7: Degeneração dos Triângulos L_2 e Cubicidade Geral (Teorema 15) -/

/-- Corolário 15.1: Em todo contraexemplo mínimo geral, 3 |V_3| ≥ 2 |V| + 1 (ou seja, |V_3| > 2/3 |V|). -/
theorem minimal_general_cubicity {V : Type} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmin : IsMinimalCounterexample G) :
    2 * Fintype.card V + 1 ≤ 3 * (Finset.univ.filter (fun v : V => G.degree v = 3)).card := by
  sorry

/-- Corolário 15.2: Se nenhum par de vértices adjacentes em V_3 forma componente K_2 em G[V_3]
(isto é, S = ∅), então |V_3| ≥ (12/17) |V|. -/
theorem minimal_no_K2_in_V3_cubicity {V : Type} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmin : IsMinimalCounterexample G)
    (hnoK2 : ∀ u v : V, G.Adj u v → G.degree u = 3 → G.degree v = 3 →
      ∃ w : V, w ≠ u ∧ w ≠ v ∧ G.degree w = 3 ∧ (G.Adj u w ∨ G.Adj v w)) :
    12 * Fintype.card V ≤ 17 * (Finset.univ.filter (fun v : V => G.degree v = 3)).card := by
  sorry

/-! ### Rodada 8: Recobrimento Hexagonal (Teorema 17) e Desigualdade do Fulereno (Teorema 18) -/

/-- A rede hexagonal infinita `H` sobre `ℤ × ℤ × Bool`, onde `(x, y, false)` é adjacente a
`(x, y, true)`, `(x - 1, y, true)` e `(x, y - 1, true)`. -/
def hexLattice : SimpleGraph (ℤ × ℤ × Bool) where
  Adj u v :=
    (u.2.2 = false ∧ v.2.2 = true ∧
      ((v.1 = u.1 ∧ v.2.1 = u.2.1) ∨
       (v.1 = u.1 - 1 ∧ v.2.1 = u.2.1) ∨
       (v.1 = u.1 ∧ v.2.1 = u.2.1 - 1))) ∨
    (v.2.2 = false ∧ u.2.2 = true ∧
      ((u.1 = v.1 ∧ u.2.1 = v.2.1) ∨
       (u.1 = v.1 - 1 ∧ u.2.1 = v.2.1) ∨
       (u.1 = v.1 ∧ u.2.1 = v.2.1 - 1)))
  symm := ⟨by
    rintro u v (h | h)
    · exact Or.inr h
    · exact Or.inl h⟩
  loopless := ⟨by
    rintro ⟨x, y, c⟩ (⟨h1, h2, _⟩ | ⟨h1, h2, _⟩)
    · rw [h1] at h2; cases h2
    · rw [h1] at h2; cases h2⟩

/-- Um homomorfismo `π : H →g G` é um recobrimento de grafos (isomorfismo local) se induz
uma bijeção entre as vizinhanças de cada vértice `u` e de `π u`. -/
def IsGraphCovering {U V : Type*} {H : SimpleGraph U} {G : SimpleGraph V}
    (π : H →g G) : Prop :=
  ∀ u : U,
    (∀ v₁ v₂ : U, H.Adj u v₁ → H.Adj u v₂ → π v₁ = π v₂ → v₁ = v₂) ∧
    (∀ w : V, G.Adj (π u) w → ∃ v : U, H.Adj u v ∧ π v = w)

private theorem walk_dist_le_of_mem_support {V : Type*} {H : SimpleGraph V}
    {x y : V} (p : H.Walk x y) {u v : V} (hu : u ∈ p.support) (hv : v ∈ p.support) :
    H.dist u v ≤ p.length := by
  classical
  induction p with
  | @nil z =>
    have hu' : u = z := by simpa using hu
    have hv' : v = z := by simpa using hv
    subst u
    subst v
    simp
  | @cons x z y hxz q ih =>
    rw [Walk.support_cons, List.mem_cons] at hu hv
    rcases hu with rfl | hu
    · let p := q.cons hxz
      have hv' : v ∈ p.support := by simpa [p, Walk.support_cons] using hv
      exact (H.dist_le (p.takeUntil v hv')).trans (p.length_takeUntil_le_length hv')
    · rcases hv with rfl | hv
      · let p := q.cons hxz
        have hu' : u ∈ p.support := by simp [p, Walk.support_cons, hu]
        rw [H.dist_comm]
        exact (H.dist_le (p.takeUntil u hu')).trans (p.length_takeUntil_le_length hu')
      · exact (ih hu hv).trans (by simp)

/-- A projeção de um caminho mínimo entre os extremos da primeira colisão de um
homomorfismo é um ciclo quando o comprimento é pelo menos três. -/
private theorem shortest_collision_projects_cycle {U V : Type*} {H : SimpleGraph U} {G : SimpleGraph V}
    (π : H →g G) {x y : U} (p : H.Walk x y) (hshort : p.length = H.dist x y)
    (h3 : 3 ≤ p.length) (himage : π x = π y)
    (hsep : ∀ a b, H.Reachable a b → H.dist a b < p.length → π a = π b → a = b) :
    ∃ (v : V) (q : G.Walk v v), q.IsCycle ∧ q.length = p.length := by
  let q := (p.map π).copy rfl himage.symm
  have hlen : q.length = p.length := by simp [q]
  have hp : ¬ p.Nil := Walk.not_nil_iff_lt_length.mpr (by omega)
  have hq : ¬ q.Nil := Walk.not_nil_iff_lt_length.mpr (by omega)
  refine ⟨π x, q, Walk.isCycle_iff_isPath_tail_and_le_length.mpr ⟨?_, hlen.symm ▸ h3⟩, hlen⟩
  rw [Walk.isPath_def, q.support_tail_of_not_nil hq]
  simp only [q, Walk.support_copy, Walk.support_map, ← List.map_tail, ← p.support_tail_of_not_nil hp]
  apply (p.isPath_of_length_eq_dist hshort).tail.support_nodup.map_on
  intro a ha b hb hab
  apply hsep a b (Walk.reachable_of_mem_support ha hb) _ hab
  have hdist := walk_dist_le_of_mem_support p.tail ha hb
  rw [Walk.length_tail] at hdist
  omega

/-- Vértices do trapézio de cinco hexágonos, com a borda em ordem cíclica nas
primeiras 16 posições e os três vértices internos nas últimas posições. -/
private def hexPatchVertex : Fin 19 → ℤ × ℤ × Bool :=
  ![(0, 0, false), (0, -1, true), (1, -1, false), (1, -1, true),
    (2, -1, false), (2, -1, true), (3, -1, false), (3, -1, true),
    (3, 0, false), (2, 0, true), (2, 1, false), (1, 1, true),
    (1, 1, false), (0, 1, true), (0, 1, false), (0, 0, true),
    (1, 0, false), (1, 0, true), (2, 0, false)]

private def hexBoundaryIndex (i : Fin 16) : Fin 19 :=
  ⟨i.val, i.isLt.trans (by decide)⟩

private instance : DecidableRel hexLattice.Adj := by
  intro x y
  unfold hexLattice
  infer_instance

private def hexPatchBall (x : Fin 19) : ℕ → Finset (Fin 19)
  | 0 => {x}
  | n + 1 => (hexPatchBall x n).biUnion fun z =>
      insert z (Finset.univ.filter fun y => hexLattice.Adj (hexPatchVertex z) (hexPatchVertex y))

private theorem hexPatchBall_walk (x : Fin 19) (n : ℕ) {y : Fin 19}
    (hy : y ∈ hexPatchBall x n) :
    ∃ p : hexLattice.Walk (hexPatchVertex x) (hexPatchVertex y), p.length ≤ n := by
  induction n generalizing y with
  | zero =>
    have h : y = x := by simpa [hexPatchBall] using hy
    subst y
    exact ⟨.nil, le_rfl⟩
  | succ n ih =>
    rw [hexPatchBall, Finset.mem_biUnion] at hy
    obtain ⟨z, hz, hy⟩ := hy
    obtain ⟨p, hp⟩ := ih hz
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    rcases hy with rfl | hzy
    · exact ⟨p, by omega⟩
    · exact ⟨p.concat hzy, by simpa using Nat.succ_le_succ hp⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
private theorem hexPatchBoundary_walk_bound :
    ∀ i j : Fin 16, hexBoundaryIndex j ∈ hexPatchBall (hexBoundaryIndex i) 7 := by
  decide

private theorem hexPatchBoundary_adj :
    ∀ i j : Fin 16, (cycleGraph 16).Adj i j →
      hexLattice.Adj (hexPatchVertex (hexBoundaryIndex i)) (hexPatchVertex (hexBoundaryIndex j)) := by
  decide

private theorem hexPatchBoundary_inj :
    ∀ i j : Fin 16, hexPatchVertex (hexBoundaryIndex i) =
      hexPatchVertex (hexBoundaryIndex j) → i = j := by
  decide

/-- Caso de raio pelo menos 8 do Teorema 17. Se todos os pares a distância no máximo
7 têm imagens distintas quando distintos, a borda do trapézio projeta-se em um C16. -/
theorem hex_has_cycle16_of_no_close_collision {V : Type*} (G : SimpleGraph V)
    (π : hexLattice →g G)
    (hsep : ∀ x y, hexLattice.Reachable x y → hexLattice.dist x y ≤ 7 →
      π x = π y → x = y) :
    ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.length = 16 := by
  let f : cycleGraph 16 →g hexLattice :=
    ⟨fun i => hexPatchVertex (hexBoundaryIndex i), fun {i j} h => hexPatchBoundary_adj i j h⟩
  let g := π.comp f
  have hg : Function.Injective g := by
    intro i j hij
    obtain ⟨p, hp⟩ := hexPatchBall_walk _ 7 (hexPatchBoundary_walk_bound i j)
    exact hexPatchBoundary_inj i j (hsep _ _ ⟨p⟩ ((hexLattice.dist_le p).trans hp) hij)
  exact ⟨g 0, (cycleGraph.cycle 13).map g, cycleGraph.isCycle_cycle.map hg, by simp⟩

/-- Teorema 17 (Núcleo Combinatório): Todo grafo finito simples bipartido `G` que admite
um recobrimento pela rede hexagonal infinita `hexLattice` contém um ciclo simples de
comprimento `4`, `8` ou `16`. -/
theorem hex_covering_has_cycle_4_8_16 {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (hbip : ∃ c : V → Bool, ∀ u v : V, G.Adj u v → c u ≠ c v)
    (π : hexLattice →g G) (hcov : IsGraphCovering π) :
    ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ (p.length = 4 ∨ p.length = 8 ∨ p.length = 16) := by
  classical
  let P (n : ℕ) : Prop := ∃ x y, x ≠ y ∧ π x = π y ∧
    hexLattice.Reachable x y ∧ hexLattice.dist x y = n
  by_cases hfar : ∀ x y, hexLattice.Reachable x y → hexLattice.dist x y ≤ 7 →
      π x = π y → x = y
  · obtain ⟨v, p, hp, hlen⟩ := hex_has_cycle16_of_no_close_collision G π hfar
    exact ⟨v, p, hp, Or.inr (Or.inr hlen)⟩
  push Not at hfar
  obtain ⟨x, y, hxy, hbound, himage, hne⟩ := hfar
  have hwitness : P (hexLattice.dist x y) := ⟨x, y, hne, himage, hxy, rfl⟩
  have hexists : ∃ n, P n := ⟨_, hwitness⟩
  obtain ⟨u, w, huw, heq, hr, hdist⟩ := Nat.find_spec hexists
  obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
  have hl := hp.trans hdist
  have hle : p.length ≤ 7 := by
    rw [hl]
    exact (Nat.find_min' hexists hwitness).trans hbound
  have hsep (a b) (hrab : hexLattice.Reachable a b) (hab : hexLattice.dist a b < p.length)
      (he : π a = π b) : a = b := by
    by_contra hn
    rw [hl] at hab
    exact Nat.find_min hexists hab ⟨a, b, hn, he, hrab, rfl⟩
  have hEven : Even p.length := by
    obtain ⟨c, hc⟩ := hbip
    let C : G.Coloring Bool := Coloring.mk c (fun {a b} h => hc a b h)
    simpa using (C.even_length_iff_congr (p.map π)).mpr (by rw [heq])
  have h0 : p.length ≠ 0 :=
    fun h => huw (Walk.exists_length_eq_zero_iff.mp ⟨p, h⟩)
  have h2 : p.length ≠ 2 := by
    intro h
    have h01 := p.adj_getVert_succ (i := 0) (by omega)
    have h12 := p.adj_getVert_succ (i := 1) (by omega)
    rw [Walk.getVert_zero] at h01
    change hexLattice.Adj (p.getVert 1) (p.getVert 2) at h12
    rw [← h, Walk.getVert_length] at h12
    exact huw ((hcov (p.getVert 1)).1 u w h01.symm h12 heq)
  have hcases : p.length = 4 ∨ p.length = 6 := by
    rw [Nat.even_iff] at hEven
    omega
  rcases hcases with h4 | h6
  · obtain ⟨v, q, hq, hqLen⟩ := shortest_collision_projects_cycle π p hp (by omega) heq hsep
    exact ⟨v, q, hq, Or.inl (hqLen.trans h4)⟩
  · -- Raio 6: certificar quatro desvios de comprimento 8 com pares extremos distintos.
    sorry

/-- Teorema 18 (Núcleo Algébrico — SEM `sorry`): Desigualdade Exata do Fulereno para grafos
com `δ(G) ≥ 3`, cintura `≥ 5` e livres de `C_8` imersos 2-celularmente em superfície de
característica de Euler `chi`: `30 * chi ≤ 9 * |V_3| - 8 * |V|`. -/
theorem fullerene_euler_inequality {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {E F F5 Fge6 : ℕ} {chi : ℤ}
    (hdeg : ∀ v : V, 3 ≤ G.degree v)
    (hhand : ∑ v : V, G.degree v = 2 * E)
    (hF : F = F5 + Fge6)
    (hface_sum : 5 * F5 + 6 * Fge6 ≤ 2 * E)
    (hF5 : 5 * F5 ≤ ∑ v : V, G.degree v / 2)
    (heuler : chi = (Fintype.card V : ℤ) - (E : ℤ) + (F : ℤ)) :
    30 * chi ≤
      9 * ((Finset.univ.filter (fun v : V => G.degree v = 3)).card : ℤ) -
      8 * (Fintype.card V : ℤ) := by
  have hsum_ineq : ∀ s : Finset V,
      38 * s.card + ∑ v ∈ s, G.degree v / 2 ≤
        10 * (∑ v ∈ s, G.degree v) + 9 * (s.filter (fun v => G.degree v = 3)).card := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simp
    · intro a s ha ih
      have hda : 3 ≤ G.degree a := hdeg a
      have hcard_ins : (insert a s).card = s.card + 1 := by simp [ha]
      have hsum1 : ∑ v ∈ insert a s, G.degree v / 2 =
           G.degree a / 2 + ∑ v ∈ s, G.degree v / 2 := by simp [ha]
      have hsum2 : ∑ v ∈ insert a s, G.degree v =
           G.degree a + ∑ v ∈ s, G.degree v := by simp [ha]
      have hcard_filt : ((insert a s).filter (fun v => G.degree v = 3)).card =
           (s.filter (fun v => G.degree v = 3)).card + if G.degree a = 3 then 1 else 0 := by
        by_cases h3 : G.degree a = 3
        · simp [Finset.filter_insert, ha, h3]
        · simp [Finset.filter_insert, h3]
      rw [hcard_ins, hsum1, hsum2, hcard_filt]
      split_ifs <;> omega
  have hmain := hsum_ineq Finset.univ
  simp only [Finset.card_univ] at hmain
  rw [hhand] at hmain
  omega

/-- Corolário 18.1 (SEM `sorry`): Todo grafo planar (`chi = 2`) com `δ(G) ≥ 3`, cintura `≥ 5`
e livre de `C_8` possui pelo menos `60` vértices (exato, atingido pelo fulereno `C_60`) e
satisfaz `9 * |V_3| ≥ 8 * |V| + 60`. -/
theorem planar_girth5_no_C8_card_ge_60 {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {E F F5 Fge6 : ℕ}
    (hdeg : ∀ v : V, 3 ≤ G.degree v)
    (hhand : ∑ v : V, G.degree v = 2 * E)
    (hF : F = F5 + Fge6)
    (hface_sum : 5 * F5 + 6 * Fge6 ≤ 2 * E)
    (hF5 : 5 * F5 ≤ ∑ v : V, G.degree v / 2)
    (heuler : (2 : ℤ) = (Fintype.card V : ℤ) - (E : ℤ) + (F : ℤ)) :
    60 ≤ Fintype.card V ∧
    8 * Fintype.card V + 60 ≤ 9 * (Finset.univ.filter (fun v : V => G.degree v = 3)).card := by
  have hineq := fullerene_euler_inequality G hdeg hhand hF hface_sum hF5 heuler
  have hle : (Finset.univ.filter (fun v : V => G.degree v = 3)).card ≤ Fintype.card V := by
    rw [← Finset.card_univ]
    exact Finset.card_le_card (Finset.subset_univ _)
  omega

/-! ### Rodada 9: Terminais de um lado bipartido de um corte cúbico de três arestas -/

/-- Em um grafo bipartido com três vértices de grau 2 e todos os outros de grau 3,
os três terminais pertencem à mesma parte. -/
theorem bipartite_three_terminals_same_color {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj] (T : Finset V) (hT : T.card = 3)
    (hdeg : ∀ v : V, A.degree v = if v ∈ T then 2 else 3)
    (c : V → Bool) (hc : ∀ u v, A.Adj u v → c u ≠ c v) :
    ∃ b : Bool, ∀ v ∈ T, c v = b := by
  let S : Finset V := Finset.univ.filter (fun v => c v = false)
  let R : Finset V := Finset.univ.filter (fun v => c v = true)
  have hbip : A.IsBipartiteWith (S : Set V) (R : Set V) := by
    constructor
    · simp [Set.disjoint_left, S, R]
    · intro u v huv
      have h := hc u v huv
      cases hu : c u <;> cases hv : c v <;> simp_all [S, R]
  have hsum := A.isBipartiteWith_sum_degrees_eq hbip
  have hbalance (s : Finset V) :
      3 * s.card = (∑ v ∈ s, A.degree v) + (s.filter (· ∈ T)).card := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      by_cases ht : a ∈ T
      · simp [Finset.filter_insert, ha, hdeg a, ht]
        omega
      · simp [Finset.filter_insert, ha, hdeg a, ht]
        omega
  have hs : S.filter (· ∈ T) = T.filter (fun v => c v = false) := by
    ext v
    simp [S, and_comm]
  have hr : R.filter (· ∈ T) = T.filter (fun v => c v = true) := by
    ext v
    simp [R, and_comm]
  have hthree : (S.filter (· ∈ T)).card + (R.filter (· ∈ T)).card = 3 := by
    rw [hs, hr, ← hT]
    have hneg : (T.filter (fun v => ¬ c v = false)) = T.filter (fun v => c v = true) := by
      ext v
      cases c v <;> simp
    rw [← hneg]
    exact Finset.card_filter_add_card_filter_not (fun v => c v = false)
  have hS := hbalance S
  have hR := hbalance R
  change (∑ v ∈ S, A.degree v) = ∑ w ∈ R, A.degree w at hsum
  have hzero : (S.filter (· ∈ T)).card = 0 ∨ (R.filter (· ∈ T)).card = 0 := by
    omega
  rw [hs, hr] at hzero
  rcases hzero with hzero | hzero
  · refine ⟨true, fun v hv => ?_⟩
    have h := Finset.filter_eq_empty_iff.mp (Finset.card_eq_zero.mp hzero) hv
    cases hcv : c v <;> simp_all
  · refine ⟨false, fun v hv => ?_⟩
    have h := Finset.filter_eq_empty_iff.mp (Finset.card_eq_zero.mp hzero) hv
    cases hcv : c v <;> simp_all

private theorem walk_color_parity {V : Type*} {G : SimpleGraph V}
    (c : V → Bool) {u v : V} (p : G.Walk u v) :
    (p.length + p.darts.countP (fun d => c d.fst == c d.snd)) % 2 =
      if c u = c v then 0 else 1 := by
  induction p with
  | nil => simp
  | @cons u w v h q ih =>
    cases hu : c u <;> cases hw : c w <;> cases hv : c v <;>
      simp [Walk.darts_cons, hu, hw, hv] at ih ⊢ <;> omega

/-- Um passeio fechado de comprimento par tem um número par de ocorrências de
arestas cujos extremos recebem a mesma cor. -/
theorem even_closed_walk_same_color_edges {V : Type*} {G : SimpleGraph V}
    (c : V → Bool) {u : V} (p : G.Walk u u) (hp : p.length % 2 = 0) :
    p.darts.countP (fun d => c d.fst == c d.snd) % 2 = 0 := by
  have h : (p.length + p.darts.countP (fun d => c d.fst == c d.snd)) % 2 = 0 := by
    simpa using walk_color_parity c p
  omega

/-- Dois caminhos de comprimento par que fecham um ciclo diádico com duas arestas
de junção têm resíduos distintos módulo 4. -/
theorem two_join_edges_dyadic_residues {a b k : ℕ} (hk : 2 ≤ k)
    (ha : a % 2 = 0) (hb : b % 2 = 0) (hlen : a + b + 2 = 2 ^ k) :
    (a % 4 = 0 ∧ b % 4 = 2) ∨ (a % 4 = 2 ∧ b % 4 = 0) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [pow_add] at hlen
  norm_num at hlen
  omega

end Erdos64
