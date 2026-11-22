import Mathlib

/-!
# Projeto Erdős #64 — Formalização em Lean 4 (`Checkpoint v1.7`)

Sincronizado com `README.md` e `Erdos64_lean.md` (Pós-Rodada 12, Progresso `25% / 100%`).
Lean `v4.36.0` / Mathlib `v4.36.0`: 0 erros, 0 avisos de linter e 6 avisos de `sorry`.

24 teoremas públicos verificados sem dependência de `sorry`:
- `HasPow2Cycle.map`, `HasPow2Cycle.mono`, `HasPow2Cycle.of_induce`
- `no_two_common_neighbors`, `common_neighbors_le_one`, `triangles_edge_disjoint`
- `minimal_connected`, `high_degree_independent`, `no_L3_vertices`
- `fullerene_euler_inequality`, `planar_girth5_no_C8_card_ge_60`
- `minimal_bridgeless`
- `bipartite_three_terminals_same_color`, `even_closed_walk_same_color_edges`,
   `two_join_edges_dyadic_residues` (lemas auxiliares do Teorema 19)
- `hex_has_cycle16_of_no_close_collision`, `hex_local_injective_has_cycle_4_8_16`,
   `hex_covering_has_cycle_4_8_16` (núcleo combinatório completo do Teorema 17)
- `euler_boundary_deficit_bound` (núcleo algébrico do Teorema 20)
- `triangle_cactus_no_long_cycle` (Teorema 7)
- `single_join_edge_dyadic_residues` (núcleo aritmético do caso de uma junção do Teorema 21)
- `minimal_edge_dyadic_successor`, `minimal_not_bipartite`, `minimal_bipartite_cubicity`
  (contração de arestas fora de triângulos e Teorema 10b)
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

/-- Une dois vértices de um ciclo por seus dois arcos simples. -/
private theorem cycle_arcs {V : Type*} {G : SimpleGraph V} {v a b : V}
    (p : G.Walk v v) (hc : p.IsCycle) (ha : a ∈ p.support) (hb : b ∈ p.support) (hn : a ≠ b) :
    ∃ (q : G.Walk a b) (r : G.Walk b a), q.IsPath ∧ r.IsPath ∧
      q.length + r.length = p.length ∧ q.support ⊆ p.support ∧ r.support ⊆ p.support ∧
      q.edges ⊆ p.edges ∧ r.edges ⊆ p.edges := by
  classical
  let c := p.rotate a ha
  have hbc : b ∈ c.support := (p.mem_support_rotate_iff a ha).mpr hb
  let q := c.takeUntil b hbc
  let r := c.dropUntil b hbc
  have hc' : c.IsCycle := hc.rotate ha
  have hqr : q.append r = c := c.take_spec hbc
  have hq : q.IsPath := hc'.isPath_takeUntil hbc
  have hr : r.IsPath := (hqr.symm ▸ hc').isPath_of_append_right (Walk.not_nil_of_ne hn)
  have hcs : c.support ⊆ p.support := fun _ h => (p.mem_support_rotate_iff a ha).mp h
  have hce : c.edges ⊆ p.edges := (p.rotate_edges a ha).perm.subset
  refine ⟨q, r, hq, hr, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Walk.length_append, hqr]
    exact p.length_rotate a ha
  · exact fun _ h => hcs (c.support_takeUntil_subset_support hbc h)
  · exact fun _ h => hcs (c.support_dropUntil_subset_support hbc h)
  · exact fun _ h => hce (c.edges_takeUntil_subset_edges hbc h)
  · exact fun _ h => hce (c.edges_dropUntil_subset_edges hbc h)

/-- Uma aresta fora de um caminho simples de comprimento pelo menos dois o fecha em ciclo. -/
private theorem close_simple_path {V : Type*} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (hp : p.IsPath) (hl : 2 ≤ p.length) (e : G.Adj b a) :
    (Walk.cons e p).IsCycle := by
  apply (Walk.cons_isCycle_iff p e).mpr
  refine ⟨hp, fun h => ?_⟩
  rw [Sym2.eq_swap] at h
  have := hp.length_eq_one_of_mem_edges h
  omega

private theorem length_ge_two_of_edge_notMem {V : Type*} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b) (h : s(a, b) ∉ p.edges) (hne : a ≠ b) : 2 ≤ p.length := by
  have hpos : 0 < p.length := Walk.not_nil_iff_lt_length.mp (Walk.not_nil_of_ne hne)
  by_contra! hh
  have hl : p.length = 1 := by omega
  apply h
  apply (p.mk_mem_edges_iff_exists).mpr
  refine ⟨0, hpos, ?_⟩
  rw [Walk.getVert_zero, Nat.zero_add, ← hl, Walk.getVert_length]

private theorem shortest_long_cycle_adj_mem_edges {V : Type*} {H : SimpleGraph V} {v a b : V}
    (p : H.Walk v v) (hp : p.IsCycle) (h5 : 5 ≤ p.length)
    (hm : ∀ (u : V) (q : H.Walk u u), q.IsCycle → 4 ≤ q.length → p.length ≤ q.length)
    (ha : a ∈ p.support) (hb : b ∈ p.support) (hab : H.Adj a b) :
    s(a, b) ∈ p.edges := by
  by_contra hn
  have hne := H.ne_of_adj hab
  obtain ⟨q, r, hq, hr, hl, _, _, hqe, hre⟩ := cycle_arcs p hp ha hb hne
  have hq2 := length_ge_two_of_edge_notMem q (fun h => hn (hqe h)) hne
  have hr2 := length_ge_two_of_edge_notMem r (fun h => hn (hre (Sym2.eq_swap ▸ h))) hne.symm
  by_cases h : 3 ≤ q.length
  · have hbnd := hm b (Walk.cons hab.symm q)
      (close_simple_path q hq hq2 hab.symm) (by simp only [Walk.length_cons]; omega)
    simp only [Walk.length_cons] at hbnd
    omega
  · have hbnd := hm a (Walk.cons hab r)
      (close_simple_path r hr hr2 hab) (by simp only [Walk.length_cons]; omega)
    simp only [Walk.length_cons] at hbnd
    omega

private theorem shortest_long_cycle_external_mem_edges {V : Type*}
    {H : SimpleGraph V} {v a b z : V}
    (p : H.Walk v v) (hp : p.IsCycle) (h5 : 5 ≤ p.length)
    (hm : ∀ (u : V) (q : H.Walk u u), q.IsCycle → 4 ≤ q.length → p.length ≤ q.length)
    (ha : a ∈ p.support) (hb : b ∈ p.support) (hz : z ∉ p.support) (hne : a ≠ b)
    (haz : H.Adj a z) (hbz : H.Adj b z) :
    s(a, b) ∈ p.edges := by
  by_contra hn
  obtain ⟨q, r, hq, hr, hl, hqs, hrs, hqe, hre⟩ := cycle_arcs p hp ha hb hne
  have hq2 := length_ge_two_of_edge_notMem q (fun h => hn (hqe h)) hne
  have hr2 := length_ge_two_of_edge_notMem r (fun h => hn (hre (Sym2.eq_swap ▸ h))) hne.symm
  have shortcut {x y : V} (s : H.Walk x y) (hs : s.IsPath) (hs2 : 2 ≤ s.length)
      (hss : s.support ⊆ p.support) (hx : H.Adj x z) (hy : H.Adj y z) :
      p.length ≤ s.length + 2 := by
    have hpath : (s.concat hy).IsPath := hs.concat (fun h => hz (hss h)) hy
    have hcyc := close_simple_path (s.concat hy) hpath (by
      simp only [Walk.length_concat]; omega) hx.symm
    have hc4 : 4 ≤ (Walk.cons hx.symm (s.concat hy)).length := by
      simp only [Walk.length_cons, Walk.length_concat]
      omega
    simpa [Walk.length_cons, Walk.length_concat, Nat.add_assoc] using hm z _ hcyc hc4
  have hq' := shortcut q hq hq2 hqs haz hbz
  have hr' := shortcut r hr hr2 hrs hbz haz
  omega

private theorem long_cycle_not_triangle_in_edges {V : Type*}
    {H : SimpleGraph V} {v a b z : V} (p : H.Walk v v) (hp : p.IsCycle) (h5 : 5 ≤ p.length)
    (hab : s(a, b) ∈ p.edges) (haz : s(a, z) ∈ p.edges) (hbz : s(b, z) ∈ p.edges) : False := by
  classical
  let c := p.rotate a (p.fst_mem_support_of_mem_edges hab)
  have hc : c.IsCycle := hp.rotate _
  have hc5 : 5 ≤ c.length := by simpa [c] using h5
  have he : ∀ e ∈ p.edges, e ∈ c.edges :=
    (p.rotate_edges a _).perm.symm.subset
  have hcb := hc.isPath_dropLast.eq_snd_or_eq_penultimate_of_start_mem_edges (he _ hab)
  have hcz := hc.isPath_dropLast.eq_snd_or_eq_penultimate_of_start_mem_edges (he _ haz)
  have hne : b ≠ z := H.ne_of_adj (p.adj_of_mem_edges hbz)
  have hm : s(c.snd, c.penultimate) ∈ c.edges := by
    rcases hcb with hb | hb <;> rcases hcz with hz | hz
    · exact (hne (hb.trans hz.symm)).elim
    · rw [← hb, ← hz]
      exact he _ hbz
    · rw [← hz, ← hb]
      exact he _ (Sym2.eq_swap ▸ hbz)
    · exact (hne (hb.trans hz.symm)).elim
  have hEdges : c.edges = s(a, c.snd) :: c.tail.edges := by
    have h := congrArg Walk.edges (c.cons_tail_eq hc.not_nil)
    simpa only [Walk.edges_cons] using h.symm
  rw [hEdges, List.mem_cons] at hm
  rcases hm with hm | hm
  · rw [Sym2.eq_iff] at hm
    rcases hm with ⟨h, _⟩ | ⟨_, h⟩
    · exact (H.ne_of_adj (c.adj_snd hc.not_nil)) h.symm
    · have hf := hc.getVert_endpoint_iff
        (i := c.length - 1) (by omega : c.length - 1 ≤ c.length)
      rcases hf.mp h with he | he <;> omega
  · have h := hc.isPath_tail.eq_snd_of_mem_edges hm
    change c.getVert (c.length - 1) = c.tail.getVert 1 at h
    rw [Walk.getVert_tail] at h
    have hi : 1 ≤ c.length - 1 ∧ c.length - 1 ≤ c.length := by omega
    have hj : 1 ≤ 2 ∧ 2 ≤ c.length := by omega
    have hidx := hc.getVert_injOn hi hj h
    omega

private def tipOnWalk {V : Type*} {G : SimpleGraph V} {a b : V}
    (p : (triangleSubgraph G).Walk a b) (z : V) : Prop :=
  ∃ x y, s(x, y) ∈ p.edges ∧ G.Adj x z ∧ G.Adj y z

private theorem expand_triangle_path {V : Type*} {G : SimpleGraph V} {a b : V}
    (p : (triangleSubgraph G).Walk a b) (hp : p.IsPath)
    (hfresh : ∀ z, tipOnWalk p z → z ∉ p.support)
    (hunique : ∀ x y u v z, s(x, y) ∈ p.edges → s(u, v) ∈ p.edges →
      G.Adj x z → G.Adj y z → G.Adj u z → G.Adj v z → s(x, y) = s(u, v))
    (k : ℕ) (hk : k ≤ p.length) :
    ∃ q : G.Walk a b, q.IsPath ∧ q.length = p.length + k ∧
      ∀ z ∈ q.support, z ∈ p.support ∨ tipOnWalk p z := by
  induction p generalizing k with
  | nil =>
    have h : k = 0 := by simpa using hk
    subst k
    exact ⟨Walk.nil, Walk.IsPath.nil, rfl, fun _ hz => Or.inl hz⟩
  | @cons x y b h tail ih =>
    by_cases hzero : k = 0
    · subst k
      let hle : triangleSubgraph G ≤ G := fun _ _ h => h.1
      refine ⟨(Walk.cons h tail).mapLe hle, hp.mapLe hle, by simp, ?_⟩
      intro z hz
      left
      rwa [Walk.support_mapLe_eq_support] at hz
    have lfresh (z) (ht : tipOnWalk tail z) : z ∉ tail.support := by
      obtain ⟨i, j, hij, h1, h2⟩ := ht
      exact fun hs => hfresh z
        ⟨i, j, List.mem_cons_of_mem _ hij, h1, h2⟩ (List.mem_cons_of_mem _ hs)
    have lunique i j l r z (hij : s(i, j) ∈ tail.edges) (hlr : s(l, r) ∈ tail.edges) :=
      hunique i j l r z (List.mem_cons_of_mem _ hij) (List.mem_cons_of_mem _ hlr)
    have hkt : k - 1 ≤ tail.length := by
      simp only [Walk.length_cons] at hk
      omega
    obtain ⟨q, hq, hlen, hs⟩ := ih hp.of_cons lfresh lunique (k - 1) hkt
    obtain ⟨z, hxz, hyz⟩ := h.2
    have hhead : s(x, y) ∈ (Walk.cons h tail).edges := List.mem_cons_self
    have hztip : tipOnWalk (Walk.cons h tail) z := ⟨x, y, hhead, hxz, hyz⟩
    have htails (u) (hu : tipOnWalk tail u) : tipOnWalk (Walk.cons h tail) u := by
      obtain ⟨i, j, he, h1, h2⟩ := hu
      exact ⟨i, j, List.mem_cons_of_mem _ he, h1, h2⟩
    have hzd : z ∉ q.support := by
      intro hm
      rcases hs z hm with ht | hz
      · exact hfresh z hztip (List.mem_cons_of_mem _ ht)
      · obtain ⟨i, j, he, h1, h2⟩ := hz
        have hEq := hunique x y i j z hhead (List.mem_cons_of_mem _ he) hxz hyz h1 h2
        have hn := hp.isTrail.edges_nodup
        simp only [Walk.edges_cons, List.nodup_cons] at hn
        exact hn.1 (hEq ▸ he)
    have hxd : x ∉ q.support := by
      intro hm
      rcases hs x hm with ht | hz
      · exact ((Walk.cons_isPath_iff h tail).mp hp).2 ht
      · exact hfresh x (htails x hz) List.mem_cons_self
    have hqz : (Walk.cons hyz.symm q).IsPath := hq.cons hzd
    have hqx : (Walk.cons hxz (Walk.cons hyz.symm q)).IsPath := by
      apply hqz.cons
      simp only [Walk.support_cons, List.mem_cons, not_or]
      exact ⟨G.ne_of_adj hxz, hxd⟩
    refine ⟨_, hqx, ?_, ?_⟩
    · simp only [Walk.length_cons]
      omega
    · intro u hu
      simp only [Walk.support_cons, List.mem_cons] at hu
      rcases hu with rfl | rfl | hu
      · exact Or.inl List.mem_cons_self
      · exact Or.inr hztip
      · exact (hs u hu).imp (List.mem_cons_of_mem _) (htails u)
private theorem pow_two_in_cycle_interval {n : ℕ} (hn : 4 ≤ n) :
    ∃ k : ℕ, 2 ≤ k ∧ n ≤ 2 ^ k ∧ 2 ^ k < 2 * n := by
  let k := Nat.log 2 (n - 1)
  have hlow := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (n - 1)
  have hhigh := Nat.pow_log_le_self 2 (x := n - 1) (by omega)
  change n - 1 < 2 ^ (k + 1) at hlow
  change 2 ^ k ≤ n - 1 at hhigh
  refine ⟨k + 1, ?_, by omega, ?_⟩
  · by_contra! h
    have hk : k = 0 := by omega
    rw [hk] at hlow
    norm_num at hlow
    omega
  · rw [pow_succ]
    omega

/-- Teorema 7: Em qualquer grafo livre de C_{2^k}, `G_Δ` não possui ciclos de comprimento ≥ 4. -/
theorem triangle_cactus_no_long_cycle {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hfree : ¬ HasPow2Cycle G) :
    ∀ (v : V) (p : (triangleSubgraph G).Walk v v), p.IsCycle → p.length = 3 := by
  classical
  let H := triangleSubgraph G
  have hle : H ≤ G := fun _ _ h => h.1
  intro u p hp
  by_contra hne
  let P (n : ℕ) := ∃ (v : V) (q : H.Walk v v), q.IsCycle ∧ 4 ≤ q.length ∧ q.length = n
  have hw : ∃ n, P n := ⟨p.length, u, p, hp, by have := hp.three_le_length; omega, rfl⟩
  obtain ⟨v, c, hc, hc4, hen⟩ := Nat.find_spec hw
  have hm (w : V) (q : H.Walk w w) (hq : q.IsCycle) (hq4 : 4 ≤ q.length) :
      c.length ≤ q.length :=
    hen ▸ Nat.find_min' hw (show P q.length from ⟨w, q, hq, hq4, rfl⟩)
  have hc5 : 5 ≤ c.length := by
    by_contra! h
    have hl : c.length = 4 := by omega
    exact hfree ⟨v, c.mapLe hle, 2, le_rfl, hc.mapLe hle, by simpa using hl⟩
  have outside {a b z : V} (he : s(a, b) ∈ c.edges) (haz : G.Adj a z) (hbz : G.Adj b z) :
      z ∉ c.support := by
    intro hz
    have hab : G.Adj a b := hle (c.adj_of_mem_edges he)
    have h1 : H.Adj a z := ⟨haz, b, hab, hbz.symm⟩
    have h2 : H.Adj b z := ⟨hbz, a, hab.symm, haz.symm⟩
    have h3 := shortest_long_cycle_adj_mem_edges c hc hc5 hm
      (c.fst_mem_support_of_mem_edges he) hz h1
    have h4 := shortest_long_cycle_adj_mem_edges c hc hc5 hm
      (c.snd_mem_support_of_mem_edges he) hz h2
    exact long_cycle_not_triangle_in_edges c hc hc5 he h3 h4
  have unique {a b i j z : V} (he : s(a, b) ∈ c.edges) (he' : s(i, j) ∈ c.edges)
      (haz : G.Adj a z) (hbz : G.Adj b z) (hiz : G.Adj i z) (hjz : G.Adj j z) :
      s(a, b) = s(i, j) := by
    by_contra hh
    have hthird : (i ≠ a ∧ i ≠ b) ∨ (j ≠ a ∧ j ≠ b) := by
      by_contra! h
      have hn := H.ne_of_adj (c.adj_of_mem_edges he')
      apply hh
      rw [Sym2.eq_iff]
      have hi : i = a ∨ i = b := by
        by_cases hi : i = a
        · exact Or.inl hi
        · exact Or.inr (h.1 hi)
      have hj : j = a ∨ j = b := by
        by_cases hj : j = a
        · exact Or.inl hj
        · exact Or.inr (h.2 hj)
      rcases hi with hi | hi <;> rcases hj with hj | hj
      · exact (hn (hi.trans hj.symm)).elim
      · exact Or.inl ⟨hi.symm, hj.symm⟩
      · exact Or.inr ⟨hj.symm, hi.symm⟩
      · exact (hn (hi.trans hj.symm)).elim
    have hab : G.Adj a b := hle (c.adj_of_mem_edges he)
    have haz' : H.Adj a z := ⟨haz, b, hab, hbz.symm⟩
    have hbz' : H.Adj b z := ⟨hbz, a, hab.symm, haz.symm⟩
    have contradiction {d : V} (hd : d ∈ c.support) (hda : d ≠ a) (hdb : d ≠ b)
        (hdz : H.Adj d z) : False := by
      have ha := c.fst_mem_support_of_mem_edges he
      have hb := c.snd_mem_support_of_mem_edges he
      have hz := outside he haz hbz
      have h1 := shortest_long_cycle_external_mem_edges c hc hc5 hm ha hd hz hda.symm haz' hdz
      have h2 := shortest_long_cycle_external_mem_edges c hc hc5 hm hb hd hz hdb.symm hbz' hdz
      exact long_cycle_not_triangle_in_edges c hc hc5 he h1 h2
    have hij : G.Adj i j := hle (c.adj_of_mem_edges he')
    rcases hthird with ⟨hia, hib⟩ | ⟨hja, hjb⟩
    · exact contradiction (c.fst_mem_support_of_mem_edges he') hia hib
        ⟨hiz, j, hij, hjz.symm⟩
    · exact contradiction (c.snd_mem_support_of_mem_edges he') hja hjb
        ⟨hjz, i, hij.symm, hiz.symm⟩
  obtain ⟨k, hk, hlow, hhigh⟩ := pow_two_in_cycle_interval hc4
  have hcEdges : c.edges = s(v, c.snd) :: c.tail.edges := by
    have he := congrArg Walk.edges (c.cons_tail_eq hc.not_nil)
    simpa only [Walk.edges_cons] using he.symm
  have addEdge : c.tail.edges ⊆ c.edges := by
    rw [hcEdges]
    exact fun _ h => List.mem_cons_of_mem _ h
  have addSupport : c.tail.support ⊆ c.support := by
    rw [← Walk.cons_support_tail hc.not_nil]
    exact fun _ h => List.mem_cons_of_mem _ h
  have hfresh (z) (hz : tipOnWalk c.tail z) : z ∉ c.tail.support := by
    obtain ⟨a, b, he, haz, hbz⟩ := hz
    exact fun h => outside (addEdge he) haz hbz (addSupport h)
  have hunique a b i j z (he : s(a, b) ∈ c.tail.edges) (he' : s(i, j) ∈ c.tail.edges) :=
    unique (addEdge he) (addEdge he') (z := z)
  have ht := c.length_tail_add_one hc.not_nil
  have hcap : 2 ^ k - c.length ≤ c.tail.length := by omega
  obtain ⟨q, hq, hqlen, _⟩ :=
    expand_triangle_path c.tail hc.isPath_tail hfresh hunique _ hcap
  have ha : G.Adj v c.snd := hle (c.adj_snd hc.not_nil)
  have hcyc := close_simple_path q hq (by omega) ha
  exact hfree ⟨v, Walk.cons ha q, k, hk, hcyc, by simp only [Walk.length_cons]; omega⟩

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

/-! ### Rodada 12: Contração de uma aresta fora de triângulos -/

private abbrev ContractVerts {V : Type*} (v : V) := {x : V // x ≠ v}

private def contractEdge {V : Type*} (G : SimpleGraph V) {v : V}
    (r : ContractVerts v) : SimpleGraph (ContractVerts v) where
  Adj a b := a ≠ b ∧
    (G.Adj a.val b.val ∨ a = r ∧ G.Adj v b.val ∨ b = r ∧ G.Adj a.val v)
  symm := ⟨by
    rintro a b ⟨hab, h | ⟨ha, h⟩ | ⟨hb, h⟩⟩
    · exact ⟨hab.symm, Or.inl h.symm⟩
    · exact ⟨hab.symm, Or.inr (Or.inr ⟨ha, h.symm⟩)⟩
    · exact ⟨hab.symm, Or.inr (Or.inl ⟨hb, h.symm⟩)⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

private theorem contractEdge_adj_away {V : Type*} {G : SimpleGraph V} {v : V}
    {r a b : ContractVerts v} (ha : a ≠ r) (hb : b ≠ r)
    (h : (contractEdge G r).Adj a b) : G.Adj a.val b.val := by
  rcases h.2 with h | ⟨h, _⟩ | ⟨h, _⟩
  · exact h
  · exact (ha h).elim
  · exact (hb h).elim

private theorem contractEdge_adj_root {V : Type*} {G : SimpleGraph V} {v : V}
    {r a : ContractVerts v} (h : (contractEdge G r).Adj r a) :
    G.Adj r.val a.val ∨ G.Adj v a.val := by
  rcases h.2 with h' | ⟨_, h'⟩ | ⟨ha, _⟩
  · exact Or.inl h'
  · exact Or.inr h'
  · exact (h.1 ha.symm).elim

private theorem contractEdge_minDegree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {v : V} (r : ContractVerts v)
    [Fintype (ContractVerts v)] [DecidableRel (contractEdge G r).Adj]
    (he : G.Adj r.val v) (hcommon : ∀ z, G.Adj r.val z → ¬ G.Adj v z)
    (hdeg : ∀ x, 3 ≤ G.degree x) (x : ContractVerts v) :
    3 ≤ (contractEdge G r).degree x := by
  classical
  let D := contractEdge G r
  let collapse (a : V) : ContractVerts v := if ha : a = v then r else ⟨a, ha⟩
  have collapse_of_ne {a : V} (ha : a ≠ v) : (collapse a).val = a := by
    simp [collapse, ha]
  have collapse_v : collapse v = r := by simp [collapse]
  change 3 ≤ D.degree x
  by_cases hx : x = r
  · subst x
    let S := (G.neighborFinset v).erase r.val
    have hrv : r.val ∈ G.neighborFinset v := by simpa using he.symm
    have hS : S.Nonempty := by
      apply Finset.card_pos.mp
      rw [Finset.card_erase_of_mem hrv]
      have hd := hdeg v
      change 0 < G.degree v - 1
      omega
    obtain ⟨z, hz⟩ := hS
    have hzAdj : G.Adj v z := by simpa using (Finset.mem_erase.mp hz).2
    have hzv : z ≠ v := (G.ne_of_adj hzAdj).symm
    let T := (G.neighborFinset r.val).erase v
    let U := insert z T
    have hzT : z ∉ T := fun h => hcommon z (by simpa using (Finset.mem_erase.mp h).2) hzAdj
    have hU (y : V) (hy : y ∈ U) : y ≠ v ∧ y ≠ r.val ∧
        (G.Adj r.val y ∨ G.Adj v y) := by
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact ⟨hzv, (Finset.mem_erase.mp hz).1, Or.inr hzAdj⟩
      · have hya : G.Adj r.val y := by simpa using (Finset.mem_erase.mp hy).2
        exact ⟨(Finset.mem_erase.mp hy).1, (G.ne_of_adj hya).symm, Or.inl hya⟩
    have hsub : U ⊆ (D.neighborFinset r).image Subtype.val := by
      intro y hy
      obtain ⟨hyv, hyr, hya | hya⟩ := hU y hy
      · exact Finset.mem_image.mpr ⟨⟨y, hyv⟩, by
          rw [SimpleGraph.mem_neighborFinset]
          exact ⟨fun h => hyr (congrArg Subtype.val h).symm, Or.inl hya⟩, rfl⟩
      · exact Finset.mem_image.mpr ⟨⟨y, hyv⟩, by
          rw [SimpleGraph.mem_neighborFinset]
          exact ⟨fun h => hyr (congrArg Subtype.val h).symm, Or.inr (Or.inl ⟨rfl, hya⟩)⟩, rfl⟩
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ Subtype.val_injective] at hcard
    have hv : v ∈ G.neighborFinset r.val := by simpa using he
    rw [show U = insert z T from rfl, Finset.card_insert_of_notMem hzT,
      show T = (G.neighborFinset r.val).erase v from rfl, Finset.card_erase_of_mem hv] at hcard
    change G.degree r.val - 1 + 1 ≤ D.degree r at hcard
    have hd := hdeg r.val
    omega
  · let f : G.neighborSet x.val → D.neighborSet x := fun a =>
      ⟨collapse a.val, by
        change D.Adj x (collapse a.val)
        have haAdj : G.Adj x.val a.val := a.property
        by_cases ha : a.val = v
        · rw [ha, collapse_v]
          rw [ha] at haAdj
          exact ⟨hx, Or.inr (Or.inr ⟨rfl, haAdj⟩)⟩
        · refine ⟨fun h => G.ne_of_adj a.property ?_, Or.inl ?_⟩
          · simpa only [collapse_of_ne ha] using congrArg Subtype.val h
          · simpa only [collapse_of_ne ha] using haAdj⟩
    have hf : Function.Injective f := by
      intro a b hab
      have hc : collapse a.val = collapse b.val :=
        congrArg (fun z : D.neighborSet x => z.val) hab
      apply Subtype.ext
      by_cases ha : a.val = v
      · by_cases hb : b.val = v
        · exact ha.trans hb.symm
        · have hbr : b.val = r.val := by
            rw [ha, collapse_v] at hc
            simpa only [collapse_of_ne hb] using (congrArg Subtype.val hc).symm
          exact (hcommon x.val (hbr ▸ b.property).symm (ha ▸ a.property).symm).elim
      · by_cases hb : b.val = v
        · have har : a.val = r.val := by
            rw [hb, collapse_v] at hc
            simpa only [collapse_of_ne ha] using congrArg Subtype.val hc
          exact (hcommon x.val (har ▸ a.property).symm (hb ▸ b.property).symm).elim
        · simpa only [collapse_of_ne ha, collapse_of_ne hb] using congrArg Subtype.val hc
    have hcard := Fintype.card_le_of_injective f hf
    rw [G.card_neighborSet_eq_degree, D.card_neighborSet_eq_degree] at hcard
    exact (hdeg x.val).trans hcard

private theorem contractEdge_transfer {V : Type*} {G : SimpleGraph V} {v : V}
    {r a b : ContractVerts v} (p : (contractEdge G r).Walk a b) (hr : r ∉ p.support) :
    ∀ e, e ∈ p.edges → e ∈ (G.comap (Subtype.val : ContractVerts v → V)).edgeSet := by
  intro e he
  induction e using Sym2.ind with | _ x y =>
  have hx : x ≠ r := fun h => hr (h ▸ p.fst_mem_support_of_mem_edges he)
  have hy : y ≠ r := fun h => hr (h ▸ p.snd_mem_support_of_mem_edges he)
  exact contractEdge_adj_away hx hy (p.edges_subset_edgeSet he)

private theorem contractEdge_lift_cycle {V : Type*} {G : SimpleGraph V} {v : V}
    {r : ContractVerts v} (he : G.Adj r.val v)
    (h : HasPow2Cycle (contractEdge G r)) :
    HasPow2Cycle G ∨ ∃ (p : G.Walk r.val r.val) (k : ℕ),
      2 ≤ k ∧ p.IsCycle ∧ p.length = 2 ^ k + 1 ∧ s(r.val, v) ∈ p.edges := by
  classical
  obtain ⟨x, p, k, hk, hp, hlen⟩ := h
  let A := G.comap (Subtype.val : ContractVerts v → V)
  let f : A →g G := ⟨Subtype.val, fun h => h⟩
  by_cases hr : r ∈ p.support
  · let q := p.rotate r hr
    have hq : q.IsCycle := hp.rotate hr
    have hqlen : q.length = 2 ^ k := by simpa [q] using hlen
    have hfour : 4 ≤ q.length := by
      rw [hqlen]
      exact Nat.pow_le_pow_right (by decide : 0 < 2) hk
    have ht : ¬ q.tail.Nil := Walk.not_nil_iff_lt_length.mpr (by rw [Walk.length_tail]; omega)
    let t := q.tail.dropLast
    have htr : r ∉ t.support := by
      have hn := hq.isPath_tail.support_nodup
      rw [← q.tail.support_dropLast_concat ht] at hn
      exact fun hm => List.disjoint_of_nodup_append hn hm (by simp)
    have hleft : (contractEdge G r).Adj r q.snd := q.adj_snd hq.not_nil
    have hright : (contractEdge G r).Adj r q.tail.penultimate :=
      (q.tail.adj_penultimate ht).symm
    let w := (t.transfer A (contractEdge_transfer t htr)).map f
    have hw : w.IsPath :=
      ((Walk.isPath_transfer _).mpr hq.isPath_tail.dropLast).map Subtype.val_injective
    have hwl : w.length + 2 = 2 ^ k := by
      change ((t.transfer A (contractEdge_transfer t htr)).map f).length + 2 = _
      rw [Walk.length_map, Walk.length_transfer]
      change q.tail.dropLast.length + 2 = _
      rw [Walk.length_dropLast, Walk.length_tail]
      omega
    have hws : w.support = t.support.map Subtype.val := by
      change ((t.transfer A (contractEdge_transfer t htr)).map f).support = _
      rw [Walk.support_map, Walk.support_transfer]
      rfl
    have hwr : r.val ∉ w.support := by
      intro hm
      rw [hws] at hm
      obtain ⟨z, hz, heq⟩ := List.mem_map.mp hm
      exact htr ((Subtype.ext heq : z = r) ▸ hz)
    have hwv : v ∉ w.support := by
      intro hm
      rw [hws] at hm
      obtain ⟨z, _, heq⟩ := List.mem_map.mp hm
      exact z.property heq
    have hs (y : V) (ha : G.Adj y q.snd.val)
        (hb : G.Adj y q.tail.penultimate.val) (hy : y ∉ w.support) :
        HasPow2Cycle G := by
      let path := w.concat hb.symm
      have hpath : path.IsPath := hw.concat hy _
      have hlpath : path.length = w.length + 1 := Walk.length_concat _ _
      exact ⟨y, Walk.cons ha path, k, hk, close_simple_path path hpath (by omega) ha,
        by rw [Walk.length_cons, hlpath]; omega⟩
    have hm {y z : V} (ha : G.Adj y q.snd.val)
        (hb : G.Adj z q.tail.penultimate.val) (hz : z ∉ w.support)
        (hy : y ∉ w.support) (hyz : G.Adj z y) :
        ∃ c : G.Walk y y, c.IsCycle ∧ c.length = 2 ^ k + 1 ∧ s(z, y) ∈ c.edges := by
      let path := w.concat hb.symm
      let extPath := path.concat hyz
      have hp₁ : path.IsPath := hw.concat hz _
      have hy' : y ∉ path.support := by
        rw [Walk.support_concat]
        simp [hy, G.ne_of_adj hyz.symm]
      have hp₂ : extPath.IsPath := hp₁.concat hy' _
      have hlpath : extPath.length = w.length + 2 := by simp [extPath, path]
      refine ⟨Walk.cons ha extPath, close_simple_path extPath hp₂ (by omega) ha, ?_, ?_⟩
      · rw [Walk.length_cons, hlpath]
        omega
      · simp [extPath, Walk.edges_concat]
    rcases contractEdge_adj_root hleft with ha | ha <;>
      rcases contractEdge_adj_root hright with hb | hb
    · exact Or.inl (hs r.val ha hb hwr)
    · obtain ⟨c, hc, hl, hm⟩ := hm ha hb hwv hwr he.symm
      exact Or.inr ⟨c, k, hk, hc, hl, Sym2.eq_swap ▸ hm⟩
    · obtain ⟨c, hc, hl, hm⟩ := hm ha hb hwr hwv he
      have hv : r.val ∈ c.support := c.fst_mem_support_of_mem_edges hm
      exact Or.inr ⟨c.rotate r.val hv, k, hk, hc.rotate hv,
        (c.length_rotate r.val hv).trans hl, (c.rotate_edges r.val hv).perm.mem_iff.mpr hm⟩
    · exact Or.inl (hs v ha hb hwv)
  · let w := p.transfer A (contractEdge_transfer p hr)
    have hw : w.IsCycle := (Walk.isCycle_transfer _).mpr hp
    exact Or.inl ⟨x.val, w.map f, k, hk, hw.map Subtype.val_injective, by simpa [w] using hlen⟩

/-- Num contraexemplo mínimo global, cada aresta fora de triângulos pertence
a um ciclo de comprimento `2^k + 1`, com `k ≥ 2`. -/
theorem minimal_edge_dyadic_successor {V : Type} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hmin : IsMinimalCounterexample G)
    {u v : V} (he : G.Adj u v) (hcommon : ∀ z, G.Adj u z → ¬ G.Adj v z) :
    ∃ (p : G.Walk u u) (k : ℕ),
      2 ≤ k ∧ p.IsCycle ∧ p.length = 2 ^ k + 1 ∧ s(u, v) ∈ p.edges := by
  classical
  let r : ContractVerts v := ⟨u, G.ne_of_adj he⟩
  have : Nonempty (ContractVerts v) := ⟨r⟩
  have hlt : Fintype.card (ContractVerts v) < Fintype.card V := by
    apply Fintype.card_lt_of_injective_not_surjective Subtype.val Subtype.val_injective
    intro hs
    obtain ⟨x, hx⟩ := hs v
    exact x.property hx
  have hcycle : HasPow2Cycle (contractEdge G r) := by
    by_contra hfree
    have hcmp := hmin.2 (ContractVerts v) (contractEdge G r)
      ⟨contractEdge_minDegree G r he hcommon hmin.1.1, hfree⟩
    omega
  exact (contractEdge_lift_cycle he hcycle).resolve_left hmin.1.2

private theorem bipartite_walk_length_parity {V : Type*} {G : SimpleGraph V}
    (c : V → Bool) (hc : ∀ a b, G.Adj a b → c a ≠ c b)
    {a b : V} (p : G.Walk a b) :
    p.length % 2 = if c a = c b then 0 else 1 := by
  induction p with
  | nil => simp
  | @cons a x b h q ih =>
    have hax := hc a x h
    cases ha : c a <;> cases hx : c x <;> cases hb : c b <;>
      simp_all <;> omega

/-- A minimalidade global exclui grafos bipartidos, pois um ciclo de
comprimento `2^k + 1` tem comprimento ímpar. -/
theorem minimal_not_bipartite {V : Type} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hmin : IsMinimalCounterexample G)
    (c : V → Bool) (hc : ∀ a b, G.Adj a b → c a ≠ c b) : False := by
  classical
  let u : V := Classical.arbitrary V
  have hne : (G.neighborFinset u).Nonempty := by
    apply Finset.card_pos.mp
    change 0 < G.degree u
    exact (by decide : 0 < 3).trans_le (hmin.1.1 u)
  obtain ⟨v, hv⟩ := hne
  have he : G.Adj u v := by simpa using hv
  have hcommon (z : V) (hu : G.Adj u z) (hv : G.Adj v z) : False := by
    have h1 := hc u v he
    have h2 := hc u z hu
    have h3 := hc v z hv
    cases hu' : c u <;> cases hv' : c v <;> cases hz' : c z <;>
      simp_all
  obtain ⟨p, k, hk, _, hl, _⟩ := minimal_edge_dyadic_successor G hmin he hcommon
  have hp : p.length % 2 = 0 := by simpa using bipartite_walk_length_parity c hc p
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [pow_add] at hl
  norm_num at hl
  omega

/-- Teorema 10b: Todo contraexemplo mínimo bipartido satisfaz |V_3| ≥ (20/27) |V|. -/
theorem minimal_bipartite_cubicity {V : Type} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmin : IsMinimalCounterexample G)
    (hbip : ∃ c : V → Bool, ∀ u v : V, G.Adj u v → c u ≠ c v) :
    20 * Fintype.card V ≤ 27 * (Finset.univ.filter (fun v : V => G.degree v = 3)).card := by
  obtain ⟨c, hc⟩ := hbip
  exact (minimal_not_bipartite G hmin c hc).elim

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

/-! #### Rodada 10: Coordenadas e certificados locais dos desvios hexagonais -/

private abbrev HexVertex := ℤ × ℤ × Bool

private def hexOrigin : HexVertex := (0, 0, false)

private def hexPlace (o z : HexVertex) : HexVertex :=
  if o.2.2 then (o.1 - z.1, o.2.1 - z.2.1, !z.2.2)
  else (o.1 + z.1, o.2.1 + z.2.1, z.2.2)

private def hexRebase (o z : HexVertex) : HexVertex :=
  if o.2.2 then (o.1 - z.1, o.2.1 - z.2.1, !z.2.2)
  else (z.1 - o.1, z.2.1 - o.2.1, z.2.2)

/-- Translação, com inversão das duas coordenadas e das cores quando a raiz é da cor oposta. -/
private def hexCoordinateIso (o : HexVertex) : hexLattice ≃g hexLattice where
  toFun := hexPlace o
  invFun := hexRebase o
  left_inv := by
    rintro ⟨x, y, b⟩
    rcases o with ⟨a, z, c⟩
    cases c <;> simp [hexPlace, hexRebase]
  right_inv := by
    rintro ⟨x, y, b⟩
    rcases o with ⟨a, z, c⟩
    cases c <;> simp [hexPlace, hexRebase]
  map_rel_iff' := by
    rintro ⟨x, y, b⟩ ⟨x', y', b'⟩
    rcases o with ⟨a, z, c⟩
    cases c <;> cases b <;> cases b' <;> simp [hexLattice, hexPlace] <;> omega

private theorem hexCoordinateIso_origin (o : HexVertex) :
    hexCoordinateIso o hexOrigin = o := by
  rcases o with ⟨x, y, c⟩
  cases c <;> simp [hexCoordinateIso, hexPlace, hexOrigin]

/-- Os três vizinhos, numerados a partir da aresta que mantém as coordenadas. -/
private def hexStep (o : HexVertex) (i : Fin 3) : HexVertex :=
  let d : ℤ := if o.2.2 then 1 else -1
  if i = 0 then (o.1, o.2.1, !o.2.2)
  else if i = 1 then (o.1 + d, o.2.1, !o.2.2)
  else (o.1, o.2.1 + d, !o.2.2)

private theorem hexStep_adj (o : HexVertex) (i : Fin 3) : hexLattice.Adj o (hexStep o i) := by
  rcases o with ⟨x, y, c⟩
  fin_cases i <;> cases c <;> simp [hexLattice, hexStep] <;> omega

private theorem hexAdj_color {u v : HexVertex} (h : hexLattice.Adj u v) :
    u.2.2 ≠ v.2.2 := by
  rcases h with ⟨a, b, _⟩ | ⟨a, b, _⟩ <;> simp [a, b]

private abbrev hexWithin (r : ℤ) (u v : HexVertex) : Prop :=
  u.1 - r ≤ v.1 ∧ v.1 ≤ u.1 + r ∧
  u.2.1 - r ≤ v.2.1 ∧ v.2.1 ≤ u.2.1 + r ∧
  u.1 + u.2.1 - r ≤ v.1 + v.2.1 ∧ v.1 + v.2.1 ≤ u.1 + u.2.1 + r

private theorem hexEdge_within {u v : HexVertex} (h : hexLattice.Adj u v) :
    hexWithin 1 u v := by
  rcases h with ⟨_, _, h⟩ | ⟨_, _, h⟩ <;>
    rcases h with h | h | h <;> dsimp [hexWithin] <;> omega

private theorem hexTwoEdges_within {u v w : HexVertex} (h : hexLattice.Adj u v)
    (h' : hexLattice.Adj v w) : hexWithin 1 u w := by
  rcases h with ⟨a, b, h⟩ | ⟨a, b, h⟩ <;>
    rcases h' with ⟨a', b', h'⟩ | ⟨a', b', h'⟩
  · simp_all
  · rcases h with h | h | h <;> rcases h' with h' | h' | h' <;> dsimp [hexWithin] <;> omega
  · rcases h with h | h | h <;> rcases h' with h' | h' | h' <;> dsimp [hexWithin] <;> omega
  · simp_all

private theorem hexWalk_within : ∀ {u v} (p : hexLattice.Walk u v),
    hexWithin (↑((p.length + 1) / 2)) u v
  | _, _, .nil => by simp [hexWithin]
  | _, _, .cons h .nil => by simpa using hexEdge_within h
  | _, _, .cons h (.cons h' tail) => by
    have h1 := hexTwoEdges_within h h'
    have h2 := hexWalk_within tail
    simp only [Walk.length_cons]
    dsimp [hexWithin] at *
    omega

private def hexDestination (u : HexVertex) : List (Fin 3) → HexVertex
  | [] => u
  | i :: s => hexDestination (hexStep u i) s

private def hexRoute : (u : HexVertex) → (s : List (Fin 3)) →
    hexLattice.Walk u (hexDestination u s)
  | _, [] => .nil
  | u, i :: s => .cons (hexStep_adj u i) (hexRoute (hexStep u i) s)

@[simp] private theorem hexRoute_length : ∀ (u) (s), (hexRoute u s).length = s.length
  | _, [] => rfl
  | u, i :: s => by
    change (hexRoute (hexStep u i) s).length + 1 = s.length + 1
    rw [hexRoute_length (hexStep u i) s]

/-- Palavras de passos centradas na origem. Pontos interiores têm um caminho curto.
Os dezoito pontos da borda têm quatro desvios de comprimento oito. -/
private def hexLocalData : ℕ → ℕ → (List (Fin 3) ⊕ (Fin 4 → List (Fin 3)))
  | 0, 3 => .inr ![
      [1, 0, 1, 0, 2, 0, 1, 2], [1, 0, 1, 2, 1, 0, 2, 0],
      [2, 0, 1, 0, 1, 0, 1, 2], [2, 0, 1, 0, 1, 2, 1, 0]]
  | 0, 4 => .inr ![
      [0, 2, 1, 0, 1, 0, 1, 0], [1, 0, 2, 0, 1, 2, 1, 2],
      [1, 2, 1, 2, 1, 0, 2, 0], [2, 0, 1, 0, 1, 2, 1, 2]]
  | 0, 5 => .inr ![
      [0, 2, 1, 0, 1, 0, 1, 2], [0, 2, 1, 0, 1, 2, 1, 0],
      [1, 0, 1, 0, 1, 2, 0, 2], [1, 0, 1, 2, 0, 2, 1, 0]]
  | 0, 6 => .inr ![
      [0, 2, 1, 0, 1, 2, 1, 2], [0, 2, 1, 2, 1, 2, 1, 0],
      [1, 0, 1, 2, 0, 2, 1, 2], [1, 2, 0, 2, 1, 2, 1, 0]]
  | 1, 2 => .inr ![
      [1, 0, 1, 0, 1, 0, 2, 1], [1, 0, 2, 0, 2, 0, 1, 2],
      [1, 2, 1, 0, 2, 0, 2, 0], [2, 0, 1, 0, 2, 0, 1, 2]]
  | 1, 3 => .inl [1, 0, 1, 0]
  | 1, 4 => .inl [1, 0, 1, 2]
  | 1, 5 => .inl [1, 2, 1, 2]
  | 1, 6 => .inr ![
      [0, 2, 0, 2, 1, 0, 1, 2], [0, 2, 0, 2, 1, 2, 1, 0],
      [1, 0, 1, 2, 0, 2, 0, 2], [1, 2, 0, 2, 0, 2, 1, 0]]
  | 2, 1 => .inr ![
      [1, 0, 1, 0, 2, 0, 2, 1], [1, 0, 1, 0, 2, 1, 2, 0],
      [2, 0, 1, 0, 1, 0, 2, 1], [2, 0, 2, 0, 2, 0, 1, 2]]
  | 2, 2 => .inl [1, 0, 2, 0]
  | 2, 3 => .inl [1, 0]
  | 2, 4 => .inl [1, 2]
  | 2, 5 => .inl [0, 2, 1, 2]
  | 2, 6 => .inr ![
      [0, 1, 0, 2, 1, 2, 1, 2], [0, 2, 0, 2, 0, 2, 1, 0],
      [0, 2, 1, 2, 1, 2, 0, 1], [1, 2, 0, 1, 0, 2, 1, 2]]
  | 3, 0 => .inr ![
      [1, 0, 2, 0, 2, 0, 2, 1], [1, 0, 2, 0, 2, 1, 2, 0],
      [2, 0, 1, 0, 2, 0, 2, 1], [2, 0, 1, 0, 2, 1, 2, 0]]
  | 3, 1 => .inl [2, 0, 2, 0]
  | 3, 2 => .inl [2, 0]
  | 3, 4 => .inl [0, 2]
  | 3, 5 => .inl [0, 2, 0, 2]
  | 3, 6 => .inr ![
      [0, 1, 0, 2, 0, 2, 1, 2], [0, 2, 0, 2, 1, 2, 0, 1],
      [1, 2, 0, 1, 0, 2, 0, 2], [1, 2, 0, 2, 0, 2, 0, 1]]
  | 4, 0 => .inr ![
      [0, 1, 2, 0, 2, 0, 2, 0], [1, 0, 2, 0, 2, 1, 2, 1],
      [1, 0, 2, 1, 2, 1, 2, 0], [2, 0, 1, 0, 2, 1, 2, 1]]
  | 4, 1 => .inl [2, 0, 2, 1]
  | 4, 2 => .inl [2, 1]
  | 4, 3 => .inl [0, 1]
  | 4, 4 => .inl [0, 1, 0, 2]
  | 4, 5 => .inr ![
      [0, 1, 0, 1, 0, 2, 1, 2], [0, 1, 0, 2, 1, 2, 0, 1],
      [1, 2, 0, 1, 0, 1, 0, 2], [1, 2, 0, 1, 0, 2, 0, 1]]
  | 5, 0 => .inr ![
      [0, 1, 2, 0, 2, 0, 2, 1], [0, 1, 2, 0, 2, 1, 2, 0],
      [1, 0, 2, 1, 2, 1, 2, 1], [2, 0, 2, 0, 2, 1, 0, 1]]
  | 5, 1 => .inl [2, 1, 2, 1]
  | 5, 2 => .inl [0, 1, 2, 1]
  | 5, 3 => .inl [0, 1, 0, 1]
  | 5, 4 => .inr ![
      [0, 1, 2, 1, 0, 2, 0, 2], [0, 2, 0, 2, 0, 1, 2, 1],
      [1, 2, 0, 1, 0, 1, 0, 1], [2, 1, 0, 1, 0, 2, 0, 2]]
  | 6, 0 => .inr ![
      [0, 1, 2, 0, 2, 1, 2, 1], [0, 1, 2, 1, 2, 1, 2, 0],
      [2, 0, 2, 1, 0, 1, 2, 1], [2, 1, 0, 1, 2, 1, 2, 0]]
  | 6, 1 => .inr ![
      [0, 1, 0, 1, 2, 0, 2, 1], [0, 1, 0, 1, 2, 1, 2, 0],
      [2, 0, 2, 1, 0, 1, 0, 1], [2, 1, 0, 1, 0, 1, 2, 0]]
  | 6, 2 => .inr ![
      [0, 1, 0, 1, 0, 1, 2, 0], [0, 1, 2, 1, 2, 1, 0, 2],
      [0, 2, 0, 1, 2, 1, 2, 1], [2, 1, 0, 1, 2, 1, 0, 2]]
  | 6, 3 => .inr ![
      [0, 1, 0, 1, 2, 1, 0, 2], [0, 1, 0, 2, 0, 1, 2, 1],
      [2, 1, 0, 1, 0, 1, 0, 2], [2, 1, 0, 1, 0, 2, 0, 1]]
  | _, _ => .inl []

private def hexOffset (i j : Fin 7) : HexVertex := ((i.val : ℤ) - 3, (j.val : ℤ) - 3, false)

private def hexEndNeighbors (word : List (Fin 3)) : HexVertex × HexVertex :=
  let p := hexRoute hexOrigin word
  (p.getVert 1, p.getVert 7)

private def hexLocalCorrect (z : HexVertex) :
    (List (Fin 3) ⊕ (Fin 4 → List (Fin 3))) → Prop
  | .inl word => word.length < 6 ∧ hexDestination hexOrigin word = z
  | .inr words =>
    (∀ i, (words i).length = 8 ∧ hexDestination hexOrigin (words i) = z ∧
      (hexRoute hexOrigin (words i)).support.Nodup) ∧
    ∀ i j, hexEndNeighbors (words i) = hexEndNeighbors (words j) → i = j

private instance (z : HexVertex) (data : List (Fin 3) ⊕ (Fin 4 → List (Fin 3))) :
    Decidable (hexLocalCorrect z data) := by
  cases data <;> unfold hexLocalCorrect <;> infer_instance

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem hexLocalData_correct : ∀ i j : Fin 7,
    hexWithin 3 hexOrigin (hexOffset i j) →
    hexLocalCorrect (hexOffset i j) (hexLocalData i.val j.val) := by
  decide

private theorem walk_between_indices {U : Type*} {H : SimpleGraph U}
    {a b : U} (p : H.Walk a b) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ p.length) :
    ∃ r : H.Walk (p.getVert i) (p.getVert j), r.length = j - i := by
  let q := (p.drop i).take (j - i)
  have hEnd : (p.drop i).getVert (j - i) = p.getVert j := by
    rw [Walk.drop_getVert]
    congr 1
    omega
  refine ⟨q.copy rfl hEnd, ?_⟩
  simp [q, min_eq_left (show j - i ≤ p.length - i by omega)]

/-- Se o desvio evita a colisão entre os dois vizinhos extremos, sua projeção
é um ciclo simples de comprimento oito. -/
private theorem hex_detour_projects_cycle {U V : Type*}
    {H : SimpleGraph U} {G : SimpleGraph V} (π : H →g G) (C : G.Coloring Bool)
    {u w : U} (p : H.Walk u w) (hp : p.IsPath) (hlen : p.length = 8) (heq : π u = π w)
    (hsep : ∀ a b, H.Reachable a b → H.dist a b < 6 → π a = π b → a = b)
    (hends : π (p.getVert 1) ≠ π (p.getVert 7)) :
    ∃ (v : V) (q : G.Walk v v), q.IsCycle ∧ q.length = 8 := by
  have gap {i j : ℕ} (hij : i < j) (hj : j ≤ 8)
      (he : π (p.getVert i) = π (p.getVert j)) : 6 ≤ j - i ∧ Even (j - i) := by
    obtain ⟨r, hlenR⟩ := walk_between_indices p hij.le (by omega : j ≤ p.length)
    refine ⟨?_, ?_⟩
    · by_contra! h
      have hdist := H.dist_le r
      have he' := hsep _ _ ⟨r⟩ (by omega) he
      have : i = j := hp.getVert_injOn (by change i ≤ p.length; omega)
        (by change j ≤ p.length; omega) he'
      omega
    · have h := (C.even_length_iff_congr (r.map π)).mpr (by rw [he])
      simpa [hlenR] using h
  have no_repeat {i j : ℕ} (hij : i < j) (hj : j ≤ 7)
      (he : π (p.getVert i) = π (p.getVert j)) : False := by
    obtain ⟨hge, hpar⟩ := gap hij (by omega) he
    rw [Nat.even_iff] at hpar
    have hcases : (i = 0 ∧ j = 6) ∨ (i = 1 ∧ j = 7) := by omega
    rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hp8 : p.getVert 8 = w := hlen ▸ p.getVert_length
      have he68 : π (p.getVert 6) = π (p.getVert 8) := by
        rw [hp8, ← heq, ← he, Walk.getVert_zero]
      have := (gap (by decide : 6 < 8) (by decide) he68).1
      omega
    · exact hends he
  let q := (p.map π).copy rfl heq.symm
  have hqLen : q.length = 8 := by simp [q, hlen]
  refine ⟨π u, q, Walk.isCycle_iff_isPath_dropLast_and_le_length.mpr ⟨?_, by omega⟩, hqLen⟩
  apply (Walk.IsPath.getVert_injOn_iff q.dropLast).mp
  intro i hi j hj hij
  change i ≤ q.dropLast.length at hi
  change j ≤ q.dropLast.length at hj
  rw [Walk.length_dropLast, hqLen] at hi hj
  rw [Walk.getVert_dropLast (by omega : i < q.length),
    Walk.getVert_dropLast (by omega : j < q.length)] at hij
  simp only [q, Walk.getVert_copy, Walk.getVert_map] at hij
  rcases lt_trichotomy i j with h | h | h
  · exact (no_repeat h hj hij).elim
  · exact h
  · exact (no_repeat h hi hij.symm).elim

private theorem hexRoute_first (u : HexVertex) (word : List (Fin 3)) (hne : word ≠ []) :
    (hexRoute u word).getVert 1 = hexStep u (word.headD 0) := by
  cases word with
  | nil => exact (hne rfl).elim
  | cons i rest =>
    change (hexRoute (hexStep u i) rest).getVert 0 = hexStep u i
    exact Walk.getVert_zero _

private theorem hex_collision_detour {V : Type*} {G : SimpleGraph V} (π : hexLattice →g G)
    (hlocal : ∀ o a b, hexLattice.Adj o a → hexLattice.Adj o b → π a = π b → a = b)
    {u w : HexVertex} (p : hexLattice.Walk u w) (hp : p.length = 6)
    (hdist : hexLattice.dist u w = 6) :
    ∃ q : hexLattice.Walk u w, q.IsPath ∧ q.length = 8 ∧
      π (q.getVert 1) ≠ π (q.getVert 7) := by
  let E := hexCoordinateIso u
  let v := E.symm w
  have hOrigin : E hexOrigin = u := hexCoordinateIso_origin u
  have hRoot : E.symm u = hexOrigin := E.injective (by simp [hOrigin])
  let r : hexLattice.Walk hexOrigin v := (p.map E.symm.toHom).copy hRoot rfl
  have hr : r.length = 6 := by simp [r, hp]
  have hBox : hexWithin 3 hexOrigin v := by simpa [hr] using hexWalk_within r
  have hColor : v.2.2 = false := by
    let C : hexLattice.Coloring Bool := Coloring.mk (fun z => z.2.2) (fun h => hexAdj_color h)
    have heven : Even r.length := by rw [hr]; decide
    have h := (C.even_length_iff_congr r).mp heven
    have heq : C hexOrigin = C v := by simpa only [Bool.coe_iff_coe] using h
    change false = v.2.2 at heq
    exact heq.symm
  have hCoords : -3 ≤ v.1 ∧ v.1 ≤ 3 ∧ -3 ≤ v.2.1 ∧ v.2.1 ≤ 3 := by
    dsimp [hexWithin, hexOrigin] at hBox
    omega
  let i : Fin 7 := ⟨(v.1 + 3).toNat, by omega⟩
  let j : Fin 7 := ⟨(v.2.1 + 3).toNat, by omega⟩
  have hOffset : hexOffset i j = v := by
    refine Prod.ext ?_ (Prod.ext ?_ hColor.symm)
    · change ((v.1 + 3).toNat : ℤ) - 3 = v.1
      omega
    · change ((v.2.1 + 3).toNat : ℤ) - 3 = v.2.1
      omega
  have hCert := hexLocalData_correct i j (hOffset.symm ▸ hBox)
  let placed (word : List (Fin 3)) (he : hexDestination hexOrigin word = hexOffset i j) :
      hexLattice.Walk u w :=
    ((hexRoute hexOrigin word).map E.toHom).copy hOrigin
      (by simp [he, hOffset, v])
  have hPlacedLength (word) (he) : (placed word he).length = word.length := by
    simp [placed]
  have hPlacedVertex (word) (he) (n) :
      (placed word he).getVert n = E ((hexRoute hexOrigin word).getVert n) := by
    simp [placed, Walk.getVert_map]
  cases hData : hexLocalData i.val j.val with
  | inl word =>
    rw [hData] at hCert
    obtain ⟨hLen, hEnd⟩ := hCert
    have h := hexLattice.dist_le (placed word hEnd)
    rw [hPlacedLength word hEnd, hdist] at h
    omega
  | inr words =>
    rw [hData] at hCert
    obtain ⟨hRoute, hPairs⟩ := hCert
    let q (k : Fin 4) := placed (words k) (hRoute k).2.1
    have hLen (k) : (q k).length = 8 := (hPlacedLength (words k) (hRoute k).2.1).trans (hRoute k).1
    have hVertex (k n) :
        (q k).getVert n = E ((hexRoute hexOrigin (words k)).getVert n) :=
      hPlacedVertex (words k) (hRoute k).2.1 n
    have hLast (k) : hexLattice.Adj w ((q k).getVert 7) := by
      have h := (q k).adj_getVert_succ (i := 7) (by rw [hLen]; decide)
      change hexLattice.Adj ((q k).getVert 7) ((q k).getVert 8) at h
      rw [← hLen k, Walk.getVert_length] at h
      exact h.symm
    have hGood : ∃ k, π ((q k).getVert 1) ≠ π ((q k).getVert 7) := by
      by_contra h
      push Not at h
      have hHead : Function.Injective (fun k : Fin 4 => (words k).headD 0) := by
        intro a b hab
        change (words a).headD 0 = (words b).headD 0 at hab
        have hFirst (k : Fin 4) :
            (q k).getVert 1 = E (hexStep hexOrigin ((words k).headD 0)) := by
          rw [hVertex, hexRoute_first]
          intro hn
          have hlen := (hRoute k).1
          simp [hn] at hlen
        have hF : (q a).getVert 1 = (q b).getVert 1 := by rw [hFirst, hFirst, hab]
        have hL : (q a).getVert 7 = (q b).getVert 7 := by
          apply hlocal w _ _ (hLast a) (hLast b)
          rw [← h a, ← h b, hF]
        rw [hVertex a 1, hVertex b 1] at hF
        rw [hVertex a 7, hVertex b 7] at hL
        exact hPairs a b (Prod.ext (E.injective hF) (E.injective hL))
      have hCard := Fintype.card_le_of_injective _ hHead
      simp at hCard
    obtain ⟨k, hk⟩ := hGood
    have hRawPath := (Walk.isPath_def (hexRoute hexOrigin (words k))).mpr (hRoute k).2.2
    have hPath : (q k).IsPath := by
      simpa [q, placed] using hRawPath.map E.injective
    exact ⟨q k, hPath, hLen k, hk⟩

/-- Uma imagem bipartida e localmente injetiva da rede hexagonal contém
um ciclo simples de comprimento quatro, oito ou dezesseis.
A prova usa apenas a injetividade nas vizinhanças. -/
theorem hex_local_injective_has_cycle_4_8_16 {V : Type*} (G : SimpleGraph V)
    (C : G.Coloring Bool) (π : hexLattice →g G)
    (hlocal : ∀ o a b, hexLattice.Adj o a → hexLattice.Adj o b → π a = π b → a = b) :
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
    exact huw (hlocal (p.getVert 1) u w h01.symm h12 heq)
  have hcases : p.length = 4 ∨ p.length = 6 := by
    rw [Nat.even_iff] at hEven
    omega
  rcases hcases with h4 | h6
  · obtain ⟨v, q, hq, hqLen⟩ := shortest_collision_projects_cycle π p hp (by omega) heq hsep
    exact ⟨v, q, hq, Or.inl (hqLen.trans h4)⟩
  · obtain ⟨q, hqPath, hqLen, hqEnds⟩ :=
      hex_collision_detour π hlocal p h6 (hp.symm.trans h6)
    have hs (a b) (hrab : hexLattice.Reachable a b) (hd : hexLattice.dist a b < 6)
        (he : π a = π b) : a = b :=
      hsep a b hrab (h6.symm ▸ hd) he
    obtain ⟨v, r, hr, hrLen⟩ := hex_detour_projects_cycle π C q hqPath hqLen heq hs hqEnds
    exact ⟨v, r, hr, Or.inr (Or.inl hrLen)⟩

/-- Teorema 17 (Núcleo Combinatório): Todo grafo finito simples bipartido `G` que admite
um recobrimento pela rede hexagonal infinita `hexLattice` contém um ciclo simples de
comprimento `4`, `8` ou `16`. -/
theorem hex_covering_has_cycle_4_8_16 {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (hbip : ∃ c : V → Bool, ∀ u v : V, G.Adj u v → c u ≠ c v)
    (π : hexLattice →g G) (hcov : IsGraphCovering π) :
    ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ (p.length = 4 ∨ p.length = 8 ∨ p.length = 16) := by
  obtain ⟨c, hc⟩ := hbip
  let C : G.Coloring Bool := Coloring.mk c (fun {a b} h => hc a b h)
  exact hex_local_injective_has_cycle_4_8_16 G C π (fun o => (hcov o).1)

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

/-! ### Rodada 10: Balanço de fronteira em superfícies -/

/-- Núcleo algébrico do Teorema 20. `boundary` conta as arestas de corte,
`surplus` é a soma dos excessos de grau sobre três e `chi` é a característica
de Euler do mergulho celular do lado considerado. -/
theorem euler_boundary_deficit_bound {n e f boundary surplus : ℕ} {chi : ℤ}
    (hhand : 2 * e + boundary = 3 * n + surplus)
    (hfaces : 6 * f ≤ 2 * e)
    (heuler : chi = (n : ℤ) - (e : ℤ) + (f : ℤ)) :
    3 * chi + (surplus : ℤ) ≤ (boundary : ℤ) := by
  omega

/-! ### Rodada 11: Um corte cúbico e a colagem com uma aresta de junção -/

/-- Com uma só aresta de junção, os dois caminhos de um ciclo diádico
têm paridades opostas e seus comprimentos somam 3 módulo 4. -/
theorem single_join_edge_dyadic_residues {a b k : ℕ} (hk : 2 ≤ k)
    (hlen : a + b + 1 = 2 ^ k) :
    a % 2 ≠ b % 2 ∧ (a + b) % 4 = 3 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [pow_add] at hlen
  norm_num at hlen
  omega

end Erdos64
