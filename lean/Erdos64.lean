import Mathlib

/-!
# Projeto Erdős #64 — Formalização em Lean 4 (`Checkpoint v1.2.1`)

Sincronizado com `README.md` (v1.2.1 — Calibração Lean `v4.36.0` / Mathlib `v4.36.0`, Progresso `18% / 100%`).

Status dos blocos:
- `HasPow2Cycle.mono`                   : VERIFIED (sem `sorry`, intocado)
- `HasPow2Cycle.of_induce`              : VERIFIED (sem `sorry`, intocado)
- `common_neighbors_le_one`             : VERIFIED (sem `sorry`, intocado)
- `triangles_edge_disjoint`             : VERIFIED (sem `sorry`, intocado)
- `minimal_connected`                   : VERIFIED (sem `sorry`, intocado)
- `HasPow2Cycle.map`                    : READY_TO_COMPILE (corrigido sem `sorry`)
- `no_two_common_neighbors`             : READY_TO_COMPILE (corrigido sem `sorry`)
- `high_degree_independent`             : READY_TO_COMPILE (corrigido sem `sorry`)
- `no_L3_vertices`                      : READY_TO_COMPILE (corrigido sem `sorry`)
- Demais 9 teoremas (Rodadas 2–7)       : enunciados tipados com `sorry`
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

/-! ### Infraestrutura Formal: Transporte de Ciclos C_{2^k} -/

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

/-! ### Rodada 1: Propriedades Básicas (Lemas 1–4) — TODOS SEM `sorry` -/

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
  haveI : Nonempty W := ⟨⟨u₀, SimpleGraph.Reachable.refl u₀⟩⟩
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
          Set.mem_singleton_iff, Finset.mem_erase, Sym2.eq_iff, huv_ne] <;> tauto
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
            Set.mem_singleton_iff, Finset.mem_erase, Sym2.eq_iff, huv_ne, huv_ne.symm] <;> tauto
        have hu_mem : u ∈ G.neighborFinset x := by
          simpa [SimpleGraph.mem_neighborFinset] using huv.symm
        rw [SimpleGraph.degree, hnb, Finset.card_erase_of_mem hu_mem]
        change 3 ≤ G.degree x - 1
        omega
      · have hnb : H.neighborFinset x = G.neighborFinset x := by
          ext y
          simp [H, SimpleGraph.mem_neighborFinset, SimpleGraph.deleteEdges_adj,
            Set.mem_singleton_iff, Sym2.eq_iff, hxu, hxv]
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

/-- Lema 5: Todo contraexemplo mínimo não possui pontes (é 2-aresta-conexo). -/
theorem minimal_bridgeless {V : Type} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmin : IsMinimalCounterexample G) (e : Sym2 V) : ¬ G.IsBridge e := by
  sorry

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

/-- Teorema 7: Em qualquer grafo livre de C_{2^k}, `G_Δ` não possui ciclos de comprimento ≥ 4. -/
theorem triangle_cactus_no_long_cycle {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hfree : ¬ HasPow2Cycle G) :
    ∀ (v : V) (p : (triangleSubgraph G).Walk v v), p.IsCycle → p.length = 3 := by
  sorry

/-! ### Rodada 4: Componentes de V_3 e Pisos de Cubicidade (Teoremas 8–10) -/

/-- Corolário 8.1 (SEM `sorry`): Em um contraexemplo mínimo, todo vértice de grau 3 tem pelo
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

end Erdos64
