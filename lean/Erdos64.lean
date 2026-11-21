import Mathlib

/-!
# Projeto Erdős #64 — Formalização em Lean 4 (`Checkpoint v1.1`)

Sincronizado com `README.md` (v1.1 — Pós-Rodada 5).
Status dos teoremas:
- `no_two_common_neighbors`        : READY_TO_COMPILE (sem `sorry`)
- `common_neighbors_le_one`        : READY_TO_COMPILE (sem `sorry`)
- `triangles_edge_disjoint`        : READY_TO_COMPILE (sem `sorry`)
- Demais declarações (Rodadas 1–5) : enunciados tipados com `sorry`
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

/-! ### Rodada 1: Propriedades Básicas (Lemas 1–4) -/

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
      exact ⟨⟨hne_vw₁.symm, hw, hne_uw₁.symm⟩, ⟨hne_vw₂, huv.symm⟩, hne_uw₂.symm⟩
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
  sorry

/-- Lema 4: Em um contraexemplo mínimo, os vértices de grau ≥ 4 formam conjunto independente. -/
theorem high_degree_independent {V : Type} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmin : IsMinimalCounterexample G) {u v : V}
    (hu : 4 ≤ G.degree u) (hv : 4 ≤ G.degree v) : ¬ G.Adj u v := by
  sorry

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
  symm := by
    rintro u v ⟨huv, w, huw, hvw⟩
    exact ⟨huv.symm, w, hvw, huw⟩
  loopless := by
    intro v ⟨hvv, _⟩
    exact G.loopless v hvv

/-- Teorema 7: Em qualquer grafo livre de C_{2^k}, `G_Δ` não possui ciclos de comprimento ≥ 4. -/
theorem triangle_cactus_no_long_cycle {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hfree : ¬ HasPow2Cycle G) :
    ∀ (v : V) (p : (triangleSubgraph G).Walk v v), p.IsCycle → p.length = 3 := by
  sorry

/-! ### Rodada 4: Componentes de V_3 e Pisos de Cubicidade (Teoremas 8–10) -/

/-- Corolário 8.1: Em um contraexemplo mínimo, nenhum vértice de grau 3 tem todos os vizinhos
em H = V_{≥ 4} (ou seja, L_3 = ∅). -/
theorem no_L3_vertices {V : Type} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmin : IsMinimalCounterexample G) {v : V} (hv : G.degree v = 3) :
    ∃ u : V, G.Adj v u ∧ G.degree u = 3 := by
  sorry

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
    ∀ (i : ι) (j : Fin d), G.Adj (f i j) (f i (j + 1))

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

end Erdos64
