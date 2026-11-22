> **INSTRUÇÃO AUTOMÁTICA DE RETOMADA PARA A IA (LEIA PRIMEIRO):**  
> Se o usuário enviou este arquivo (ou link) em uma nova conversa — mesmo acompanhado apenas de um comando curto como *"segue"* ou *"continua"* — **assuma imediatamente a continuidade da pesquisa abaixo sem pedir confirmação**.  
> 1. Considere todos os resultados da **Seção 3** como provados matematicamente (ver status real de compilação formal na tabela da Seção 3 e na Seção 5).  
> 2. Se o usuário colou logs/erros do compilador Lean 4, priorize corrigir e validar os teoremas em `lean/Erdos64.lean` antes ou em conjunto com a nova rodada teórica.  
> 3. **Ambiente Lean confirmado:** escreva **sempre** para **Lean 4 `v4.36.0` + Mathlib `v4.36.0`** respeitando rigorosamente as regras de compatibilidade da **Seção 5** (nunca chute nomes de lemas; prefira `simp`, `simpa`, `omega`, `aesop` ou `grind`).  
> 4. Respeite os **Becos Sem Saída** da **Seção 4** para não repetir caminhos descartados.  
> 5. Escolha **autonomamente** o ataque e execute diretamente a **Próxima Rodada** definida na **Seção 6** (neste checkpoint: **Rodada 9**), abrindo sua resposta com o indicador `**Progresso: X% / 100%**`.  
> 6. Sempre que gerar um novo checkpoint, atualize **simultaneamente** `README.md` e `Erdos64_lean.md` (envelope para `lean/Erdos64.lean` — Regra do Par Sincronizado).

---

# Projeto Erdős #64 — Conjectura de Erdős–Gyárfás

> **Arquivo Mestre de Estado, Memória e Continuidade (`Checkpoint v1.3`)**  
> **Última atualização:** 22 de novembro de 2026 (Pós-Rodada 8 — Superfícies $\chi \ge 0$ & Limpeza de Linter)  
> **Progresso Atual:** `22% / 100%`  
> **Alvo Oficial:** `https://erdosproblems.com/64` (Prêmio de \$1.000 — Teoria dos Grafos / Ciclos)  
> **Arquivo Lean Sincronizado:** `lean/Erdos64.lean` (entregue via envelope `Erdos64_lean.md`)  
> **Contagem Formal Honesta (`lean/Erdos64.lean`):** **9 teoremas `VERIFIED`** (0 erros em Lean `v4.36.0`; 4 avisos de linter limpos na v1.3) | **2 novos teoremas `READY_TO_COMPILE`** (sem `sorry`, Rodada 8) | **10 declarações com `sorry`**

---

## 1. Protocolo de Continuidade e Regras do Projeto

1. **Retomada Imediata Sem Regressão:**
   - Todos os teoremas listados na **Seção 3** estão com demonstração matemática fechada; só revisite algum deles se o compilador Lean 4 apontar um erro ou durante a eliminação de seus `sorry` em `lean/Erdos64.lean`.
   - Leia a **Seção 4** (Becos Sem Saída) e a **Seção 5** (Regras Lean `v4.36.0`) antes de propor qualquer ataque ou código novo.
   - Retome sempre pela **Próxima Rodada** da **Seção 6** (neste checkpoint: **Rodada 9**).

2. **Divisão de Papéis:**
   - **IA (Estrategista e Demonstradora):** Decide **autonomamente** qual frente atacar em cada rodada, conduz as demonstrações com rigor completo, decide o momento de emitir novos checkpoints e mantém o código Lean 4 atualizado. Não pergunte ao usuário qual subproblema escolher.
   - **Usuário (Orquestrador / Ponte de Verificação):** Controla o ritmo (*"segue"*), envia os arquivos `.md` ao seu agente com acesso ao GitHub e ao compilador **Lean 4 `v4.36.0` + Mathlib `v4.36.0`**, devolve relatórios/erros de compilação e mantém o repositório sincronizado.

3. **Regra do Termômetro de Progresso (`0%` a `100%`):**
   - Toda rodada de pesquisa **deve começar** com `**Progresso: X% / 100%**` seguido de justificativa breve e honesta.
   - Escala:
     - `0%`: Mapeamento inicial, sem resultado estrutural próprio.
     - `1%` a `25%`: Reduções estruturais, eliminação de classes específicas e resultados parciais sólidos.
     - `26%` a `60%`: Quebra de barreiras centrais no núcleo cúbico 3-conexo ou ferramenta geral aplicável a estruturas globais de ciclos.
     - `61%` a `95%`: Arquitetura de prova global fechada com poucos lemas técnicos pendentes (ou candidato real a contraexemplo superando filtros profundos).
     - `100%`: Prova completa fechada (ou contraexemplo explícito verificado), faltando apenas a verificação final sem `sorry` no Lean 4.

4. **Regra do Par Sincronizado (`README.md` + `Erdos64_lean.md` $\to$ `lean/Erdos64.lean`):**
   - **Sempre** que a IA gerar uma atualização de `README.md`, **deve gerar na mesma resposta** o arquivo `Erdos64_lean.md` contendo o código completo de `lean/Erdos64.lean` em bloco `lean` para extração automática pelo agente.
   - Substituir sempre os mesmos arquivos no GitHub (`README.md` e `lean/Erdos64.lean`), sem criar arquivos `v2`, `v3`.
   - Nunca substituir uma prova com erro por `sorry` para esconder erro de compilação; preservar sempre os teoremas já `VERIFIED`.
   - Usar exclusivamente LaTeX (`$...$` e `$$...$$`) para notação matemática fora dos blocos de código Lean.

---

## 2. Enunciado Oficial e Fronteira da Literatura (Nov/2026)

### Enunciado (Problema #64 — Erdős & Gyárfás, 1995)
> Todo grafo finito simples $G$ com grau mínimo $\delta(G) \ge 3$ contém um ciclo simples de comprimento $2^k$ para algum inteiro $k \ge 2$ (ou seja, $4, 8, 16, 32, \dots$)?

### Fronteira Conhecida até Novembro de 2026
* **Grau médio alto:** Liu e Montgomery (existe constante grande $C$ tal que todo grafo com grau médio $\ge C$ contém um ciclo $C_{2^k}$).
* **Classes resolvidas conhecidas:** Grafos cúbicos planares 3-conexos (Heckman–Krakovski, 2013); grafos planares livres de garra (Daniel–Shauger); grafos $P_{13}$-livres (Hegde–Sandeep–Shashank, 2025, com busca computacional); grafos bipartidos planares (fórmula de Euler).
* **Redução estrutural recente (2026):** Avery Carr (`arXiv:2605.22844`, mai/2026: $|V_3| \ge \frac{4}{7}n$) e Guillaume Ducoffe & Bogdan Dumitru (`arXiv:2609.28594`, jul–set/2026: 2-conexo ou 1-clique-soma de dois blocos 2-conexos, e $|V_3| > \frac{2}{3}n$).
* **Limites computacionais certificados (2026 — Ducoffe–Dumitru, Balaji, Tranquilli):** Não existe contraexemplo com:
  * $n \le 40$ vértices (grafos gerais);
  * $n \le 48$ vértices (grafos cúbicos);
  * $n \le 66$ vértices (grafos bipartidos; $n \ge 60$ também certificado para cúbicos bipartidos por Tranquilli, `arXiv:2608.02675`).

---

## 3. Inventário de Resultados Provados (Rodadas 1 a 8)

### Convenções Fixas
* Um grafo $G$ é **livre de $C_{2^k}$** se não contém ciclo simples de comprimento $2^k$ com $k \ge 2$.
* Um **contraexemplo mínimo** $G$ é um grafo finito simples, não vazio, com $\delta(G) \ge 3$ e livre de $C_{2^k}$, com **menor $|V(G)|$** possível e, no empate, **menor $|E(G)|$** possível.
* Partição por graus: $H = V_{\ge 4}$ (tamanho $h$), $H_4 = V_4$, $L = V_3$ (tamanho $\ell$), e $L_j = \{v \in L : |N_G(v) \cap H| = j\}$ ($j \in \{0, 1, 2, 3\}$).

### Tabela Mestre de Progresso e Sincronização com `lean/Erdos64.lean`

| ID | Resultado | Rodada | Declaração em `lean/Erdos64.lean` | Status Lean 4 (`v4.36.0`) |
| :--- | :--- | :---: | :--- | :---: |
| **Infra 1** | Transporte de `HasPow2Cycle` por homomorfismo injetivo | 7 | `HasPow2Cycle.map` | **`VERIFIED`** |
| **Infra 2** | Monotonicidade de `HasPow2Cycle` em subgrafos geradores | 7 | `HasPow2Cycle.mono` | **`VERIFIED`** |
| **Infra 3** | Monotonicidade de `HasPow2Cycle` em subgrafos induzidos | 7 | `HasPow2Cycle.of_induce` | **`VERIFIED`** |
| **Lema 1** | Contraexemplo mínimo é conexo | 1 | `minimal_connected` | **`VERIFIED`** *(linter limpo v1.3)* |
| **Lema 2a** | Dois vértices distintos têm no máximo 1 vizinho comum (estrutural) | 1 | `no_two_common_neighbors` | **`VERIFIED`** |
| **Lema 2b** | Dois vértices distintos têm no máximo 1 vizinho comum (cardinalidade) | 1 | `common_neighbors_le_one` | **`VERIFIED`** |
| **Lema 3** | Triângulos nunca compartilham arestas | 1 | `triangles_edge_disjoint` | **`VERIFIED`** |
| **Lema 4** | $H = V_{\ge 4}$ é um conjunto independente | 1 | `high_degree_independent` | **`VERIFIED`** *(linter limpo v1.3)* |
| **Lema 5** | Contraexemplo mínimo não possui pontes | 2 | `minimal_bridgeless` | `SORRY` |
| **Lema 6** | Dicotomia do vértice de corte e Redução ao Bloco Pinçado $\mathcal{K}$ | 2 | `pinched_block_equiv` | `PLANNED` |
| **Teorema 7** | **Teorema do Cacto de Triângulos** ($G_\Delta$ sem ciclos $\ge 4$) | 3 | `triangle_cactus_no_long_cycle` | `SORRY` |
| **Teoremas 8–9** | Fronteira das componentes de $G[L]$, $L_3 = \emptyset$, $\|E(G[L_2])\| \le \|H_4\|$ | 4 | `no_L3_vertices` | **`VERIFIED`** |
| **Teorema 10** | Pisos de cubicidade: $\|V_3\| \ge \frac{8}{11}n$ (sem $K_3$) e $\ge \frac{20}{27}n$ (bipartido) | 4 | `minimal_triangle_free_cubicity`, `minimal_bipartite_cubicity` | `SORRY` |
| **Teorema 11** | **Autorredução de $K_3$-fatores** em cúbicos ($H_3$ cúbico simples) | 5 | `minimal_no_K3_factor` | `SORRY` |
| **Teorema 12** | **Autorredução de $C_5$-fatores** em cúbicos ($H_5$ 5-regular; $n \ge 110$) | 5 | `minimal_no_C5_factor` | `SORRY` |
| **Teorema 13** | **3-Conectividade e Redução à Metade em Bipartidos** ($\|V(G')\| \le \lfloor (n+2)/2 \rfloor$) | 6 | `bipartite_not_3connected_halving` | `SORRY` |
| **Teorema 14** | **Obstrução de Colagem Assimétrica** em cortes de 2 arestas | 6 | `two_edge_cut_asymmetric_gluing` | `PLANNED` |
| **Teorema 15** | **Degeneração dos Triângulos $L_2$** ($G_S$ simples, livre de $C_{2^k}$, 2-degenerado) + $3\|V_3\| \ge 2n + 1$ + $\|V_3\| \ge \frac{12}{17}n$ ($S = \emptyset$) | 7 | `minimal_general_cubicity`, `minimal_no_K2_in_V3_cubicity` | `SORRY` |
| **Prop. 16** | Rigidez de $C_7$-fatores sem $K_3$ ($\delta(H_7^{\text{simp}}) \ge 3$) + Lei Modular $p \mid (d+2)$ | 7 | *(classificação de fronteira)* | `N/A` |
| **Teorema 17** | **Bipartidos em Superfícies $\chi \ge 0$:** todo bipartido com $\delta \ge 3$ no plano, $\mathbb{RP}^2$, toro ou garrafa de Klein contém $C_4$, $C_8$ ou $C_{16}$ (conjunto ótimo) | 8 | `hex_covering_has_cycle_4_8_16` | `SORRY` |
| **Teorema 18** | **Desigualdade Exata do Fulereno ($C_{60}$):** cintura $\ge 5$ sem $C_8$ em superfície $\chi$ satisfaz $30\chi \le 9n_3 - 8n$; no plano $n \ge 60$ (exato) e $n_3 \ge \frac{8n+60}{9}$ | 8 | `fullerene_euler_inequality`, `planar_girth5_no_C8_card_ge_60` | `READY_TO_COMPILE` |

*(Legenda Lean 4: **`VERIFIED`** = compilado com 0 erros e sem `sorry` em Lean `v4.36.0` — **9 teoremas**; `READY_TO_COMPILE` = prova escrita sem `sorry`, aguardando compilação — **2 teoremas**; `SORRY` = enunciado tipado aguardando prova formal — **10 declarações**; `PLANNED` = pendente de transcrição.)*

---

### 3.1. Resumo das Rodadas 1 a 7 (Lemas 1–6, Teoremas 7–15 e Proposição 16)

* **Rodada 1 (Lemas 1–4 — TODOS `VERIFIED`):** Todo contraexemplo mínimo $G$ é conexo, tem no máximo 1 vizinho comum entre vértices distintos, não tem triângulos compartilhando aresta e tem $H = V_{\ge 4}$ como conjunto independente.
* **Rodada 2 (Lemas 5–6 e Bloco Pinçado):** $G$ não tem pontes. Se $G$ tem vértice de corte $v$, então $v$ é único, $\deg_G(v) = 4$, e $G$ é colagem de dois blocos 2-conexos $H_1, H_2$ de mesma ordem $k + 1$ e mesmo número de arestas. A conjectura equivale a $\mathcal{K} = \emptyset$ ($\mathcal{K}$ = grafos 2-conexos livres de $C_{2^k}$ com todos os graus $\ge 3$ exceto no máximo um vértice de grau $2$).
* **Rodada 3 (Teorema 7 — Cacto de Triângulos):** Em qualquer grafo livre de $C_{2^k}$, o subgrafo $G_\Delta$ das arestas em triângulos não tem ciclo de comprimento $\ge 4$ (todo bloco de $G_\Delta$ é um $K_3$; $G_\Delta$ é 2-degenerado com $|E_\Delta| \le \frac{3}{2}(n-1)$; conjectura vale se $\delta(G_\Delta) \ge 3$).
* **Rodada 4 (Teoremas 8–10):** Em qualquer contraexemplo mínimo (geral, sem triângulos ou bipartido) com $H \ne \emptyset$, toda componente conexa $C$ de $G[L]$ tem $x \in H$ com $|N_G(x) \cap V(C)| \ge \deg_G(x) - 2 \ge 2$ (Teorema 8), implicando $L_3 = \emptyset$ (`VERIFIED`), $c_2 \le c_0 + 2$, toda componente $K_2$ de $G[L]$ forma triângulo com único $x \in H_4$ e $|E(G[L_2])| \le |H_4|$ (Teorema 9). Pisos de cubicidade: $|V_3| \ge \frac{8}{11}n \approx 72{,}73\%$ (sem $K_3$) e $|V_3| \ge \frac{20}{27}n \approx 74{,}07\%$ (bipartido) (Teorema 10).
* **Rodada 5 (Teoremas 11–12):** Nenhum contraexemplo mínimo é cúbico com $K_3$-fator ($H_3$ cúbico simples sobre $n/3$ vértices) nem com $C_5$-fator ($H_5$ 5-regular simples sobre $n/5$ vértices; $n \ge 110$ elementar, $n > 200$ com $n > 40$).
* **Rodada 6 (Teoremas 13–14):**
  * **Teorema 13:** Todo bipartido não-3-conexo com $\delta \ge 3$ e livre de $C_{2^k}$ gera um **menor próprio** simples $G'$ com $\delta(G') \ge 3$, livre de $C_{2^k}$ e $|V(G')| \le \lfloor (n+2)/2 \rfloor$ ($\le \lfloor (n+1)/2 \rfloor$ com vértice de corte; $\le \lfloor n/2 \rfloor$ com corte de 2 arestas). Consequências: todo contraexemplo mínimo bipartido em classe fechada por menores é **3-conexo**; combinado com $n > 40$, todo bipartido não-3-conexo com $n \le 79$ ($n \le 81$ com corte de 2 arestas) satisfaz a conjectura.
  * **Teorema 14:** Em corte de 2 arestas não trivial $\{u_1 v_1, u_2 v_2\}$ de um contraexemplo mínimo geral (lados $A, B$ com $|V(A)| \le |V(B)|$), a colagem assimétrica força $\ell_1 + \ell_2 = 2^d - 1$ em $S(A)$ (logo $A$ nunca é bipartido), e se $u_1 u_2 \notin E(A), v_1 v_2 \notin E(B)$ então $P_A, P_B$ são não vazios e disjuntos.
* **Rodada 7 (Teorema 15 e Proposição 16):**
  * **Teorema 15:** Contraindo os triângulos disjuntos $T_x = \{x, v_x, w_x\}$ ($x \in S \subseteq H_4$) das componentes $K_2$ de $G[L]$, o grafo $G_S$ é simples, $\Delta(G_S) \le 4$ ($\deg^+, \deg^- \le 2$), livre de $C_{2^k}$ ($2^k \mapsto 2^{k+1}$) e 2-degenerado. Consequências: $|S| < |H|$ se $H \ne \emptyset$, nova prova combinatória de $3|V_3| \ge 2n + 1$, e $|V_3| \ge \frac{12}{17}n \approx 70{,}59\%$ se $S = \emptyset$.
  * **Proposição 16:** Em cúbicos sem $K_3$ com $C_7$-fator, $\delta(H_7^{\text{simp}}) \ge 3$; Lei Modular $p \mid (d+2)$ explica obstrução de levantamento para $d = 6$ ($\bmod 4$) e $d = 7$ ($\bmod 3$).

---

### 3.2. Rodada 8 — Bipartidos em Superfícies ($\chi \ge 0$) e Desigualdade Exata do Fulereno

#### Teorema 17 (Resolução Completa de Bipartidos em Superfícies $\chi \ge 0$)
> Todo grafo finito simples **bipartido** $G$ com $\delta(G) \ge 3$ imersível em uma superfície fechada $\Sigma$ com $\chi(\Sigma) \ge 0$ (plano/esfera, plano projetivo, toro ou garrafa de Klein) contém um ciclo simples de comprimento **$4$, $8$ ou $16$**. O conjunto $\{4, 8, 16\}$ é ótimo no toro e na garrafa de Klein (grade hexagonal toroidal $5 \times 5$ de 50 vértices tem ciclos $\le 16$ em $\{6, 10, 12, 14, 16\}$).

* **Esquema da prova fechada:**
  1. Se $G_0$ (componente conexa) não contém $C_4$, redução a mergulho 2-celular com $\chi(\Sigma') \ge 0$ força $6F \le 2E$ e $3V \le 2E$. Se $\chi > 0$, contradição imediata (contém $C_4$). Se $\chi = 0$, igualdade exata: $G_0$ é cúbico com todas as faces 6-ciclos simples, induzindo recobrimento de grafos bipartido $\pi : H \to G_0$ a partir da rede hexagonal infinita $H$ ($\mathbb{Z}^2 \times \{0, 1\}$).
  2. Seja $\rho(\pi) = \min\{d_H(x, y) : x \ne y,\, \pi(x) = \pi(y)\}$ (par, $\ge 4$ por injetividade local e bipartição):
     * $\rho(\pi) = 4 \implies$ caminho mínimo de comprimento 4 projeta em $C_4$ simples.
     * $\rho(\pi) = 6 \implies$ **Lema do Desvio Hexagonal:** nas 2 órbitas à distância 6 (representantes $(3, 0, 0)$ e $(2, 1, 0)$), existem $\ge 4$ caminhos simples de comprimento 8 com pares de vizinhos extremos $(w_1, w_7)$ distintos; pelo Princípio da Casa dos Pombos ($4 > 3$), ao menos um evita a bijeção local $f : N_H(u) \xrightarrow{\sim} N_H(v)$ e projeta em $C_8$ simples.
     * $\rho(\pi) \ge 8 \implies$ o trapézio de 5 hexágonos $\{(0,0),(1,0),(2,0),(0,1),(1,1)\}$ tem borda $C_{16}$ com diâmetro de mesma cor $\le 6 < 8 \le \rho(\pi)$, logo $\pi|_{V(C_{16})}$ é injetora e projeta em $C_{16}$ simples.

#### Teorema 18 (Desigualdade Exata do Fulereno — Cintura $\ge 5$, Livre de $C_8$)
> Para todo grafo finito simples $G$ com $\delta(G) \ge 3$, cintura $\ge 5$ e livre de $C_8$, imerso 2-celularmente em superfície fechada de característica $\chi$:
> $$30\chi \le \sum_{d \ge 3} \left(30 - 10d + \left\lfloor \frac{d}{2} \right\rfloor\right) n_d \le 9n_3 - 8n.$$
> Em particular:
> * **Plano ($\chi = 2$):** **$n \ge 60$** (exato — atingido pelo fulereno $C_{60}$, cujos ciclos $\le 16$ são $\{5, 6, 9, \dots, 16\}$) e **$n_3 \ge \frac{8n + 60}{9} > 88{,}9\%$**.
> * **Plano Projetivo ($\chi = 1$):** $n \ge 30$ e $n_3 \ge \frac{8n + 30}{9}$.
> * **Toro / Garrafa de Klein ($\chi = 0$):** $n_3 \ge \frac{8}{9}n \approx 88{,}89\%$.

* **Esquema da prova fechada:** Nenhuma aresta separa duas 5-faces (caso contrário as duas 5-faces formariam um $C_8$ simples, já que qualquer coincidência extra cria $C_3$ ou $C_4$). Logo cada vértice de grau $d$ incide em no máximo $\lfloor d/2 \rfloor$ faces pentagonais ($5F_5 \le \sum \lfloor \deg(v)/2 \rfloor$). Combinando com $6F \le 2E + F_5$ em $30\chi = 30V - 30E + 30F$ segue a desigualdade exata (núcleo algébrico já formalizado sem `sorry` na v1.3).

---

## 4. Becos Sem Saída e Obstruções Mapeadas (Não Repetir)

1. **Busca bruta computacional em grafos pequenos:** Descartada até $n \le 40$ (geral), $n \le 48$ (cúbico), $n \le 66$ (bipartido) e $n \le 79$ (bipartido não-3-conexo, pelo Corolário 13.2).
2. **Grafos planares bipartidos:** Caso trivial por Euler (já englobado pelo Teorema 17 para todo $\chi \ge 0$).
3. **Densidade pura de grafos 2-degenerados com $\Delta \le 4$ (como $G_S$ ou $M$):** Atingem $2m - O(1)$ arestas mesmo com cintura arbitrariamente alta.
4. **Contração simples de todos os triângulos $G / \mathcal{T}$ em cúbicos:** Um $C_4$ contraído com $t = 1$ triângulo levanta apenas para $\{5, 6\}$.
5. **Levantamento incondicional de $C_d$-fatores para $d \ge 6$:** Bloqueado pela Lei Modular (Proposição 16: $d=6 \bmod 4$, $d=7 \bmod 3$) e por cordas internas.
6. **Contração de 2-fator misto $\{C_3, C_5\}$:** $C_4$ contraído com três $K_3$ e um $C_5$ ($\{2,3\}$) levanta apenas para $[9, 13]$.

---

## 5. Ambiente Lean 4 e Regras Obrigatórias (`v4.36.0`)

* **Toolchain confirmado:** **Lean 4 `v4.36.0` + Mathlib `v4.36.0`** (novembro de 2026).
* **Contagem honesta atual (`lean/Erdos64.lean` — v1.3):**
  * **`VERIFIED` (9 teoremas — 0 erros em Lean `v4.36.0`):** `HasPow2Cycle.map`, `HasPow2Cycle.mono`, `HasPow2Cycle.of_induce`, `no_two_common_neighbors`, `common_neighbors_le_one`, `triangles_edge_disjoint`, `minimal_connected` *(linter limpo v1.3)*, `high_degree_independent` *(linter limpo v1.3)*, `no_L3_vertices`.
  * **`READY_TO_COMPILE` (2 novos teoremas sem `sorry` — Rodada 8):** `fullerene_euler_inequality`, `planar_girth5_no_C8_card_ge_60`.
  * **`SORRY` (10 declarações):** `minimal_bridgeless`, `triangle_cactus_no_long_cycle`, `minimal_triangle_free_cubicity`, `minimal_bipartite_cubicity`, `minimal_no_K3_factor`, `minimal_no_C5_factor`, `bipartite_not_3connected_halving`, `minimal_general_cubicity`, `minimal_no_K2_in_V3_cubicity`, `hex_covering_has_cycle_4_8_16`.

### Regras de Compatibilidade Confirmadas para Lean `v4.36.0` / Mathlib `v4.36.0`
1. **Não inventar nem chutar nomes de lemas** (em `v4.36.0`, convenções como `not_mem` viraram `notMem` camelCase; `Sym2.map_pair_eq`, `Finset.erase_eq_of_not_mem` e `SimpleGraph.mem_neighborFinset.mp/.mpr` **não existem**). Na dúvida, use `simp`, `simpa`, `omega`, `aesop`, `tauto` ou `grind`.
2. **`Std.Symm` e `Std.Irrefl` são estruturas:** ao construir um `SimpleGraph`, use `⟨by ...⟩`; para irreflexividade de `G.Adj`, use `G.ne_of_adj hvv rfl`.
3. **`push_neg` foi substituído por `push Not`.**
4. **Linters ativos:** use `have` (nunca `haveI`) para proposições; evite argumentos redundantes no `simp`; use `;` em vez de `<;>` quando houver apenas 1 submeta.
5. **Aritmética em `Fin d` genérico:** use `⟨(j.val + 1) % d, Nat.mod_lt _ (by have := j.isLt; omega)⟩` em vez de `j + 1`.
6. **`Sym2.map f s(a₁, a₂)`:** use `change s(f a₁, f a₂) = s(f b₁, f b₂) at hab` seguido de `rw [Sym2.eq_iff]`.
7. **`SimpleGraph.deleteEdges`:** simplifique sempre com `SimpleGraph.deleteEdges_adj`.

---

## 6. Plano Imediato para a Rodada 9

1. **Verificação da `v1.3` (meta: 11/11 blocos sem `sorry` + 0 avisos de linter):** Se o usuário trouxer o relatório da `v1.3`, corrigir eventual detalhe e confirmar `11 VERIFIED`.
2. **Ataque Teórico Principal (Rodada 9) — Duas frentes de maior retorno:**
   - **Frente A (Planares gerais de cintura $\ge 5$):** O Teorema 18 encurralou todo grafo planar de cintura $\ge 5$ sem $C_8$ para $n \ge 60$ e $> 88{,}9\%$ de vértices cúbicos (forçando "ilhas" de hexágonos em torno dos pentágonos isolados, como no fulereno $C_{60}$, que imediatamente gera $C_{16}$). Investigar via **método de descarga (*discharging*)** se todo planar de cintura $\ge 5$ (não necessariamente cúbico nem 3-conexo) contém $C_8$ ou $C_{16}$ (ou $C_{32}$).
   - **Frente B (Núcleo Cúbico 3-Conexo Geral):** Atacar a álgebra de **cordas sobre ciclos longos / Hamiltonianos** e **cortes de 3 arestas não triviais** em grafos cúbicos 3-conexos (em especial bipartidos, degrau seguinte ao Teorema 13).
3. **Formalização contínua em Lean 4:** Próximos alvos para eliminar `sorry`: `minimal_bridgeless` (Lema 5) e o núcleo combinatório do Teorema 17 (`hex_covering_has_cycle_4_8_16`).

---

## 7. Changelog de Sessões

* **v1.3 (22/11/2026 — Rodada 8 & Limpeza Lean `v4.36.0`):** Confirmados 9/9 blocos sem `sorry` com 0 erros; limpos os 4 avisos de linter; provados Teorema 17 (bipartidos em superfícies $\chi \ge 0$ contêm $C_4, C_8$ ou $C_{16}$, ótimo) e Teorema 18 (Desigualdade Exata do Fulereno $30\chi \le 9n_3 - 8n$, $n \ge 60$ no plano); formalizados sem `sorry` os 2 teoremas algébricos do Teorema 18 e definida `hexLattice` + enunciado do Teorema 17. Progresso: `22% / 100%`.
* **v1.2.1 (22/11/2026 — Calibração Lean `v4.36.0`):** Corrigidos todos os 15 erros de compilação para Lean `v4.36.0` + Mathlib `v4.36.0`. Progresso: `18% / 100%`.
* **v1.2 (21/11/2026 — Rodadas 6 e 7):** Teoremas 13, 14, 15 e Proposição 16. Progresso: `18% / 100%`.
* **v1.1 (21/11/2026 — Sincronização):** Comando automático no topo, Regra do Par Sincronizado e extração de `Erdos64_lean.md`. Progresso: `11% / 100%`.
* **v1.0 (21/11/2026 — Rodadas 1 a 5):** Lemas 1–6, Bloco Pinçado, Teoremas 7–12. Progresso: `11% / 100%`.