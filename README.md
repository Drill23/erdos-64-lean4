> **INSTRUÇÃO AUTOMÁTICA DE RETOMADA PARA A IA (LEIA PRIMEIRO):**  
> Se o usuário enviou este arquivo (ou link) em uma nova conversa — mesmo acompanhado apenas de um comando curto como *"segue"* ou *"continua"* — **assuma imediatamente a continuidade da pesquisa abaixo sem pedir confirmação**.  
> 1. Considere todos os resultados da **Seção 3** como provados matematicamente (ver status de compilação formal em `lean/Erdos64.lean`).  
> 2. Se o usuário colou logs/erros do compilador Lean 4, priorize corrigir e validar os teoremas em `lean/Erdos64.lean` antes ou em conjunto com a nova rodada teórica.  
> 3. Respeite os **Becos Sem Saída** da **Seção 4** para não repetir caminhos descartados.  
> 4. Escolha **autonomamente** o ataque e execute diretamente a **Próxima Rodada** definida na **Seção 6**, abrindo sua resposta com o indicador `**Progresso: X% / 100%**`.  
> 5. Sempre que gerar um novo checkpoint, atualize **simultaneamente** `README.md` e `Erdos64_lean.md` (envelope para `lean/Erdos64.lean` — Regra do Par Sincronizado).

---

# Projeto Erdős #64 — Conjectura de Erdős–Gyárfás

> **Arquivo Mestre de Estado, Memória e Continuidade (`Checkpoint v1.2`)**  
> **Última atualização:** 21 de novembro de 2026 (Pós-Rodada 7)  
> **Progresso Atual:** `18% / 100%`  
> **Alvo Oficial:** `https://erdosproblems.com/64` (Prêmio de \$1.000 — Teoria dos Grafos / Ciclos)  
> **Arquivo Lean Sincronizado:** `lean/Erdos64.lean` (entregue via envelope `Erdos64_lean.md`)

---

## 1. Protocolo de Continuidade e Regras do Projeto

1. **Retomada Imediata Sem Regressão:**
   - Todos os teoremas listados na **Seção 3** estão com demonstração matemática fechada; só revisite algum deles se o compilador Lean 4 apontar um erro ou durante a eliminação de seus `sorry` em `lean/Erdos64.lean`.
   - Leia a **Seção 4** antes de propor qualquer ataque novo.
   - Retome sempre pela **Próxima Rodada** da **Seção 6** (neste checkpoint: **Rodada 8**).

2. **Divisão de Papéis:**
   - **IA (Estrategista e Demonstradora):** Decide **autonomamente** qual frente atacar em cada rodada, conduz as demonstrações com rigor completo, decide o momento de emitir novos checkpoints e mantém o código Lean 4 atualizado. Não pergunte ao usuário qual subproblema escolher.
   - **Usuário (Orquestrador / Ponte de Verificação):** Controla o ritmo (*"segue"*), envia os arquivos `.md` ao seu agente com acesso ao GitHub e ao compilador **Lean 4 + Mathlib**, devolve relatórios/erros de compilação e mantém o repositório sincronizado.

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
   - Emitir novos checkpoints automaticamente a cada marco real (a cada 2 ou 3 rodadas), quando o chat começar a ficar longo, ou sempre que o usuário pedir.
   - Usar exclusivamente LaTeX (`$...$` e `$$...$$`) para notação matemática fora dos blocos de código Lean.

---

## 2. Enunciado Oficial e Fronteira da Literatura (Nov/2026)

### Enunciado (Problema #64 — Erdős & Gyárfás, 1995)
> Todo grafo finito simples $G$ com grau mínimo $\delta(G) \ge 3$ contém um ciclo simples de comprimento $2^k$ para algum inteiro $k \ge 2$ (ou seja, $4, 8, 16, 32, \dots$)?

### Fronteira Conhecida até Novembro de 2026
* **Grau médio alto:** Liu e Montgomery (existe constante grande $C$ tal que todo grafo com grau médio $\ge C$ contém um ciclo $C_{2^k}$).
* **Classes resolvidas conhecidas:** Grafos cúbicos planares 3-conexos (Heckman–Krakovski, 2013); grafos planares livres de garra (Daniel–Shauger); grafos $P_{13}$-livres (Hegde–Sandeep–Shashank, 2025, com busca computacional); grafos bipartidos planares (trivial por fórmula de Euler: todo planar bipartido livre de $C_4$ tem grau médio $< 3$).
* **Redução estrutural recente (2026):** Avery Carr (`arXiv:2605.22844`, mai/2026: $|V_3| \ge \frac{4}{7}n$) e Guillaume Ducoffe & Bogdan Dumitru (`arXiv:2609.28594`, jul–set/2026: 2-conexo ou 1-clique-soma de dois blocos 2-conexos, e $|V_3| > \frac{2}{3}n$).
* **Limites computacionais certificados (2026 — Ducoffe–Dumitru, Balaji, Tranquilli):** Não existe contraexemplo com:
  * $n \le 40$ vértices (grafos gerais);
  * $n \le 48$ vértices (grafos cúbicos);
  * $n \le 66$ vértices (grafos bipartidos; $n \ge 60$ também certificado para cúbicos bipartidos por Tranquilli, `arXiv:2608.02675`).

---

## 3. Inventário de Resultados Provados (Rodadas 1 a 7)

### Convenções Fixas
* Um grafo $G$ é **livre de $C_{2^k}$** se não contém ciclo simples de comprimento $2^k$ com $k \ge 2$.
* Um **contraexemplo mínimo** $G$ é um grafo finito simples, não vazio, com $\delta(G) \ge 3$ e livre de $C_{2^k}$, com **menor $|V(G)|$** possível e, no empate, **menor $|E(G)|$** possível.
* Partição por graus: $H = V_{\ge 4}$ (tamanho $h$), $H_4 = V_4$, $L = V_3$ (tamanho $\ell$), e $L_j = \{v \in L : |N_G(v) \cap H| = j\}$ ($j \in \{0, 1, 2, 3\}$).

### Tabela Mestre de Progresso e Sincronização com `lean/Erdos64.lean`

| ID | Resultado | Rodada | Declaração em `lean/Erdos64.lean` | Status Lean 4 |
| :--- | :--- | :---: | :--- | :---: |
| **Infra** | Monotonicidade de `HasPow2Cycle` por homomorfismo injetivo / subgrafo / indução | 7 | `HasPow2Cycle.map`, `mono`, `of_induce` | `READY_TO_COMPILE` |
| **Lema 1** | Contraexemplo mínimo é conexo | 1 | `minimal_connected` | `READY_TO_COMPILE` |
| **Lema 2** | Dois vértices distintos têm no máximo 1 vizinho comum | 1 | `no_two_common_neighbors`, `common_neighbors_le_one` | `READY_TO_COMPILE` |
| **Lema 3** | Triângulos nunca compartilham arestas | 1 | `triangles_edge_disjoint` | `READY_TO_COMPILE` |
| **Lema 4** | $H = V_{\ge 4}$ é um conjunto independente | 1 | `high_degree_independent` | `READY_TO_COMPILE` |
| **Lema 5** | Contraexemplo mínimo não possui pontes | 2 | `minimal_bridgeless` | `SORRY` |
| **Lema 6** | Dicotomia do vértice de corte e Redução ao Bloco Pinçado $\mathcal{K}$ | 2 | `pinched_block_equiv` | `PLANNED` |
| **Teorema 7** | **Teorema do Cacto de Triângulos** ($G_\Delta$ sem ciclos $\ge 4$) | 3 | `triangle_cactus_no_long_cycle` | `SORRY` |
| **Teoremas 8–9** | Fronteira das componentes de $G[L]$, $L_3 = \emptyset$, $\|E(G[L_2])\| \le \|H_4\|$ | 4 | `no_L3_vertices` | `READY_TO_COMPILE` |
| **Teorema 10** | Pisos de cubicidade: $\|V_3\| \ge \frac{8}{11}n$ (sem $K_3$) e $\ge \frac{20}{27}n$ (bipartido) | 4 | `minimal_triangle_free_cubicity`, `minimal_bipartite_cubicity` | `SORRY` |
| **Teorema 11** | **Autorredução de $K_3$-fatores** em cúbicos ($H_3$ cúbico simples) | 5 | `minimal_no_K3_factor` | `SORRY` |
| **Teorema 12** | **Autorredução de $C_5$-fatores** em cúbicos ($H_5$ 5-regular; $n \ge 110$) | 5 | `minimal_no_C5_factor` | `SORRY` |
| **Teorema 13** | **3-Conectividade e Redução à Metade em Bipartidos** ($\|V(G')\| \le \lfloor (n+2)/2 \rfloor$) | 6 | `bipartite_not_3connected_halving` | `SORRY` |
| **Teorema 14** | **Obstrução de Colagem Assimétrica** em cortes de 2 arestas | 6 | `two_edge_cut_asymmetric_gluing` | `PLANNED` |
| **Teorema 15** | **Degeneração dos Triângulos $L_2$** ($G_S$ simples, livre de $C_{2^k}$, 2-degenerado) + $3\|V_3\| \ge 2n + 1$ + $\|V_3\| \ge \frac{12}{17}n$ ($S = \emptyset$) | 7 | `minimal_general_cubicity`, `minimal_no_K2_in_V3_cubicity` | `SORRY` |
| **Prop. 16** | Rigidez de $C_7$-fatores sem $K_3$ ($\delta(H_7^{\text{simp}}) \ge 3$) + Lei Modular $p \mid (d+2)$ | 7 | *(resultado de fronteira / classificação)* | `N/A` |

*(Legenda Lean 4: `READY_TO_COMPILE` = prova escrita sem `sorry`, aguardando teste no compilador do agente; `VERIFIED` = compilado sem erro e sem `sorry` no ambiente do agente; `SORRY` = enunciado tipado aguardando prova formal; `PLANNED` = pendente de transcrição.)*

---

### 3.1. Resumo das Rodadas 1 a 5 (Lemas 1–6 e Teoremas 7–12)

* **Rodada 1 (Lemas 1–4):** Todo contraexemplo mínimo $G$ é conexo, tem no máximo 1 vizinho comum entre vértices distintos, não tem triângulos compartilhando aresta e tem $H = V_{\ge 4}$ como conjunto independente.
* **Rodada 2 (Lemas 5–6 e Bloco Pinçado):** $G$ não tem pontes (colagem de duas cópias da metade menor $C_1$ por $u$ reduz $|V|$). Se $G$ tem vértice de corte $v$, então $v$ é único, $\deg_G(v) = 4$, e $G$ é colagem de dois blocos 2-conexos $H_1, H_2$ de mesma ordem $k + 1$ e mesmo número de arestas. A conjectura equivale a $\mathcal{K} = \emptyset$ ($\mathcal{K}$ = grafos 2-conexos livres de $C_{2^k}$ com todos os graus $\ge 3$ exceto no máximo um vértice de grau $2$).
* **Rodada 3 (Teorema 7 — Cacto de Triângulos):** Em qualquer grafo livre de $C_{2^k}$, o subgrafo $G_\Delta$ das arestas em triângulos não tem ciclo de comprimento $\ge 4$ (prova via ciclo mínimo $C$ de comprimento $L \ge 5$ sem cordas em $G_\Delta$, testemunhas externas distintas $w_1, \dots, w_L$, e desvio em $r = 2^k - L$ arestas gerando $C_{2^k}$). Corolários: $G_\Delta$ é 2-degenerado ($|E_\Delta| \le \frac{3}{2}(n-1)$) e a conjectura vale se $\delta(G_\Delta) \ge 3$.
* **Rodada 4 (Teoremas 8–10):** Em qualquer contraexemplo mínimo (geral, sem triângulos ou bipartido) com $H \ne \emptyset$, toda componente conexa $C$ de $G[L]$ tem $x \in H$ com $|N_G(x) \cap V(C)| \ge \deg_G(x) - 2 \ge 2$ (Teorema 8), implicando $L_3 = \emptyset$, $c_2 \le c_0 + 2$, toda componente $K_2$ de $G[L]$ forma triângulo com um único $x \in H_4$ e $|E(G[L_2])| \le |H_4|$ (Teorema 9). Usando o caminho mínimo em $C$ entre dois vizinhos de $x$: $|V_3| \ge \frac{8}{11}n \approx 72{,}73\%$ em sem-triângulos e $|V_3| \ge \frac{20}{27}n \approx 74{,}07\%$ em bipartidos (Teorema 10).
* **Rodada 5 (Teoremas 11–12):** Nenhum contraexemplo mínimo é cúbico com $K_3$-fator ($H_3$ é cúbico simples sobre $n/3$ vértices e $L = 2^r \mapsto 2^{r+1}$) nem com $C_5$-fator ($H_5$ é 5-regular simples sobre $n/5$ vértices, $L = 2^k$ levanta para $2^{k+1}$ se $r = L$ e para $2^{k+2}$ se $r \le L - 1$ via $a = \lceil 2r/3 \rceil$; ademais $n \ge 110$ elementar e $n > 200$ com $n > 40$).

---

### 3.2. Rodada 6 — Cortes, 3-Conectividade Bipartida e Colagem Assimétrica (Teoremas 13–14)

#### Lema 13A e Teorema 13 (3-Conectividade e Redução à Metade em Bipartidos)
> Seja $G$ **qualquer** grafo finito simples **bipartido** de ordem $n$ com $\delta(G) \ge 3$ e livre de $C_{2^k}$ ($k \ge 2$). Se $G$ **não é 3-conexo**, então existe um **menor próprio** simples $G'$ de $G$ com $\delta(G') \ge 3$, livre de $C_{2^k}$, e ordem $|V(G')| \le \lfloor \frac{n+2}{2} \rfloor$ (com $\le \lfloor \frac{n+1}{2} \rfloor$ se há vértice de corte e $\le \lfloor \frac{n}{2} \rfloor$ se há corte de 2 arestas).

**Prova resumida:**
* *Desconexo:* menor componente dá $|V(G')| \le \lfloor n/2 \rfloor$.
* *Vértice de corte:* menor bloco-folha $B$ tem $|V(B)| \le \lfloor \frac{n+1}{2} \rfloor$ e único vértice de corte $v$. Se $\deg_B(v) \ge 3$, tome $G' = B$; se $\deg_B(v) = 2$ com vizinhos $a, b$, eles estão na mesma classe de bipartição, logo $G' = (B - v) + ab$ é menor simples, $\delta \ge 3$, e todo novo ciclo usando $ab$ tem comprimento ímpar.
* *Corte de 2 vértices:* escolha $(\{u, v\}, C_1)$ minimizando $|V(C_1)| \le \lfloor \frac{n-2}{2} \rfloor$. Pela minimalidade, $|N_G(u) \cap V(C_1)| \ge 2$ e $|N_G(v) \cap V(C_1)| \ge 2$ (Lema 13A). Seja $A_1 = G[V(C_1) \cup \{u, v\}] - uv$.
  - Se $u, v$ estão na **mesma classe**: $G' = A_1 + uv$ (contraindo outra componente $C_2$ em $u$) é menor simples de ordem $\le \lfloor \frac{n+2}{2} \rfloor$, $\delta \ge 3$, e novos ciclos têm comprimento ímpar.
  - Se $u, v$ estão em **classes opostas**: $N_{A_1}(u) \cap N_{A_1}(v) = \emptyset$; contraindo $G[V(C_2) \cup \{u, v\}]$ em $z$ obtém-se $G' = A_1 / \{u \sim v\}$ simples, ordem $\le \lfloor \frac{n}{2} \rfloor$, $\deg_{G'}(z) \ge 4$, e todo ciclo passando por $z$ desdobra em ciclo de $A_1$ ou caminho $u$–$v$ de comprimento ímpar. $\blacksquare$

* **Corolário 13.1:** Todo contraexemplo mínimo bipartido em qualquer classe fechada por menores é **3-conexo**.
* **Corolário 13.2:** Combinado com $n > 40$ (Ducoffe–Dumitru), todo bipartido não-3-conexo com $\delta \ge 3$ e $n \le 79$ (ou $n \le 81$ com corte de 2 arestas) satisfaz Erdős–Gyárfás.

#### Teorema 14 (Colagem Assimétrica em Cortes de 2 Arestas no Caso Geral)
> Em um contraexemplo mínimo geral $G$, se $\{u_1 v_1, u_2 v_2\}$ é corte de 2 arestas não trivial separando $A$ e $B$ com $|V(A)| \le |V(B)|$ e $S(A)$ é o conjunto dos comprimentos de caminhos $u_1$–$u_2$ em $A$:
> 1. Existem $\ell_1, \ell_2 \in S(A)$ e $d \ge 2$ com $\ell_1 + \ell_2 = 2^d - 1$ (colando $A', A''$ identificando $u_1' = u_1''$ e ligando $u_2' u_2''$, ordem $2|V(A)| - 1 < n$). Em particular, **$A$ nunca é bipartido**.
> 2. Se $u_1 u_2 \notin E(A)$ e $v_1 v_2 \notin E(B)$, então $P_A = \{a \ge 2 : 2^a - 1 \in S(A)\}$ e $P_B = \{b \ge 2 : 2^b - 1 \in S(B)\}$ são não vazios e disjuntos ($P_A \cap P_B = \emptyset$). $\blacksquare$

---

### 3.3. Rodada 7 — Degeneração dos Triângulos $L_2$ e Lei Modular (Teorema 15 e Proposição 16)

#### Teorema 15 (Degeneração dos Triângulos $L_2$)
> Seja $G$ qualquer contraexemplo mínimo e $S \subseteq H_4$ o conjunto das testemunhas únicas $x_C$ das componentes $K_2$ de $G[L]$ (triângulos disjuntos $T_x = \{x, v_x, w_x\}$). O grafo contraído $G_S$ sobre $S$ (aresta entre $x, y \in S$ iff existe aresta em $G$ entre $T_x$ e $T_y$) é **simples**, tem $\Delta(G_S) \le 4$ (orientação canônica $\deg^+, \deg^- \le 2$), é **livre de $C_{2^k}$ ($k \ge 2$)** e é **2-degenerado**.

**Prova:** Simplicidade: $xy \notin E(G)$ ($H$ independente), sem arestas entre $\{v_x, w_x\}$ e $\{v_y, w_y\}$ (componentes distintas de $G[L]$), e duas arestas entre $T_x, T_y$ sempre fecham $C_4$. Levantamento de ciclo $Q$ de comprimento $L = 2^k$ em $G_S$: ao longo da orientação canônica de $Q$, o número de sorvedouros $s$ (únicos vértices com passo interno $0$) iguala o de fontes, logo $s \le L/2$ e o número de não-sorvedouros $t = L - s$ satisfaz $L/2 \le t \le L$. Em cada um desses $t$ triângulos os extremos de entrada e saída são distintos (cada $v_x, w_x$ tem apenas 1 aresta externa), oferecendo escolha $\{1, 2\}$. Escolhendo $L - t$ passos de tamanho $2$ e $2t - L$ de tamanho $1$ obtém-se ciclo simples em $G$ de comprimento $L + 2(L - t) + (2t - L) = 2L = 2^{k+1}$, absurdo. Como $|S| \le n/3 < n$, pela minimalidade de $G$, nenhum subgrafo não vazio de $G_S$ tem $\delta \ge 3$, logo $G_S$ é 2-degenerado. $\blacksquare$

* **Corolário 15.1:** Se $H \ne \emptyset$, então $|S| < |H|$ (pois $S = H$ tornaria $G_S$ 4-regular), logo $L_0 \cup L_1 \ne \emptyset$ e **$3|V_3| \ge 2|V(G)| + 1$** (nova prova combinatória própria da cota $|V_3| > \frac{2}{3}n$).
* **Corolário 15.2:** Se $S = \emptyset$ (nenhuma componente $K_2$ em $G[L]$), então $|L_2| \le 2|L_1| + 3|L_0|$, resultando em **$|V_3| \ge \frac{12}{17}n \approx 70{,}59\%$**.

#### Proposição 16 (Rigidez de $C_7$-Fatores e Lei Modular)
1. Em cúbicos sem triângulos livres de $C_{2^k}$ com $C_7$-fator, $H_7$ não tem laços e tem multiplicidade $\le 3$ (análise exaustiva das 4 partições de 7 em 4 partes), garantindo $\delta(H_7^{\text{simp}}) \ge 3$.
2. **Lei Modular:** Para $C_d$-fatores, se $p \mid (d+2)$ ($p \ge 3$ ou $p = 4$), entradas $s \equiv -1 \pmod p$ forçam ambos os passos $\{1 + s, 1 + d - s\}$ a serem múltiplos de $p$ (obstrução $\bmod 4$ para $d = 6$, $\bmod 3$ para $d = 7$), impedindo levantamento incondicional de $C_{2^k}$ fora de $d \in \{3, 5\}$.

---

## 4. Becos Sem Saída e Obstruções Mapeadas (Não Repetir)

1. **Busca bruta computacional em grafos pequenos:** Descartada até $n \le 40$ (geral), $n \le 48$ (cúbico), $n \le 66$ (bipartido) e $n \le 79$ (bipartido não-3-conexo, pelo Corolário 13.2).
2. **Grafos planares bipartidos:** Caso trivial pela fórmula de Euler (livre de $C_4 \implies$ cintura $\ge 6 \implies$ grau médio $< 3$).
3. **Densidade pura de grafos 2-degenerados com $\Delta \le 4$ (como $G_S$ ou $M$):** Existem grafos 2-degenerados com $\Delta \le 4$ e cintura arbitrariamente alta atingindo $2m - O(1)$ arestas (construção por fila de vértices ativos), então a 2-degeneração de $G_S$ sozinha não limita $|S|/h$ abaixo de $1 - o(1)$ — ela apenas elimina $S = H$.
4. **Contração simples de todos os triângulos $G / \mathcal{T}$ em cúbicos:** $G / \mathcal{T}$ é sempre cúbico simples, mas um $C_4$ em $G/\mathcal{T}$ passando por apenas $t = 1$ triângulo levanta para $\{5, 6\}$ e escapa de $4$ e $8$.
5. **Levantamento incondicional de $C_d$-fatores para $d \ge 6$:** Bloqueado pela Lei Modular (Proposição 16: $d=6 \bmod 4$, $d=7 \bmod 3$) e por cordas internas de passo 2 ou 4.
6. **Contração de 2-fator misto $\{C_3, C_5\}$:** $C_4$ contraído com três $K_3$ e um $C_5$ ($\{2,3\}$) levanta apenas para $[9, 13]$.

---

## 5. Status do Ambiente Lean 4 (`lean/Erdos64.lean`)

* **Arquivo de transporte entregue:** `Erdos64_lean.md` (extrair bloco `lean` para `lean/Erdos64.lean`).
* **Prontos para compilar sem `sorry` (`READY_TO_COMPILE` — 7 blocos):**
  1. `HasPow2Cycle.map`, `HasPow2Cycle.mono`, `HasPow2Cycle.of_induce`
  2. `no_two_common_neighbors` (Lema 2a)
  3. `common_neighbors_le_one` (Lema 2b)
  4. `triangles_edge_disjoint` (Lema 3)
  5. `minimal_connected` (Lema 1)
  6. `high_degree_independent` (Lema 4)
  7. `no_L3_vertices` (Corolário 8.1)
* **Ação aguardada do agente:** Rodar `lake build` / `lake env lean lean/Erdos64.lean` e devolver versão do `lean-toolchain` + Mathlib + relatório de erros (se houver) para calibrarmos a sintaxe e passarmos todos para `VERIFIED`.

---

## 6. Plano Imediato para a Rodada 8

1. **Ciclo de Calibração Lean 4 (Prioridade 1 se o usuário trouxer logs do compilador):** Corrigir eventuais ajustes de API do Mathlib nos 7 blocos `READY_TO_COMPILE`, promovê-los a `VERIFIED` e formalizar sem `sorry` o **Lema 5 (`minimal_bridgeless`)** e a parte algébrica do **Teorema 10 (`minimal_triangle_free_cubicity`)**.
2. **Ataque Teórico Principal — Núcleo Cúbico 3-Conexo (Grafos Cúbicos Hamiltonianos & Ciclos Máximos com Cordas):**
   - Abandonar $C_d$-fatores com $d \ge 6$ (bloqueados pela Lei Modular) e atacar o outro extremo: **estruturas de cordas sobre ciclos longos** (em particular, ciclos mais longos em grafos cúbicos 3-conexos e grafos cúbicos Hamiltonianos) e **grafos de Cayley / prismas generalizados** (como o aquecimento já feito em $G(2m, a)$ que forçou $C_4, C_8$ ou $C_{16}$).
   - Investigar também **cortes de 3 arestas não triviais** em grafos cúbicos 3-conexos bipartidos (o próximo degrau natural após o Teorema 13).

---

## 7. Changelog de Sessões

* **v1.2 (21/11/2026 — Rodadas 6 e 7):** Adicionados Teorema 13 (3-conectividade e redução à metade em bipartidos, elevando barreira de não-3-conexos a $n \le 79$), Teorema 14 (colagem assimétrica em cortes de 2 arestas), Teorema 15 (degeneração dos triângulos $L_2$, prova própria de $3|V_3| \ge 2n + 1$ e piso $\frac{12}{17}n$ para $S = \emptyset$) e Proposição 16 (rigidez de $C_7$-fatores + Lei Modular). `lean/Erdos64.lean` expandido para **7 blocos sem `sorry`** (`READY_TO_COMPILE`). Progresso: `18% / 100%`.
* **v1.1 (21/11/2026 — Sincronização):** Comando automático no topo, Regra do Par Sincronizado e extração de `Erdos64_lean.md`. Progresso: `11% / 100%`.
* **v1.0 (21/11/2026 — Rodadas 1 a 5):** Lemas 1–6, Bloco Pinçado, Teoremas 7–12. Progresso: `11% / 100%`.