> **INSTRUÇÃO AUTOMÁTICA DE RETOMADA PARA A IA (LEIA PRIMEIRO):**
> Se o usuário enviou este arquivo (ou link) em uma nova conversa — mesmo acompanhado apenas de um comando curto como
*"segue"* ou *"continua"* — **assuma imediatamente a continuidade da pesquisa abaixo sem pedir confirmação**.
> 1. Considere todos os resultados da **Seção 3** como provados matematicamente (ver status real de compilação formal
na tabela da Seção 3 e na Seção 5).
> 2. Se o usuário colou logs/erros do compilador Lean 4, priorize corrigir e validar os teoremas em
`lean/Erdos64.lean` antes ou em conjunto com a nova rodada teórica.
> 3. **Ambiente Lean confirmado:** escreva **sempre** para **Lean 4 `v4.36.0` + Mathlib `v4.36.0`** respeitando
rigorosamente as regras de compatibilidade da **Seção 5** (nunca chute nomes de lemas; prefira `simp`, `simpa`,
`omega`, `aesop` ou `grind`).
> 4. Respeite os **Becos Sem Saída** da **Seção 4** para não repetir caminhos descartados.
> 5. Escolha **autonomamente** o ataque e execute diretamente a **Próxima Rodada** definida na **Seção 6** (neste checkpoint: **Rodada 12**), abrindo sua resposta com o indicador `**Progresso: X% / 100%**`.
> 6. Sempre que gerar um novo checkpoint, atualize **simultaneamente** `README.md` e `Erdos64_lean.md` (envelope para
`lean/Erdos64.lean` — Regra do Par Sincronizado).

---

# Projeto Erdős #64 — Conjectura de Erdős–Gyárfás

> **Arquivo Mestre de Estado, Memória e Continuidade (`Checkpoint v1.6`)**  
> **Última atualização:** 22 de novembro de 2026 (Pós-Rodada 11 — Cacto de Triângulos e colagem com uma ou duas junções)  
> **Progresso Atual:** `25% / 100%`  
> **Alvo Oficial:** [Problema #64 de Erdős](https://erdosproblems.com/64) (Prêmio de \$1.000 — Teoria dos Grafos / Ciclos)  
> **Arquivo Lean Sincronizado:** `lean/Erdos64.lean` (também no envelope `Erdos64_lean.md`)  
> **Contagem Formal (`lean/Erdos64.lean`):** **21 teoremas públicos `VERIFIED`** | **7 declarações com `sorry`** | **0 erros e 0 avisos de linter** em Lean `v4.36.0` + Mathlib `v4.36.0`.

---

## 1. Protocolo de Continuidade e Regras do Projeto

1. **Retomada Imediata Sem Regressão:**
   - Todos os teoremas listados na **Seção 3** estão com demonstração matemática fechada; só revisite algum deles se o
compilador Lean 4 apontar um erro ou durante a eliminação de seus `sorry` em `lean/Erdos64.lean`.
   - Leia a **Seção 4** (Becos Sem Saída) e a **Seção 5** (Regras Lean `v4.36.0`) antes de propor qualquer ataque ou
código novo.
   - Retome sempre pela **Próxima Rodada** da **Seção 6** (neste checkpoint: **Rodada 12**).

2. **Divisão de Papéis:**
   - **IA (Estrategista e Demonstradora):** Decide **autonomamente** qual frente atacar em cada rodada, conduz as
demonstrações com rigor completo, decide o momento de emitir novos checkpoints e mantém o código Lean 4 atualizado.
Não pergunte ao usuário qual subproblema escolher.
   - **Usuário (Orquestrador / Ponte de Verificação):** Controla o ritmo (*"segue"*), envia os arquivos `.md` ao seu
agente com acesso ao GitHub e ao compilador **Lean 4 `v4.36.0` + Mathlib `v4.36.0`**, devolve relatórios/erros de
compilação e mantém o repositório sincronizado.

3. **Regra do Termômetro de Progresso (`0%` a `100%`):**
   - Toda rodada de pesquisa **deve começar** com `**Progresso: X% / 100%**` seguido de justificativa breve e honesta.
   - Escala:
     - `0%`: Mapeamento inicial, sem resultado estrutural próprio.
     - `1%` a `25%`: Reduções estruturais, eliminação de classes específicas e resultados parciais sólidos.
     - `26%` a `60%`: Quebra de barreiras centrais no núcleo cúbico 3-conexo ou ferramenta geral aplicável a
estruturas globais de ciclos.
     - `61%` a `95%`: Arquitetura de prova global fechada com poucos lemas técnicos pendentes (ou candidato real a
contraexemplo superando filtros profundos).
     - `100%`: Prova completa fechada (ou contraexemplo explícito verificado), faltando apenas a verificação final sem
`sorry` no Lean 4.

4. **Regra do Par Sincronizado (`README.md` + `Erdos64_lean.md` $\to$ `lean/Erdos64.lean`):**
   - **Sempre** que a IA gerar uma atualização de `README.md`, **deve gerar na mesma resposta** o arquivo
`Erdos64_lean.md` contendo o código completo de `lean/Erdos64.lean` em bloco `lean` para extração automática pelo
agente.
   - Substituir sempre os mesmos arquivos no GitHub (`README.md` e `lean/Erdos64.lean`), sem criar arquivos `v2`,
`v3`.
   - Nunca substituir uma prova com erro por `sorry` para esconder erro de compilação; preservar sempre os teoremas já
`VERIFIED`.
   - Usar exclusivamente LaTeX (`$...$` e `$$...$$`) para notação matemática fora dos blocos de código Lean.

---

## 2. Enunciado Oficial e Fronteira da Literatura (Nov/2026)

### Enunciado (Problema #64 — Erdős & Gyárfás, 1995)
> Todo grafo finito simples $G$ com grau mínimo $\delta(G) \ge 3$ contém um ciclo simples de comprimento $2^k$ para
algum inteiro $k \ge 2$ (ou seja, $4, 8, 16, 32, \dots$)?

### Fronteira Conhecida até Novembro de 2026
* **Grau médio alto:** Liu e Montgomery (existe constante grande $C$ tal que todo grafo com grau médio $\ge C$ contém
um ciclo $C_{2^k}$).
* **Classes resolvidas conhecidas:** Grafos cúbicos planares 3-conexos (Heckman–Krakovski, 2013); grafos planares
livres de garra (Daniel–Shauger); grafos $P_{13}$-livres (Hegde–Sandeep–Shashank, 2025, com busca computacional);
grafos bipartidos planares (fórmula de Euler).
* **Redução estrutural recente (2026):** Avery Carr (`arXiv:2605.22844`, mai/2026: $|V_3| \ge \frac{4}{7}n$) e
Guillaume Ducoffe & Bogdan Dumitru (`arXiv:2609.28594`, jul–set/2026: 2-conexo ou 1-clique-soma de dois blocos
2-conexos, e $|V_3| > \frac{2}{3}n$).
* **Limites computacionais certificados (2026 — Ducoffe–Dumitru, Balaji, Tranquilli):** Não existe contraexemplo com:
  * $n \le 40$ vértices (grafos gerais);
  * $n \le 48$ vértices (grafos cúbicos);
  * $n \le 66$ vértices (grafos bipartidos; $n \ge 60$ também certificado para cúbicos bipartidos por Tranquilli,
`arXiv:2608.02675`).

---

## 3. Inventário de Resultados Provados (Rodadas 1 a 11)

### Convenções Fixas
* Um grafo $G$ é **livre de $C_{2^k}$** se não contém ciclo simples de comprimento $2^k$ com $k \ge 2$.
* Um **contraexemplo mínimo** $G$ é um grafo finito simples, não vazio, com $\delta(G) \ge 3$ e livre de $C_{2^k}$,
com **menor $|V(G)|$** possível e, no empate, **menor $|E(G)|$** possível.
* Partição por graus: $H = V_{\ge 4}$ (tamanho $h$), $H_4 = V_4$, $L = V_3$ (tamanho $\ell$), e $L_j = \{v \in L :
  \lvert N_G(v) \cap H\rvert = j\}$ ($j \in \{0, 1, 2, 3\}$).

### Tabela Mestre de Progresso e Sincronização com `lean/Erdos64.lean`

| ID | Resultado | Rodada | Declaração em `lean/Erdos64.lean` | Status Lean 4 (`v4.36.0`) |
| :--- | :--- | :---: | :--- | :--- |
| **Infra 1** | Transporte de `HasPow2Cycle` por homomorfismo injetivo | 7 | `HasPow2Cycle.map` | `VERIFIED` |
| **Infra 2** | Monotonicidade de `HasPow2Cycle` em subgrafos geradores | 7 | `HasPow2Cycle.mono` | `VERIFIED` |
| **Infra 3** | Monotonicidade de `HasPow2Cycle` em subgrafos induzidos | 7 | `HasPow2Cycle.of_induce` | `VERIFIED` |
| **Lema 1** | Contraexemplo mínimo é conexo | 1 | `minimal_connected` | `VERIFIED` |
| **Lema 2a** | Dois vértices distintos têm no máximo um vizinho comum (estrutural) | 1 | `no_two_common_neighbors` | `VERIFIED` |
| **Lema 2b** | Dois vértices distintos têm no máximo um vizinho comum (cardinalidade) | 1 | `common_neighbors_le_one` | `VERIFIED` |
| **Lema 3** | Triângulos nunca compartilham arestas | 1 | `triangles_edge_disjoint` | `VERIFIED` |
| **Lema 4** | $H=V_{\ge 4}$ é independente | 1 | `high_degree_independent` | `VERIFIED` |
| **Lema 5** | Contraexemplo mínimo não possui pontes | 2, 9 | `minimal_bridgeless` | `VERIFIED` |
| **Lema 6** | Dicotomia do vértice de corte e redução ao Bloco Pinçado $\mathcal{K}$ | 2 | `pinched_block_equiv` | `PLANNED` |
| **Teorema 7** | Cacto de Triângulos ($G_\Delta$ sem ciclos de comprimento $\ge 4$) | 3, 11 | `triangle_cactus_no_long_cycle` | `VERIFIED` |
| **Teoremas 8–9** | Fronteira das componentes de $G[L]$, $L_3=\emptyset$, $\lvert E(G[L_2])\rvert\le\lvert H_4\rvert$ | 4 | `no_L3_vertices` | `VERIFIED` para $L_3=\emptyset$ |
| **Teorema 10** | Pisos de cubicidade $\lvert V_3\rvert\ge \frac{8}{11}n$ (sem $K_3$) e $\lvert V_3\rvert\ge \frac{20}{27}n$ (bipartido) | 4 | `minimal_triangle_free_cubicity`, `minimal_bipartite_cubicity` | `SORRY` |
| **Teorema 11** | Autorredução de $K_3$-fatores em cúbicos ($H_3$ cúbico simples) | 5 | `minimal_no_K3_factor` | `SORRY` |
| **Teorema 12** | Autorredução de $C_5$-fatores em cúbicos ($H_5$ 5-regular; $n\ge 110$) | 5 | `minimal_no_C5_factor` | `SORRY` |
| **Teorema 13** | 3-conectividade e redução à metade em bipartidos ($\lvert V(G')\rvert\le \lfloor(n+2)/2\rfloor$) | 6 | `bipartite_not_3connected_halving` | `SORRY` |
| **Teorema 14** | Obstrução de colagem assimétrica em cortes de duas arestas | 6 | `two_edge_cut_asymmetric_gluing` | `PLANNED` |
| **Teorema 15** | Degeneração dos Triângulos $L_2$ ($G_S$ simples, livre de $C_{2^k}$, 2-degenerado), $3\lvert V_3\rvert\ge 2n+1$ e $\lvert V_3\rvert\ge \frac{12}{17}n$ se $S=\emptyset$ | 7 | `minimal_general_cubicity`, `minimal_no_K2_in_V3_cubicity` | `SORRY` |
| **Prop. 16** | Rigidez de $C_7$-fatores sem $K_3$ ($\delta(H_7^{\text{simp}})\ge 3$) e Lei Modular $p\mid(d+2)$ | 7 | Classificação de fronteira | `N/A` |
| **Teorema 17** | Bipartidos de grau mínimo $\ge 3$ em superfícies com $\chi\ge 0$ contêm $C_4$, $C_8$ ou $C_{16}$ (conjunto ótimo) | 8, 10 | `hex_covering_has_cycle_4_8_16`, `hex_local_injective_has_cycle_4_8_16`, `hex_has_cycle16_of_no_close_collision` | `VERIFIED` para o núcleo combinatório |
| **Teorema 18** | Desigualdade exata do fulereno ($C_{60}$). Para cintura $\ge 5$ sem $C_8$, $30\chi\le 9n_3-8n$. No plano, $n\ge 60$ e $n_3\ge(8n+60)/9$ | 8 | `fullerene_euler_inequality`, `planar_girth5_no_C8_card_ge_60` | `VERIFIED` para o núcleo algébrico |
| **Teorema 19** | Em um lado bipartido de ordem no máximo igual à do outro lado de um corte cúbico de três arestas, quaisquer dois pares de terminais admitem caminhos cujos comprimentos satisfazem $p+q+2=2^m$; ao menos um evita o terceiro terminal de sua cópia | 9 | `bipartite_three_terminals_same_color`, `even_closed_walk_same_color_edges`, `two_join_edges_dyadic_residues` | `VERIFIED` para os três lemas auxiliares. Colagem completa demonstrada em texto. |
| **Teorema 20** | Fronteira de fragmento bipartido em superfície: $b\ge 3\chi+s$ | 10 | `euler_boundary_deficit_bound` | `VERIFIED` para o núcleo algébrico |
| **Teorema 21** | Colagem de um lado cúbico com uma ou duas junções, incluindo o caso não bipartido | 11 | `single_join_edge_dyadic_residues` | `VERIFIED` para o critério aritmético de uma junção |

*Status Lean.* `VERIFIED` indica uma prova compilada sem dependência de `sorry`. `READY_TO_COMPILE` indica prova escrita aguardando compilação. `SORRY` indica enunciado tipado com prova pendente. `PLANNED` indica transcrição pendente.

---

### 3.1. Resumo das Rodadas 1 a 7 (Lemas 1–6, Teoremas 7–15 e Proposição 16)

* **Rodada 1 (Lemas 1–4 — TODOS `VERIFIED`):** Todo contraexemplo mínimo $G$ é conexo, tem no máximo 1 vizinho comum
entre vértices distintos, não tem triângulos compartilhando aresta e tem $H = V_{\ge 4}$ como conjunto independente.
* **Rodada 2 (Lemas 5–6 e Bloco Pinçado):** $G$ não tem pontes. Se $G$ tem vértice de corte $v$, então $v$ é único,
$\deg_G(v) = 4$, e $G$ é colagem de dois blocos 2-conexos $H_1, H_2$ de mesma ordem $k + 1$ e mesmo número de arestas.
A conjectura equivale a $\mathcal{K} = \emptyset$ ($\mathcal{K}$ = grafos 2-conexos livres de $C_{2^k}$ com todos os
graus $\ge 3$ exceto no máximo um vértice de grau $2$).
* **Rodada 3 (Teorema 7 — Cacto de Triângulos):** Em qualquer grafo livre de $C_{2^k}$, o subgrafo $G_\Delta$ das
arestas em triângulos não tem ciclo de comprimento $\ge 4$ (todo bloco de $G_\Delta$ é um $K_3$; $G_\Delta$ é
2-degenerado com $|E_\Delta| \le \frac{3}{2}(n-1)$; conjectura vale se $\delta(G_\Delta) \ge 3$).
* **Rodada 4 (Teoremas 8–10):** Em qualquer contraexemplo mínimo (geral, sem triângulos ou bipartido) com $H \ne
\emptyset$, toda componente conexa $C$ de $G[L]$ tem $x \in H$ com $|N_G(x) \cap V(C)| \ge \deg_G(x) - 2 \ge 2$
(Teorema 8), implicando $L_3 = \emptyset$ (`VERIFIED`), $c_2 \le c_0 + 2$, toda componente $K_2$ de $G[L]$ forma
triângulo com único $x \in H_4$ e $|E(G[L_2])| \le |H_4|$ (Teorema 9). Pisos de cubicidade: $|V_3| \ge \frac{8}{11}n
\approx 72{,}73\%$ (sem $K_3$) e $|V_3| \ge \frac{20}{27}n \approx 74{,}07\%$ (bipartido) (Teorema 10).
* **Rodada 5 (Teoremas 11–12):** Nenhum contraexemplo mínimo é cúbico com $K_3$-fator ($H_3$ cúbico simples sobre
$n/3$ vértices) nem com $C_5$-fator ($H_5$ 5-regular simples sobre $n/5$ vértices; $n \ge 110$ elementar, $n > 200$
com $n > 40$).
* **Rodada 6 (Teoremas 13–14):**
   * **Teorema 13:** Todo bipartido não-3-conexo com $\delta \ge 3$ e livre de $C_{2^k}$ gera um **menor próprio**
simples $G'$ com $\delta(G') \ge 3$, livre de $C_{2^k}$ e $|V(G')| \le \lfloor (n+2)/2 \rfloor$ ($\le \lfloor (n+1)/2
\rfloor$ com vértice de corte; $\le \lfloor n/2 \rfloor$ com corte de 2 arestas). Consequências: todo contraexemplo
mínimo bipartido em classe fechada por menores é **3-conexo**; combinado com $n > 40$, todo bipartido não-3-conexo com
$n \le 79$ ($n \le 81$ com corte de 2 arestas) satisfaz a conjectura.
  * **Teorema 14:** Em corte de 2 arestas não trivial $\{u_1 v_1, u_2 v_2\}$ de um contraexemplo mínimo geral (lados
$A, B$ com $|V(A)| \le |V(B)|$), a colagem assimétrica força $\ell_1 + \ell_2 = 2^d - 1$ em $S(A)$ (logo $A$ nunca é
bipartido), e se $u_1 u_2 \notin E(A), v_1 v_2 \notin E(B)$ então $P_A, P_B$ são não vazios e disjuntos.
* **Rodada 7 (Teorema 15 e Proposição 16):**
    * **Teorema 15:** Contraindo os triângulos disjuntos $T_x = \{x, v_x, w_x\}$ ($x \in S \subseteq H_4$) das
componentes $K_2$ de $G[L]$, o grafo $G_S$ é simples, $\Delta(G_S) \le 4$ ($\deg^+, \deg^- \le 2$), livre de $C_{2^k}$
($2^k \mapsto 2^{k+1}$) e 2-degenerado. Consequências: $|S| < |H|$ se $H \ne \emptyset$, nova prova combinatória de
$3|V_3| \ge 2n + 1$, e $|V_3| \ge \frac{12}{17}n \approx 70{,}59\%$ se $S = \emptyset$.
  * **Proposição 16:** Em cúbicos sem $K_3$ com $C_7$-fator, $\delta(H_7^{\text{simp}}) \ge 3$; Lei Modular $p \mid
(d+2)$ explica obstrução de levantamento para $d = 6$ ($\bmod 4$) e $d = 7$ ($\bmod 3$).

---

### 3.2. Rodada 8 — Bipartidos em Superfícies ($\chi \ge 0$) e Desigualdade Exata do Fulereno

#### Teorema 17 (Resolução Completa de Bipartidos em Superfícies $\chi \ge 0$)
> Todo grafo finito simples **bipartido** $G$ com $\delta(G) \ge 3$ imersível em uma superfície fechada $\Sigma$ com
$\chi(\Sigma) \ge 0$ (plano/esfera, plano projetivo, toro ou garrafa de Klein) contém um ciclo simples de comprimento
**$4$, $8$ ou $16$**. O conjunto $\{4, 8, 16\}$ é ótimo no toro e na garrafa de Klein (grade hexagonal toroidal $5
\times 5$ de 50 vértices tem ciclos $\le 16$ em $\{6, 10, 12, 14, 16\}$).

* **Esquema da prova fechada:**
  1. Se $G_0$ (componente conexa) não contém $C_4$, redução a mergulho 2-celular com $\chi(\Sigma') \ge 0$ força $6F
\le 2E$ e $3V \le 2E$. Se $\chi > 0$, contradição imediata (contém $C_4$). Se $\chi = 0$, igualdade exata: $G_0$ é
cúbico com todas as faces 6-ciclos simples, induzindo recobrimento de grafos bipartido $\pi : H \to G_0$ a partir da
rede hexagonal infinita $H$ ($\mathbb{Z}^2 \times \{0, 1\}$).
   2. Seja $\rho(\pi) = \min\{d_H(x, y) : x \ne y,\, \pi(x) = \pi(y)\}$ (par, $\ge 4$ por injetividade local e
bipartição):
     * $\rho(\pi) = 4 \implies$ caminho mínimo de comprimento 4 projeta em $C_4$ simples.
     * $\rho(\pi) = 6 \implies$ **Lema do Desvio Hexagonal:** para cada posição à distância $6$, existem $\ge 4$ caminhos simples de comprimento 8 com pares de vizinhos extremos $(w_1, w_7)$
distintos; pelo Princípio da Casa dos Pombos ($4 > 3$), ao menos um evita a bijeção local $f : N_H(u)
\xrightarrow{\sim} N_H(v)$ e projeta em $C_8$ simples.
     * $\rho(\pi) \ge 8 \implies$ o trapézio de 5 hexágonos $\{(0,0),(1,0),(2,0),(0,1),(1,1)\}$ tem borda $C_{16}$ com
diâmetro de mesma cor $\le 6 < 8 \le \rho(\pi)$, logo $\pi|_{V(C_{16})}$ é injetora e projeta em $C_{16}$ simples.

#### Teorema 18 (Desigualdade Exata do Fulereno — Cintura $\ge 5$, Livre de $C_8$)
> Para todo grafo finito simples $G$ com $\delta(G) \ge 3$, cintura $\ge 5$ e livre de $C_8$, imerso 2-celularmente em
superfície fechada de característica $\chi$:
> $$30\chi \le \sum_{d \ge 3} \left(30 - 10d + \left\lfloor \frac{d}{2} \right\rfloor\right) n_d \le 9n_3 - 8n.$$
> Em particular:
> * **Plano ($\chi = 2$):** **$n \ge 60$** (exato — atingido pelo fulereno $C_{60}$, cujos ciclos $\le 16$ são $\{5,
6, 9, \dots, 16\}$) e **$n_3 \ge \frac{8n + 60}{9} > 88{,}9\%$**.
> * **Plano Projetivo ($\chi = 1$):** $n \ge 30$ e $n_3 \ge \frac{8n + 30}{9}$.
> * **Toro / Garrafa de Klein ($\chi = 0$):** $n_3 \ge \frac{8}{9}n \approx 88{,}89\%$.

* **Esquema da prova fechada:** Nenhuma aresta separa duas 5-faces (caso contrário as duas 5-faces formariam um $C_8$
simples, já que qualquer coincidência extra cria $C_3$ ou $C_4$). Logo cada vértice de grau $d$ incide em no máximo
$\lfloor d/2 \rfloor$ faces pentagonais ($5F_5 \le \sum \lfloor \deg(v)/2 \rfloor$). Combinando com $6F \le 2E + F_5$
em $30\chi = 30V - 30E + 30F$ segue a desigualdade exata (núcleo algébrico já formalizado sem `sorry` na v1.3).


### 3.3. Rodada 9 — Espectros de caminhos em um lado bipartido de um corte cúbico

#### Teorema 19 — Colagem de duas cópias com um terminal identificado

Seja $G$ um contraexemplo mínimo **entre todos os grafos**, cúbico, e seja
$V(G)=A\sqcup B$ uma partição cujo corte consiste nas três arestas $a_i b_i$,
com $a_i\in A$ e $b_i\in B$ para $i\in\{1,2,3\}$. Suponha que
as três arestas formem um emparelhamento, que $|A|\le |B|$ e que $G[A]$ seja
bipartido. Para cada par de terminais $I\subset\{1,2,3\}$ de tamanho dois,
escreva $P_I$ para o conjunto dos comprimentos de caminhos simples
entre os terminais desse par e $P_I^\circ$ para o conjunto correspondente
quando o caminho evita o terceiro terminal de $A$.

Para **quaisquer** pares $I,J$, inclusive $I=J$, existem $p\in P_I$,
$q\in P_J$ e um inteiro $m\ge 3$ tais que
$$
p+q+2=2^m,
\qquad
p\in P_I^\circ\ \text{ou}\ q\in P_J^\circ.
$$
Os resíduos de $p$ e $q$ módulo $4$ são $0$ e $2$, em alguma ordem.
Em particular, cada um dos três pares admite caminhos de **ambos** os resíduos.
Se nenhum dos pares $I,J$ admite caminho de comprimento $2$, então $m\ge 4$.

**Demonstração.**

1. **Cor dos terminais.** Os três terminais têm grau $2$ em $G[A]$ e todos
   os demais vértices têm grau $3$. Se a bipartição é $X\sqcup Y$, com
   $t_X$ e $t_Y$ terminais nas respectivas classes, contar as arestas por
   cada classe dá $3|X|-t_X=3|Y|-t_Y$. Como $t_X+t_Y=3$, a diferença
   $t_X-t_Y$ só pode ser $3$ ou $-3$. Portanto, os três terminais estão
   na mesma cor e todos os caminhos entre eles têm comprimento par.
2. **Grafo auxiliar.** Tome duas cópias de $G[A]$. Na primeira, escolha o
   par $I$. Na segunda, escolha $J$. Identifique entre si os dois
   terminais que ficaram fora dos pares, obtendo um vértice $r$. Acrescente
   duas arestas de junção que liguem os terminais de $I$ aos de $J$ por
   qualquer uma das duas bijeções. As cópias têm apenas $r$ em comum.
   O grafo resultante é simples. O vértice $r$ tem grau $4$, os outros
   quatro terminais passam a ter grau $3$, e os graus restantes continuam
   $3$. Sua ordem é $2|A|-1<|V(G)|$, inclusive com $|A|=|B|$.
   Pela minimalidade global, ele contém um ciclo simples de comprimento
   $2^m$ para algum $m\ge 2$.
3. **Uso das arestas de junção.** Alinhe as duas bipartições pela cor
   comum de $r$. Toda aresta interna a uma cópia muda de cor. Cada
   aresta de junção conserva a cor. Em um ciclo fechado o número de
   mudanças de cor é par. Logo um ciclo de comprimento par usa zero
   ou duas arestas de junção. Sem usá-las, um ciclo simples fica
   inteiramente em uma cópia, pois mudar de cópia exigiria voltar a $r$
   para fechar o ciclo. Isso contradiria a hipótese sobre $G$.
4. **Leitura do ciclo.** As duas arestas de junção trocam de cópia.
   Uma troca adicional em $r$ tornaria ímpar o número total de trocas
   ao percorrer um ciclo fechado. Como o ciclo é simples, ele pode passar
   por $r$ no máximo uma vez na ordem cíclica. Portanto, cada um dos
   dois trechos entre as arestas de junção é um caminho simples em sua
   própria cópia, e no máximo um deles contém $r$. Seus comprimentos
   $p,q$ satisfazem a igualdade e a condição de desvio.
   Como os terminais são distintos e têm a mesma cor, $p,q\ge 2$.
   Assim, $2^m\ge 6$ e $m\ge 3$. Reduzindo a igualdade módulo $4$,
   obtemos $p+q\equiv 2\pmod 4$. Se $p,q\ge 4$, então
   $2^m\ge 10$, o que dá $m\ge 4$.

**Consequências.**

- As três condições com $I=J$ testam separadamente os três pares de
  terminais. As outras três com $I\ne J$, consideradas sem ordem,
  ligam seus espectros e também exigem que pelo menos um dos caminhos
  testemunhas evite o terceiro terminal de sua cópia.
- Em um grafo cúbico 3-conexo, qualquer corte de três arestas com
  $|A|,|B|\ge 2$ é um emparelhamento. Um lado com dois vértices teria
  pelo menos quatro arestas no corte. Se duas arestas de corte
  compartilhassem um extremo de um lado com pelo menos três vértices,
  remover os no máximo dois extremos desse lado separaria os seus
  vértices restantes do lado oposto, contra a 3-conectividade.
- Se $G$ é livre de $C_4$, então $|A|\ge 13$. Com os terminais em $X$,
  a contagem do item 1 dá $|X|=|Y|+1$. Se $|X|=3$, os três
  terminais têm os mesmos dois vizinhos, formando $C_4$. Portanto,
  $X$ contém um vértice $x$ de grau $3$. Cada um de seus três vizinhos
  em $Y$ tem dois outros vizinhos em $X$ e esses três pares são
  disjuntos pela ausência de $C_4$. Logo $|X|\ge 7$ e
  $|A|=2|X|-1\ge 13$.
- Nos dois lados originais, a relação é de exclusão. Se $p$ e $q$
  são comprimentos de caminhos entre os terminais do mesmo par de
  índices, um em $A$ e o outro em $B$, então $p+q+2\ne 2^m$ para todo
  $m\ge 2$. Os dois caminhos e as duas arestas de corte formariam
  diretamente um ciclo simples caso houvesse igualdade.
- Pelo Lema 2.1 de [Ducoffe–Dumitru](https://arxiv.org/abs/2609.28594),
  cada aresta do corte pertence a um ciclo de comprimento $2^k+1$,
  com $k\ge 2$. Um triângulo cruzando o corte exigiria duas arestas
  de corte com extremo comum. Cada ciclo testemunha cruza exatamente
  duas das três arestas e se decompõe em um caminho par em $A$ e um
  caminho ímpar em $B$. Os pares com tal testemunha cobrem os três
  terminais. Em particular, **pelo menos dois pares em $B$ têm caminho
  ímpar**. A colagem do teorema fornece condições do lado $A$, enquanto
  esse argumento fornece condições do lado oposto.

**Escopo.** A construção usa minimalidade na classe geral, pois o grafo
auxiliar pode ter ciclos ímpares e tem um vértice de grau $4$. A condição
se aplica a um **lado** bipartido de um grafo que pode ter ciclos ímpares.
De fato, o mesmo Lema 2.1 implica que um contraexemplo mínimo global
jamais é bipartido. Isso deixa em aberto a existência de contraexemplos
mínimos *dentro* da classe bipartida. Para a frente planar geral, permanece como referência o caso cúbico
3-conexo de [Heckman–Krakovski](https://doi.org/10.37236/3252).

**Extensão planar com terminais na borda.** O mesmo teste se aplica à
minimalidade na classe dos grafos planares de cintura pelo menos $5$,
desde que $G$ pertença a essa classe e $G[A]$ admita um desenho em disco
com os três terminais na borda. Antes de identificar a raiz, disponha
as duas cópias em discos e desenhe as três junções no anel entre suas
bordas. Com três terminais, é possível alinhar qualquer bijeção por
rotação da ordem cíclica e, se necessário, reflexão de um disco.
Contraia a junção dos dois terminais que se tornam a raiz. Isso
preserva a planaridade. Um ciclo simples que usa uma junção percorre
um caminho entre terminais distintos em cada cópia e troca de cópia
também na raiz. Seu comprimento é pelo menos $2+2+1=5$.
Se usa duas junções, o mínimo é $2+2+2=6$. Ciclos sem junções ficam em
uma cópia. Assim, o grafo auxiliar também tem cintura pelo menos $5$ e
a contradição de minimalidade vale na classe indicada. O caso planar
geral permanece aberto nesta rodada.

**Formalização.** `bipartite_three_terminals_same_color` verifica o
balanço de graus. `even_closed_walk_same_color_edges` verifica a
paridade das junções, e `two_join_edges_dyadic_residues` verifica a
conclusão módulo $4$. A colagem com duas arestas de junção e o levantamento dos
caminhos são demonstrados acima em texto.

#### Lema 5 — Prova formal por identificação de uma raiz

Remova uma ponte e tome o menor dos dois lados. O subgrafo induzido
retém todos os graus, exceto o do extremo da ponte, que conserva pelo
menos dois vizinhos no lado. Duplique o lado e identifique os dois
extremos correspondentes. O vértice identificado tem grau pelo menos
quatro e todos os demais têm grau pelo menos três. Cada ciclo simples
permanece em uma das cópias, portanto não há ciclo de comprimento
diádico. A ordem do grafo é estritamente menor que a original,
contrariando a minimalidade. Lean verifica essa prova em
`minimal_bridgeless`.

#### Teorema 17 — Dois casos do raio de colisão formalizados

Para raio de colisão $4$, a projeção de um caminho mínimo fecha um
ciclo simples de comprimento $4$. Lean usa a injetividade em
distâncias menores para verificar que a cauda projetada é um caminho
simples. Na ausência de colisões a distância até $7$, o teorema
`hex_has_cycle16_of_no_close_collision` verifica a borda de $16$
vértices. Uma busca finita em $19$ vértices do trapézio certifica que
quaisquer dois vértices da borda se ligam por um passeio de comprimento
no máximo $7$. A verificação finita usa `decide`.

A declaração `hex_covering_has_cycle_4_8_16` escolhe a menor colisão
quando existe uma a distância até $7$. A bipartição do destino exclui
distâncias ímpares, e a injetividade local do recobrimento exclui
distância $2$. Na v1.4, o último ramo pendente era o raio $6$. A prova da Rodada 10 está na Seção 3.4.


### 3.4. Rodada 10 — Recobrimento hexagonal e fronteira de fragmentos bipartidos

#### Teorema 17 — Núcleo combinatório completo em Lean

Basta que o homomorfismo $\pi\colon H\to G$ da rede hexagonal tenha destino
bipartido e seja injetivo em cada vizinhança. A conclusão vale para destino
finito ou infinito. A forma mais geral está em
`hex_local_injective_has_cycle_4_8_16`. A declaração anterior
`hex_covering_has_cycle_4_8_16` conserva seu enunciado e segue da forma geral.

**Raio de colisão $6$.** Sejam $u,w$ dois vértices distintos com
$\pi(u)=\pi(w)$, a distância mínima $6$ entre vértices identificados.
A rede é bipartida por cor de coordenada. Uma translação, combinada com
$(x,y,b)\mapsto(-x,-y,1-b)$ quando necessário, leva $u$ a $(0,0,0)$.
O outro extremo tem cor $0$. Em dois passos, cada uma das coordenadas $x$,
$y$ e $x+y$ varia no máximo uma unidade em valor absoluto. Portanto
$\lvert x\rvert,\lvert y\rvert,\lvert x+y\rvert\le 3$ após seis passos.

O certificado em Lean considera essa região de $37$ pontos. Para os $19$
pontos com os três valores absolutos no máximo $2$, fornece um passeio de
comprimento no máximo $4$. A hipótese de distância $6$ exclui esses pontos.
Para cada um dos $18$ pontos restantes, o certificado fornece quatro
caminhos simples de comprimento $8$, com quatro pares distintos de
vizinhos extremos. Cada passo é um dentre os três vizinhos da rede.
O Lean verifica com `decide` o destino, o comprimento, a simplicidade e
a distinção dos pares. A verificação é local à rede fixada.

Ao menos um desses caminhos $p$ satisfaz
$\pi(p_1)\ne\pi(p_7)$. Se os quatro pares colidissem nas imagens, dois
deles teriam o mesmo primeiro vizinho, pois há apenas três possibilidades.
A injetividade local em $w$ forçaria também o mesmo último vizinho,
contradizendo a distinção dos pares.

Na projeção do caminho escolhido, uma repetição entre posições
$0\le i<j\le 7$ exige que $j-i$ seja par, pela bipartição do destino,
e que $j-i\ge 6$, pela escolha da distância mínima de colisão.
As possibilidades são $(0,6)$ e $(1,7)$. A primeira implicaria a colisão
$(6,8)$, de distância no máximo $2$, já que $\pi(p_0)=\pi(p_8)$.
A segunda foi excluída na escolha do caminho. Os oito primeiros vértices
projetados são distintos, e a posição $8$ fecha o ciclo na posição $0$.
O ramo de raio $6$ produz assim um $C_8$. Os ramos de raio $4$ e sem
colisões até distância $7$ completam a prova. A passagem de um mergulho
em superfície para o recobrimento da rede, descrita na Seção 3.2,
permanece uma etapa da demonstração em texto.

#### Teorema 20 — A fronteira de um fragmento bipartido em superfície

Seja $G$ um grafo simples finito com $\delta(G)\ge 3$. Seja $A\subseteq V(G)$
não vazio, com $H=G[A]$ conexo, bipartido, livre de $C_4$ e de grau mínimo
interno pelo menos $2$. Suponha que $H$ tenha um mergulho celular em uma
superfície fechada de característica de Euler $\chi$. Defina $b$ como a
quantidade de arestas de $G$ com exatamente um extremo em $A$, e
$s=\sum_{v\in A}(\deg_G(v)-3)$. Então
$$
b\ge 3\chi+s.
$$

**Demonstração.** Escreva $n,e,f$ para os números de vértices, arestas e
faces de $H$. Contar graus em $G$ sobre $A$ dá $2e+b=3n+s$.
Ao percorrer a fronteira de uma face, uma aresta só pode ser seguida
imediatamente da sua inversa em um vértice de grau interno $1$.
Logo essas fronteiras são passeios fechados sem retorno imediato, inclusive
na junção entre o último e o primeiro passo. Têm comprimento par pela
bipartição. Comprimento $2$ exigiria um retorno imediato. Comprimento $4$
sem retorno imediato, em um grafo simples, exigiria quatro vértices
distintos e produziria um $C_4$. Assim cada face tem comprimento pelo
menos $6$ e $6f\le 2e$, contando os dois lados de cada aresta.
Isso permite faces com vértices repetidos e arestas que aparecem mais
de uma vez na fronteira. Por Euler,
$$
3\chi=3n-3e+3f\le 3n-2e=b-s.
$$

**Aplicação a cortes de três arestas.** Se $G$ é planar e livre de $C_4$,
qualquer fragmento induzido conexo e bipartido com grau mínimo interno
pelo menos $2$ precisa de pelo menos $6+s$ arestas de fronteira. Em
particular, em um grafo cúbico planar e livre de $C_4$, um corte de
três arestas que forma um emparelhamento tem ambos os lados não
bipartidos. Cada vértice perde no máximo uma aresta no corte, de modo
que o grau interno é pelo menos $2$. Se um lado fosse bipartido, cada
componente conexa desse lado teria no máximo três arestas de fronteira. Se o fragmento admite um
mergulho celular com $\chi=1$, um corte de três arestas força $s=0$
e todas as faces têm comprimento $6$. A assinatura de comprimentos
do Teorema 19 continua aplicável em superfícies e cortes em que esta
contagem permite um lado bipartido.

**Formalização.** `euler_boundary_deficit_bound` verifica a dedução
numérica a partir das três contagens. A interpretação de faces e a
aplicação a cortes acima são demonstradas em texto.


### 3.5. Rodada 11: Cacto de Triângulos e a colagem de um lado não bipartido

#### Teorema 7: Prova pelo menor ciclo longo

Suponha que $G$ seja livre de ciclos de comprimento $2^k$, para $k\ge 2$.
Escreva $H=G_\Delta$ para o subgrafo das arestas que pertencem a triângulos.
Se $H$ contém um ciclo de comprimento pelo menos quatro, escolha um de
comprimento mínimo $n$. Como $G$ é livre de $C_4$, temos $n\ge 5$.

1. **Cordas.** Uma aresta de $H$ entre dois vértices não consecutivos do
   ciclo o divide em arcos de comprimentos $p,q\ge 2$ com $p+q=n$.
   Ao menos um arco tem comprimento pelo menos três. Juntá-lo à aresta
   forma um ciclo em $H$ de comprimento entre quatro e $n-1$.
   Assim toda aresta de $H$ entre vértices do ciclo é consecutiva nele.
2. **Vértices externos.** Se um vértice externo $z$ tem dois vizinhos
   não consecutivos no ciclo em $H$, tome o menor arco entre esses
   vizinhos. Seu comprimento $p$ satisfaz $2\le p\le\lfloor n/2\rfloor$.
   O arco, junto com as duas arestas incidentes a $z$, dá em $H$
   um ciclo de comprimento $p+2$ entre quatro e $n-1$.
   Portanto quaisquer dois vizinhos de $z$ no ciclo são consecutivos.
   Um ciclo simples de comprimento maior que três não pode conter
   as três arestas de um triângulo entre as próprias arestas. Logo
   $z$ tem no máximo dois vizinhos no ciclo em $H$.
3. **Desvios.** Para cada aresta $uv$ do ciclo, escolha o terceiro
   vértice $z$ de um triângulo que a contém. Tanto $uz$ quanto $vz$
   pertencem a $H$. Se $z$ estivesse no ciclo, o item 1 forçaria
   as três arestas do triângulo a serem consecutivas no ciclo,
   o que é impossível. Dois lados distintos não podem escolher
   o mesmo terceiro vértice, pois o item 2 então seria violado
   por pelo menos três vizinhos no ciclo.
4. **Comprimentos.** Mantenha uma aresta fixa e substitua qualquer
   quantidade entre zero e $n-1$ das outras arestas pelo caminho
   de dois passos de seu triângulo. Como os vértices inseridos são
   externos e distintos, cada resultado é um ciclo simples em $G$.
   São obtidos todos os comprimentos de $n$ até $2n-1$. A menor
   potência de dois maior ou igual a $n$ pertence ao intervalo,
   contradizendo a hipótese sobre $G$.

#### Teorema 21: Comprimentos na colagem com uma ou duas junções

Seja $G$ um contraexemplo mínimo global que é cúbico. Suponha que três
arestas que formam um emparelhamento separem os lados $A$ e $B$,
com $|A|\le |B|$. Tome duas cópias de $G[A]$. Em cada uma, escolha
um dos três terminais como raiz. Identifique as duas raízes em $r$
e conecte os dois terminais restantes de uma cópia aos da outra
por qualquer bijeção. Chame essas duas novas arestas de junções.

Para **cada** escolha de raízes e bijeção, pelo menos uma das situações
abaixo ocorre, com $k\ge 2$.

- **Uma junção.** Para uma das junções, cada cópia tem um caminho
  simples entre seu extremo da junção e sua própria raiz. Os
  comprimentos $p,q$ satisfazem $p+q+1=2^k$. Em particular, os
  comprimentos têm paridades opostas e $p+q\equiv 3\pmod 4$.
- **Duas junções.** Cada cópia tem um caminho simples entre seus
  dois terminais não identificados. Ao menos um desses caminhos
  evita sua raiz. Os comprimentos $p,q$ satisfazem $p+q+2=2^k$.

**Demonstração.** O grafo auxiliar é simples, tem grau mínimo pelo
menos três e tem $2|A|-1<|V(G)|$ vértices. Pela minimalidade global,
contém um ciclo simples de comprimento $2^k$. Um ciclo sem junções
fica dentro de uma cópia, pois as cópias têm apenas $r$ em comum.
Isso daria um ciclo proibido em $G[A]$. O ciclo procurado usa uma
ou duas junções.

Ao percorrer o ciclo, cada junção troca de cópia. A passagem por
$r$ pode trocar de cópia no máximo uma vez, pois o ciclo é simples.
Unidades de troca têm de somar um número par numa volta fechada.
Se há uma junção, o ciclo troca de cópia em $r$ também. Os dois
trechos são caminhos até as respectivas raízes. Se há duas, o ciclo
permanece na mesma cópia quando passa por $r$, caso passe. Assim cada
trecho entre junções permanece em sua cópia e ao menos um deles evita
a raiz. As somas seguem contando arestas. Reciprocamente, cada
par de caminhos descrito forma um ciclo simples no grafo auxiliar.

**Consequência para o núcleo 3-conexo.** Num grafo cúbico 3-conexo,
cada lado não trivial de um corte de três arestas em emparelhamento
é 2-conexo. De fato, para cada componente de um lado, suas arestas
ao outro lado formam um corte que precisa ter pelo menos três
arestas. Há apenas três, então o lado é conexo. Se um vértice $x$ do
lado o separasse, cada componente de $G[A]-x$ teria de conter
pelo menos dois terminais do corte. Se tivesse zero ou um, retirar
$x$ e, quando houver um terminal, o extremo correspondente no
lado oposto separaria essa componente do restante do grafo.
Duas componentes já exigiriam quatro terminais.

Em qualquer grafo 2-conexo não bipartido, todo par de vértices
distintos é ligado por caminhos simples de ambas as paridades.
Para ver isso, escolha um ciclo ímpar. Pelo teorema de Menger,
o par pode ser ligado a dois vértices distintos do ciclo por
caminhos disjuntos, que encontram o ciclo somente nos respectivos
extremos. Permitem-se caminhos triviais para vértices já no ciclo.
Os dois arcos entre esses pontos têm paridades opostas. Juntar
cada arco aos dois caminhos dá a afirmação. Portanto, num lado
não bipartido do corte, a paridade por si só deixa o caso de uma
junção aberto. A obstrução exata exige comparar os comprimentos
disponíveis e suas somas diádicas.

**Formalização.** O critério aritmético de uma junção está em
`single_join_edge_dyadic_residues`. A construção da colagem e a
classificação de seus ciclos acima são demonstradas em texto.

---

## 4. Becos Sem Saída e Obstruções Mapeadas (Não Repetir)

1. **Busca bruta computacional em grafos pequenos:** Descartada até $n \le 40$ (geral), $n \le 48$ (cúbico), $n \le
66$ (bipartido) e $n \le 79$ (bipartido não-3-conexo, pelo Corolário 13.2).
2. **Grafos planares bipartidos:** Caso trivial por Euler (já englobado pelo Teorema 17 para todo $\chi \ge 0$).
3. **Densidade pura de grafos 2-degenerados com $\Delta \le 4$ (como $G_S$ ou $M$):** Atingem $2m - O(1)$ arestas
mesmo com cintura arbitrariamente alta.
4. **Contração simples de todos os triângulos $G / \mathcal{T}$ em cúbicos:** Um $C_4$ contraído com $t = 1$ triângulo
levanta apenas para $\{5, 6\}$.
5. **Levantamento incondicional de $C_d$-fatores para $d \ge 6$:** Bloqueado pela Lei Modular (Proposição 16: $d=6
\bmod 4$, $d=7 \bmod 3$) e por cordas internas.
6. **Contração de 2-fator misto $\{C_3, C_5\}$:** $C_4$ contraído com três $K_3$ e um $C_5$ ($\{2,3\}$) levanta apenas
para $[9, 13]$.

7. **Colagem da Rodada 9 dentro da classe bipartida ou cúbica:** A construção pode gerar ciclos ímpares e tem um vértice de grau $4$. Sua aplicação exige minimalidade global, ou uma classe que contenha o grafo auxiliar.

8. **Lado bipartido planar de corte de três arestas em emparelhamento.** O Teorema 20 exige pelo menos $6$ arestas de fronteira em cada componente conexa de um lado bipartido com grau interno pelo menos $2$ e sem $C_4$.

9. **Bloquear uma junção usando somente a paridade dos caminhos.** Num lado não bipartido de um corte cúbico 3-conexo que é um emparelhamento, cada par de terminais admite ambas as paridades. Examine as somas de comprimentos do Teorema 21.

---

## 5. Ambiente Lean 4 e Regras Obrigatórias (`v4.36.0`)

* **Toolchain:** Lean 4 `v4.36.0` e Mathlib `v4.36.0`. Compilação de `lean/Erdos64.lean` com `lake env lean` executada localmente no checkout dessa versão de Mathlib.
* **v1.3:** O relatório anexado lista 0 erros e 10 avisos de `sorry`, confirmando os 11 teoremas sem `sorry` da versão. Ao recuperar o código do PDF, a indentação no cálculo de cardinalidade em `fullerene_euler_inequality` causou erros. O passo foi reescrito com `Finset.filter_insert`, preservando os enunciados do Teorema 18.
* **v1.4:** O relatório informado confirma 0 erros e 9 declarações com `sorry`. `minimal_bridgeless` está entre os 16 teoremas públicos verificados.
* **v1.5:** 19 teoremas públicos verificados e 8 declarações com `sorry`. O núcleo combinatório do recobrimento hexagonal foi fechado nessa versão.
* **v1.6 — `VERIFIED` (21 teoremas públicos):** `HasPow2Cycle.map`, `HasPow2Cycle.mono`, `HasPow2Cycle.of_induce`, `no_two_common_neighbors`, `common_neighbors_le_one`, `triangles_edge_disjoint`, `minimal_connected`, `high_degree_independent`, `minimal_bridgeless`, `triangle_cactus_no_long_cycle`, `no_L3_vertices`, `hex_has_cycle16_of_no_close_collision`, `hex_local_injective_has_cycle_4_8_16`, `hex_covering_has_cycle_4_8_16`, `fullerene_euler_inequality`, `planar_girth5_no_C8_card_ge_60`, `bipartite_three_terminals_same_color`, `even_closed_walk_same_color_edges`, `two_join_edges_dyadic_residues`, `euler_boundary_deficit_bound`, `single_join_edge_dyadic_residues`. Auditados com `#print axioms` e livres de dependência de `sorryAx`.
* **v1.6 — `SORRY` (7 declarações):** `minimal_triangle_free_cubicity`, `minimal_bipartite_cubicity`, `minimal_no_K3_factor`, `minimal_no_C5_factor`, `bipartite_not_3connected_halving`, `minimal_general_cubicity`, `minimal_no_K2_in_V3_cubicity`.

### Regras de Compatibilidade Confirmadas para Lean `v4.36.0` / Mathlib `v4.36.0`
1. **Não inventar nem chutar nomes de lemas** (em `v4.36.0`, convenções como `not_mem` viraram `notMem` camelCase;
`Sym2.map_pair_eq`, `Finset.erase_eq_of_not_mem` e `SimpleGraph.mem_neighborFinset.mp/.mpr` **não existem**). Na
dúvida, use `simp`, `simpa`, `omega`, `aesop`, `tauto` ou `grind`.
2. **`Std.Symm` e `Std.Irrefl` são estruturas:** ao construir um `SimpleGraph`, use `⟨by ...⟩`; para irreflexividade
de `G.Adj`, use `G.ne_of_adj hvv rfl`.
3. **`push_neg` foi substituído por `push Not`.**
4. **Linters ativos:** use `have` (nunca `haveI`) para proposições; evite argumentos redundantes no `simp`; use `;` em
vez de `<;>` quando houver apenas 1 submeta.
5. **Aritmética em `Fin d` genérico:** use `⟨(j.val + 1) % d, Nat.mod_lt _ (by have := j.isLt; omega)⟩` em vez de `j +
1`.
6. **`Sym2.map f s(a₁, a₂)`:** use `change s(f a₁, f a₂) = s(f b₁, f b₂) at hab` seguido de `rw [Sym2.eq_iff]`.
7. **`SimpleGraph.deleteEdges`:** simplifique sempre com `SimpleGraph.deleteEdges_adj`.

---

## 6. Plano Imediato para a Rodada 12

1. **Núcleo cúbico 3-conexo.** Para cada escolha de raízes e junções, comparar os espectros de caminhos do Teorema 21 com as somas proibidas no corte original. Procurar famílias em que os dois tipos de ciclo da colagem sejam simultaneamente bloqueados.
2. **Formalização Lean.** Reutilizar os arcos de ciclos e o fechamento de caminhos simples da Rodada 11 na colagem do Teorema 21. Separar a preservação de grau da classificação de ciclos.
3. **Frente planar.** Investigar se a ausência de ciclos longos no subgrafo triangular restringe as configurações de descarga com faces triangulares. Tratar explicitamente passeios faciais com repetições.

---

## 7. Changelog de Sessões

* **v1.6 (22/11/2026 — Rodada 11):** Verificado o Teorema 7, o Cacto de Triângulos. Provado o Teorema 21 em texto, com o critério aritmético de uma junção verificado em Lean. Recompilação com 0 erros, 0 avisos de linter e 7 avisos de `sorry`. Progresso: `25% / 100%`.
* **v1.5 (22/11/2026 — Rodada 10):** Fechado o raio de colisão $6$ em Lean. Verificada a versão localmente injetiva do núcleo do Teorema 17, sem restrição de finitude. Provado o Teorema 20 sobre a fronteira de fragmentos bipartidos e verificado seu núcleo algébrico. Recompilação com 0 erros, 0 avisos de linter e 8 avisos de `sorry`. Progresso: `25% / 100%`. A conjectura geral permanece aberta.
* **v1.4 (22/11/2026 — Rodada 9):** Provado o Teorema 19 sobre as seis combinações de pares de terminais de um lado bipartido de corte cúbico. Formalizado `minimal_bridgeless` e verificados três lemas auxiliares do Teorema 19. Verificados os casos de raio de colisão $4$ e $\ge 8$ do Teorema 17. Recompilação completa com 0 erros, 0 avisos de linter e 9 avisos de `sorry`. Progresso: `24% / 100%`.
* **v1.3 (22/11/2026 — Rodada 8 & Limpeza Lean `v4.36.0`):** Confirmados 9/9 blocos sem `sorry` com 0 erros; limpos os
4 avisos de linter; provados Teorema 17 (bipartidos em superfícies $\chi \ge 0$ contêm $C_4, C_8$ ou $C_{16}$, ótimo)
e Teorema 18 (Desigualdade Exata do Fulereno $30\chi \le 9n_3 - 8n$, $n \ge 60$ no plano); formalizados sem `sorry` os
2 teoremas algébricos do Teorema 18 e definida `hexLattice` + enunciado do Teorema 17. Progresso: `22% / 100%`.
* **v1.2.1 (22/11/2026 — Calibração Lean `v4.36.0`):** Corrigidos todos os 15 erros de compilação para Lean `v4.36.0`
+ Mathlib `v4.36.0`. Progresso: `18% / 100%`.
* **v1.2 (21/11/2026 — Rodadas 6 e 7):** Teoremas 13, 14, 15 e Proposição 16. Progresso: `18% / 100%`.
* **v1.1 (21/11/2026 — Sincronização):** Comando automático no topo, Regra do Par Sincronizado e extração    de
`Erdos64_lean.md`. Progresso: `11% / 100%`.
* **v1.0 (21/11/2026 — Rodadas 1 a 5):** Lemas 1–6, Bloco Pinçado, Teoremas 7–12. Progresso: `11% / 100%`.
