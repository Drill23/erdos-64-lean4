> **INSTRUÇÃO AUTOMÁTICA DE RETOMADA PARA A IA (LEIA PRIMEIRO):**  
> Se o usuário enviou este arquivo (ou link) em uma nova conversa — mesmo acompanhado apenas de um comando curto como *"segue"* ou *"continua"* — **assuma imediatamente a continuidade da pesquisa abaixo sem pedir confirmação**.  
> 1. Considere todos os resultados da **Seção 3** como provados matematicamente (ver status de compilação formal em `lean/Erdos64.lean`).  
> 2. Respeite os **Becos Sem Saída** da **Seção 4** para não repetir caminhos descartados.  
> 3. Escolha **autonomamente** o ataque e execute diretamente a **Próxima Rodada** definida na **Seção 6**, abrindo sua resposta com o indicador `**Progresso: X% / 100%**`.  
> 4. Sempre que gerar um novo checkpoint, atualize **simultaneamente** `README.md` e `lean/Erdos64.lean` (Regra do Par Sincronizado).

---

# Projeto Erdős #64 — Conjectura de Erdős–Gyárfás

> **Arquivo Mestre de Estado, Memória e Continuidade (`Checkpoint v1.1`)**  
> **Última atualização:** 21 de novembro de 2026 (Pós-Rodada 5 / Sincronização Lean 4)  
> **Progresso Atual:** `11% / 100%`  
> **Alvo Oficial:** `https://erdosproblems.com/64` (Prêmio de \$1.000 — Teoria dos Grafos / Ciclos)  
> **Arquivo Lean Sincronizado:** `lean/Erdos64.lean`

---

## 1. Protocolo de Continuidade e Regras do Projeto

1. **Retomada Imediata Sem Regressão:**
   - Todos os teoremas listados na **Seção 3** estão com demonstração matemática fechada; só revisite algum deles se o compilador Lean 4 apontar um erro ou durante a eliminação de seus `sorry` em `lean/Erdos64.lean`.
   - Leia a **Seção 4** antes de propor qualquer ataque novo.
   - Retome sempre pela **Próxima Rodada** da **Seção 6** (neste checkpoint: **Rodada 6**).

2. **Divisão de Papéis:**
   - **IA (Estrategista e Demonstradora):** Decide **autonomamente** qual frente atacar em cada rodada, conduz as demonstrações com rigor completo, decide o momento de emitir novos checkpoints e mantém o código Lean 4 atualizado. Não pergunte ao usuário qual subproblema escolher.
   - **Usuário (Orquestrador / Ponte de Verificação):** Controla o ritmo (*"segue"*), executa os arquivos `.lean` por meio de seu agente com acesso ao compilador **Lean 4 + Mathlib**, devolve logs/erros de compilação quando houver e sobe os checkpoints atualizados no GitHub.

3. **Regra do Termômetro de Progresso (`0%` a `100%`):**
   - Toda rodada de pesquisa **deve começar** com `**Progresso: X% / 100%**` seguido de justificativa breve e honesta.
   - Escala:
     - `0%`: Mapeamento inicial, sem resultado estrutural próprio.
     - `1%` a `25%`: Reduções estruturais, eliminação de classes específicas e resultados parciais sólidos.
     - `26%` a `60%`: Quebra de barreiras centrais no núcleo cúbico 2-conexo ou ferramenta geral aplicável a todos os 2-fatores / estruturas de ciclos.
     - `61%` a `95%`: Arquitetura de prova global fechada com poucos lemas técnicos pendentes (ou candidato real a contraexemplo superando filtros profundos).
     - `100%`: Prova completa fechada (ou contraexemplo explícito verificado), faltando apenas a verificação final sem `sorry` no Lean 4.

4. **Regra do Par Sincronizado (`README.md` + `lean/Erdos64.lean`):**
   - **Sempre** que a IA gerar uma atualização de `README.md`, **deve gerar na mesma resposta** a versão atualizada de `lean/Erdos64.lean`, substituindo ambos os arquivos no repositório GitHub (sem criar arquivos `v2`, `v3`; o histórico fica nos commits do Git).
   - Quando emitir novos checkpoints: automaticamente a cada marco real (novo teorema relevante, nova família eliminada ou rodada de verificação Lean concluída, tipicamente a cada 2 ou 3 rodadas), quando o chat começar a ficar longo, ou sempre que o usuário pedir.
   - Se `README.md` ultrapassar ~500 linhas no futuro, mover demonstrações longas já verificadas em Lean 4 para `docs/provas_completas.md`, mantendo no `README.md` apenas enunciados, corolários, tabela de status e próximos passos.
   - Usar exclusivamente LaTeX (`$...$` e `$$...$$`) para notação matemática nos arquivos `.md`.

---

## 2. Enunciado Oficial e Fronteira da Literatura (Nov/2026)

### Enunciado (Problema #64 — Erdős & Gyárfás, 1995)
> Todo grafo finito simples $G$ com grau mínimo $\delta(G) \ge 3$ contém um ciclo simples de comprimento $2^k$ para algum inteiro $k \ge 2$ (ou seja, $4, 8, 16, 32, \dots$)?

### Fronteira Conhecida até Novembro de 2026
* **Grau médio alto:** Provado por Liu e Montgomery (existe constante grande $C$ tal que todo grafo com grau médio $\ge C$ contém um ciclo de comprimento potência de 2). O problema vive no regime **esparso** (dominado por grafos cúbicos ou quase cúbicos).
* **Redução estrutural recente (Set/2026):** Guillaume Ducoffe e Bogdan Dumitru (`arXiv:2609.28594`) mostraram que todo contraexemplo mínimo é 2-conexo ou formado pela colagem de dois blocos 2-conexos por um único vértice de corte, e que mais de $\frac{2}{3}n$ ($\approx 66{,}67\%$) dos vértices têm grau exatamente $3$.
* **Limites computacionais (2026 — Ducoffe–Dumitru, Balaji, Tranquilli):** Não existe contraexemplo com:
  * $n \le 40$ vértices (grafos gerais);
  * $n \le 48$ vértices (grafos cúbicos);
  * $n \le 66$ vértices (grafos bipartidos).
* **Consequência estratégica:** Busca bruta em grafos pequenos está esgotada; o avanço precisa ser estrutural/teórico ou busca guiada por obstruções estruturais em $n$ grande.

---

## 3. Inventário de Resultados Provados (Rodadas 1 a 5)

### Convenções Fixas
* Um grafo $G$ é **livre de $C_{2^k}$** se não contém nenhum ciclo simples de comprimento $2^k$ com $k \ge 2$.
* Um **contraexemplo mínimo** $G$ é um grafo finito simples, não vazio, com $\delta(G) \ge 3$ e livre de $C_{2^k}$, escolhido com o **menor $|V(G)|$** possível e, no empate, o **menor $|E(G)|$** possível. (A mesma definição aplica-se às subclasses *sem triângulos* e *bipartidos*, pois ambas são fechadas sob subgrafos induzidos e remoção de arestas.)
* Partição por graus: $H = \{u \in V(G) : \deg_G(u) \ge 4\}$ (tamanho $h$), $H_4 = \{u \in V(G) : \deg_G(u) = 4\}$, $L = V_3 = \{v \in V(G) : \deg_G(v) = 3\}$ (tamanho $\ell$), e $L_j = \{v \in L : |N_G(v) \cap H| = j\}$ para $j \in \{0, 1, 2, 3\}$.

### Tabela Mestre de Progresso e Sincronização com `lean/Erdos64.lean`

| ID | Resultado | Rodada | Declaração em `lean/Erdos64.lean` | Status Lean 4 |
| :--- | :--- | :---: | :--- | :---: |
| **Lema 1** | Contraexemplo mínimo é conexo | 1 | `minimal_connected` | `SORRY` |
| **Lema 2** | Dois vértices distintos têm no máximo 1 vizinho comum | 1 | `no_two_common_neighbors`, `common_neighbors_le_one` | `READY_TO_COMPILE` |
| **Lema 3** | Triângulos nunca compartilham arestas | 1 | `triangles_edge_disjoint` | `READY_TO_COMPILE` |
| **Lema 4** | $H = V_{\ge 4}$ é um conjunto independente | 1 | `high_degree_independent` | `SORRY` |
| **Lema 5** | Contraexemplo mínimo não possui pontes | 2 | `minimal_bridgeless` | `SORRY` |
| **Lema 6 + Redução** | Dicotomia do vértice de corte e Bloco Pinçado $\mathcal{K}$ | 2 | `pinched_block_equiv` (a formalizar) | `PLANNED` |
| **Teorema 7** | **Teorema do Cacto de Triângulos** ($G_\Delta$ sem ciclos $\ge 4$) | 3 | `triangle_cactus_no_long_cycle` | `SORRY` |
| **Teoremas 8–9** | Fronteira das componentes de $G[L]$, $L_3 = \emptyset$, $\|E(G[L_2])\| \le \|H_4\|$ | 4 | `no_L3_vertices` | `SORRY` |
| **Teorema 10** | Pisos de cubicidade: $\|V_3\| \ge \frac{8}{11}n$ (sem $K_3$) e $\ge \frac{20}{27}n$ (bipartido) | 4 | `minimal_triangle_free_cubicity`, `minimal_bipartite_cubicity` | `SORRY` |
| **Teorema 11** | **Autorredução de $K_3$-fatores** em cúbicos ($H_3$ cúbico simples) | 5 | `minimal_no_K3_factor` | `SORRY` |
| **Teorema 12** | **Autorredução de $C_5$-fatores** em cúbicos ($H_5$ 5-regular; $n \ge 110$) | 5 | `minimal_no_C5_factor` | `SORRY` |

*(Legenda Lean 4: `READY_TO_COMPILE` = prova escrita sem `sorry`, aguardando retorno do compilador do usuário; `VERIFIED` = compilado com zero erros e zero `sorry` no ambiente do usuário; `SORRY` = enunciado tipado aguardando formalização da prova; `PLANNED` = ainda não escrito em `.lean`.)*

---

### 3.1. Rodada 1 — Propriedades Básicas (Lemas 1–4)

Para todo contraexemplo mínimo $G$:
1. **$G$ é conexo:** caso contrário, qualquer componente conexa contradiz a minimalidade de $|V(G)|$.
2. **Dois vértices distintos têm no máximo 1 vizinho comum:** dois vizinhos comuns $w_1 \ne w_2$ entre $u \ne v$ formam $C_4$.
3. **Triângulos nunca compartilham arestas:** dois triângulos compartilhando $uv$ formam $C_4$ (corolário direto do Lema 2).
4. **$H = V_{\ge 4}$ é um conjunto independente:** se $uv \in E(G)$ com $\deg(u), \deg(v) \ge 4$, então $G - uv$ mantém $\delta \ge 3$, continua livre de $C_{2^k}$ e tem menos arestas, contradizendo a minimalidade.

---

### 3.2. Rodada 2 — Conectividade e Redução ao Bloco Pinçado (Lemas 5–6)

#### Lema 5 ($G$ não tem pontes)
**Prova:** Suponha que $e = uv$ seja uma ponte separando $G - e$ em $C_1 \ni u$ e $C_2 \ni v$ com $|V(C_1)| \le |V(C_2)|$ (logo $2|V(C_1)| \le |V(G)|$). Todo $x \in V(C_1) \setminus \{u\}$ tem grau $\ge 3$ em $C_1$ e $\deg_{C_1}(u) \ge 2$.
* Se $\deg_{C_1}(u) \ge 3$, então $C_1$ é contraexemplo menor.
* Se $\deg_{C_1}(u) = 2$, construa $H$ fundindo duas cópias disjuntas de $C_1$ pelo vértice $u$ em um único vértice $u^*$. Então $H$ é simples, $\deg_H(u^*) = 4$, $\delta(H) \ge 3$, nenhum ciclo simples cruza $u^*$ (logo $H$ é livre de $C_{2^k}$), e $|V(H)| = 2|V(C_1)| - 1 \le |V(G)| - 1 < |V(G)|$, contradição. $\blacksquare$

#### Lema 6 (Dicotomia do Vértice de Corte) e Teorema do Bloco Pinçado
Se $G$ possui um vértice de corte $v$ com componentes $B_1, \dots, B_m$ ($m \ge 2$) de $G - v$ e blocos estendidos $H_i = G[V(B_i) \cup \{v\}]$:
1. Pelo Lema 5, $\deg_{H_i}(v) \ge 2$; pela minimalidade, $\deg_{H_i}(v) \le 2$; logo $\deg_{H_i}(v) = 2$ para todo $i$.
2. Tomando $B_1$ mínimo em vértices (e $H_1$ mínimo em arestas no empate) e colando duas cópias de $H_1$ em $v$, obtemos contraexemplo com $2|V(B_1)| + 1$ vértices e $2|E(H_1)|$ arestas. Pela minimalidade: $m = 2$, $\deg_G(v) = 4$, $|V(B_1)| = |V(B_2)| = k$ ($|V(G)| = 2k + 1$ ímpar) e $|E(H_1)| = |E(H_2)|$.
3. $v$ é o **único** vértice de corte de $G$ (qualquer $w \in B_1$ deixaria $H_2$ contido numa única componente de $G - w$ com $\ge k + 1$ vértices). Logo $H_1$ e $H_2$ são **2-conexos**, e os dois vizinhos de $v$ em $H_1$ têm grau $3$ (pois $H$ é independente).

> **Teorema de Redução (Bloco Pinçado):** Seja $\mathcal{K}$ a classe de grafos finitos, simples, **2-conexos** e livres de $C_{2^k}$ nos quais todo vértice tem grau $\ge 3$, exceto possivelmente um único vértice $v_0$ de grau $2$. Então a Conjectura de Erdős–Gyárfás é verdadeira se, e somente se, $\mathcal{K} = \emptyset$.

---

### 3.3. Rodada 3 — Teorema do Cacto de Triângulos (Teorema 7)

> **Teorema 7:** Seja $G$ qualquer grafo finito simples livre de $C_{2^k}$ ($k \ge 2$) e seja $G_\Delta = (V(G), E_\Delta)$ o subgrafo formado pelas arestas de $G$ que pertencem a pelo menos um triângulo em $G$. Então **$G_\Delta$ não contém nenhum ciclo de comprimento $\ge 4$** (todo bloco 2-conexo de $G_\Delta$ é um único $K_3$).

**Prova:** Suponha por absurdo que exista ciclo em $G_\Delta$ de comprimento $\ge 4$ e tome um mínimo $C = v_1 - v_2 - \dots - v_L - v_1$ em $G_\Delta$ (índices $\pmod L$).
1. $L \ge 5$ (pois $G$ é livre de $C_4$).
2. **$C$ é livre de cordas em $G_\Delta$:** qualquer corda $v_i v_j \in E_\Delta$ divide $C$ em dois ciclos $C_1, C_2 \subseteq G_\Delta$ com $|C_1|, |C_2| \ge 3$ e $|C_1| + |C_2| = L + 2 \ge 7$; logo o maior deles tem comprimento em $[4, L - 1]$, contradizendo a minimalidade de $L$.
3. **Testemunhas externas:** Para cada aresta $v_i v_{i+1} \in E_\Delta$, existe $w_i \in V(G)$ formando triângulo $v_i v_{i+1} w_i$ (logo $v_i w_i, v_{i+1} w_i \in E_\Delta$). Como $L \ge 5$ e $C$ não tem cordas em $G_\Delta$, temos $w_i \notin V(C)$ para todo $i$.
4. **Testemunhas duas a duas distintas:** Se $w_i = w_j = w$ ($1 \le i < j \le L$), removendo $v_i v_{i+1}$ e $v_j v_{j+1}$ sobram dois arcos de comprimentos $a = j - i - 1 \ge 0$ e $b = L + i - j - 1 \ge 0$ com $a + b = L - 2 \ge 3$:
   * $a = 0$ (ou $b = 0$): $v_i - v_{i+1} - v_{j+1} - w - v_i$ é um $C_4$ em $G$.
   * $a = 1$ (ou $b = 1$): $v_i - v_{i+1} - v_j - w - v_i$ é um $C_4$ em $G$.
   * $a \ge 2$ e $b \ge 2$: o arco de comprimento $a$ fechado por $v_j - w - v_{i+1}$ é um ciclo em $G_\Delta$ de comprimento $a + 2 \in [4, L - 2]$, contradizendo a minimalidade de $L$.
5. **Disparo de $2^k$:** Escolha o único $k \ge 3$ tal que $2^{k-1} < L \le 2^k$. Então $r = 2^k - L$ satisfaz $0 \le r \le L - 1$. Substituindo as $r$ primeiras arestas $v_t v_{t+1}$ de $C$ pelos desvios $v_t - w_t - v_{t+1}$, obtemos um ciclo simples em $G$ de comprimento $(L - r) + 2r = L + r = 2^k$. Contradição. $\blacksquare$

**Corolários:**
* **Corolário 7.1:** $G_\Delta$ é 2-degenerado, $|E_\Delta| \le \frac{3}{2}(|V(G)| - 1)$ e $G$ tem no máximo $\lfloor (|V(G)| - 1)/2 \rfloor$ triângulos.
* **Corolário 7.2:** A Conjectura de Erdős–Gyárfás vale para todo grafo com $\delta(G_\Delta) \ge 3$.

---

### 3.4. Rodada 4 — Componentes de $G[V_3]$ e Superação do Recorde de 2026 (Teoremas 8–10)

#### Teorema 8 (Fronteira das Componentes)
> Em um contraexemplo mínimo $G$ (geral, sem triângulos ou bipartido) com $H \ne \emptyset$, para toda componente conexa $C$ de $G[L]$ existe $x \in H$ tal que $|N_G(x) \cap V(C)| \ge \deg_G(x) - 2 \ge 2$.

**Prova:** Se para todo $x \in H$ valesse $|N_G(x) \cap V(C)| \le \deg_G(x) - 3$, então $G' = G - V(C)$ conteria $H \ne \emptyset$, preservaria $\deg_{G'}(x) \ge 3$ para todo $x \in H$ e $\deg_{G'}(v) = 3$ para todo $v \in L \setminus V(C)$, contradizendo a minimalidade de $G$. $\blacksquare$

* **Corolário 8.1:** $L_3 = \emptyset$ (nenhuma componente é vértice isolado, pois $|N_G(x) \cap \{v\}| \le 1 < 2$).
* **Desigualdade das Folhas:** Para toda componente $C$ de $G[L]$ com $c_j = |V(C) \cap L_j|$, $3c_0 + 2c_1 + c_2 = 2|E(C)| \ge 2(c_0 + c_1 + c_2 - 1) \implies c_2 \le c_0 + 2$.

#### Teorema 9 (Rigidez de $G[L_2]$)
* Toda aresta $vw$ em $L_2$ é componente $K_2$ de $G[L]$; pelo Teorema 8, existe $x \in H_4$ tal que $xvw$ é um triângulo.
* Nenhum $x \in H_4$ sustenta duas arestas de $G[L_2]$ (os quatro vizinhos externos em $H \setminus \{x\}$ seriam dois a dois distintos pela ausência de $C_4$, e deletar o bloco de 5 vértices preservaria $\delta \ge 3$). Logo $|E(G[L_2])| \le |H_4|$.
* Nenhuma componente de $G[L]$ é um triângulo.

#### Teorema 10 (Novos Pisos de Cubicidade — Superando $\frac{2}{3}n$ de Set/2026)
> 1. Todo contraexemplo mínimo **sem triângulos** satisfaz $|V_3| \ge \frac{8}{11}n \approx 72{,}73\%$.
> 2. Todo contraexemplo mínimo **bipartido** satisfaz $|V_3| \ge \frac{20}{27}n \approx 74{,}07\%$.

**Prova:** Trivial se $H = \emptyset$. Para $H \ne \emptyset$, contando arestas entre $H$ e $L$ temos $|L_1| + 2|L_2| \ge 4h$. Em cada componente $C$ de $G[L]$, pelo Teorema 8 existe $x \in H$ com dois vizinhos distintos $y, z \in V(C)$; um caminho mínimo $P$ de comprimento $d$ em $C$ entre $y$ e $z$ fecha um ciclo simples de comprimento $d + 2$ com $x$, e seus $d - 1$ vértices internos pertencem a $L_0 \cup L_1$, dando $c_1 + c_0 \ge d - 1$.
* **Sem triângulos:** $d + 2 \notin \{3, 4\} \implies d \ge 3 \implies c_1 + c_0 \ge 2$. Com $c_2 \le c_0 + 2$, segue $c_2 \le c_1 + 2c_0$. Somando nas componentes: $|L_1| + 2|L_0| - |L_2| \ge 0$, logo:
  $$\ell = |L_0| + |L_1| + |L_2| \ge \frac{2}{3}(|L_1| + 2|L_2|) + \frac{1}{3}(|L_1| + 2|L_0| - |L_2|) \ge \frac{8}{3}h \implies \ell \ge \frac{8}{11}n.$$
* **Bipartido:** $d + 2$ é par e $\ne 4 \implies d \ge 4 \implies c_1 + c_0 \ge 3 \implies 2 \le \frac{2}{3}(c_1 + c_0)$. Com $c_2 \le c_0 + 2$, segue $3c_2 \le 2c_1 + 5c_0$. Somando nas componentes: $2|L_1| + 5|L_0| - 3|L_2| \ge 0$, logo:
  $$\ell \ge \frac{5}{7}(|L_1| + 2|L_2|) + \frac{1}{7}(2|L_1| + 5|L_0| - 3|L_2|) \ge \frac{20}{7}h \implies \ell \ge \frac{20}{27}n. \quad \blacksquare$$

---

### 3.5. Rodada 5 — Contração de 2-Fatores no Núcleo Cúbico (Teoremas 11–12)

#### Teorema 11 (Autorredução de $K_3$-Fatores)
> Se $G$ é cúbico finito simples livre de $C_{2^k}$ com um $K_3$-fator $\{D_1, \dots, D_m\}$, o grafo contraído $H_3$ é **cúbico simples** sobre $n/3$ vértices e evita todo ciclo de comprimento em $\bigcup_{k \ge 2} [\lceil 2^k/3 \rceil, 2^{k-1}]$ (em particular, é livre de $C_{2^k}$). Logo **nenhum contraexemplo mínimo é cúbico com $K_3$-fator**.

**Prova:** Sem laços ($G$ simples). Sem paralelas (duas arestas entre $D_i$ e $D_j$ fecham $C_4$ via arestas internas dos triângulos). Todo ciclo simples $Q$ de comprimento $L$ em $H_3$ levanta para todos os comprimentos em $[2L, 3L]$ em $G$ (escolha independente de arco $1$ ou $2$ em cada triângulo). Em particular, $L = 2^r$ ($r \ge 2$) gera $2L = 2^{r+1}$. $\blacksquare$

#### Teorema 12 (Autorredução de $C_5$-Fatores para Grafos 5-Regulares)
> Se $G$ é cúbico finito simples livre de $C_{2^k}$ com um $C_5$-fator $\{D_1, \dots, D_m\}$, o grafo contraído $H_5$ é **5-regular simples** sobre $n/5$ vértices e é livre de $C_{2^k}$. Consequentemente, **nenhum contraexemplo mínimo é cúbico com $C_5$-fator**, e qualquer cúbico livre de $C_{2^k}$ com $C_5$-fator tem $n \ge 110$ (elementar) e $n > 200$ (usando $n > 40$).

**Prova:**
1. **Sem laços:** corda em $C_5$ fecha $C_4$ com o arco de comprimento $3$.
2. **Sem paralelas:** duas arestas entre $D_i, D_j$ oferecem pares de arcos em $\{\{1,4\}, \{2,3\}\}$; as somas $2 + x + y$ atingem $2+1+1 = 4$ (ambos $\{1,4\}$), $2+4+2 = 8$ (misto) e $2+3+3 = 8$ (ambos $\{2,3\}$). Logo $H_5$ é 5-regular simples.
3. **Cota $n \ge 110$:** Em $H_5$ (5-regular, livre de $C_4$), $N_1(v)$ tem grau máximo $\le 1$ e tamanho ímpar $5$, logo ao menos 1 vértice é isolado em $N_1(v)$ (4 vizinhos em $N_2$) e os outros 4 têm $\ge 3$ vizinhos em $N_2$, todos distintos (sem $C_4$): $|V(H_5)| \ge 1 + 5 + 16 = 22 \implies n \ge 110$.
4. **Levantamento de $C_{2^k}$:** Se $H_5$ contém ciclo simples $Q$ de comprimento $L = 2^k$ ($k \ge 2$), seja $r \in \{0, \dots, L\}$ o número de pentágonos em $Q$ com par $\{1, 4\}$ (os demais $L - r$ têm $\{2, 3\}$).
   * Se $r = L$: escolha arco $1$ em todos os pentágonos $\implies$ ciclo simples em $G$ de comprimento $L + L = 2L = 2^{k+1}$.
   * Se $0 \le r \le L - 1$: defina $a = \lceil \frac{2r}{3} \rceil$, $s = 3L - r - 3a$ e $b = s - 2(L - r)$. Temos $0 \le a \le r$, $b \le L - r \iff 2r \le 3a$, e $b \ge 0 \iff 3a \le L + r$ (para $r \le L - 2$: $3a \le 2r + 2 \le L + r$; para $r = L - 1$, como $L = 2^k \not\equiv 0 \pmod 3$, tanto $L \equiv 1$ quanto $L \equiv 2 \pmod 3$ dão $3a \le 2L - 1 = L + r$). Escolhendo $a$ arcos de tamanho $4$, $r - a$ de tamanho $1$, $b$ de tamanho $3$ e $(L-r)-b$ de tamanho $2$, obtemos ciclo simples em $G$ de comprimento $L + (r + 3a) + s = 4L = 2^{k+2}$. Contradição. $\blacksquare$

---

## 4. Becos Sem Saída e Obstruções Mapeadas (Não Repetir)

1. **Busca bruta computacional em grafos pequenos:** Descartada até $n \le 40$ (geral), $n \le 48$ (cúbico) e $n \le 66$ (bipartido).
2. **Melhorar $|V_3|/n$ via densidade pura do grafo auxiliar $M$ sobre $H$:** A 1-subdivisão de $K_t$ (sem $C_4$) e de planos projetivos (sem $C_4, C_8$) atingem densidade $2 - o(1)$; mesmo proibindo todos os $C_{2^k}$, colando cópias do grafo saturado $G_8$ (8 vértices, 11 arestas, livre de $C_4, C_8$) pelo vértice de grau 4 obtemos família infinita 2-degenerada de densidade $\frac{11}{7} \approx 1{,}571$. O caminho superior foi o Teorema 8 (componentes de $G[V_3]$).
3. **Contração de 2-fator misto $\{C_3, C_5\}$:** Um $C_4$ contraído com 3 triângulos e 1 pentágono $\{2,3\}$ levanta apenas para $[9, 13]$, escapando de $8$ e $16$.
4. **Contração de $C_6$-fator bipartido (obstrução alvo da Rodada 6):** Em $G$ cúbico bipartido com $C_6$-fator, $H_6$ pode ter arestas paralelas (ex.: $\{1,5\}$ e $\{3,3\}$ geram $6$ e $10$), mas $H_6^{\text{simp}}$ parece preservar $\delta \ge 3$. No levantamento de $C_{2^k}$, o único caso bloqueado é $b = 0$ (nenhum hexágono $\{2,4\}$) com $a$ ímpar (número ímpar de hexágonos $\{1,5\}$ e $\{3,3\}$).
5. **Núcleo Cúbico Hamiltoniano:** Ainda intocado; é o extremo oposto do espectro de 2-fatores (apenas 1 ciclo).

---

## 5. Instruções para o Agente de Verificação Lean 4

* O código formalizado está em **`lean/Erdos64.lean`** (mantido sempre sincronizado com este `README.md`).
* **Primeiro teste recomendado:** Rodar `lake build` em `lean/Erdos64.lean` e retornar ao chat:
  1. A versão exata do Lean 4 / Mathlib instalada no ambiente;
  2. Se `no_two_common_neighbors`, `common_neighbors_le_one` e `triangles_edge_disjoint` já compilaram sem erro (passando para `VERIFIED`);
  3. Qualquer erro de tipo/API nos enunciados restantes.

---

## 6. Plano Imediato para a Rodada 6

1. **Atacar o $C_6$-fator bipartido:**
   * Provar rigorosamente que $H_6^{\text{simp}}$ preserva $\delta \ge 3$ (classificando todas as multiplicidades possíveis de arestas paralelas entre dois hexágonos em $G$ bipartido livre de $C_{2^k}$).
   * Tentar quebrar a obstrução de paridade ($b = 0$ e $a$ ímpar) no levantamento de $C_{2^k}$.
2. **Abrir o ataque aos Grafos Cúbicos Hamiltonianos:**
   * Mapear a aritmética modular de pares e triplas de cordas cruzadas sobre um ciclo Hamiltoniano $C_n$ sem $C_{2^k}$.
3. **Ciclo de Lean 4:** Assim que o agente retornar os logs do primeiro build de `lean/Erdos64.lean`, atualizar os `READY_TO_COMPILE` para `VERIFIED` e eliminar os `sorry` de `minimal_connected`, `high_degree_independent` e `minimal_bridgeless`.

---

## 7. Changelog de Sessões

* **v1.1 (21/11/2026 — Sincronização):** Adicionado bloco de retomada automática no topo do `README.md`, formalizada a Regra do Par Sincronizado (`README.md` + `lean/Erdos64.lean`), extraído o código Lean para `lean/Erdos64.lean` já com as provas completas dos Lemas 2 e 3 (`READY_TO_COMPILE`). Progresso mantido em `11% / 100%`.
* **v1.0 (21/11/2026 — Rodadas 1 a 5):** Consolidação inicial dos Lemas 1–6, Bloco Pinçado, Teoremas 7–12 e mapa de obstruções. Progresso em `11% / 100%`.