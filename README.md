# Projeto Erdős #64 — Conjectura de Erdős–Gyárfás

> **Arquivo Mestre de Estado, Memória e Continuidade (`Checkpoint v1.0`)**  
> **Última atualização:** 21 de novembro de 2026 (Fim da Rodada 5)  
> **Progresso Atual:** `11% / 100%`  
> **Alvo Oficial:** `https://erdosproblems.com/64` (Prêmio de \$1.000 — Teoria dos Grafos / Ciclos)

---

## 1. Protocolo de Continuidade (Instruções Obrigatórias para a IA)

**Se você é uma nova instância/sessão de IA lendo este repositório a partir de um link enviado pelo usuário, siga estritamente estas regras antes de responder:**

1. **Retomada Imediata Sem Regressão:**
   - Considere **todos os resultados da Seção 3 como já provados matematicamente** (embora ainda aguardem compilação formal em Lean 4, conforme a tabela de status). Não gaste rodadas re-provando resultados já fechados, a menos que o compilador Lean 4 aponte um erro ou que o usuário peça a formalização deles.
   - Consulte a **Seção 4 (Becos Sem Saída)** antes de propor qualquer ataque para não repetir caminhos já descartados.
   - Retome diretamente pela **Próxima Rodada** indicada na **Seção 6** (neste checkpoint: **Rodada 6**).

2. **Divisão de Papéis:**
   - **IA (Estrategista e Demonstradora):** Escolhe **autonomamente** qual frente atacar em cada rodada, conduz as provas com rigor total, escreve código Lean 4 ou scripts auxiliares quando estratégico e mantém o registro honesto de obstruções. **Não peça ao usuário para escolher qual subproblema atacar**, a menos que haja necessidade operacional externa (como rodar Lean 4 ou subir arquivo).
   - **Usuário (Orquestrador / Ponte de Verificação):** Comanda o ritmo ("segue"), aciona um agente local com acesso ao compilador **Lean 4 + Mathlib** para validar código e sobe os checkpoints atualizados neste repositório GitHub.

3. **Regra do Termômetro de Progresso (`0%` a `100%`):**
   - Toda rodada de pesquisa **deve abrir** com o marcador `**Progresso: X% / 100%**` seguido de justificativa concisa entre parênteses.
   - Escala **brutalmente honesta**:
     - `0%`: Mapeamento inicial, nenhum resultado estrutural próprio.
     - `1%–25%`: Reduções estruturais, eliminação de classes específicas e resultados parciais relevantes.
     - `26%–60%`: Quebra de barreiras centrais no núcleo cúbico 2-conexo ou construção de ferramenta geral aplicável a todos os 2-fatores / estruturas de ciclos.
     - `61%–95%`: Arquitetura de prova global fechada com poucos lemas técnicos pendentes (ou candidato sério a contraexemplo passando em filtros profundos).
     - `100%`: Prova completa fechada (ou contraexemplo explícito verificado), faltando exclusivamente a compilação final sem `sorry` no Lean 4.
   - Nunca infle o percentual artificialmente. Se uma rodada descobrir apenas uma obstrução importante sem novo teorema, o percentual pode ficar estacionado.

4. **Regras para Construir Futuros Checkpoints (Próximos Arquivos):**
   - Sempre que o usuário solicitar um novo checkpoint de contexto (quando o chat ficar longo), gere uma versão atualizada deste `README.md` (incrementando `Checkpoint vX.Y` e atualizando a **Seção 7 — Changelog**).
   - **Autossuficiência obrigatória:** Toda prova nova fechada deve entrar na Seção 3 com enunciado e demonstração completos (não apenas resumos vagos), para que futuras sessões consigam reutilizar os detalhes técnicos exatos.
   - **Separação Modular de Arquivos (quando crescer):**
     - Mantenha `README.md` como índice mestre, protocolo, tabela de progresso, becos sem saída e próximas rodadas.
     - Quando o código Lean 4 passar de ~250 linhas ou começar a ser compilado de fato pelo agente do usuário, extraia-o para `lean/Erdos64.lean` (ou arquivos por módulo: `Basic.lean`, `PinchedBlock.lean`, `TriangleCactus.lean`, `Cubicity.lean`, `TwoFactors.lean`) e mantenha aqui os links relativos e o status exato de cada `theorem` (`SORRY`, `IN_PROGRESS`, `VERIFIED`).
     - Se este `README.md` ficar grande demais para leitura em uma única passada (~500+ linhas), mova demonstrações antigas já verificadas em Lean para `docs/PROOFS_ARCHIVE.md` e mantenha apenas os enunciados e corolários no `README.md`.
   - **Notação:** Use exclusivamente sintaxe LaTeX (`$...$` e `$$...$$`) para fórmulas matemáticas no Markdown. Dentro de blocos de código Lean 4, use a sintaxe padrão do Lean 4 / Mathlib.

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
* **Consequência estratégica:** Busca exaustiva em grafos pequenos está esgotada; o avanço precisa ser estrutural/teórico (ou busca altamente guiada por obstruções estruturais em $n$ grande).

---

## 3. Inventário de Resultados Provados (Rodadas 1 a 5)

### Convenções Fixas
* Um grafo $G$ é **livre de $C_{2^k}$** se não contém nenhum ciclo simples de comprimento $2^k$ com $k \ge 2$.
* Um **contraexemplo mínimo** $G$ é um grafo finito simples, não vazio, com $\delta(G) \ge 3$ e livre de $C_{2^k}$, escolhido com o **menor $|V(G)|$** possível e, em caso de empate, o **menor $|E(G)|$** possível. (A mesma definição aplica-se a contraexemplos mínimos nas subclasses *sem triângulos* e *bipartidos*, pois ambas são fechadas sob subgrafos induzidos e remoção de arestas.)
* Partição por graus: $H = \{u \in V(G) : \deg_G(u) \ge 4\}$ (tamanho $h$), $H_4 = \{u \in V(G) : \deg_G(u) = 4\}$, $L = V_3 = \{v \in V(G) : \deg_G(v) = 3\}$ (tamanho $\ell$), e $L_j = \{v \in L : |N_G(v) \cap H| = j\}$ para $j \in \{0, 1, 2, 3\}$.

### Tabela Mestre de Progresso e Formalização

| ID | Resultado | Rodada | Prova Matemática | Status Lean 4 |
| :--- | :--- | :---: | :---: | :---: |
| **Lemas 1–4** | Conexo, sem $C_4$, triângulos aresta-disjuntos, $H$ independente | 1 | Fechada | `TO_VERIFY` |
| **Lema 5** | Contraexemplo mínimo não tem pontes (2-aresta-conexo) | 2 | Fechada | `TO_VERIFY` |
| **Lema 6 + Teo. Redução** | Dicotomia de vértice de corte e equivalência com Bloco Pinçado $\mathcal{K}$ | 2 | Fechada | `TO_VERIFY` |
| **Teorema 7** | **Teorema do Cacto de Triângulos** ($G_\Delta$ não tem ciclos $\ge 4$) + Cor. 7.1, 7.2 | 3 | Fechada | `TO_VERIFY` |
| **Teorema 8 + Cor. 8.1** | **Fronteira das Componentes** de $G[L]$, $L_3 = \emptyset$, $c_2 \le c_0 + 2$ | 4 | Fechada | `TO_VERIFY` |
| **Teorema 9** | Rigidez de $G[L_2]$: cada aresta fecha $K_3$ com $H_4$ e $|E(G[L_2])| \le |H_4|$ | 4 | Fechada | `TO_VERIFY` |
| **Teorema 10** | **Novos pisos de cubicidade:** $|V_3| \ge \frac{8}{11}n$ (sem $K_3$) e $\ge \frac{20}{27}n$ (bipartido) | 4 | Fechada | `TO_VERIFY` |
| **Teorema 11** | **Autorredução de $K_3$-fatores** em grafos cúbicos ($H_3$ cúbico simples) | 5 | Fechada | `TO_VERIFY` |
| **Teorema 12** | **Autorredução de $C_5$-fatores** em cúbicos ($H_5$ 5-regular simples; $n \ge 110$) | 5 | Fechada | `TO_VERIFY` |

---

### 3.1. Rodada 1 — Propriedades Básicas (Lemas 1–4)

Para todo contraexemplo mínimo $G$:
1. **$G$ é conexo:** caso contrário, qualquer componente conexa contradiz a minimalidade de $|V(G)|$.
2. **Dois vértices distintos têm no máximo 1 vizinho em comum:** dois vizinhos comuns $w_1 \ne w_2$ entre $u \ne v$ formam $C_4$.
3. **Triângulos nunca compartilham arestas:** dois triângulos compartilhando $uv$ formam $C_4$.
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

**Prova:** Se para toda $x \in H$ valesse $|N_G(x) \cap V(C)| \le \deg_G(x) - 3$, então $G' = G - V(C)$ conteria $H \ne \emptyset$, preservaria $\deg_{G'}(x) \ge 3$ para todo $x \in H$ e $\deg_{G'}(v) = 3$ para todo $v \in L \setminus V(C)$ (nenhuma aresta cruza entre $C$ e $L \setminus V(C)$), contradizendo a minimalidade de $G$. $\blacksquare$

* **Corolário 8.1:** $L_3 = \emptyset$ (nenhuma componente é vértice isolado, pois $|N_G(x) \cap \{v\}| \le 1 < 2$).
* **Desigualdade das Folhas:** Para toda componente $C$ de $G[L]$ com $c_j = |V(C) \cap L_j|$, $3c_0 + 2c_1 + c_2 = 2|E(C)| \ge 2(c_0 + c_1 + c_2 - 1) \implies c_2 \le c_0 + 2$.

#### Teorema 9 (Rigidez de $G[L_2]$)
* Toda aresta $vw$ em $L_2$ é componente $K_2$ de $G[L]$; pelo Teorema 8, existe $x \in H$ com $N_G(x) \supseteq \{v, w\}$ e $\deg_G(x) - 2 \le 2 \implies x \in H_4$ e $xvw$ é um triângulo.
* Nenhum $x \in H_4$ sustenta duas arestas de $G[L_2]$: se formasse dois triângulos $xv_1w_1$ e $xv_2w_2$ com $v_1,w_1,v_2,w_2 \in L_2$, os quatro vizinhos externos em $H \setminus \{x\}$ seriam dois a dois distintos (senão surgiria $C_4$ por $x$); deletar $\{x, v_1, w_1, v_2, w_2\}$ reduz o grau de cada um desses quatro vértices em apenas $1$ (mantendo $\ge 3$), gerando contraexemplo menor. Logo $|E(G[L_2])| \le |H_4|$.
* Nenhuma componente de $G[L]$ é um triângulo (um $x \in H$ com 2 vizinhos nele criaria dois triângulos compartilhando aresta).

#### Teorema 10 (Novos Pisos de Cubicidade — Superando $\frac{2}{3}n$ de Set/2026)
> 1. Todo contraexemplo mínimo **sem triângulos** satisfaz $|V_3| \ge \frac{8}{11}n \approx 72{,}73\%$.
> 2. Todo contraexemplo mínimo **bipartido** satisfaz $|V_3| \ge \frac{20}{27}n \approx 74{,}07\%$.

**Prova:** Trivial se $H = \emptyset$. Para $H \ne \emptyset$, contando arestas entre $H$ e $L$ (com $H$ independente e $L_3 = \emptyset$) temos $|L_1| + 2|L_2| \ge 4h$. Em cada componente $C$ de $G[L]$, pelo Teorema 8 existe $x \in H$ com dois vizinhos distintos $y, z \in V(C)$; um caminho mínimo $P$ de comprimento $d$ em $C$ entre $y$ e $z$ fecha um ciclo simples de comprimento $d + 2$ com $x$, e seus $d - 1$ vértices internos pertencem a $L_0 \cup L_1$, dando $c_1 + c_0 \ge d - 1$.
* **Sem triângulos:** $d + 2 \notin \{3, 4\} \implies d \ge 3 \implies c_1 + c_0 \ge 2$. Com $c_2 \le c_0 + 2$, segue $c_2 \le c_1 + 2c_0$. Somando nas componentes: $|L_1| + 2|L_0| - |L_2| \ge 0$. Logo:
  $$\ell = |L_0| + |L_1| + |L_2| \ge \frac{2}{3}(|L_1| + 2|L_2|) + \frac{1}{3}(|L_1| + 2|L_0| - |L_2|) \ge \frac{8}{3}h \implies \ell \ge \frac{8}{11}n.$$
* **Bipartido:** $d + 2$ é par e $\ne 4 \implies d \ge 4 \implies c_1 + c_0 \ge 3 \implies 2 \le \frac{2}{3}(c_1 + c_0)$. Com $c_2 \le c_0 + 2$, segue $3c_2 \le 2c_1 + 5c_0$. Somando nas componentes: $2|L_1| + 5|L_0| - 3|L_2| \ge 0$. Logo:
  $$\ell \ge \frac{5}{7}(|L_1| + 2|L_2|) + \frac{1}{7}(2|L_1| + 5|L_0| - 3|L_2|) \ge \frac{20}{7}h \implies \ell \ge \frac{20}{27}n. \quad \blacksquare$$

---

### 3.5. Rodada 5 — Contração de 2-Fatores no Núcleo Cúbico (Teoremas 11–12)

#### Teorema 11 (Autorredução de $K_3$-Fatores)
> Se $G$ é cúbico finito simples livre de $C_{2^k}$ com um $K_3$-fator $\{D_1, \dots, D_m\}$, o grafo contraído $H_3$ é **cúbico simples** sobre $n/3$ vértices e evita todo ciclo de comprimento em $\bigcup_{k \ge 2} [\lceil 2^k/3 \rceil, 2^{k-1}]$ (em particular, é livre de $C_{2^k}$). Logo **nenhum contraexemplo mínimo é cúbico com $K_3$-fator**.

**Prova:** Sem laços ($G$ simples). Sem arestas paralelas (duas arestas entre $D_i$ e $D_j$ têm extremos distintos em ambos, fechando $C_4$ via arestas internas dos triângulos). Todo ciclo simples $Q$ de comprimento $L$ em $H_3$ levanta para todos os comprimentos em $[2L, 3L]$ em $G$ (cada triângulo oferece escolha independente de arco $1$ ou $2$). Em particular, $L = 2^r$ ($r \ge 2$) gera $2L = 2^{r+1}$. $\blacksquare$

#### Teorema 12 (Autorredução de $C_5$-Fatores para Grafos 5-Regulares)
> Se $G$ é cúbico finito simples livre de $C_{2^k}$ com um $C_5$-fator $\{D_1, \dots, D_m\}$, o grafo contraído $H_5$ é **5-regular simples** sobre $n/5$ vértices e é livre de $C_{2^k}$. Consequentemente, **nenhum contraexemplo mínimo é cúbico com $C_5$-fator**, e qualquer cúbico livre de $C_{2^k}$ com $C_5$-fator tem $n \ge 110$ (elementar) e $n > 200$ (usando $n > 40$).

**Prova:**
1. **Sem laços:** corda em $C_5$ fecha $C_4$ com o arco de comprimento $3$.
2. **Sem paralelas:** duas arestas entre $D_i, D_j$ oferecem pares de arcos em $\{\{1,4\}, \{2,3\}\}$; as somas $2 + x + y$ atingem $2+1+1 = 4$ (se ambos $\{1,4\}$), $2+4+2 = 8$ (se misto) e $2+3+3 = 8$ (se ambos $\{2,3\}$). Logo $H_5$ é 5-regular simples.
3. **Cota $n \ge 110$:** Em $H_5$ (5-regular, livre de $C_4$), $N_1(v)$ tem grau máximo $\le 1$ (triângulos não dividem aresta) e tamanho ímpar $5$, logo ao menos 1 vértice é isolado em $N_1(v)$ (4 vizinhos em $N_2$) e os outros 4 têm $\ge 3$ vizinhos em $N_2$, todos distintos (sem $C_4$): $|V(H_5)| \ge 1 + 5 + 16 = 22 \implies n \ge 110$.
4. **Levantamento de $C_{2^k}$:** Se $H_5$ contém ciclo simples $Q$ de comprimento $L = 2^k$ ($k \ge 2$), seja $r \in \{0, \dots, L\}$ o número de pentágonos em $Q$ com par de arcos $\{1, 4\}$ (os demais $L - r$ têm $\{2, 3\}$).
   * Se $r = L$: escolha arco $1$ em todos os pentágonos $\implies$ ciclo simples em $G$ de comprimento $L + L = 2L = 2^{k+1}$.
   * Se $0 \le r \le L - 1$: defina $a = \lceil \frac{2r}{3} \rceil$, $s = 3L - r - 3a$ e $b = s - 2(L - r)$. Verifica-se:
     - $0 \le a \le r$ (direto para $r \le 2$; para $r \ge 3$, $\frac{2r+2}{3} \le r$);
     - $b \le L - r \iff 2r \le 3a$ (definição de teto);
     - $b \ge 0 \iff 3a \le L + r$: se $r \le L - 2$, então $3a \le 2r + 2 \le L + r$; se $r = L - 1$, como $L = 2^k \not\equiv 0 \pmod 3$, para $L \equiv 1 \pmod 3$ temos $3a = 2L - 2 < 2L - 1 = L + r$, e para $L \equiv 2 \pmod 3$ temos $3a = 2L - 1 = L + r$.
     Escolhendo $a$ arcos de tamanho $4$ e $r - a$ de tamanho $1$ (soma $r + 3a$), e $b$ arcos de tamanho $3$ e $(L-r)-b$ de tamanho $2$ (soma $s$), obtemos ciclo simples em $G$ de comprimento $L + (r + 3a) + s = 4L = 2^{k+2}$. Contradição. $\blacksquare$

---

## 4. Becos Sem Saída e Obstruções Mapeadas (Não Repetir)

1. **Busca bruta computacional em grafos pequenos:** Já descartada na literatura de 2026 até $n \le 40$ (geral), $n \le 48$ (cúbico) e $n \le 66$ (bipartido).
2. **Tentar melhorar $|V_3|/n$ via densidade pura do grafo auxiliar $M$ sobre $H$:**
   * A ideia da Rodada 3 era limitar $|E(M)| \le \alpha |H|$ com $\alpha < 2$ usando apenas 2-degeneração + ausência de $C_{2^k}$.
   * **Por que travou:** a 1-subdivisão de $K_t$ (sem $C_4$) e de planos projetivos (sem $C_4, C_8$) atingem densidade $2 - o(1)$; mesmo proibindo **todos** os $C_{2^k}$, colando cópias do grafo saturado $G_8$ (8 vértices, 11 arestas, livre de $C_4$ e $C_8$) pelo vértice de grau 4 obtemos família infinita 2-degenerada de densidade $\frac{11}{7} \approx 1{,}571$. Portanto, só 2-degeneração não esmaga $M$ facilmente; o caminho superior foi o Teorema 8 (componentes de $G[V_3]$).
3. **Contração de 2-fator misto $\{C_3, C_5\}$:** Um $C_4$ contraído formado por 3 triângulos e 1 pentágono do tipo $\{2, 3\}$ levanta apenas para comprimentos em $[9, 13]$, escapando tanto de $8$ quanto de $16$.
4. **Contração de $C_6$-fator bipartido (obstrução exata para a Rodada 6):**
   * Em $G$ cúbico bipartido com $C_6$-fator, $H_6$ pode ter arestas paralelas (ex.: 2 arestas com pares $\{1,5\}$ e $\{3,3\}$ só geram $6$ e $10$), mas sua simplificação $H_6^{\text{simp}}$ preserva $\delta \ge 3$ (a verificar formalmente na Rodada 6).
   * No levantamento de $C_{2^k}$ em $H_6^{\text{simp}}$, todos os casos fecham exceto a obstrução de paridade: quando nenhum hexágono do ciclo tem par $\{2,4\}$ (isto é, $b = 0$) e o número $a$ de hexágonos com par $\{1,5\}$ é ímpar (deixando o número de arcos $\{3,3\}$ também ímpar e travando a paridade da soma).
5. **Núcleo Cúbico Hamiltoniano:** Ainda totalmente intocado; é o outro extremo do espectro de 2-fatores (apenas 1 ciclo).

---

## 5. Especificação e Esqueleto em Lean 4 (`Erdos64.lean`)

> **Instrução para o Agente de Verificação Lean 4:**  
> Extraia o bloco abaixo para `lean/Erdos64.lean` em um projeto Lake configurado com `Mathlib`. O objetivo inicial é validar que todas as definições e enunciados compilam sem erro de tipo (com `sorry` temporários) e, em seguida, eliminar os `sorry` na ordem: `Lemas 1–4` -> `Lemas 5–6` -> `Teorema 7` -> `Teoremas 8–10` -> `Teoremas 11–12`. Sempre que houver erro de compilação ou *goal state* travado, envie a mensagem exata do Lean de volta no chat.

~~~lean
import Mathlib

open SimpleGraph

namespace Erdos64

/-- Um grafo `G` contém um ciclo simples de comprimento `2^k` para algum `k ≥ 2`. -/
def HasPow2Cycle {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ (v : V) (p : G.Walk v v) (k : ℕ), 2 ≤ k ∧ p.IsCycle ∧ p.length = 2 ^ k

/-- Enunciado oficial do Problema #64 de Erdős (Conjectura de Erdős–Gyárfás). -/
def ErdosGyarfasConjecture : Prop :=
  ∀ (V : Type) [Fintype V] [Nonempty V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj],
    (∀ v : V, 3 ≤ G.degree v) → HasPow2Cycle G

/-- Um grafo finito simples é um contraexemplo à conjectura se tem δ(G) ≥ 3 e é livre de C_{2^k}. -/
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

/-- Lema 1: Todo contraexemplo mínimo é conexo. -/
theorem minimal_connected {V : Type} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmin : IsMinimalCounterexample G) : G.Connected := by
  sorry

/-- Lema 2: Em qualquer grafo livre de C_{2^k}, dois vértices distintos têm no máximo 1 vizinho comum. -/
theorem common_neighbors_le_one {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ HasPow2Cycle G) {u v : V} (huv : u ≠ v) :
    (G.commonNeighbors u v).toFinset.card ≤ 1 := by
  sorry

/-- Lema 4: Em um contraexemplo mínimo, vértices de grau ≥ 4 formam conjunto independente. -/
theorem high_degree_independent {V : Type} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmin : IsMinimalCounterexample G) {u v : V}
    (hu : 4 ≤ G.degree u) (hv : 4 ≤ G.degree v) : ¬ G.Adj u v := by
  sorry

/-! ### Rodada 2: Conectividade (Lema 5) -/

/-- Lema 5: Todo contraexemplo mínimo não possui pontes. -/
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

/-! ### Rodada 4: Pisos de Cubicidade (Teorema 10) -/

/-- Teorema 10a: Todo contraexemplo mínimo sem triângulos tem |V_3| ≥ (8/11) |V|. -/
theorem minimal_triangle_free_cubicity {V : Type} [Fintype V] [Nonempty V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmin : IsMinimalCounterexample G)
    (htf : G.CliqueFree 3) :
    8 * Fintype.card V ≤ 11 * (Finset.univ.filter (fun v : V => G.degree v = 3)).card := by
  sorry

/-! ### Rodada 5: Autorredução de K_3-fatores e C_5-fatores (Teoremas 11–12) -/

/-- Partição em ciclos de comprimento `d` (d-fator puro) em um grafo cúbico. -/
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
~~~

---

## 6. Plano Imediato para a Rodada 6

Ao retomar a pesquisa na **Rodada 6**, atacar prioritariamente:

1. **Fechar o $C_6$-fator bipartido:**
   * Formalizar primeiro que a simplificação $H_6^{\text{simp}}$ preserva $\delta \ge 3$ (ou classificar exatamente as multiplicidades de arestas paralelas em $H_6$).
   * Atacar a única obstrução de paridade restante ($b = 0$ e $a$ ímpar no levantamento de $C_{2^k}$), investigando se a 2-conectividade ou a existência de dois ciclos / caminhos alternantes em $H_6^{\text{simp}}$ força um ciclo $C_{2^k}$ fora dessa classe de paridade.
2. **Abrir a frente dos Grafos Cúbicos Hamiltonianos (extremo oposto dos 2-fatores):**
   * Mapear a aritmética modular das cordas cruzadas sobre um ciclo Hamiltoniano $C_n$ (como pares e triplas de cordas forçam ciclos de comprimentos combinados $2^k$).
   * Se necessário, projetar um script em Python/SAT específico para testar obstruções de cordas em $C_n$ (não força bruta em grafos gerais, mas busca de padrões de cordas livres de $C_{2^k}$).
3. **Ciclo paralelo de Lean 4:** Assim que o usuário retornar os primeiros logs de compilação de `Erdos64.lean`, fechar os `sorry` dos Lemas 1–5 e do Teorema 7.

---

## 7. Changelog de Sessões

* **v1.0 (21/11/2026 — Rodadas 1 a 5):** Criação do arquivo mestre. Consolidados Lemas 1–6, Teorema do Bloco Pinçado, Teorema 7 (Cacto de Triângulos), Teoremas 8–10 (Fronteira das Componentes e pisos $\frac{8}{11}n$ / $\frac{20}{27}n$), Teoremas 11–12 (Autorredução de $K_3$-fatores e $C_5$-fatores), mapa de becos sem saída e esqueleto inicial em Lean 4. Progresso em `11% / 100%`.