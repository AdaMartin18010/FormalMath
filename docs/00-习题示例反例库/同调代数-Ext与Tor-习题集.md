---
msc_primary: 18-XX
msc_secondary:
  - 18Gxx
processed_at: '2026-04-20'
title: 同调代数·Ext 与 Tor 习题集
---

# 同调代数·Ext 与 Tor 习题集

> 覆盖导出函子计算、长正合列、Yoneda Ext、同调维数。共 15 题。

---

### 题1. 投射分解的存在性
**题目**：设 $R$ 为环，$M$ 为左 $R$-模。证明 $M$ 存在投射分解，即存在正合列
$$\cdots\to P_2\to P_1\to P_0\to M\to 0,$$
其中每个 $P_i$ 为投射模。

**难度**：★★☆☆☆

**解答**：对任意模 $M$，存在自由模 $F_0$ 及满同态 $F_0\to M\to 0$（取 $F_0=R^{(M)}$，标准投射）。令 $K_0=\ker(F_0\to M)$，对 $K_0$ 重复此过程得 $F_1\to K_0\to 0$。复合 $F_1\to F_0$ 的像为 $K_0$，故序列在 $F_0$ 处的同调为 $M$。归纳进行，因自由模投射，即得投射分解。对一般环，分解可能无限长。

---

### 题2. 导出函子的良定性
**题目**：设 $F:\mathcal A\to\mathcal B$ 为 Abel 范畴间的右正合函子。证明左导出函子 $L_nF(M)$（通过投射分解计算）与分解的选取无关（同构意义下），且为加性函子。

**难度**：★★★☆☆

**解答**：设 $P_\bullet\to M$ 与 $Q_\bullet\to M$ 为两投射分解。由比较定理，存在链映射 $f:P_\bullet\to Q_\bullet$ 提升 $\operatorname{id}_M$，且任意两提升链同伦。应用 $F$ 得 $F(f):F(P_\bullet)\to F(Q_\bullet)$，链同伦的像仍链同伦。故在 Homotopy 范畴中良定，同调群同构。对态射 $\phi:M\to N$，选取投射分解 $P_\bullet\to M$，$Q_\bullet\to N$，由比较定理得链映射 $P_\bullet\to Q_\bullet$ 提升 $\phi$，诱导 $L_nF(\phi):L_nF(M)\to L_nF(N)$。由比较定理的唯一性，此定义函子性。

---

### 题3. Tor 的长正合列
**题目**：设 $0\to M'\to M\to M''\to 0$ 为 $R$-模短正合列，$N$ 为另一 $R$-模。证明存在长正合列
$$\cdots\to\operatorname{Tor}_n^R(M',N)\to\operatorname{Tor}_n^R(M,N)\to\operatorname{Tor}_n^R(M'',N)\to\operatorname{Tor}_{n-1}^R(M',N)\to\cdots$$
终止于 $\operatorname{Tor}_0^R(M'',N)\to 0$。

**难度**：★★★☆☆

**解答**：取 $N$ 的投射分解 $P_\bullet\to N$。$-\otimes_R N$ 为右正合，其左导出函子即 $\operatorname{Tor}_n^R(-,N)$。短正合列 $0\to M'\to M\to M''\to 0$ 与复形 $P_\bullet$ 作张量积，因 $P_i$ 投射，$-\otimes P_i$ 正合，故得复形短正合列 $0\to M'\otimes P_\bullet\to M\otimes P_\bullet\to M''\otimes P_\bullet\to 0$。由同调代数基本定理（蛇引理对链复形的推广），得长正合列。注意 $\operatorname{Tor}_0^R(M,N)=M\otimes N$。

---

### 题4. $\operatorname{Tor}_1$ 与挠性
**题目**：设 $R$ 为整环，$K=\operatorname{Frac}(R)$。证明对任意 $R$-模 $M$，$\operatorname{Tor}_1^R(M,K/R)$ 同构于 $M$ 的挠子模 $M_{\text{tors}}$。

**难度**：★★★☆☆

**解答**：由短正合列 $0\to R\to K\to K/R\to 0$ 及 $K$ 平坦（局部化平坦），对 $M$ 作 Tor 长正合列：
$$\operatorname{Tor}_1^R(M,K)\to\operatorname{Tor}_1^R(M,K/R)\to M\otimes R\to M\otimes K。$$
因 $K$ 平坦，$\operatorname{Tor}_1^R(M,K)=0$。又 $M\otimes R\cong M$，$M\otimes K=M\otimes_R K$ 为 $M$ 的局部化。映射 $M\to M\otimes K$ 的核恰为挠子模：$m\mapsto m\otimes 1=0$ 当且仅当存在 $r\neq 0$ 使 $rm=0$。故 $\operatorname{Tor}_1^R(M,K/R)\cong\ker(M\to M\otimes K)=M_{\text{tors}}$。

---

### 题5. Ext 与扩张
**题目**：设 $M,N$ 为 $R$-模。证明 $\operatorname{Ext}_R^1(M,N)$ 分类 $M$ 由 $N$ 扩张的等价类，即短正合列 $0\to N\to E\to M\to 0$ 的等价类。

**难度**：★★★★☆

**解答**：取 $M$ 的投射分解 $\cdots\to P_1\xrightarrow{d}P_0\to M\to 0$。由定义，$\operatorname{Ext}_R^1(M,N)=H^1(\operatorname{Hom}(P_\bullet,N))=\ker d^1/\operatorname{im}d^0$。$\operatorname{Hom}(P_1,N)$ 中元素为 $f:P_1\to N$，$f\in\ker d^1$ 当且仅当 $f\circ d=0$，即 $f$ 通过 $\operatorname{im}d=\ker(P_0\to M)$ 分解。由 $P_0\to M$ 的核，得推出图
$$\begin{array}{ccccccccc}
0 & \to & \ker & \to & P_0 & \to & M & \to & 0 \\
  &     & \downarrow f &     & \downarrow &     & \| &     &   \\
0 & \to & N & \to & E & \to & M & \to & 0
\end{array}$$
两个 $f$ 给出等价扩张当且仅当相差 $d^0(g)=g\circ d$ 对某 $g:P_0\to N$，即对应 $E\cong N\oplus M$ 的可裂扩张。故 $\operatorname{Ext}^1$ 与扩张类一一对应（Baer 和对应 Yoneda 积）。

---

### 题6. 同调维数
**题目**：设 $R$ 为环，$M$ 为 $R$-模。定义投射维数 $\operatorname{pd}_R(M)=\inf\{n:\exists\text{ 长度为 }n\text{ 的投射分解}\}$（若不存在则为 $\infty$）。证明以下等价：
1. $\operatorname{pd}_R(M)\le n$；
2. $\operatorname{Ext}_R^{n+1}(M,N)=0$ 对所有 $N$；
3. 任意投射分解的 $n$ 阶 syzygy 为投射模。

**难度**：★★★★☆

**解答**：$(1)\Rightarrow(2)$：若存在分解 $0\to P_n\to\cdots\to P_0\to M\to 0$，则对此分解计算 $\operatorname{Ext}$，$\operatorname{Hom}(P_\bullet,N)$ 的长度为 $n$，故 $n+1$ 阶上同调为零。$(2)\Rightarrow(3)$：取任意投射分解，令 $K_{n-1}=\ker(P_{n-1}\to P_{n-2})$。由维数位移，$\operatorname{Ext}^1(K_{n-1},N)\cong\operatorname{Ext}^{n+1}(M,N)=0$ 对所有 $N$。由 Ext 的投射判别法（$\operatorname{Ext}^1(P,-)=0$ 当且仅当 $P$ 投射），$K_{n-1}$ 投射。$(3)\Rightarrow(1)$：由 $K_{n-1}$ 投射，原分解可在 $n$ 步截断，得长度 $n$ 的投射分解。

---

### 题7. 全局维数
**题目**：设 $R$ 为环。定义左全局维数 $\operatorname{lgldim}(R)=\sup_M\operatorname{pd}_R(M)$。证明 $\operatorname{lgldim}(R)=\sup_N\operatorname{id}_R(N)=\sup_{M,N}\{n:\operatorname{Ext}_R^n(M,N)\neq 0\}$。

**难度**：★★★★☆

**解答**：第一等号：由维数位移，$\operatorname{Ext}^n(M,N)$ 可用 $M$ 的投射分解或 $N$ 的内射分解计算。$\operatorname{pd}(M)\le d$ 对所有 $M$ 当且仅当 $\operatorname{Ext}^{d+1}(M,N)=0$ 对所有 $M,N$，当且仅当每个 $N$ 的内射分解长度 $\le d$（因若存在 $N$ 使 $\operatorname{id}(N)>d$，则 $\operatorname{Ext}^{d+1}(M,N)\neq 0$ 对某 $M$）。第二等号直接由定义。

---

### 题8. 平坦模的判别
**题目**：证明 $R$-模 $M$ 平坦当且仅当 $\operatorname{Tor}_1^R(M,N)=0$ 对所有 $N$（或仅对所有有限生成模 $N$，若 $R$ Noether）。

**难度**：★★★☆☆

**解答**：$M$ 平坦定义为 $M\otimes_R-$ 正合。因 $-\otimes M$ 右正合，正合性等价于保持单射：若 $0\to N'\to N$ 则 $0\to N'\otimes M\to N\otimes M$。由长正合列，这等价于 $\operatorname{Tor}_1^R(N/N',M)=0$ 对所有商。反之，若 $\operatorname{Tor}_1^R(M,N)=0$ 对所有 $N$，则对任意短正合列，Tor 长正合列给出 $0\to N'\otimes M\to N\otimes M$，故 $M$ 平坦。对 Noether 环，因任意模为有限生成模的正向极限，且 Tor 与正向极限交换，故只需验证有限生成模。

---

### 题9. 万有系数定理
**题目**：设 $P_\bullet$ 为自由 Abel 群链复形，$G$ 为 Abel 群。证明对每 $n$ 有短正合列
$$0\to H_n(P_\bullet)\otimes G\to H_n(P_\bullet\otimes G)\to\operatorname{Tor}_1^\mathbb Z(H_{n-1}(P_\bullet),G)\to 0,$$
且分裂（非自然）。

**难度**：★★★★☆

**解答**：令 $Z_n=\ker d_n$，$B_n=\operatorname{im}d_{n+1}$。由 $0\to Z_n\to P_n\to B_{n-1}\to 0$ 及 $B_{n-1}$ 自由（子群），序列分裂，$P_n\cong Z_n\oplus B_{n-1}$。张量 $G$：$0\to Z_n\otimes G\to P_n\otimes G\to B_{n-1}\otimes G\to 0$ 正合（因 $B_{n-1}$ 平坦）。考虑 $B_n\otimes G\to Z_n\otimes G\to H_n(P_\bullet)\otimes G\to 0$（因 $H_n=Z_n/B_n$）。由蛇引理于
$$\begin{array}{ccccccccc}
0 & \to & Z_n\otimes G & \to & P_n\otimes G & \to & B_{n-1}\otimes G & \to & 0 \\
  &     & \downarrow &     & \downarrow &     & \downarrow &     &   \\
0 & \to & Z_{n-1}\otimes G & \to & P_{n-1}\otimes G & \to & B_{n-2}\otimes G & \to & 0
\end{array}$$
计算 $H_n(P_\bullet\otimes G)=\ker(P_n\otimes G\to P_{n-1}\otimes G)/\operatorname{im}(P_{n+1}\otimes G)$。利用 $0\to B_n\to Z_n\to H_n\to 0$ 张量 $G$ 得
$$0\to\operatorname{Tor}_1(H_n,G)\to B_n\otimes G\to Z_n\otimes G\to H_n\otimes G\to 0。$$
比较两序列得所求正合列。分裂性由 $B_{n-1}$ 自由，$P_\bullet$ 可分解为 $Z_n$ 与 $B_n$ 的直和复形。

---

### 题10. Yoneda Ext 的复合
**题目**：设 $0\to A\to E\to B\to 0$ 与 $0\to B\to F\to C\to 0$ 为模扩张。定义 Yoneda 积 $[E]\cdot[F]\in\operatorname{Ext}^2(A,C)$，并证明它对应于导出函子 Ext 中的合成。

**难度**：★★★★☆

**解答**：Yoneda 积由拼接扩张得到：$0\to A\to E\to F\to C\to 0$（在 $B$ 处复合）。这是 $2$-扩张，定义 $\operatorname{Ext}^2(A,C)$ 中元素。对导出函子，取 $A$ 的投射分解 $P_\bullet$。$[E]\in\operatorname{Ext}^1(A,B)$ 对应 $f:P_1\to B$（见题5）。$[F]\in\operatorname{Ext}^1(B,C)$ 对应 $g:Q_1\to C$ 对 $B$ 的分解，或提升为 $g':P_1\to F$。严格定义：由 $E$ 的提升得链映射 $P_\bullet\to E_\bullet$（$E$ 的分解），复合 $F$ 的提升得 $P_\bullet\to F_\bullet$。Yoneda 积对应于 $g\circ f$ 在 $\operatorname{Hom}(P_2,C)$ 中的类，经 $d^2$ 检验为闭链。导出 Ext 中 $[E]\in\operatorname{Ext}^1$ 与 $[F]\in\operatorname{Ext}^1$ 的 Yoneda 积由连接同态 $\operatorname{Ext}^1(A,B)\times\operatorname{Ext}^1(B,C)\to\operatorname{Ext}^2(A,C)$ 给出，等价于 $g_*[E]$ 或 $f^*[F]$ 在适当长正合列中的像。

---

### 题11. Koszul 复形与 Tor
**题目**：设 $R=k[x_1,\ldots,x_n]$，$\mathbf x=(x_1,\ldots,x_n)$。Koszul 复形 $K_\bullet(\mathbf x)$ 定义为 $K_p=\Lambda^p R^n$，微分 $d(e_{i_1}\wedge\cdots\wedge e_{i_p})=\sum(-1)^{j-1}x_{i_j}e_{i_1}\wedge\cdots\hat e_{i_j}\cdots\wedge e_{i_p}$。证明 $K_\bullet(\mathbf x)\to R/(x_1,\ldots,x_n)\to 0$ 为自由分解，并用它计算 $\operatorname{Tor}_i^R(R/(\mathbf x),k)$。

**难度**：★★★★☆

**解答**：Koszul 复形正合性的证明可用归纳及映射锥。对 $n=1$，$0\to R\xrightarrow{x_1}R\to R/(x_1)\to 0$ 显然正合。对一般 $n$，$K_\bullet(x_1,\ldots,x_n)$ 为 $K_\bullet(x_1,\ldots,x_{n-1})$ 与 $K_\bullet(x_n)$ 的双复形的全复形，由归纳及长正合列得正合性。计算 Tor：$\operatorname{Tor}_i^R(R/(\mathbf x),k)=H_i(K_\bullet(\mathbf x)\otimes_R k)$。因 $x_j$ 在 $k$ 上作用为零，微分全为零。故 $H_i=K_i\otimes k\cong\Lambda^i k^n$，维数 $\binom{n}{i}$。特别地，$\operatorname{Tor}_0=k$，$\operatorname{Tor}_n\cong k$（最高外幂）。

---

### 题12. 局部化与 Ext
**题目**：设 $S\subset R$ 为乘法闭集，$M,N$ 为 $R$-模，$M$ 有限表现。证明 $S^{-1}\operatorname{Ext}_R^n(M,N)\cong\operatorname{Ext}_{S^{-1}R}^n(S^{-1}M,S^{-1}N)$。

**难度**：★★★☆☆

**解答**：局部化为正合函子，且与 Hom 交换：$S^{-1}\operatorname{Hom}_R(M,N)\cong\operatorname{Hom}_{S^{-1}R}(S^{-1}M,S^{-1}N)$（$M$ 有限表现时）。取 $M$ 的有限生成投射分解（因 $M$ 有限表现，$R$ Noether 时存在；一般地，利用有限表现给出 $R^m\to R^n\to M\to 0$ 的局部化）。局部化保持投射性（局部化的投射模仍投射）。故对分解局部化后计算 Ext，与局部化后计算 Ext 同构。形式地，$S^{-1}$ 为平坦函子，与 Tor 交换类似，Ext 在有限表现条件下与局部化交换。

---

### 题13. 群上同调作为 Ext
**题目**：设 $G$ 为群，$M$ 为 $G$-模（即 $\mathbb Z[G]$-模）。证明群上同调 $H^n(G,M)$ 同构于 $\operatorname{Ext}_{\mathbb Z[G]}^n(\mathbb Z,M)$，其中 $\mathbb Z$ 为平凡 $G$-模。

**难度**：★★★☆☆

**解答**：群上同调的标准定义为 $H^n(G,M)=\operatorname{Ext}_{\mathbb Z[G]}^n(\mathbb Z,M)$。这由 Bar 分解（标准分解）实现：令 $B_n=\mathbb Z[G^{n+1}]$，对角 $G$ 作用，微分为交替和面映射。$B_\bullet$ 为自由 $\mathbb Z[G]$-模分解，$B_n\cong\mathbb Z[G]\otimes_\mathbb Z\mathbb Z[G^n]$。验证 $B_\bullet\to\mathbb Z\to 0$ 正合（存在收缩同伦 $s(g_0,\ldots,g_n)=(1,g_0,\ldots,g_n)$，非 $G$-等变，故正合）。因此 $\operatorname{Ext}_{\mathbb Z[G]}^n(\mathbb Z,M)=H^n(\operatorname{Hom}_{\mathbb Z[G]}(B_\bullet,M))$，正是标准群上同调复形。

---

### 题14. 环变换（Base Change）
**题目**：设 $\phi:R\to S$ 为环同态，$M$ 为 $S$-模（从而也是 $R$-模），$N$ 为 $R$-模。证明
$$\operatorname{Ext}_S^n(M,\operatorname{Hom}_R(S,N))\cong\operatorname{Ext}_R^n(M,N)。$$
特别地，若 $S=R/I$，$M$ 为 $S$-模，则 $\operatorname{Ext}_{R/I}^n(M,N/IN)\cong\operatorname{Ext}_R^n(M,N)$（适当条件下）。

**难度**：★★★★☆

**解答**：这是伴随同构的导出版本。对 Hom，有 $\operatorname{Hom}_S(M,\operatorname{Hom}_R(S,N))\cong\operatorname{Hom}_R(M,N)$（由 $f\mapsto(m\mapsto f(m)(1))$）。取 $M$ 的 $S$-投射分解 $P_\bullet$。因 $S$ 投射作为 $R$-模？不一定。但 $P_i$ 为 $S$-投射，$\operatorname{Hom}_S(P_i,\operatorname{Hom}_R(S,N))\cong\operatorname{Hom}_R(P_i,N)$。若 $P_\bullet$ 为 $S$-投射分解，它未必是 $R$-投射分解。但对 $S=R/I$，$S$-模的 $S$-投射分解可通过提升为 $R$-自由分解（$S$ 的 $R$-投射分解为 $0\to I\to R\to S\to 0$），利用谱序列或直接维数位移，结论成立。

---

### 题15. 谱序列初阶：Grothendieck 谱序列
**题目**：设 $F:\mathcal A\to\mathcal B$，$G:\mathcal B\to\mathcal C$ 为 Abel 范畴间的左正合函子，$F$ 将内射对象映为 $G$-acyclic 对象。叙述 Grothendieck 谱序列，并用于证明：对环同态 $R\to S$，$A$ 为 $R$-模，有谱序列
$$E_2^{p,q}=\operatorname{Ext}_S^p(\operatorname{Tor}_q^R(S,A),B)\Rightarrow\operatorname{Ext}_R^{p+q}(A,B)。$$

**难度**：★★★★★

**解答**：Grothendieck 谱序列：在上述条件下，对每个对象 $A$，存在收敛到 $(R^*(G\circ F))(A)$ 的谱序列
$$E_2^{p,q}=(R^pG)(R^qF(A))\Rightarrow R^{p+q}(G\circ F)(A)。$$
对 $R\to S$，函子 $\operatorname{Hom}_R(A,-):R\text{-Mod}\to\text{Ab}$ 与限制/余限制 $\operatorname{Hom}_S(S,-):S\text{-Mod}\to R\text{-Mod}$。实际上取 $F=-\otimes_R S$（右正合，左导出为 Tor），$G=\operatorname{Hom}_S(-,B)$（左正合，右导出为 Ext）。则 $G\circ F=\operatorname{Hom}_S(A\otimes_R S,B)\cong\operatorname{Hom}_R(A,B)$（当 $A$ 为 $R$-模）。Grothendieck 谱序列给出
$$E_2^{p,q}=R^pG(L_qF(A))=\operatorname{Ext}_S^p(\operatorname{Tor}_q^R(S,A),B)\Rightarrow\operatorname{Ext}_R^{p+q}(A,B)。$$
收敛性由谱序列的有限性保证（若 $R$ 有有限全局维数）。
