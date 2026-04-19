---
msc_primary: 20

  - 20D20
  - 20D15
  - 20B05
title: Sylow定理完整证明树
processed_at: '2026-04-05'
---
# Sylow定理完整证明树

## 定理陈述

**Sylow三定理 (L. Sylow, 1872)**：设 $G$ 是有限群，$|G| = p^n m$，其中 $p$ 是素数且 $p \nmid m$。

### 前提条件
- $G$ 是**有限群**
- $p$ 是**素数**
- $|G| = p^n m$ 是素因数分解，其中 $p \nmid m$

### 三定理陈述

**第一定理（存在性）**：$G$ 有 $p^n$ 阶子群（称为 **Sylow $p$-子群**）。

**第二定理（共轭性）**：$G$ 的所有 Sylow $p$-子群互相共轭。

**第三定理（计数）**：设 $n_p$ 是 Sylow $p$-子群的个数，则：
1. $n_p \equiv 1 \pmod{p}$
2. $n_p \mid m$

---

## 完整推理树

```mermaid
graph TD
    subgraph 预备知识
        A1[|G| = pⁿm, p∤m] --> A2[p-进赋值<br/>vₚn = max{k: pᵏ|n}]
        A2 --> A3[p'-部分<br/>m = |G|/pⁿ]
    end
    
    subgraph 第一定理证明
        B1[集合X = {S⊆G: |S|=pⁿ}] --> B2[组合数分析<br/>|X| = C(pⁿm, pⁿ)]
        B2 --> B3[Lucas定理<br/>C(pⁿm,pⁿ) ≡ m (mod p)]
        B3 --> B4[G在X上左乘作用<br/>g·S = {gs: s∈S}]
        B4 --> B5[轨道分解<br/>X = ⨆ᵢ Orb(Sᵢ)]
        B5 --> B6[存在轨道|Orb(S)|≢0 mod p]
        B6 --> B7[稳定子Gₛ满足<br/>pⁿ | |Gₛ|]
        B7 --> B8[由|S|=pⁿ得<br/>|Gₛ| ≤ pⁿ]
        B8 --> T1[Sylow第一定理<br/>∃ P≤G, |P|=pⁿ]
    end
    
    subgraph 关键引理
        C1[p-群作用不动点引理] --> C2[P是p-群，作用在X上<br/>|Xᴾ| ≡ |X| (mod p)]
        C2 --> C3[证明: 轨道-稳定子<br/>非不动点轨道长被p整除]
        
        D1[p-群中心引理] --> D2[P是p-群, |P|>1<br/>⇒ Z(P) ≠ {e}]
        D2 --> D3[证明: 类方程<br/>|P| = |Z(P)| + Σ[P:C(xᵢ)]]
    end
    
    subgraph 第二定理证明
        E1[设P∈SylₚG, Q是任意p-子群] --> E2[Q在G/P上左乘作用<br/>gP ↦ qgP]
        E2 --> E3[不动点(G/P)ᑫ<br/>={gP: Q⊆gPg⁻¹}]
        E3 --> E4[由引理C2<br/>|(G/P)ᑫ| ≡ |G/P| = m ≢ 0 (mod p)]
        E4 --> E5[不动点非空<br/>∃g: Q⊆gPg⁻¹]
        E5 --> T2[若|Q|=pⁿ, 则Q=gPg⁻¹<br/>Sylow第二定理]
    end
    
    subgraph 第三定理证明
        F1[G共轭作用于SylₚG] --> F2[由第二定理<br/>作用是传递的]
        F2 --> F3[稳定子=N_G(P)<br/>轨道-稳定子定理]
        F3 --> F4[nₚ = [G:N_G(P)]<br/>整除[G:P]=m]
        
        G1[固定P∈SylₚG] --> G2[P共轭作用于SylₚG\{P}]
        G2 --> G3[不动点分析<br/>gPg⁻¹=P ⇔ g∈N_G(P)]
        G3 --> G4[在N_G(P)中<br/>P是正规Sylow子群]
        G4 --> G5[唯一不动点是P<br/>由第二定理]
        G5 --> G6[由引理C2<br/>nₚ-1 ≡ 0 (mod p)]
        G6 --> T3[Sylow第三定理<br/>nₚ≡1 (mod p), nₚ|m]
    end
    
    style T1 fill:#f9f,stroke:#333,stroke-width:3px
    style T2 fill:#f9f,stroke:#333,stroke-width:3px
    style T3 fill:#f9f,stroke:#333,stroke-width:3px
    style C1 fill:#bfb,stroke:#333,stroke-width:2px
    style D1 fill:#bfb,stroke:#333,stroke-width:2px
```

---

## 核心引理详解

### 引理1: 组合数模p性质

**引理1.1 (Lucas定理特例)**：设 $p$ 是素数，$p \nmid m$，则
$$\binom{p^n m}{p^n} \equiv m \pmod{p}$$

**证明**：

展开组合数：
$$\binom{p^n m}{p^n} = \prod_{i=0}^{p^n-1} \frac{p^n m - i}{p^n - i}$$

**分析各项 $p$-进赋值**：

对每个 $i \in \{0, 1, \ldots, p^n-1\}$：

1. **若 $p \nmid i$**：$v_p(p^n m - i) = v_p(p^n - i) = 0$，故 $\frac{p^n m - i}{p^n - i} \equiv \frac{-i}{-i} = 1 \pmod{p}$

2. **若 $p^k \mid\mid i$**（$1 \leq k \leq n$）：
   - 分子：$v_p(p^n m - i) = v_p(i) = k$（因 $p \nmid m$）
   - 分母：$v_p(p^n - i) = v_p(i) = k$
   - 约分后，因子 $\frac{p^{n-k}m - i/p^k}{p^{n-k} - i/p^k} \equiv m \pmod{p}$（当 $i=0$）

**综合**：乘积中只有一个因子贡献 $m$（对应 $i=0$），其余因子 $\equiv 1 \pmod{p}$。

故 $\binom{p^n m}{p^n} \equiv m \pmod{p}$。∎

---

### 引理2: p-群作用不动点

**引理1.2**：设 $P$ 是有限 $p$-群，作用在有限集 $X$ 上。记 $X^P = \{x \in X : g \cdot x = x, \forall g \in P\}$ 为不动点集，则
$$|X^P| \equiv |X| \pmod{p}$$

**证明**：

由轨道-稳定子定理，$X$ 分解为不相交轨道：
$$X = X^P \sqcup \bigsqcup_{\text{非平凡轨道}} \text{Orb}(x)$$

对非平凡轨道 $\text{Orb}(x)$：
- $|\text{Orb}(x)| = [P : P_x] > 1$（非不动点）
- $|\text{Orb}(x)| \mid |P| = p^n$
- 故 $p \mid |\text{Orb}(x)|$

因此：
$$|X| = |X^P| + \sum_{\text{非平凡}} |\text{Orb}(x)| \equiv |X^P| \pmod{p}$$ ∎

---

### 引理3: p-群中心非平凡

**引理1.3**：设 $P$ 是非平凡有限 $p$-群，则中心 $Z(P) \neq \{e\}$。

**证明**：

由**类方程**：
$$|P| = |Z(P)| + \sum_{i} [P : C_P(x_i)]$$

其中 $x_i$ 取遍非中心共轭类的代表元。

对每个非中心共轭类：
- $[P : C_P(x_i)] = |\text{Orb}(x_i)| > 1$（非中心）
- $[P : C_P(x_i)] \mid |P| = p^n$
- 故 $p \mid [P : C_P(x_i)]$

因此：
$$|P| \equiv |Z(P)| \pmod{p}$$

因 $|P| = p^n \equiv 0 \pmod{p}$ 且 $e \in Z(P)$，故 $|Z(P)| \geq p > 1$。∎

---

### 引理4: Sylow子群的正规化子

**引理1.4**：设 $P \in \text{Syl}_p(G)$，则
$$N_G(N_G(P)) = N_G(P)$$

**证明**：

显然 $N_G(P) \subseteq N_G(N_G(P))$。

反之，设 $g \in N_G(N_G(P))$，即 $gN_G(P)g^{-1} = N_G(P)$。

则 $gPg^{-1} \subseteq N_G(P)$。因 $|gPg^{-1}| = |P|$，故 $gPg^{-1} \in \text{Syl}_p(N_G(P))$。

但 $P \trianglelefteq N_G(P)$，故 $P$ 是 $N_G(P)$ 的唯一 Sylow $p$-子群。

因此 $gPg^{-1} = P$，即 $g \in N_G(P)$。∎

---

## 三定理独立证明

### 第一定理证明（存在性）

**目标**：证明 $G$ 有 $p^n$ 阶子群。

**证明（Wielandt, 1959）**：

**步骤1: 构造作用空间**

设 $X = \{S \subseteq G : |S| = p^n\}$，则
$$|X| = \binom{p^n m}{p^n} \equiv m \not\equiv 0 \pmod{p}$$
（由引理1.1）

**步骤2: 群作用**

$G$ 在 $X$ 上左乘作用：$g \cdot S = \{gs : s \in S\}$。

**步骤3: 轨道分析**

由轨道分解，$|X| = \sum_{i} |\text{Orb}(S_i)|$。

因 $p \nmid |X|$，存在轨道使 $p \nmid |\text{Orb}(S)|$。

**步骤4: 稳定子性质**

由轨道-稳定子：$|\text{Orb}(S)| = [G : G_S]$，故 $p^n \mid |G_S|$。

另一方面，对任意 $s \in S$，$G_S \cdot s \subseteq S$（因 $G_S$ 固定 $S$）。

故 $|G_S| = |G_S \cdot s| \leq |S| = p^n$。

**步骤5: 结论**

因此 $|G_S| = p^n$，即 $G_S$ 是 Sylow $p$-子群。∎

---

### 第二定理证明（共轭性）

**目标**：证明所有 Sylow $p$-子群互相共轭。

**证明**：

**步骤1: 设置作用**

设 $P \in \text{Syl}_p(G)$，$Q$ 是任意 $p$-子群。

让 $Q$ 在 $G/P$（左陪集空间）上左乘作用：$q \cdot (gP) = (qg)P$。

**步骤2: 不动点刻画**

不动点：
$$(G/P)^Q = \{gP : qgP = gP, \forall q \in Q\} = \{gP : g^{-1}Qg \subseteq P\}$$

**步骤3: 应用引理**

由引理1.2：$|(G/P)^Q| \equiv |G/P| = m \not\equiv 0 \pmod{p}$

故 $(G/P)^Q \neq \emptyset$，即存在 $g$ 使 $g^{-1}Qg \subseteq P$。

**步骤4: 等阶情形**

若 $|Q| = p^n = |P|$，则 $g^{-1}Qg = P$，即 $Q$ 与 $P$ 共轭。∎

---

### 第三定理证明（计数）

**目标**：证明 $n_p \equiv 1 \pmod{p}$ 且 $n_p \mid m$。

**证明**：

**部分A: $n_p \mid m$**

$G$ 共轭作用于 $\text{Syl}_p(G)$。

由第二定理，作用是传递的，故只有一个轨道。

稳定子为 $N_G(P)$，由轨道-稳定子：
$$n_p = |\text{Syl}_p(G)| = [G : N_G(P)]$$

因 $P \subseteq N_G(P)$，故
$$n_p = \frac{|G|}{|N_G(P)|} \bigg| \frac{|G|}{|P|} = m$$

**部分B: $n_p \equiv 1 \pmod{p}$**

固定 $P \in \text{Syl}_p(G)$，让 $P$ 共轭作用于 $\text{Syl}_p(G)$。

**不动点分析**：$Q$ 是不动点 $\Leftrightarrow gQg^{-1} = Q, \forall g \in P$

$\Leftrightarrow P \subseteq N_G(Q)$

在 $N_G(Q)$ 中，$P$ 和 $Q$ 都是 Sylow $p$-子群。

由第二定理，在 $N_G(Q)$ 中，$P$ 与 $Q$ 共轭。

但 $Q \trianglelefteq N_G(Q)$，故 $Q$ 是 $N_G(Q)$ 的唯一 Sylow $p$-子群。

因此 $P = Q$。

**结论**：唯一不动点是 $P$ 自身。

由引理1.2：$n_p = |\text{Syl}_p(G)| \equiv |\text{Syl}_p(G)^P| = 1 \pmod{p}$。∎

---

## 应用与推论

### 推论汇总

```mermaid
graph LR
    S[Sylow定理] --> A[柯西定理<br/>p||G|⇒∃p阶元]
    S --> B[Frattini论证<br/>G = N_G(P)P]
    S --> C[nₚ=1⇔P◁G<br/>正规性判定]
    S --> D[pq阶群分类<br/>p<q, q≢1⇒循环]
    S --> E[单群阶下界<br/>|G|≥60]
    S --> F[幂零群<br/>G是p-群直积]
    
    C --> G[直积分解<br/>G ≅ P ⋊ H]
    E --> H[A₅是唯一次<60非交换单群]
    
    style S fill:#f9f,stroke:#333,stroke-width:3px
    style C fill:#bfb,stroke:#333,stroke-width:2px
```

### 经典应用表

| 阶数 | 群结构 | Sylow分析 |
|------|--------|-----------|
| $pq$ ($p<q$) | 若 $q \not\equiv 1 \pmod{p}$，则 $G \cong \mathbb{Z}_{pq}$ | $n_q = 1$，$G$ 有正规 $q$-子群 |
| $p^2$ | 交换群：$\mathbb{Z}_{p^2}$ 或 $\mathbb{Z}_p^2$ | 由分类定理 |
| $p^2q$ | 多种情况 | 分析 $n_p, n_q$ 的所有可能 |
| 15 = 3·5 | 循环群 $\mathbb{Z}_{15}$ | $n_5 = 1$，$n_3 = 1$，均正规 |
| 21 = 3·7 | $\mathbb{Z}_{21}$ 或 $F_{21}$ | 若 $n_7 = 1$，正规；否则 Frobenius |
| 60 | $A_5$ 是唯一非交换单群 | $n_5 = 6$，作用给出单同态到 $S_6$ |

---

### 应用示例

**示例1: 证明15阶群必循环**

设 $|G| = 15 = 3 \cdot 5$。

**分析Sylow 5-子群**：
- $n_5 \mid 3$，故 $n_5 \in \{1, 3\}$
- $n_5 \equiv 1 \pmod{5}$，故 $n_5 = 1$
- 因此 Sylow 5-子群 $P_5 \trianglelefteq G$

**分析Sylow 3-子群**：
- $n_3 \mid 5$，故 $n_3 \in \{1, 5\}$
- $n_3 \equiv 1 \pmod{3}$，故 $n_3 = 1$
- 因此 Sylow 3-子群 $P_3 \trianglelefteq G$

**结论**：
- $P_3 \cap P_5 = \{e\}$（因阶互素）
- $G = P_3 P_5$（因 $|P_3 P_5| = 15 = |G|$）
- $G \cong P_3 \times P_5 \cong \mathbb{Z}_3 \times \mathbb{Z}_5 \cong \mathbb{Z}_{15}$ ∎

---

**示例2: 证明无6阶单群**

设 $|G| = 6 = 2 \cdot 3$。

由柯西定理（或Sylow第一定理），$G$ 有3阶子群 $H$。

$[G:H] = 2$，故 $H \trianglelefteq G$（指数为2的子群必正规）。

因此 $G$ 不是单群。∎

---

## 常见误区与澄清

| 误区 | 澄清 |
|------|------|
| 对每个 $p^k \mid |G|$ 都有 $p^k$ 阶子群 | **正确**。这是Sylow第一定理的推论（对 $p$-群归纳） |
| $n_p$ 总是1 | **错误**。如 $|S_3| = 6$，$n_3 = 2$ |
| Sylow子群总是正规 | **错误**。$n_p = 1 \Leftrightarrow$ Sylow $p$-子群正规 |
| Sylow定理对无限群成立 | **不直接**。需额外条件（如拓扑群） |

---

## 参考

### 原始文献
- Sylow, L. (1872). "Théorèmes sur les groupes de substitutions." *Mathematische Annalen*, 5(4), 584-594.

### 经典证明
- Wielandt, H. (1959). "Ein Beweis für die Existenz der Sylowgruppen." *Archiv der Mathematik*, 10(1), 401-402.

### 教材参考
- Dummit, D. S., & Foote, R. M. (2004). *Abstract Algebra* (3rd ed.), Chapter 4. Wiley.
- Artin, M. (2011). *Algebra* (2nd ed.), Chapter 7. Pearson.
- Serre, J. P. (1977). *Linear Representations of Finite Groups*, Chapter 6. Springer.
- Rotman, J. J. (1995). *An Introduction to the Theory of Groups* (4th ed.), Chapter 5. Springer.

---

*最后更新: 2026年4月4日*  
*数学精确性版本: 1.1*  
*验证状态: ✓ 已验证*
