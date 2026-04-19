---
msc_primary: 55A99
university: Princeton
synonym: [Spectral Sequence, Leray-Serre谱序列, Adams谱序列]
type: 定义
level: L3-理论建构层
difficulty: ⭐⭐⭐⭐⭐
concept_dependency: [同调代数, 滤过, 分次模]
prerequisite_concepts: [同调群, 正合序列, 分次代数]
prerequisite_theorems: [长正合序列, 双复形]
course_context: MAT 365 Topology
msc2010: [55T05, 55T10, 55T15]
related_concepts: [纤维化, 滤过, 收敛]
---

# AT-PN-009: 谱序列 (Spectral Sequence)

> **来源**: Princeton MAT 365 (Topology) | Hatcher Chapter 5 (Draft)
> **级别**: 本科高阶/研究生初级
> **领域**: 代数拓扑 · 同伦论进阶

---

## 定义

### 谱序列的定义

**定义**：**谱序列**（spectral sequence）是一族 $(E^r, d^r)_{r \geq r_0}$，其中：

1. $E^r = \{E^r_{p,q}\}$ 是**双分次**Abel群（或模），$p, q \in \mathbb{Z}$
2. $d^r: E^r_{p,q} \to E^r_{p-r, q+r-1}$ 是**微分**，满足 $d^r \circ d^r = 0$
3. $E^{r+1} = H(E^r, d^r) = \ker d^r / \text{im } d^r$（同调）

**示意图**（$E^2$ 页）：

$$
\begin{array}{c|cccc}
q & E^2_{0,2} & E^2_{1,2} & E^2_{2,2} & \cdots \\
\hline
1 & E^2_{0,1} & E^2_{1,1} & E^2_{2,1} & \cdots \\
0 & E^2_{0,0} & E^2_{1,0} & E^2_{2,0} & \cdots \\
\hline
 & 0 & 1 & 2 & p
\end{array}
$$

### 收敛

**定义**：谱序列**收敛**到分次群 $H_*$，记作 $E^r \Rightarrow H_*$，如果：

- 对每个 $n$，存在滤过 $0 = F_{-1}H_n \subset F_0H_n \subset \cdots \subset H_n$
- $E^\infty_{p,q} \cong F_pH_{p+q}/F_{p-1}H_{p+q}$

通常 $H_n$ 是某个空间的同调。

### 常见谱序列

| 谱序列 | $E^2$ 页 | 收敛到 |
|--------|---------|--------|
| **Leray-Serre** | $H_p(B; H_q(F))$ | $H_{p+q}(E)$ |
| **Leray** | $H^p(X, \mathcal{H}^q)$ | $H^{p+q}(X, \mathcal{F})$ |
| **Lyndon-Hochschild-Serre** | $H_p(G/N; H_q(N))$ | $H_{p+q}(G)$ |
| **Adams** | $Ext_{A}^{s,t}(\mathbb{Z}/2, \mathbb{Z}/2)$ | $\pi_{t-s}^S$（稳定同伦群） |
| **Atiyah-Hirzebruch** | $H_p(X; K_q(*))$ | $K_{p+q}(X)$ |

---

## 例子

### 例1：Serre谱序列（纤维化）

**设定**：纤维化 $F \to E \xrightarrow{p} B$，$B$ 单连通。

**Serre谱序列**：$E^2_{p,q} = H_p(B; H_q(F)) \Rightarrow H_{p+q}(E)$

**应用**：计算环路空间 $\Omega S^n$ 的同调。

对纤维化 $\Omega S^n \to PS^n \to S^n$（$PS^n$ 可缩）：

- $E^2_{0,0} = \mathbb{Z}$，$E^2_{n, k(n-1)} = \mathbb{Z}$
- 微分 $d^n$ 非平凡
- 结果：$H_k(\Omega S^n) = \mathbb{Z}$ 对 $k$ 是 $(n-1)$ 的倍数，否则为0

### 例2：双复形的谱序列

**设定**：双复形 $(C_{*,*}, d^h, d^v)$，两个方向都有微分，且反对易 $d^h d^v + d^v d^h = 0$。

**谱序列1**（先水平后垂直）：$E^2_{p,q} = H_p^h(H_q^v(C)) \Rightarrow H_{p+q}(\text{Tot}(C))$

**谱序列2**（先垂直后水平）：$E^2_{p,q} = H_q^v(H_p^h(C)) \Rightarrow H_{p+q}(\text{Tot}(C))$

### 例3：滤过空间的谱序列

**设定**：空间 $X$ 有滤过 $\emptyset = X_{-1} \subset X_0 \subset X_1 \subset \cdots \subset X$。

**谱序列**：$E^1_{p,q} = H_{p+q}(X_p, X_{p-1}) \Rightarrow H_{p+q}(X)$

这是胞腔同调的推广。

---

## 性质

### 边缘同态

谱序列中存在**边缘同态**（edge homomorphisms）：

$$H_n(E) \twoheadrightarrow E^\infty_{n,0} \hookrightarrow E^2_{n,0} = H_n(B)$$

（当纤维化有截面时这是 $p_*$）

### 横截性

若 $d^r$ 对 $r < k$ 都为零，则 $E^2_{p,q} = E^k_{p,q}$。

### 五项正合序列

对第一象限谱序列，有正合序列：

$$0 \to E^2_{2,0} \to H_2 \to E^2_{0,1} \to E^2_{1,0} \to H_1 \to 0$$

---

## FormalMath对应

### 主要文档

- `docs/数学家理念体系/格洛腾迪克/03-上同调理论/` — 谱序列相关
- `docs/00-习题示例反例库/代数/ALG-062-谱序列基础.md` — 计算练习

### 概念映射

| Princeton MAT 365 | FormalMath |
|------------------|------------|
| 谱序列 | `同调代数/谱序列` |
| Serre谱序列 | `代数拓扑/Serre谱序列` |
| 收敛 | `同调代数/谱序列收敛` |

### Lean 4形式化参考

```lean
-- 谱序列的形式化是同调代数的高级主题
-- 需要定义filtered complex和spectral sequence结构
structure SpectralSequence (R : Type) [CommRing R] where
  E : ℕ → ℤ → ℤ → Module R  -- E^r_{p,q}
  d : (r : ℕ) → (p q : ℤ) → LinearMap R (E r p q) (E r (p-r) (q+r-1))
  differential_squared : ∀ r p q, (d r (p-r) (q+r-1)).comp (d r p q) = 0
  E_next : ∀ r, E (r+1) ≅ λ p q => LinearMap.ker (d r p q) ⧸ LinearMap.range (d r (p+r) (q-r+1))
```

### 交叉引用

- **前序定义**: AT-PN-004 (奇异同调)
- **后续概念**: AT-PN-010 (同伦群的计算)
- **相关领域**: 同调代数、代数几何（层上同调）

---

## Hatcher参考

- **章节**: Chapter 5 (在线草稿), "Spectral Sequences"
- **关键内容**：
  - 谱序列的定义
  - Serre谱序列的构造
  - 应用：计算同伦群
- **延伸阅读**:
  - McCleary, *A User's Guide to Spectral Sequences*
  - Spanier, *Algebraic Topology*, Chapter 9

---

## 总结

谱序列是代数拓扑中最强大的计算工具之一，它将复杂的问题分解为可管理的代数步骤。

**关键要点**：

1. 谱序列是带微分的分次代数系统
2. 每页是前一页的同调
3. 收敛到感兴趣的不变量
4. Serre谱序列是计算纤维化和同伦群的主要工具
