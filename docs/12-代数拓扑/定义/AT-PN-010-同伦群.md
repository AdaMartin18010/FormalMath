---
msc_primary: 55A99
university: Princeton
synonym: [Homotopy Groups, 高阶同伦群, 球面同伦群]
type: 定义
level: L3-理论建构层
difficulty: ⭐⭐⭐⭐⭐
concept_dependency: [同伦, 球面, 基点]
prerequisite_concepts: [基本群, 同伦, 拓扑空间]
prerequisite_theorems: [Hurewicz定理, 纤维化长正合序列]
course_context: MAT 365 Topology
msc2010: [55Q05, 55Q15, 55Q40]
related_concepts: [纤维化, 障碍理论, 稳定同伦群]
---

# AT-PN-010: 同伦群 (Homotopy Groups)

> **来源**: Princeton MAT 365 (Topology) | Hatcher Chapter 4, Section 1, p. 337-345
> **级别**: 本科高阶/研究生初级
> **领域**: 代数拓扑 · 同伦论进阶

---

## 定义

### 高阶同伦群

**定义**：设 $X$ 是拓扑空间，$x_0 \in X$。对 $n \geq 1$，**第 $n$ 同伦群**定义为：

$$\pi_n(X, x_0) = [S^n, X]_{*} = \{f: S^n \to X \text{ 连续，} f(s_0) = x_0\}/\text{同伦}$$

其中 $s_0 \in S^n$ 是基点，同伦保持基点。

### 群结构（$n \geq 2$）

**定理**：对 $n \geq 2$，$\pi_n(X, x_0)$ 是Abel群。

**群运算**：对 $[f], [g] \in \pi_n(X, x_0)$，定义 $[f] + [g] = [f + g]$，其中：

$$(f + g)(t_1, \ldots, t_n) = \begin{cases} f(2t_1, t_2, \ldots, t_n) & 0 \leq t_1 \leq 1/2 \\ g(2t_1-1, t_2, \ldots, t_n) & 1/2 \leq t_1 \leq 1 \end{cases}$$

**Abel性证明**：当 $n \geq 2$ 时，可在另一维度"滑动"，证明 $f + g \simeq g + f$。

### 等价定义

**等价定义**：$\pi_n(X, x_0) = [(I^n, \partial I^n), (X, x_0)]$

即映射 $I^n \to X$ 将边界 $\partial I^n$ 映到 $x_0$，模保持边界的同伦。

---

## 例子

### 例1：球面的同伦群

**定理**：$\pi_n(S^n) \cong \mathbb{Z}$

**生成元**：恒等映射 $\text{id}: S^n \to S^n$，度数为1。

**低维结果**：

- $\pi_1(S^1) = \mathbb{Z}$
- $\pi_k(S^1) = 0$ 对 $k \geq 2$
- $\pi_k(S^n) = 0$ 对 $k < n$

### 例2：Hopf纤维化

**Hopf纤维化**：$S^1 \to S^3 \xrightarrow{\eta} S^2$

**定理**：$\eta$ 生成 $\pi_3(S^2) \cong \mathbb{Z}$

这是第一个非平凡的 $n < k$ 时的 $\pi_n(S^k)$，证明了高阶同伦群的复杂性。

### 例3：球面的同伦群表格

|  | $S^1$ | $S^2$ | $S^3$ | $S^4$ |
|--|-------|-------|-------|-------|
| $\pi_1$ | $\mathbb{Z}$ | 0 | 0 | 0 |
| $\pi_2$ | 0 | $\mathbb{Z}$ | 0 | 0 |
| $\pi_3$ | 0 | $\mathbb{Z}$ | $\mathbb{Z}$ | 0 |
| $\pi_4$ | 0 | $\mathbb{Z}/2$ | $\mathbb{Z}/2$ | $\mathbb{Z}$ |
| $\pi_5$ | 0 | $\mathbb{Z}/2$ | $\mathbb{Z}/2$ | $\mathbb{Z}/2$ |
| $\pi_6$ | 0 | $\mathbb{Z}/12$ | $\mathbb{Z}/12$ | $\mathbb{Z}/2$ |

**规律**：没有明显的模式，球面同伦群的计算是代数拓扑的核心难题。

### 例4：乘积公式

**定理**：$\pi_n(X \times Y) \cong \pi_n(X) \times \pi_n(Y)$

### 例5：Eilenberg-MacLane空间

**定义**：空间 $K(G, n)$ 满足 $\pi_n = G$，其他同伦群平凡。

**性质**：$K(G, n)$ 在同伦等价下唯一，且 $[X, K(G, n)] \cong H^n(X; G)$。

---

## 性质

### 函子性

**定理**：连续映射 $f: X \to Y$ 诱导同态 $f_*: \pi_n(X) \to \pi_n(Y)$，且：

- $(f \circ g)_* = f_* \circ g_*$
- $(\text{id})_* = \text{id}$

### 同伦不变性

**定理**：同伦等价的映射诱导同伦群的同构。

### Hurewicz定理

**定理（Hurewicz）**：设 $X$ $(n-1)$-连通（即 $\pi_k(X) = 0$ 对 $k < n$）。则：

$$\pi_n(X) \cong H_n(X)$$

（通过Hurewicz同态）

**应用**：若知道同伦群到某维数，可计算同调。

### 纤维化长正合序列

**定理**：对纤维化 $F \to E \to B$，有长正合序列：

$$\cdots \to \pi_{n+1}(B) \to \pi_n(F) \to \pi_n(E) \to \pi_n(B) \to \pi_{n-1}(F) \to \cdots$$

这是计算同伦群的主要工具。

### 相对同伦群

**定义**：对空间对 $(X, A)$，定义：

$$\pi_n(X, A, x_0) = [(I^n, \partial I^n, J^{n-1}), (X, A, x_0)]$$

其中 $J^{n-1} = \partial I^n \setminus (I^{n-1} \times \{0\})$。

有长正合序列：
$$\cdots \to \pi_n(A) \to \pi_n(X) \to \pi_n(X, A) \to \pi_{n-1}(A) \to \cdots$$

---

## FormalMath对应

### 主要文档

- `docs/05-拓扑学/02-代数拓扑.md` — 同伦论进阶
- `docs/00-习题示例反例库/拓扑/TOP-071-同伦群基础.md` — 计算练习

### 概念映射

| Princeton MAT 365 | FormalMath |
|------------------|------------|
| 同伦群 $\pi_n$ | `代数拓扑/同伦群` |
| Hopf纤维化 | `代数拓扑/Hopf纤维化` |
| 稳定同伦群 | `代数拓扑/稳定同伦论` |

### Lean 4形式化参考

```lean
-- 同伦群在mathlib的同伦论库中
import Mathlib.AlgebraicTopology.HomotopyGroup

-- π_n的定义（概念性）
-- 使用loop space的迭代：π_n(X) = π_1(Ω^{n-1}X)
```

### 交叉引用

- **前序定义**: AT-PN-002 (基本群), AT-PN-003 (覆叠空间)
- **后续概念**: 稳定同伦论、谱序列
- **计算工具**: AT-PN-009 (谱序列)

---

## Hatcher参考

- **章节**: Chapter 4, Section 1, "The Homotopy Groups", p. 337-345
- **关键内容**：
  - 同伦群的定义 (p. 337-338)
  - Hurewicz定理 (p. 366-370)
  - 纤维化长正合序列 (p. 375-378)
- **关键习题**:
  - Exercise 4.1.1: 计算 $\pi_n(S^1)$
  - Exercise 4.1.5: 证明Hopf纤维化的非平凡性

---

## 总结

同伦群是代数拓扑中最精细但也最难计算的不变量。它们比同调群包含更多信息，但计算极其困难。

**关键要点**：

1. $\pi_n(X) = [S^n, X]$（基点保持）
2. $n \geq 2$ 时是Abel群
3. 球面同伦群极其复杂，至今未完全了解
4. Hurewicz定理联系同伦与同调
5. 纤维化长正合序列是主要计算工具
