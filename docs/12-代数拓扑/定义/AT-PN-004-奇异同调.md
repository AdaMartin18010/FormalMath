---
msc_primary: 55A99
university: Princeton
synonym: [Singular Homology, 奇异同调群, 拓扑不变量]
type: 定义
level: L3-理论建构层
difficulty: ⭐⭐⭐⭐
concept_dependency: [自由Abel群, 链复形, 边缘算子]
prerequisite_concepts: [拓扑空间, Abel群, 自由Abel群]
prerequisite_theorems: [同伦不变性定理]
course_context: MAT 365 Topology
msc2010: [55N10, 55U10]
related_concepts: [胞腔同调, 上同调, 长正合序列]
---

# AT-PN-004: 奇异同调 (Singular Homology)

> **来源**: Princeton MAT 365 (Topology) | Hatcher Chapter 2, Section 1, p. 97-106
> **级别**: 本科高阶/研究生初级
> **领域**: 代数拓扑 · 同调论

---

## 定义

### 奇异单形

**标准 $n$-单形**：
$$\Delta^n = \{(t_0, t_1, \ldots, t_n) \in \mathbb{R}^{n+1} : t_i \geq 0, \sum t_i = 1\}$$

这是 $\mathbb{R}^{n+1}$ 中的 $n$ 维单纯形，顶点为 $e_0, e_1, \ldots, e_n$。

**奇异 $n$-单形**：设 $X$ 是拓扑空间。连续映射 $\sigma: \Delta^n \to X$ 称为 $X$ 中的**奇异 $n$-单形**（singular $n$-simplex）。

### 奇异链群

**定义**：$X$ 的**奇异 $n$-链群** $C_n(X)$ 是由所有奇异 $n$-单形生成的自由Abel群：

$$C_n(X) = \mathbb{Z}\langle \sigma: \Delta^n \to X \rangle = \left\{\sum_i n_i \sigma_i : n_i \in \mathbb{Z}, \sigma_i \text{ 奇异 } n\text{-单形}\right\}$$

### 边缘算子

定义**第 $i$ 个面映射** $\varepsilon_i^n: \Delta^{n-1} \to \Delta^n$：

$$\varepsilon_i^n(t_0, \ldots, t_{n-1}) = (t_0, \ldots, t_{i-1}, 0, t_i, \ldots, t_{n-1})$$

**边缘算子** $\partial_n: C_n(X) \to C_{n-1}(X)$ 定义为：

$$\partial_n(\sigma) = \sum_{i=0}^n (-1)^i \sigma \circ \varepsilon_i^n$$

对链 $\sum n_i \sigma_i$，线性延拓。

### 关键性质：$\partial^2 = 0$

**引理**：$\partial_{n-1} \circ \partial_n = 0$

**证明**：对奇异单形 $\sigma$：
$$\partial^2 \sigma = \sum_{j < i} (-1)^{i+j} \sigma \circ \varepsilon_i \circ \varepsilon_j + \sum_{j > i} (-1)^{i+j} \sigma \circ \varepsilon_i \circ \varepsilon_j = 0$$

因为 $\varepsilon_i \circ \varepsilon_j = \varepsilon_j \circ \varepsilon_{i-1}$ 当 $j < i$。$\square$

### 奇异同调群

**定义**：$X$ 的**奇异 $n$-同调群**定义为：

$$H_n(X) = \frac{\ker \partial_n}{\text{im } \partial_{n+1}} = \frac{Z_n(X)}{B_n(X)}$$

其中：

- $Z_n(X) = \ker \partial_n$ 称为**$n$-闭链群**（cycles）
- $B_n(X) = \text{im } \partial_{n+1}$ 称为**$n$-边缘链群**（boundaries）

元素 $[z] \in H_n(X)$ 称为**同调类**，$z \in Z_n(X)$ 是其代表元。

---

## 例子

### 例1：一点的同调

**定理**：设 $X = \{pt\}$，则：
$$H_n(X) = \begin{cases} \mathbb{Z} & n = 0 \\ 0 & n > 0 \end{cases}$$

**证明**：对每个 $n$，存在唯一的奇异 $n$-单形 $\sigma_n: \Delta^n \to X$。故 $C_n(X) \cong \mathbb{Z}$。

边缘算子：$\partial_n(\sigma_n) = \sum_{i=0}^n (-1)^i \sigma_{n-1} = \begin{cases} 0 & n \text{ 奇数} \\ \sigma_{n-1} & n \text{ 偶数} \end{cases}$

因此链复形为：$\cdots \to \mathbb{Z} \xrightarrow{0} \mathbb{Z} \xrightarrow{\cong} \mathbb{Z} \xrightarrow{0} \mathbb{Z} \to 0$

同调计算即得。$\square$

### 例2：球面 $S^n$

**定理**：
$$H_k(S^n) = \begin{cases} \mathbb{Z} & k = 0, n \\ 0 & \text{其他} \end{cases}$$

**证明思路**：用Mayer-Vietoris序列，将 $S^n = D^n_+ \cup D^n_-$（两个半球），$D^n_+ \cap D^n_- \simeq S^{n-1}$。$\square$

### 例3：圆周 $S^1$

**定理**：$H_1(S^1) \cong \mathbb{Z}$

**解释**：生成元由环路 $\sigma: [0,1] \to S^1$（将 $\Delta^1 = [0,1]$ 映满整个圆周）代表。这不是边缘（因为不是某个2-单形的边界）。

### 例4：环面 $T^2 = S^1 \times S^1$

**定理**：$H_1(T^2) \cong \mathbb{Z} \oplus \mathbb{Z}$

生成元对应两个 $S^1$ 因子。

---

## 性质

### 同伦不变性

**定理**：同伦等价的映射诱导同调的同构。即若 $f \simeq g: X \to Y$，则 $f_* = g_*: H_n(X) \to H_n(Y)$。

**推论**：同伦等价的空间有同构的同调群。

### 函子性

**定理**：$H_n$ 是从拓扑空间到Abel群的协变函子：

- 对 $f: X \to Y$，诱导 $f_*: H_n(X) \to H_n(Y)$
- $(f \circ g)_* = f_* \circ g_*$
- $(\text{id})_* = \text{id}$

### 长正合序列

**定理（对空间对 $(X, A)$）**：设 $A \subset X$ 是子空间。则有**长正合序列**：

$$\cdots \to H_n(A) \xrightarrow{i_*} H_n(X) \xrightarrow{j_*} H_n(X, A) \xrightarrow{\partial} H_{n-1}(A) \to \cdots$$

其中 $H_n(X, A)$ 是**相对同调**。

### 维度公理

**性质**：若 $X = \emptyset$，则 $H_n(X) = 0$ 对所有 $n$。

若 $X$ 道路连通，则 $H_0(X) \cong \mathbb{Z}$。

---

## FormalMath对应

### 主要文档

- `docs/05-拓扑学/02-代数拓扑.md` — 同调论基础
- `docs/00-习题示例反例库/拓扑/TOP-052-同调的长正合序列.md` — 计算练习

### 概念映射

| Princeton MAT 365 | FormalMath |
|------------------|------------|
| 奇异同调 | `代数拓扑/奇异同调` |
| 链复形 | `同调代数/链复形` |
| 边缘算子 | `同调代数/微分` |
| 同调群 | `代数拓扑/同调群` |

### Lean 4形式化参考

```lean
-- 同调代数基础已在mathlib中建立
-- 奇异同调需要额外定义
import Mathlib.Algebra.Homology.ChainComplex

-- 链复形的定义
abbrev ChainComplex (C : Type) [Category C] [Abelian C] :=
  ComplexShape.down C
```

### 交叉引用

- **前序定义**: AT-PN-001 (同伦等价)
- **后续定义**: AT-PN-005 (胞腔同调), AT-PN-006 (上同调环)
- **相关定理**: 同伦不变性、Mayer-Vietoris序列

---

## Hatcher参考

- **章节**: Chapter 2, Section 1, "Homology Groups", p. 97-106
- **关键内容**：
  - 奇异单形的定义 (p. 97)
  - 边缘算子的定义 (p. 98)
  - 同调群的定义 (p. 99)
  - 同伦不变性 (p. 110-113)
- **关键习题**:
  - Exercise 2.1.5: 计算 $\mathbb{R}^n \setminus \{0\}$ 的同调
  - Exercise 2.1.8: 证明 $H_0(X) \cong \mathbb{Z}$ 当 $X$ 道路连通

---

## 总结

奇异同调是代数拓扑中最基本的同调理论，它通过"代数化"拓扑空间的结构来提取不变量。

**关键要点**：

1. 奇异单形是到拓扑空间的连续映射
2. 边缘算子满足 $\partial^2 = 0$，保证同调定义良好
3. 同调是同伦不变量
4. 与基本群的关系：$H_1(X) \cong \pi_1(X)^{ab}$（Abel化）
