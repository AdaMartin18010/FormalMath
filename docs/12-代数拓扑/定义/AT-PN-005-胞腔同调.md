---
university: Princeton
synonym: [Cellular Homology, CW同调, 胞腔链复形]
type: 定义
level: L3-理论建构层
difficulty: ⭐⭐⭐⭐
concept_dependency: [CW复形, 胞腔结构, 同调群]
prerequisite_concepts: [奇异同调, CW复形, 维数]
prerequisite_theorems: [同调的长正合序列]
course_context: MAT 365 Topology
msc2010: [55N10, 55U10, 57Q10]
related_concepts: [奇异同调, 胞腔映射, 欧拉示性数]
---

# AT-PN-005: 胞腔同调 (Cellular Homology)

> **来源**: Princeton MAT 365 (Topology) | Hatcher Chapter 2, Section 2, p. 137-142
> **级别**: 本科高阶/研究生初级
> **领域**: 代数拓扑 · 同调论

---

## 定义

### CW复形回顾

**CW复形** $X$ 是通过归纳法构造的空间：
- $X^0$：离散点集（0-骨架）
- $X^n$ 由 $X^{n-1}$ 粘合 $n$-胞腔 $e_\alpha^n \cong D^n$ 得到（通过附着映射 $\varphi_\alpha: S^{n-1} \to X^{n-1}$）
- $X = \bigcup_n X^n$

### 胞腔链群

**定义**：$X$ 的**胞腔链群**定义为：

$$C_n^{CW}(X) = H_n(X^n, X^{n-1})$$

其中 $H_n(X^n, X^{n-1})$ 是**相对同调**。

**性质**：$C_n^{CW}(X) \cong \mathbb{Z}^{\text{(n-胞腔数)}}$ 是自由Abel群，每个 $n$-胞腔对应一个生成元。

### 胞腔边缘算子

**定义**：胞腔边缘算子 $d_n: C_n^{CW}(X) \to C_{n-1}^{CW}(X)$ 是三元组 $(X^n, X^{n-1}, X^{n-2})$ 的长正合序列中的连接同态：

$$d_n: H_n(X^n, X^{n-1}) \xrightarrow{\partial} H_{n-1}(X^{n-1}) \xrightarrow{j} H_{n-1}(X^{n-1}, X^{n-2})$$

或等价地，是以下复合：

$$\begin{CD}
H_n(X^n, X^{n-1}) @>{\partial_n}>> H_{n-1}(X^{n-1}) @>{j_{n-1}}>> H_{n-1}(X^{n-1}, X^{n-2})
\end{CD}$$

### 胞腔同调群

**定义**：$X$ 的**胞腔 $n$-同调群**定义为：

$$H_n^{CW}(X) = \frac{\ker d_n}{\text{im } d_{n+1}}$$

---

## 例子

### 例1：圆周 $S^1$

**胞腔结构**：一个0-胞腔 $e^0$，一个1-胞腔 $e^1$（两端粘合到 $e^0$）。

**链复形**：
$$0 \to \mathbb{Z} \xrightarrow{d_1} \mathbb{Z} \to 0$$

边缘算子 $d_1$：附着映射 $S^0 \to X^0$ 将两点映到同一点，度数为0。故 $d_1 = 0$。

**同调**：$H_1^{CW}(S^1) = \mathbb{Z}$，$H_0^{CW}(S^1) = \mathbb{Z}$。

### 例2：球面 $S^n$

**胞腔结构**：一个0-胞腔，一个 $n$-胞腔（边界粘合到一点）。

**链复形**：
$$0 \to \mathbb{Z} \to 0 \to \cdots \to 0 \to \mathbb{Z} \to 0$$

中间所有链群为0，所有边缘算子为0。

**同调**：$H_0 = H_n = \mathbb{Z}$，其他为0。

### 例3：实射影空间 $\mathbb{R}P^n$

**胞腔结构**：每个维数一个胞腔：$e^0, e^1, \ldots, e^n$。

**链复形**：$C_k^{CW} = \mathbb{Z}$ 对 $0 \leq k \leq n$。

边缘算子：$d_k: \mathbb{Z} \to \mathbb{Z}$ 是乘以 $1 + (-1)^k$：
- $k$ 奇数：$d_k = 0$
- $k$ 偶数：$d_k = 2$

**同调**：
$$H_k(\mathbb{R}P^n) = \begin{cases} \mathbb{Z} & k = 0 \\ \mathbb{Z}/2\mathbb{Z} & 0 < k < n, k \text{ 奇数} \\ 0 & \text{其他} \end{cases}$$
（对 $k = n$ 需单独处理）

### 例4：环面 $T^2 = S^1 \times S^1$

**胞腔结构**：一个0-胞腔，两个1-胞腔 $a, b$，一个2-胞腔（边界 $aba^{-1}b^{-1}$）。

**链复形**：
$$0 \to \mathbb{Z} \xrightarrow{d_2} \mathbb{Z}^2 \xrightarrow{d_1} \mathbb{Z} \to 0$$

$d_1 = 0$（1-胞腔两端都到唯一的0-胞腔）

$d_2 = 0$（边界在Abel化后为0）

**同调**：$H_2 = \mathbb{Z}$，$H_1 = \mathbb{Z}^2$，$H_0 = \mathbb{Z}$。

---

## 性质

### 与奇异同调的等价性

**定理**：对CW复形 $X$，$H_n^{CW}(X) \cong H_n(X)$（奇异同调）。

**证明概要**：考虑 $(X^n, X^{n-1})$ 的长正合序列，以及 $H_k(X^n) = 0$ 对 $k > n$（由维数论证）。$\square$

### 计算优势

| 特点 | 奇异同调 | 胞腔同调 |
|------|---------|---------|
| 链群大小 | 不可数（通常） | 有限生成（有限CW复形） |
| 边缘算子 | 复杂组合 | 由附着映射的度决定 |
| 适用范围 | 所有空间 | CW复形 |
| 计算难度 | 难 | 相对容易 |

### 胞腔边界公式

对 $n$-胞腔 $e_\alpha^n$ 和 $(n-1)$-胞腔 $e_\beta^{n-1}$：

$$d_n(e_\alpha^n) = \sum_\beta d_{\alpha\beta} e_\beta^{n-1}$$

其中 $d_{\alpha\beta} = \deg(S^{n-1} \xrightarrow{\varphi_\alpha} X^{n-1} \xrightarrow{q} X^{n-1}/(X^{n-1} \setminus e_\beta^{n-1}) \cong S^{n-1})$。

这是附着映射在商空间中的**度数**。

---

## FormalMath对应

### 主要文档

- `docs/05-拓扑学/02-代数拓扑.md` — CW复形与同调
- `docs/00-习题示例反例库/代数几何/AG-018-Cech上同调.md` — 相关技巧

### 概念映射

| Princeton MAT 365 | FormalMath |
|------------------|------------|
| 胞腔同调 | `代数拓扑/胞腔同调` |
| CW复形 | `拓扑空间/CW复形` |
| 胞腔链复形 | `同调代数/胞腔链` |

### Lean 4形式化参考

```lean
-- CW复形和同调的结构
-- mathlib中已有SimplicialComplex和CWComplex相关定义
```

### 交叉引用

- **前序定义**: AT-PN-004 (奇异同调)
- **后续定义**: AT-PN-007 (Kunneth公式)
- **相关概念**: 欧拉示性数 $\chi(X) = \sum (-1)^n \text{rank } H_n(X)$

---

## Hatcher参考

- **章节**: Chapter 2, Section 2, "Computed Homology", p. 137-142
- **关键内容**：
  - 胞腔链复形的定义 (p. 137-138)
  - 胞腔边缘算子 (p. 139)
  - 与奇异同调的等价性 (p. 140)
- **关键习题**:
  - Exercise 2.2.10: 计算 $\mathbb{C}P^n$ 的胞腔同调
  - Exercise 2.2.15: 用胞腔同调计算透镜空间的同调

---

## 总结

胞腔同调提供了计算CW复形同调的有效方法，它将无限维的奇异链复形简化为有限生成的胞腔链复形。

**关键要点**：
1. 胞腔链群由胞腔生成
2. 边缘算子由附着映射的度决定
3. 胞腔同调与奇异同调同构
4. 是计算具体空间同调的主要工具
