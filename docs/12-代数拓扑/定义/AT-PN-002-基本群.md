---
university: Princeton
synonym: [Fundamental Group, 第一同伦群, Poincaré群]
type: 定义
level: L3-理论建构层
difficulty: ⭐⭐⭐
concept_dependency: [同伦, 道路, 环路, 拓扑空间]
prerequisite_concepts: [同伦, 道路连通空间]
prerequisite_theorems: []
course_context: MAT 365 Topology
msc2010: [55Q05, 55P10]
related_concepts: [覆叠空间, 同伦群, van Kampen定理]
---

# AT-PN-002: 基本群 (Fundamental Group)

> **来源**: Princeton MAT 365 (Topology) | Hatcher Chapter 1, Section 1, p. 25-30
> **级别**: 本科高阶/研究生初级
> **领域**: 代数拓扑 · 同伦论

---

## 定义

### 道路与环路

设 $X$ 是拓扑空间，$x_0, x_1 \in X$。

**道路**（path）：连续映射 $\gamma: [0, 1] \to X$ 满足 $\gamma(0) = x_0$，$\gamma(1) = x_1$，称为从 $x_0$ 到 $x_1$ 的道路。

**环路**（loop）：满足 $\gamma(0) = \gamma(1) = x_0$ 的道路，即基于 $x_0$ 的环路。

### 道路同伦

两条道路 $\gamma_0, \gamma_1: [0, 1] \to X$（从 $x_0$ 到 $x_1$）称为**道路同伦**（path-homotopic），记作 $\gamma_0 \simeq_p \gamma_1$，如果存在连续映射 $H: [0, 1] \times [0, 1] \to X$ 满足：

- $H(s, 0) = \gamma_0(s)$，$H(s, 1) = \gamma_1(s)$（连接两条道路）
- $H(0, t) = x_0$，$H(1, t) = x_1$（端点固定）

### 基本群的定义

**定义**：设 $X$ 是拓扑空间，$x_0 \in X$。基于 $x_0$ 的**基本群**（fundamental group）定义为：

$$\pi_1(X, x_0) = \{[\gamma] : \gamma \text{ 是基于 } x_0 \text{ 的环路}\}$$

其中 $[\gamma]$ 表示 $\gamma$ 的道路同伦类。

**群运算**（道路连接）：对于环路 $\gamma_1, \gamma_2$，定义

$$(\gamma_1 * \gamma_2)(s) = \begin{cases}
\gamma_1(2s) & 0 \leq s \leq 1/2 \\
\gamma_2(2s-1) & 1/2 \leq s \leq 1
\end{cases}$$

即先走 $\gamma_1$（双倍速度），再走 $\gamma_2$（双倍速度）。

### 验证群公理

**单位元**：常值环路 $e_{x_0}(s) = x_0$

**逆元**：$\gamma^{-1}(s) = \gamma(1-s)$（反向道路）

**结合律**：$(\gamma_1 * \gamma_2) * \gamma_3 \simeq_p \gamma_1 * (\gamma_2 * \gamma_3)$（重参数化同伦）

---

## 例子

### 例1：圆的基本群

**定理**：$\pi_1(S^1, 1) \cong \mathbb{Z}$

**证明概要**：

考虑覆叠映射 $p: \mathbb{R} \to S^1$，$p(t) = e^{2\pi i t}$。

**绕数**（winding number）：对环路 $\gamma: [0, 1] \to S^1$，设 $\tilde{\gamma}: [0, 1] \to \mathbb{R}$ 是 $\gamma$ 的提升（满足 $\tilde{\gamma}(0) = 0$，$p \circ \tilde{\gamma} = \gamma$）。定义 $n(\gamma) = \tilde{\gamma}(1) \in \mathbb{Z}$。

同态 $[\gamma] \mapsto n(\gamma)$ 是群同构。$\square$

### 例2：欧氏空间

**定理**：$\pi_1(\mathbb{R}^n, x_0) = 0$（平凡群）

**证明**：任何环路可通过 $H(s, t) = (1-t)\gamma(s) + tx_0$ 收缩到基点。$\square$

**定义**：若 $X$ 道路连通且 $\pi_1(X) = 0$，称 $X$ **单连通**（simply-connected）。

### 例3：高维球面

**定理**：$\pi_1(S^n) = 0$ 对 $n \geq 2$

**证明**：任何环路 $\gamma$ 可用单纯逼近变为不满射的环路（$n \geq 2$ 时）。$S^n$ 去掉一点同胚于 $\mathbb{R}^n$，故可缩。$\square$

### 例4：实射影空间

**定理**：$\pi_1(\mathbb{R}P^n) \cong \mathbb{Z}/2\mathbb{Z}$ 对 $n \geq 2$

**证明**：利用覆叠映射 $S^n \to \mathbb{R}P^n$（对径点等同）。$\square$

### 例5：环面

**定理**：$\pi_1(T^2 = S^1 \times S^1) \cong \mathbb{Z} \times \mathbb{Z}$

**证明**：由乘积公式 $\pi_1(X \times Y) \cong \pi_1(X) \times \pi_1(Y)$。$\square$

### 例6：8字图

**定理**：8字图（两个圆周交于一点）的基本群是自由群 $F_2 = \mathbb{Z} * \mathbb{Z}$

---

## 性质

### 基点变换

**定理**：若 $X$ 道路连通，$x_0, x_1 \in X$，则 $\pi_1(X, x_0) \cong \pi_1(X, x_1)$。

**证明**：选取道路 $\alpha: [0, 1] \to X$ 从 $x_0$ 到 $x_1$。定义 $\phi_\alpha: \pi_1(X, x_0) \to \pi_1(X, x_1)$ 为：

$$\phi_\alpha([\gamma]) = [\alpha^{-1} * \gamma * \alpha]$$

这是群同构。$\square$

因此，对于道路连通空间，常记 $\pi_1(X)$，忽略基点。

### 函子性

**定理**：连续映射 $f: X \to Y$ 诱导同态 $f_*: \pi_1(X, x_0) \to \pi_1(Y, f(x_0))$，$f_*([\gamma]) = [f \circ \gamma]$。

**性质**：
- $(f \circ g)_* = f_* \circ g_*$
- $(\text{id}_X)_* = \text{id}_{\pi_1(X)}$
- 同伦等价的映射诱导同构

因此 $\pi_1$ 是从带基点拓扑空间到群的函子。

### van Kampen定理（预告）

**定理（van Kampen）**：设 $X = U \cup V$，$U, V$ 开，且 $U, V, U \cap V$ 都道路连通。则：

$$\pi_1(X) \cong \pi_1(U) *_{\pi_1(U \cap V)} \pi_1(V)$$

（群的自由积的融合积）

这是计算复杂空间基本群的主要工具。

---

## FormalMath对应

### 主要文档

- `docs/05-拓扑学/02-代数拓扑.md` — 代数拓扑基础
- `docs/00-习题示例反例库/拓扑/TOP-018-单连通与基本群.md` — 计算练习

### 概念映射

| Princeton MAT 365 | FormalMath |
|------------------|------------|
| 基本群 $\pi_1$ | `代数拓扑/基本群` |
| 道路同伦 | `同伦论/道路同伦` |
| 环路 | `拓扑空间/环路` |
| 单连通 | `拓扑空间/单连通性` |

### Lean 4形式化参考

```lean
-- 基本群概念（概念性框架）
import Mathlib.Topology.Homotopy.Path

-- π₁定义为环路同伦类的集合，配备道路连接运算
-- 在mathlib中，FundamentalGroupoid已实现相关的范畴结构
```

### 交叉引用

- **前序定义**: AT-PN-001 (同伦等价)
- **后续定义**: AT-PN-003 (覆叠空间) — 利用基本群分类覆叠
- **相关定理**: van Kampen定理、Hurewicz定理

---

## Hatcher参考

- **章节**: Chapter 1, Section 1, "The Fundamental Group", p. 25-30
- **关键内容**：
  - 道路连接的定义 (p. 26)
  - 基本群的定义与验证 (p. 26-28)
  - 基本群的基本性质 (p. 28-30)
- **关键习题**:
  - Exercise 1.1.5: 计算 $\mathbb{R}^3$ 中圆周的补空间的基本群
  - Exercise 1.1.6: 证明 $\pi_1(X \times Y) \cong \pi_1(X) \times \pi_1(Y)$
  - Exercise 1.1.10: 讨论基本群对基点的依赖

---

## 总结

基本群是代数拓扑的第一个核心不变量，它用代数（群论）来刻画空间的"一维洞"。

**关键要点**：
1. 基本群是环路同伦类的群
2. 圆的基本群是 $\mathbb{Z}$（由绕数计数）
3. 高维球面单连通（$n \geq 2$）
4. 基本群是同伦不变量
5. van Kampen定理是计算复杂空间基本群的主要工具
