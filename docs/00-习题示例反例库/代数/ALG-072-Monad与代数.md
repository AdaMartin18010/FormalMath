---
exercise_id: ALG-072
title: Monad及其Eilenberg-Moore代数
msc_primary: 00A99
difficulty: ⭐⭐⭐⭐
topics: [Monad, 代数, Kleisli范畴, 伴随分解]
created: 2026-04-10
---

## 题目

设 $\mathcal{C}$ 是范畴，$T: \mathcal{C} \to \mathcal{C}$ 是Monad（三元组）。

(1) 定义**Monad** $(T, \eta, \mu)$ 并给出例子（幂集Monad、列表Monad）；

(2) 定义**Eilenberg-Moore代数** $(A, \alpha: TA \to A)$ 和代数态射；

(3) 证明Monad来自伴随的分解，并比较Eilenberg-Moore与Kleisli构造。

## 详细解答

### (1) Monad定义与例子

**定义**：Monad是 $(T, \eta: \operatorname{id} \to T, \mu: T^2 \to T)$ 满足：
- 结合律：$\mu \circ T\mu = \mu \circ \mu T: T^3 \to T$
- 单位律：$\mu \circ T\eta = \mu \circ \eta T = \operatorname{id}_T: T \to T$

**幂集Monad**（$\mathcal{C} = \mathbf{Set}$）：
- $T(X) = \mathcal{P}(X)$（幂集）
- $\eta_X(x) = \{x\}$（单点集）
- $\mu_X(\mathcal{A}) = \bigcup_{A \in \mathcal{A}} A$（大并）

**列表Monad**：
- $T(X) = X^*$（有限序列）
- $\eta_X(x) = [x]$（单元素列表）
- $\mu_X([[x_{11},...], [x_{21},...], ...]) = [x_{11}, ..., x_{21}, ...]$（扁平化）

### (2) Eilenberg-Moore代数

**定义**：代数是 $(A, \alpha: TA \to A)$ 满足：
- 结合：$\alpha \circ T\alpha = \alpha \circ \mu_A: T^2A \to A$
- 单位：$\alpha \circ \eta_A = \operatorname{id}_A: A \to A$

**代数态射**：$f: (A, \alpha) \to (B, \beta)$ 满足 $\beta \circ Tf = f \circ \alpha$。

**例子**（幂集Monad）：代数是完备格（$\alpha$ 是并运算）。

### (3) 伴随分解

**任意伴随** $F \dashv G$（$F: \mathcal{C} \to \mathcal{D}$）诱导Monad：
- $T = GF$
- $\eta$ 是单位
- $\mu = G\varepsilon F: GFGF \to GF$

**Eilenberg-Moore与Kleisli**：

- **Kleisli范畴** $\mathcal{C}_T$：对象是 $\mathcal{C}$ 的对象，态射 $X \to Y$ 是 $\mathcal{C}$ 中 $X \to TY$
  - 最小构造，对应"自由代数"

- **Eilenberg-Moore范畴** $\mathcal{C}^T$：所有代数
  - 最大构造，包含"所有可能的代数"

有伴随：$\mathcal{C}_T \to \mathcal{C}^T$，两者都给出原始Monad。

## 证明技巧

1. **图表验证**：Monad公理是复杂的交换图
2. **代数直觉**：代数将"复合结构"折叠为"单层"
3. **伴随统一**：不同伴随可给出相同Monad

## 常见错误

| 错误类型 | 错误表现 | 正确做法 |
|---------|---------|---------|
| 代数条件 | 混淆结合律方向 | 仔细验证$\alpha$的折叠顺序 |
| Kleisli复合 | 复合定义错误 | Kleisli复合用$\mu$结合 |
| Monad来源 | 认为所有Monad明显来自伴随 | 需要构造证明 |

## 变式练习

**变式1（难度⭐⭐⭐⭐）**：证明每个Monad都来自某个伴随。

**变式2（难度⭐⭐⭐⭐）**：计算Maybe Monad的Eilenberg-Moore代数。

**变式3（难度⭐⭐⭐⭐⭐）**：讨论分配律（Distributive Law）与Monad复合。
