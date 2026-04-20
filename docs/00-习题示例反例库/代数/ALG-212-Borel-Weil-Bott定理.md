---
msc_primary: 00A99
习题编号: ALG-212
学科: 代数
知识点: 表示论-Borel-Weil-Bott
难度: ⭐⭐⭐⭐⭐
预计时间: 60分钟
---

# Borel-Weil-Bott 定理

## 题目

**(a)** 陈述并证明 Borel-Weil 定理：紧 Lie 群表示的几何实现。

**(b)** 证明 Bott 定理：一般线丛的上同调。

**(c)** 讨论旗簇上的 Demazure 算子和 Schubert 演算。

## 解答

### (a) Borel-Weil 定理

**设置**：$G$ 复半单 Lie 群，$B \subset G$ 是 Borel 子群，$G/B$ 是 **旗簇**（flag variety）。

**线丛**：对权 $\lambda \in X^*(T)$（特征标格），构造 $G$-等变线丛：

$$
L_\lambda = G \times_B \mathbb{C}_\lambda = (G \times \mathbb{C})/(gb, b^{-1} \cdot z) \sim (g, z)
$$

其中 $B$ 通过 $\lambda$ 作用在 $\mathbb{C}$ 上。

**Borel-Weil 定理**：若 $\lambda$ 是 **支配权**（$\langle \lambda, \alpha^\vee \rangle \geq 0$ 对所有正根），则：

$$
H^0(G/B, L_\lambda) \cong V(\lambda)^*
$$

其中 $V(\lambda)$ 是最高权 $\lambda$ 的不可约表示。且 $H^i(G/B, L_\lambda) = 0$ 对 $i > 0$。

*证明概要*：

1. **Borel 不动点定理**：$G/B$ 是 projective，$B$ 有不动点。

2. **权分解**：$H^0(G/B, L_\lambda)$ 是 $G$-表示，有最高权理论。由 $L_\lambda$ 的构造，$B$-权恰为 $-\lambda$ 的 $W$-轨道。

3. **最高权向量**：在 $G/B$ 的 $B^-$-开轨上，$L_\lambda$ 有典则平凡化，$H^0$ 中的 $B^-$-最高权向量对应常函数。

4. **Kodaira 消失**：$L_\lambda$ 丰富（$\lambda$ 严格支配），故 $H^i = 0$ 对 $i > 0$。

---

### (b) Bott 定理

**定理（Bott, 1957）**：对任意权 $\lambda$，$G/B$ 上线丛 $L_\lambda$ 的上同调：

$$
H^i(G/B, L_\lambda) = \begin{cases} V(w(\lambda + \rho) - \rho)^* & \text{若 } \exists w \in W: l(w) = i, w(\lambda + \rho) \text{ 严格支配} \\ 0 & \text{否则} \end{cases}
$$

其中 $\rho = \frac{1}{2}\sum_{\alpha > 0} \alpha$。

*证明*（归纳 + Weyl 群作用）：

1. **正则情形**：若 $\lambda + \rho$ 正则（不在任何 Weyl 墙上），则存在唯一 $w \in W$ 使 $w(\lambda + \rho)$ 严格支配。

2. **简单反射**：对单根 $\alpha$，考虑投影 $p_\alpha: G/B \to G/P_\alpha$（$P_\alpha$ 是极小抛物）。

3. **纤维**：$p_\alpha$ 的纤维是 $\mathbb{P}^1$。在 $\mathbb{P}^1$ 上，线丛的 $H^0$ 和 $H^1$ 由权决定。

4. **Leray 谱序列**：$E_2^{i,j} = H^i(G/P_\alpha, R^j p_{\alpha*} L_\lambda) \Rightarrow H^{i+j}(G/B, L_\lambda)$。

5. **归纳**：通过 Weyl 群的长度和简单反射，将一般情形约化到 Borel-Weil 情形。

---

### (c) Demazure 算子

**Demazure 算子**：对单根 $\alpha$，$\partial_\alpha: H^*(G/B) \to H^*(G/B)$：

$$
\partial_\alpha(x) = \frac{x - s_\alpha(x)}{\alpha}
$$

其中 $s_\alpha$ 是根 $\alpha$ 的反射。

**性质**：

1. $\partial_\alpha^2 = 0$
2. $\partial_\alpha \partial_\beta \partial_\alpha = \partial_\beta \partial_\alpha \partial_\beta$（braid 关系）
3. $H^*(G/B, \mathbb{Z})$ 由 $\partial_\alpha$ 作用于最高权类生成

**Schubert 演算**：Schubert 胞腔 $X_w = \overline{BwB/B}$，$w \in W$。

- $[X_w] \in H^{2l(w)}(G/B)$
- 结构常数 $c_{uv}^w$：$[X_u] \cdot [X_v] = \sum_w c_{uv}^w [X_w]$

**Littlewood-Richardson 规则**：对 $GL_n$，Schubert 演算等价于对称函数的 LR 规则。

---

## 常见错误

- **$L_\lambda$ 的 $G$-作用**：$H^0(G/B, L_\lambda)$ 的 $G$-作用是左平移，$B$-权是 $-\lambda$ 而非 $\lambda$。
- **Bott 定理的墙情形**：若 $\lambda + \rho$ 在 Weyl 墙上，所有上同调为零（不是 $H^0$）。
- **Demazure 算子的次数**：$\partial_\alpha$ 降低次数 2，不是上同调度的同态。

## 参考文献

- Bott, *Homogeneous vector bundles*.
- Demazure, *Désingularisation des variétés de Schubert généralisées*.
- Kumar, *Kac-Moody Groups, their Flag Varieties and Representation Theory*.
