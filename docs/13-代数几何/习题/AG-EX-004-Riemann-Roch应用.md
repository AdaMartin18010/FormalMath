---
习题编号: AG-EX-004
标题: Riemann-Roch应用
类型: 理论型
难度: ⭐⭐⭐
章节: Hartshorne Ch IV
对应课程: Harvard Math 232br
预计用时: 60-90分钟
msc: 14H51, 14C40
references:
  textbooks:
    - id: hartshorne_ag
      type: textbook
      title: Algebraic Geometry
msc_primary: 14A99
      authors:
      - Robin Hartshorne
      publisher: Springer
      edition: 1st
      year: 1977
      isbn: 978-0387902449
      msc: 14-01
      chapters: 
      url: ~
    - id: vakil_foag
      type: textbook
      title: Foundations of Algebraic Geometry
      authors:
      - Ravi Vakil
      publisher: self-published
      edition: draft
      year: 2024
      isbn: ~
      msc: 14-01
      chapters: 
      url: "https://math.stanford.edu/~vakil/216blog/"
  databases:
    - id: nlab
      type: database
      name: nLab
      entry_url: "https://ncatlab.org/nlab/show/{entry}"
      consulted_at: 2026-04-17
    - id: stacks_project
      type: database
      name: Stacks Project
      entry_url: "https://stacks.math.columbia.edu/tag/{tag}"
      consulted_at: 2026-04-17
    - id: zbmath
      type: database
      name: zbMATH Open
      entry_url: "https://zbmath.org/?q=an:{zb_id}"
      consulted_at: 2026-04-17
---

# AG-EX-004: Riemann-Roch应用

## 题目

### 原题 (Hartshorne IV.1.1)

设 $X$ 是亏格 $g$ 的光滑射影曲线，$D$ 是 $X$ 上的除子。

**(a)** 证明若 $\deg(D) \geq 2g - 1$，则 $H^1(X, \mathcal{L}(D)) = 0$（消没定理）。

**(b)** 证明若 $\deg(D) \geq 2g$，则 $\mathcal{L}(D)$ 是整体生成的（globally generated）。

**(c)** 证明若 $\deg(D) \geq 2g + 1$，则 $\mathcal{L}(D)$ 是非常丰沛的（very ample），从而给出 $X$ 到 $\mathbb{P}^{\deg(D)-g}$ 的嵌入。

### 计算题目

设 $X$ 是亏格2的曲线。

**(a)** 对 $\deg(D) = 2, 3, 4, 5$，计算 $\dim |D| = h^0(D) - 1$。

**(b)** 确定哪些度数的除子给出到射影空间的嵌入。

---

## 解答

### 主题目解答

#### (a) 消没定理

**Riemann-Roch定理**:
$$h^0(D) - h^1(D) = \deg(D) + 1 - g$$

**Serre对偶**:
$$h^1(D) = h^0(K - D)$$

**证明**:

设 $\deg(D) \geq 2g - 1$。

**Step 1**: 计算 $\deg(K - D)$。

已知 $\deg(K) = 2g - 2$，故:
$$\deg(K - D) = \deg(K) - \deg(D) \leq (2g - 2) - (2g - 1) = -1$$

**Step 2**: 负度数除子没有整体截面。

若 $\deg(E) < 0$，则对任意 $0 \neq s \in H^0(\mathcal{L}(E))$，$(s) + E \geq 0$。

但 $\deg((s) + E) = \deg(E) < 0$，矛盾！

故 $h^0(K - D) = 0$。

**Step 3**: 由Serre对偶，$h^1(D) = 0$。

---

#### (b) 整体生成性

**定义**: $\mathcal{L}(D)$ 整体生成是指对任意 $P \in X$，存在 $s \in H^0(\mathcal{L}(D))$ 使得 $s(P) \neq 0$。

等价于: 限制映射 $H^0(\mathcal{L}(D)) \to \mathcal{L}(D) \otimes k(P)$ 满射。

**证明**:

设 $\deg(D) \geq 2g$，需证 $\mathcal{L}(D)$ 整体生成。

对任意点 $P \in X$，考虑短正合列:
$$0 \to \mathcal{L}(D - P) \to \mathcal{L}(D) \to \mathcal{L}(D)|_P \to 0$$

取上同调:
$$0 \to H^0(D - P) \to H^0(D) \to k \to H^1(D - P) \to \cdots$$

由 (a)，$\deg(D - P) \geq 2g - 1$，故 $H^1(D - P) = 0$。

因此 $H^0(D) \to k$ 满射，即存在截面在 $P$ 非零。

---

#### (c) 非常丰沛性

**定义**: $\mathcal{L}(D)$ 非常丰沛是指:
1. 整体生成
2. 诱导的映射 $\phi_D: X \to \mathbb{P}^{h^0(D)-1}$ 是嵌入

等价于: 对任意 $P, Q \in X$（可相同），存在截面在 $P$ 为零而在 $Q$ 非零。

**证明**:

设 $\deg(D) \geq 2g + 1$。

**Step 1**: 分离点。

对 $P \neq Q$，考虑:
$$0 \to \mathcal{L}(D - P - Q) \to \mathcal{L}(D) \to \mathcal{L}(D)|_{P+Q} \to 0$$

$\deg(D - P - Q) \geq 2g - 1$，故 $H^1(D - P - Q) = 0$。

$H^0(D) \to k^2$ 满射，故存在截面在 $P$ 为零、在 $Q$ 非零。

**Step 2**: 分离切向量。

对任意 $P$，考虑:
$$0 \to \mathcal{L}(D - 2P) \to \mathcal{L}(D) \to \mathcal{L}(D)|_{2P} \to 0$$

$\deg(D - 2P) \geq 2g - 1$，故 $H^1(D - 2P) = 0$。

$H^0(D) \to \mathcal{L}(D)|_{2P} \cong k^2$ 满射，故分离切向量。

**Step 3**: 计算像的维数。

由Riemann-Roch和消没:
$$h^0(D) = \deg(D) + 1 - g$$

嵌入到 $\mathbb{P}^{h^0(D)-1} = \mathbb{P}^{\deg(D)-g}$。

---

### 计算题目解答

#### (a) 计算 $\dim |D|$

$g = 2$，对 $\deg(D) = d$:

**$d = 2$**:
- $h^0(D) - h^1(D) = 2 + 1 - 2 = 1$
- 一般情形: $h^1(D) = h^0(K - D)$，$\deg(K - D) = 2 - 2 = 0$
- $K - D$ 可能是有效除子（若 $D \sim K$），此时 $h^0(K - D) = 1$
- 故 $h^0(D) = 1$ 或 $2$，$\dim |D| = 0$ 或 $1$

**$d = 3$**:
- $h^0(D) - h^1(D) = 3 + 1 - 2 = 2$
- $\deg(K - D) = -1 < 0$，故 $h^1(D) = 0$
- $h^0(D) = 2$，$\dim |D| = 1$

**$d = 4$**:
- $h^0(D) - h^1(D) = 4 + 1 - 2 = 3$
- $\deg(K - D) = 0$，$h^1(D) = h^0(K - D) \leq 1$
- $h^0(D) = 3$ 或 $4$，$\dim |D| = 2$ 或 $3$

**$d = 5$**:
- $\deg(K - D) = -3 < 0$，$h^1(D) = 0$
- $h^0(D) = 4$，$\dim |D| = 3$

**汇总**:

| $d$ | $h^0(D)$ | $\dim |D|$ | 备注 |
|:---:|:---:|:---:|:---|
| 2 | 1-2 | 0-1 | 超椭圆情形 |
| 3 | 2 | 1 | 到 $\mathbb{P}^1$ 的3:1映射 |
| 4 | 3-4 | 2-3 | 可能是超椭圆 |
| 5 | 4 | 3 | 典范嵌入 |

---

#### (b) 嵌入判别

由 (c) 的定理:
- $\deg(D) \geq 5 = 2g + 1$ 时一定嵌入

$d = 4$ 情形:
- 若 $h^0(D) = 4$，给出到 $\mathbb{P}^3$ 的嵌入（非超椭圆）
- 若 $h^0(D) = 3$，到 $\mathbb{P}^2$ 的映射（超椭圆情形）

---

## 解题技巧

### 技巧1: Riemann-Roch记忆

```
┌─────────────────────────────────────────┐
│  h^0(D) - h^1(D) = deg(D) + 1 - g       │
│                                         │
│  Serre对偶: h^1(D) = h^0(K - D)         │
│  deg(K) = 2g - 2                        │
└─────────────────────────────────────────┘
```

### 技巧2: 丰沛性判据速查

| 条件 | 结论 |
|:---|:---|
| $\deg(D) \geq 2g - 1$ | $H^1(D) = 0$ |
| $\deg(D) \geq 2g$ | 整体生成 |
| $\deg(D) \geq 2g + 1$ | 非常丰沛 |

### 技巧3: 超椭圆判别

亏格 $g \geq 2$ 的曲线:
- **超椭圆**: 存在度2到 $\mathbb{P}^1$ 的映射
- **非超椭圆**: 典范映射 $K$ 是嵌入

---

## 变式与推广

### 变式1: 高亏格曲线

设 $X$ 是亏格 $g = 3$ 的光滑曲线。

**问题**: 分类所有 $D$ 使得 $\phi_D$ 是到 $\mathbb{P}^2$ 的嵌入。

---

### 变式2: 椭圆曲线

设 $E$ 是椭圆曲线（$g = 1$）。

**问题**: 证明 $\mathcal{O}_E(3P)$ 是非常丰沛的，给出 $E$ 到 $\mathbb{P}^2$ 的嵌入（Weierstrass方程）。

---

### 变式3: 一般丰沛除子

设 $X$ 是曲线，$D$ 除子。

**问题**: 证明若 $\deg(D) \geq 2g + 1$，则 $D$ 给出射影正规嵌入。

---

## 相关概念

| 概念 | 定义 | 符号 |
|:---|:---|:---:|
| 完全线性系 | $|D| = \mathbb{P}(H^0(\mathcal{L}(D)))$ | $|D|$ |
| 整体生成 | 每点有截面非零 | globally generated |
| 非常丰沛 | 诱导闭嵌入 | very ample |
| 超椭圆曲线 | 有2:1映射到$\mathbb{P}^1$ | - |

## 参考文献

1. Hartshorne, R. *Algebraic Geometry*, Ch IV, §1
2. Arbarello, Cornalba, Griffiths, Harris. *Geometry of Algebraic Curves*, Ch I
3. Griffiths, P. *Introduction to Algebraic Curves*

---

**创建日期**: 2026-04-10  
**难度**: ⭐⭐⭐  
**预计用时**: 60-90分钟
