---
习题编号: AG-EX-010
标题: 典范嵌入
类型: 几何型
难度: ⭐⭐⭐⭐
章节: Hartshorne Ch IV
对应课程: Harvard Math 232br
预计用时: 120-150分钟
msc: 14H45, 14H51
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

# AG-EX-010: 典范嵌入

## 题目

### 原题 (Hartshorne IV.3.1 + IV.5.2)

设 $X$ 是亏格 $g \geq 2$ 的光滑射影曲线，$K$ 是典范除子。

**(a)** 证明典范映射 $\phi_K: X \to \mathbb{P}^{g-1}$ 是嵌入当且仅当 $X$ 是非超椭圆曲线。

**(b)** 对超椭圆曲线，描述 $\phi_K$ 的像和映射的度数。

**(c)** 证明非超椭圆曲线的典范像 $X \subseteq \mathbb{P}^{g-1}$ 是射影正规的。

### 计算题目

设 $X$ 是亏格3的光滑曲线。

**(a)** 若 $X$ 是非超椭圆的，证明典范嵌入给出 $X$ 作为 $\mathbb{P}^2$ 中的四次光滑曲线。

**(b)** 若 $X$ 是超椭圆的，描述典范映射。

**(c)** 计算两种情况下的截面空间维数 $h^0(nK)$。

---

## 解答

### 主题目解答

#### (a) 典范嵌入判据

**定义**: 典范映射 $\phi_K: X \to \mathbb{P}^{g-1}$ 由完全线性系 $|K|$ 诱导。

**Riemann-Roch**: 
$$h^0(K) = g, \quad h^1(K) = 1$$

**证明**:

**Step 1**: 超椭圆曲线的情形。

若 $X$ 超椭圆，存在2:1映射 $\pi: X \to \mathbb{P}^1$。

由超椭圆曲线理论:
$$K = \pi^*((g-1)\cdot[\infty]) = (g-1)g_2^1$$

其中 $g_2^1$ 是 $\pi$ 的纤维。

$|K|$ 由 $\pi$ 拉回给出，故 $\phi_K$ 分解为:
$$X \xrightarrow{\pi} \mathbb{P}^1 \xrightarrow{v_{g-1}} \mathbb{P}^{g-1}$$

$v_{g-1}$ 是 $(g-1)$-次Veronese嵌入。

**结论**: $\phi_K(X) \cong \mathbb{P}^1$，不是嵌入。

---

**Step 2**: 非超椭圆曲线的情形。

需证 $\phi_K$ 分离点和切向量。

**分离点**: 对 $P \neq Q$，需 $h^0(K - P - Q) = h^0(K) - 2 = g - 2$。

由Riemann-Roch:
$$h^0(K - P - Q) - h^1(K - P - Q) = (2g - 2) - 2 + 1 - g = g - 3$$

$$h^1(K - P - Q) = h^0(P + Q)$$

若 $h^0(P + Q) \geq 2$，则存在2:1映射，$X$ 超椭圆，矛盾。

故 $h^0(P + Q) = 1$（只有常函数），$h^0(K - P - Q) = g - 2$。

**分离切向量**: 对任意 $P$，需 $h^0(K - 2P) = g - 2$。

类似计算，由非超椭圆性保证。

**结论**: $\phi_K$ 是嵌入。

---

#### (b) 超椭圆曲线的典范像

**像**: $\phi_K(X) \cong \mathbb{P}^1 \subseteq \mathbb{P}^{g-1}$，是 $(g-1)$-次有理正规曲线。

**映射度数**: $\deg(\phi_K) = 2$（因 $\pi$ 是2:1）。

**方程**: 像由所有 $2 \times 2$ 子式定义（Grassmann-Plücker关系）。

---

#### (c) 射影正规性

**定义**: $X \subseteq \mathbb{P}^n$ 射影正规是指:
$$H^0(\mathbb{P}^n, \mathcal{O}(m)) \to H^0(X, \mathcal{O}_X(m))$$

对所有 $m \geq 0$ 满射。

等价于: 齐次坐标环是整闭的。

**证明**:

对典范嵌入 $X \subseteq \mathbb{P}^{g-1}$，$\mathcal{O}_X(1) = K$。

需证:
$$H^0(\mathbb{P}^{g-1}, \mathcal{O}(m)) \to H^0(X, K^{\otimes m})$$

满射。

由Noether定理（非超椭圆曲线），典范曲线的齐次理想由二次型生成。

射影正规性可从Max Noether定理推出:

**Max Noether定理**: 对非超椭圆曲线，乘法映射:
$$H^0(K)^{\otimes m} \to H^0(K^{\otimes m})$$

满射对所有 $m \geq 0$。

**结论**: 典范像是射影正规的。

---

### 计算题目解答

#### (a) 非超椭圆亏格3曲线

**典范嵌入**:

$g = 3$，$\deg(K) = 2g - 2 = 4$。

$\phi_K: X \to \mathbb{P}^{g-1} = \mathbb{P}^2$。

**像的次数**:

$\deg(\phi_K(X)) = \deg(K) = 4$（因 $\phi_K$ 是嵌入）。

**光滑性**: $X$ 光滑 $\Rightarrow$ 像光滑。

**结论**: $X$ 是 $\mathbb{P}^2$ 中的光滑四次曲线。

**注**: 非超椭圆亏格3曲线 = 光滑平面四次曲线。

---

#### (b) 超椭圆亏格3曲线

**典范映射**:

$\phi_K: X \to \mathbb{P}^2$，像为 $\mathbb{P}^1$（通过Veronese嵌入）。

具体: $\phi_K = v_2 \circ \pi$，其中:
- $\pi: X \to \mathbb{P}^1$ 是2:1映射
- $v_2: \mathbb{P}^1 \to \mathbb{P}^2$ 是二次Veronese嵌入

**像**: $v_2(\mathbb{P}^1) \subseteq \mathbb{P}^2$ 是光滑二次曲线（圆锥曲线）。

**结论**: $\phi_K(X)$ 是圆锥曲线，$\phi_K$ 是2:1映射到圆锥曲线。

---

#### (c) 截面维数

**非超椭圆** ($X \subseteq \mathbb{P}^2$ 四次曲线):

$K = \mathcal{O}_X(1)$（超平面截口）。

$$H^0(nK) = H^0(\mathcal{O}_X(n))$$

由正合列:
$$0 \to \mathcal{O}_{\mathbb{P}^2}(n-4) \to \mathcal{O}_{\mathbb{P}^2}(n) \to \mathcal{O}_X(n) \to 0$$

计算:
- $n = 1$: $h^0(K) = 3 = g$ ✓
- $n = 2$: $h^0(2K) = h^0(\mathcal{O}_{\mathbb{P}^2}(2)) - h^0(\mathcal{O}_{\mathbb{P}^2}(-2)) = 6 - 0 = 6$

**超椭圆**:

$K = (g-1)g_2^1 = 2g_2^1$（两个纤维的线性组合）。

由Riemann-Roch:
$$h^0(nK) = n(2g-2) + 1 - g = n \cdot 4 + 1 - 3 = 4n - 2$$

对 $n \geq 2$。

---

## 解题技巧

### 技巧1: 典范嵌入速查

```
┌─────────────────────────────────────────┐
│  典范映射 φ_K: X → P^{g-1}             │
│                                         │
│  超椭圆: φ_K = v_{g-1} ∘ π, deg = 2    │
│           像 ≅ P^1                     │
│                                         │
│  非超椭圆: 嵌入, 像 = X ⊆ P^{g-1}      │
│            deg(X) = 2g - 2             │
└─────────────────────────────────────────┘
```

### 技巧2: 超椭圆判别

| 亏格 | 超椭圆 | 典范像 |
|:---:|:---:|:---|
| 2 | 全部 | P^1（6次覆盖） |
| 3 | 存在 | 圆锥曲线 |
| $\geq 3$ | 一般非超椭圆 | 一般典范曲线 |

### 技巧3: 亏格3曲线分类

```
亏格3曲线:
├─ 超椭圆: y^2 = f(x), deg(f) = 8
│          典范像 = 圆锥曲线
└─ 非超椭圆: 光滑平面四次
            典范像 = 自身 ⊆ P^2
```

---

## 变式与推广

### 变式1: 亏格4曲线

**问题**: 描述非超椭圆亏格4曲线的典范嵌入。

**答案**: $X \subseteq \mathbb{P}^3$ 是二次和三次曲面的完全交。

---

### 变式2: 亏格5曲线

**问题**: 一般亏格5曲线的典范像是什么？

**答案**: $X \subseteq \mathbb{P}^4$，是三个二次超曲面的完全交。

---

### 变式3: Petri定理

**定理**: 非超椭圆典范曲线 $X \subseteq \mathbb{P}^{g-1}$ 的理想由二次型生成，除非 $X$ 是三次的或类四次的。

**问题**: 解释何为"类四次"曲线。

---

## 相关概念

| 概念 | 定义 | 符号 |
|:---|:---|:---:|
| 典范除子 | 微分形式的除子 | $K$ |
| 典范映射 | $|K|$ 诱导的映射 | $\phi_K$ |
| 超椭圆曲线 | 有2:1到$\mathbb{P}^1$的曲线 | - |
| 射影正规 | 坐标环整闭 | - |

## 参考文献

1. Hartshorne, R. *Algebraic Geometry*, Ch IV, §3-5
2. Arbarello et al. *Geometry of Algebraic Curves*, Ch III
3. Griffiths, Harris. *Principles of Algebraic Geometry*, Ch 2

---

**创建日期**: 2026-04-10  
**难度**: ⭐⭐⭐⭐  
**预计用时**: 120-150分钟
