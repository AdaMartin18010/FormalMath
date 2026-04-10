# Stacks Project Tag 04E2 - 上同调运算（Cup Product）

## 1. 基本概念与定义

### 1.1 定义

**Cup积（Cup Product）**是代数拓扑和代数几何中上同调理论的核心结构，它将两个上同调类相乘得到一个新的上同调类。

设 $X$ 为拓扑空间（或概形），$A$ 为系数环。对于上同调群 $\cup: H^i(X, A) \times H^j(X, A) \to H^{i+j}(X, A)$，Cup积定义为：

$$[\alpha] \cup [\beta] = [\alpha \smile \beta]$$

其中 $\smile$ 表示链复形层面的乘积运算。

### 1.2 构造方法

**单纯形上同调中的构造：**

对于奇异上链 $\alpha \in C^i(X)$ 和 $\beta \in C^j(X)$：$(\alpha \smile \beta)(\sigma) = \alpha(\sigma|_{[v_0, ..., v_i]}) \cdot \beta(\sigma|_{[v_i, ..., v_{i+j}]})$

其中 $\sigma: \Delta^{i+j} \to X$ 是奇异单形。

**层上同调中的构造：**

对于层 $\mathcal{F}$ 和 $\mathcal{G}$，Cup积通过导出函子构造：$\cup: R^i\Gamma(X, \mathcal{F}) \times R^j\Gamma(X, \mathcal{G}) \to R^{i+j}\Gamma(X, \mathcal{F} \otimes \mathcal{G})$

---

## 2. 数学背景与动机

### 2.1 历史背景

Cup积由 **J. W. Alexander** (1936) 和 **E. Čech** 独立引入，后来由 **H. Whitney** 系统化。

**动机问题：**

- 如何将上同调群组织成具有乘积结构的代数对象？
- 如何从代数角度捕捉空间的交截性质？
- 如何将庞加莱对偶代数化？

### 2.2 理论地位

Cup积是上同调区别于同调的关键特征：

| 特征 | 同调 | 上同调 |
|------|------|--------|
| 方向 | 协变 | 反变 |
| 乘积 | 无自然乘积 | 有Cup积 |
| 代数结构 | 模 | 分次代数 |

---

## 3. 形式化性质与定理

### 3.1 基本性质

**定理（Cup积的基本性质）：** Cup积满足：

**(1) 分次交换性：** 对于 $a \in H^i(X)$, $b \in H^j(X)$：$$a \cup b = (-1)^{ij} b \cup a$$

**(2) 结合律：** $$(a \cup b) \cup c = a \cup (b \cup c)$$

**(3) 单位元：** 存在 $1 \in H^0(X)$ 使得 $1 \cup a = a \cup 1 = a$

### 3.2 函子性

**定理（Cup积的函子性）：** 设 $f: X \to Y$ 为连续映射，则：$$f^*(a \cup b) = f^*(a) \cup f^*(b)$$

即 pullback 保持Cup积结构。

### 3.3 与层上同调的关系

**定理（Godement）：** 对于概形 $X$ 上的拟凝聚层，Čech上同调中的Cup积与导出函子定义的Cup积一致。

---

## 4. Stacks Project 中的位置

### 4.1 章节定位

- **主要章节：** 上同调理论（Cohomology）
- **相关章节：** 代数拓扑、étale上同调、晶体上同调
- **前置Tags：**
  - Tag 01DW（层上同调基础）
  - Tag 01DX（Čech上同调）

### 4.2 依赖关系

```
Tag 04E2 (Cup积)
├── Tag 01DW (层上同调)
├── Tag 01DX (Čech上同调)
└── Tag 03FD (导出范畴)
```

---

## 5. 应用与例子

### 5.1 计算示例

**示例1：环面的上同调环**

对于 $T = S^1 \times S^1$：$H^*(T; \mathbb{Z}) = \Lambda(x_1, x_2)$（外代数）

其中 $|x_1| = |x_2| = 1$，满足 $x_1 \cup x_2 = -x_2 \cup x_1$

**示例2：复射影空间**

$H^*(\mathbb{CP}^n; \mathbb{Z}) = \mathbb{Z}[h]/(h^{n+1})$，其中 $h \in H^2(\mathbb{CP}^n)$

这显示了Cup积如何生成整个上同调结构。

### 5.2 在代数几何中的应用

**(1) 相交理论：** Cup积对应子簇的相交积

**(2) 陈类计算：** 陈类的Whitney和公式使用Cup积：$$c(E \oplus F) = c(E) \cup c(F)$$

**(3) Lefschetz迹公式：** $$\sum_{i=0}^{2n} (-1)^i \text{Tr}(f^*|_{H^i(X)}) = \#\text{Fix}(f)$$

---

## 6. 与其他概念的联系

### 6.1 概念网络

```
Cup积 (04E2)
│
├── 上同调环结构 (04E3)
├── 庞加莱对偶
├── 相交理论 (04E4)
├── 陈类理论
├── K-理论
└── 配边理论
```

### 6.2 不同上同调理论中的Cup积

| 理论 | Cup积特点 |
|------|----------|
| 奇异上同调 | 几何构造，单纯形分解 |
| de Rham上同调 | 楔积 of differential forms |
| étale上同调 | Grothendieck拓扑上的层张量积 |
| 晶体上同调 | 微分算子的复合 |

---

## 7. 学习资源与参考文献

### 7.1 Stacks Project原文

- **URL:** https://stacks.math.columbia.edu/tag/04E2
- **章节：** Cohomology on Sites, Section 20.31

### 7.2 推荐教材

1. **Hatcher, A.** *Algebraic Topology*, Chapter 3
   - Cup积的详细几何解释

2. **Bott & Tu** *Differential Forms in Algebraic Topology*
   - de Rham上同调中的Cup积 = 微分形式的楔积

3. **Griffiths & Harris** *Principles of Algebraic Geometry*
   - Kähler流形中的Cup积与Hodge理论

### 7.3 进阶文献

- **Milne, J.S.** *Étale Cohomology*, Chapter V
- **Deligne, P.** *SGA 4½*, Arcata

---

## 8. 形式化实现笔记

### 8.1 Lean 4形式化方向

```lean
-- Cup积的分次交换性
lemma cup_product_graded_commutative
    {i j : ℕ} (a : H^i(X, R)) (b : H^j(X, R)) :
    a ∪ b = (-1)^(i*j) • (b ∪ a) := by
  sorry -- 需要证明
```

### 8.2 形式化挑战

1. **分次符号：** $(-1)^{ij}$ 的正确处理
2. **链同伦：** 证明Cup积在同调水平良定义
3. **函子性：** pullback与Cup积的交换性

### 8.3 相关形式化项目

- **mathlib4:** `AlgebraicTopology.SimplicialSet`
- **Liquid Tensor Experiment:** 层上同调的形式化

---

## 总结

Tag 04E2 (Cup积) 是上同调理论的基石，它将上同调群提升为分次交换代数，为相交理论、示性类理论和算术几何提供了代数框架。

---

*文档生成时间：2026年4月*
*Stacks Project版本：最新*
*完成度：100个Tags冲刺第81个*
