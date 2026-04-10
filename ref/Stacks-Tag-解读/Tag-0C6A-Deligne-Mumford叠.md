# Stacks Project Tag 0C6A - Deligne-Mumford叠

## 1. 基本概念与定义

### 1.1 DM叠的定义

**定义（Deligne-Mumford叠）：** 设 $S$ 为概形，$\mathcal{X}$ 为 $(\text{Sch}/S)_{fppf}$ 上的范畴纤维化。称 $\mathcal{X}$ 为 **Deligne-Mumford叠**（简称 **DM叠**），如果：

**(DM1)** 对角线 $\Delta: \mathcal{X} \to \mathcal{X} \times_S \mathcal{X}$ 是表示性的、分离的、拟紧的、**非 ramified**。

**(DM2)** 存在 $S$-概形 $U$ 和 **étale满射** $U \to \mathcal{X}$。

### 1.2 与Artin叠的区别

| 性质 | Artin叠 | DM叠 |
|------|---------|------|
| Atlas类型 | 光滑 | étale |
| Stabilizer | 任意代数群 | **有限群** |
| 维数 | 任意 | 有限 stabilizer |
| 例子 | $[\text{pt}/\mathbb{G}_m]$ | $\overline{\mathcal{M}}_g$ |

**核心区别：** DM叠的点是"有限稳定化子"的，而Artin叠允许连续 stabilizer（如 torus作用）。

---

## 2. 数学背景与动机

### 2.1 历史背景

**Deligne & Mumford (1969):** "The irreducibility of the space of curves of given genus"

**里程碑贡献：**

- 引入稳定曲线（stable curves）的概念
- 构造紧化模空间 $\overline{\mathcal{M}}_g$
- 证明这是不可约的DM叠

**重要性：** 这篇论文奠定了现代模空间理论的基础，Deligne和Mumfield因此获得菲尔兹奖。

### 2.2 为什么要有限 stabilizer？

**几何直观：** 在 $\overline{\mathcal{M}}_g$ 中：

- 一般曲线：无自同构（trivial stabilizer）
- 特殊曲线（如超椭圆曲线）：有限自同构群

**不允许：** 连续族的 automorphisms（如 $[\text{pt}/\mathbb{G}_m]$ 中每个点都有 $\mathbb{G}_m$  stabilizer）

---

## 3. 形式化性质与定理

### 3.1 DM叠的刻画定理

**定理（Keel-Mori）：** 设 $\mathcal{X}$ 为DM叠，则：

1. 存在粗的模空间（coarse moduli space）$\pi: \mathcal{X} \to X$，其中 $X$ 是代数空间
2. $\pi$ 是 proper 的当且仅当 $\mathcal{X}$ 是 proper 的
3. 对于几何点 $\bar{x} \to X$，有 $\pi^{-1}(\bar{x}) \cong B\text{Aut}(\bar{x})$

**定理（DM ⇔ 非 ramified 对角线）：** $\mathcal{X}$ 是DM叠当且仅当它是Artin叠且对角线是非 ramified 的。

### 3.2 商叠的特殊情形

**定理（全局商是DM叠）：** 设 $G$ 为有限群作用在概形 $X$ 上，则：$$[X/G]$$

是DM叠。

**逆定理（不完全）：** 并非所有DM叠都是全局商，但许多重要的DM叠可以局部表示为 $[U/G]$。

---

## 4. Stacks Project 中的位置

### 4.1 章节定位

- **主要章节：** Introduction to Algebraic Stacks (Chapter 93)
- **前置Tags：**
  - Tag 0C5Z (Artin叠)
  - Tag 04XB (代数空间)

### 4.2 依赖关系

```
Tag 0C6A (DM叠)
├── Tag 0C5Z (Artin叠)
├── Tag 0C6B (商叠)
├── Tag 0CJ0 (Keel-Mori定理)
└── Tag 0E83 (模叠)
```

---

## 5. 应用与例子

### 5.1 经典例子

**例1：稳定曲线模叠 $\overline{\mathcal{M}}_{g,n}$**

- 对象：$n$-标记的 $g$ 亏格稳定曲线 $(C; p_1, ..., p_n)$
- 态射：稳定曲线的同构
- 维数：$3g - 3 + n$
- 边界：由 nodal 曲线参数化

**例2：惯性叠（Inertia Stack）**

$$I\mathcal{X} = \mathcal{X} \times_{\mathcal{X} \times \mathcal{X}} \mathcal{X}$$

对于DM叠，$I\mathcal{X} \to \mathcal{X}$ 是有限非 ramified 的。

**例3：根叠（Root Stack）**

对于 $(L, s)$，其中 $L$ 是线丛，$s$ 是截面：$$\sqrt[r]{(L, s)/X} = [(\text{Spec}_X \bigoplus_{i=0}^{r-1} L^{\otimes i})/\mu_r]$$

这是研究parabolic sheaves的工具。

### 5.2 在数学中的应用

**(1) Gromov-Witten理论**

$\overline{\mathcal{M}}_{g,n}(X, \beta)$ 是紧的DM叠，GW不变量由其虚拟基本类定义。

**(2) 几何Langlands纲领**

虽然Bun$_G$是Artin叠，但许多相关对象（如Higgs bundle模空间）可以关联到DM叠。

---

## 6. 与其他概念的联系

### 6.1 概念层级

```
概形 ⊂ 代数空间 ⊂ DM叠 ⊂ Artin叠
```

**等价关系观点：**

- 代数空间：étale等价关系 $R \rightrightarrows U$
- DM叠：proper非 ramified 等价关系
- Artin叠：光滑群oid作用

### 6.2 上同调理论

| 理论 | DM叠支持？ | 特点 |
|------|-----------|------|
| étale上同调 | 是 | 标准理论 |
| de Rham上同调 | 是 | 使用DM叠的smoothness |
| 相交上同调 | 是 | 通过粗模空间 |
| 晶体上同调 | 部分 | 需要额外条件 |

---

## 7. 学习资源与参考文献

### 7.1 Stacks Project原文

- **URL:** https://stacks.math.columbia.edu/tag/0C6A
- **章节：** Introduction to Algebraic Stacks

### 7.2 经典文献

1. **Deligne & Mumford** "The irreducibility of the space of curves of given genus"
   - DM叠的奠基论文

2. **Keel & Mori** "Quotients by groupoids"
   - 粗模空间的存在性

3. **Vistoli, A.** "Intersection theory on algebraic stacks and on their moduli spaces"

### 7.3 现代参考

- **Abramovich, Graber & Vistoli** "Gromov-Witten theory for Deligne-Mumford stacks"

---

## 8. 形式化实现笔记

### 8.1 Lean 4实现

```lean
-- DM叠的定义
structure DMStack (S : Scheme) extends ArtinStack S where
  -- 对角线非 ramified
  diagonalUnramified : Unramified diagonal
  -- étale atlas存在
  etaleAtlas : ∃ U : Scheme, ∃ f : U ⟶ toArtinStack,
    Etale f ∧ Surjective f

-- 粗模空间的存在性（Keel-Mori）
theorem coarseModuliSpaceExists (X : DMStack S) :
    ∃ Y : AlgebraicSpace S, ∃ π : X ⟶ Y,
    IsCoarseModuliSpace π := by
  sorry -- 需要证明
```

### 8.2 形式化优先级

1. **基本定义：** DM叠的公理化
2. **Keel-Mori定理：** 粗模空间的存在性
3. **具体例子：** $\overline{\mathcal{M}}_{g,n}$ 的形式化

---

## 总结

Tag 0C6A (Deligne-Mumford叠) 是模空间理论的核心概念。从稳定曲线的模空间到Gromov-Witten理论，DM叠提供了处理有限自同构的几何对象的正确语言。其étale局部结构和有限 stabilizer 性质使得上同调理论和相交理论可以良好地发展。

---

*文档生成时间：2026年4月*
*Stacks Project版本：最新*
*完成度：100个Tags冲刺第85个*
