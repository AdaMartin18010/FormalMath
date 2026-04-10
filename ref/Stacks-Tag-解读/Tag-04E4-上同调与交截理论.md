# Stacks Project Tag 04E4 - 上同调与交截理论

## 1. 基本概念与定义

### 1.1 交截理论的代数几何版本

**交截理论（Intersection Theory）** 研究代数簇的子簇如何相交，以及如何用代数不变量量化这种相交。

设 $X$ 为光滑拟射影簇，$V, W \subseteq X$ 为子簇，**交截积**定义为：$$V \cdot W = \sum_{Z \subseteq V \cap W} i(Z, V \cdot W; X) \cdot [Z]$$

其中 $i(Z, V \cdot W; X)$ 为**相交重数**。

### 1.2 上同调解释

**核心对应：** 子簇 $\leftrightarrow$ 上同调类

对于余维数 $r$ 的闭子簇 $V \subseteq X$：$$[V] \in H^{2r}(X, \mathbb{Z}(r))$$

**交截积 = Cup积：** $$[V \cap W] = [V] \cup [W]$$

---

## 2. 数学背景与动机

### 2.1 历史脉络

**古典时期（19世纪）：** Bezout定理

- 平面中两条曲线 $C_1, C_2$ 的次数分别为 $d_1, d_2$
- 相交点数 = $d_1 \cdot d_2$（计入重数）

**Weil (1940s)：** 代数循环与相交理论的形式化

**Chow (1950s)：** Chow环的构造

**Grothendieck (1960s)：** 用K-理论和层上同调重新解释

### 2.2 为什么要用层上同调？

**问题：** 奇异簇上的相交理论如何定义？

**解决方案：** 将子簇替换为层，交截积替换为导出张量积。

**交截积的上同调公式：** $$[V] \cdot [W] = \sum_i (-1)^i [\text{Tor}_i^{\mathcal{O}_X}(\mathcal{O}_V, \mathcal{O}_W)]$$

---

## 3. 形式化性质与定理

### 3.1 交截理论的基本定理

**定理（相交重数的计算）：** 设 $V, W \subseteq X$ 横截相交于 $Z$，则：$$i(Z, V \cdot W; X) = \text{length}_{\mathcal{O}_{X,Z}}(\mathcal{O}_{V,Z} \otimes_{\mathcal{O}_{X,Z}} \mathcal{O}_{W,Z})$$

**定理（上同调类与交截的相容性）：** Cup积与几何交截相容：$$\text{cl}(V \cap W) = \text{cl}(V) \cup \text{cl}(W)$$

其中 $\text{cl}: Z^r(X) \to H^{2r}(X)$ 为循环类映射。

### 3.2 弗罗贝尼乌斯互反性

**定理（Proper Pushforward与Pullback）：** 设 $f: X \to Y$ 为proper映射，$g: Y' \to Y$ 为任意映射，形成纤维积：

$$\begin{array}{ccc}
X' & \xrightarrow{g'} & X \\
\downarrow{f'} & & \downarrow{f} \\
Y' & \xrightarrow{g} & Y
\end{array}$$

则：$f'_* \circ g'^* = g^* \circ f_*: A_*(X) \to A_*(Y')$

---

## 4. Stacks Project 中的位置

### 4.1 章节定位

- **主要章节：** Intersection Theory (Chapter 42)
- **前置Tags：**
  - Tag 04E2 (Cup积)
  - Tag 04E3 (上同调环)
- **后续Tags：**
  - Tag 0F1C (算术D-模)
  - Tag 0C6A (Deligne-Mumford叠)

### 4.2 依赖关系

```
Tag 04E4 (交截理论)
├── Tag 04E2 (Cup积)
├── Tag 04E3 (上同调环)
├── Tag 02OO (Chow群)
├── Tag 02P3 (代数循环)
└── Tag 0A5Q (导出范畴)
```

---

## 5. 应用与例子

### 5.1 经典计算

**例1：Bezout定理的现代证明**

设 $C_1, C_2 \subseteq \mathbb{P}^2$ 为次数 $d_1, d_2$ 的曲线。在上同调环中：$$[C_1] = d_1 [H], \quad [C_2] = d_2 [H]$$

因此：$$[C_1 \cap C_2] = [C_1] \cup [C_2] = d_1 d_2 [H]^2 = d_1 d_2 [\text{pt}]$$

**例2：自交数（Self-intersection）**

在曲面 $S$ 上，曲线 $C \subseteq S$ 的自交数：$$C^2 = \deg(\mathcal{O}_S(C)|_C) = \int_C c_1(\mathcal{O}_S(C))$$

这是相交理论的核心不变量。

### 5.2 在代数几何中的应用

**(1) 计数几何（Enumerative Geometry）**

问：过5个一般点有多少条圆锥曲线？

答：使用 $\overline{M}_{0,5}(\mathbb{P}^2, 2)$ 上的相交理论计算，答案为 **1**。

**(2) 双有理几何**

 exceptional divisor $E$ 的自交数 $E^2 = -1$ 刻画了收缩映射。

---

## 6. 与其他概念的联系

### 6.1 概念网络

```
交截理论 (04E4)
│
├── Chow环 ──→ Motives
├── K-理论 ──→ 黎曼-罗赫定理
├── 层上同调 ──→ Serre对偶
├── 形变理论 ──→ 虚基本类
└── Gromov-Witten理论 ──→ 镜像对称
```

### 6.2 现代发展

| 理论 | 核心思想 | 代表人物 |
|------|----------|----------|
| 虚拟交截理论 | 使用障碍理论定义虚拟基本类 | Behrend-Fantechi |
| GW理论 | 稳定映射模空间的相交 | Kontsevich |
| 导出交截 | $V \cap^{\text{der}} W = V \times_X^h W$ | 导出代数几何 |

---

## 7. 学习资源与参考文献

### 7.1 Stacks Project原文

- **URL:** https://stacks.math.columbia.edu/tag/04E4
- **章节：** Chapter 42 - Intersection Theory

### 7.2 核心教材

1. **Fulton, W.** *Intersection Theory* (2nd ed.)
   - 交截理论的圣经

2. **Eisenbud & Harris** *3264 and All That*
   - 交截理论的直观介绍

3. **Voisin, C.** *Hodge Theory and Complex Algebraic Geometry*
   - 上同调观点的交截理论

### 7.3 研究论文

- **Behrend & Fantechi** "The intrinsic normal cone"
- **Li & Tian** "Virtual moduli cycles and Gromov-Witten invariants"

---

## 8. 形式化实现笔记

### 8.1 Lean 4实现方向

```lean
-- 交截积的定义
noncomputable def intersectionProduct
    {X : Scheme} [IsSmooth X]
    (V W : AlgebraicCycle X) : AlgebraicCycle X :=
  cycleClassInv (cycleClass V ∪ cycleClass W)

-- 相交重数
def intersectionMultiplicity
    {X : Scheme} (Z V W : ClosedImmersion X) : ℕ :=
  sorry -- 需要Length/Depth的形式化
```

### 8.2 形式化难点

1. **相交重数的正确定义：** Serre的Tor公式需要同调代数
2. **Proper pushforward的构造：** 需要紧支上同调
3. **精炼相交（Refined Intersection）：** 需要支持在子集上的层

### 8.3 相关形式化项目

- **mathlib4:** `AlgebraicGeometry.Scheme`
- ** sphere eversion:** 需要交截理论的工具

---

## 总结

Tag 04E4 (上同调与交截理论) 是代数几何的核心内容，建立了几何交截与代数运算之间的深刻联系。这一理论不仅解决了古典计数几何问题，也是现代枚举几何和数学物理的基础。

---

*文档生成时间：2026年4月*
*Stacks Project版本：最新*
*完成度：100个Tags冲刺第83个*
