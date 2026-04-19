---
title: 可表函子
msc_primary: 14
  - 18A40
  - 14D20
course: Stanford FOAG
course_code: Math 216A/B
instructor: Ravi Vakil
foag_chapter: Ch 3
topic: 范畴论在代数几何中的应用
exercise_type: CAT (范畴型)
difficulty: ⭐⭐⭐
importance: ★★
references:
  textbooks:
    - id: hartshorne_ag
      type: textbook
      title: Algebraic Geometry
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

# AG-VK-005: 可表函子

## 习题信息

| 属性 | 内容 |
|------|------|
| **课程** | Stanford FOAG (Math 216A/B) |
| **教材章节** | Ch 3: 范畴与函子 |
| **对应FOAG习题** | 3.2.A, 3.2.C, 3.3.G |
| **类型** | CAT (范畴型) |
| **难度** | ⭐⭐⭐ |
| **重要性** | ★★ |

---

## 问题陈述

### 主问题

设 $\mathcal{C}$ 是范畴，$h: \mathcal{C} \to \operatorname{PSh}(\mathcal{C}) = \operatorname{Fun}(\mathcal{C}^{\text{op}}, \text{Set})$ 是Yoneda嵌入 $X \mapsto h_X = \operatorname{Hom}(-, X)$。

**(a)** **Yoneda引理**：

证明：对任意函子 $F: \mathcal{C}^{\text{op}} \to \text{Set}$ 和对象 $X \in \mathcal{C}$，存在自然同构：
$$\operatorname{Nat}(h_X, F) \cong F(X)$$

特别地，Yoneda嵌入是完全忠实的（fully faithful）。

**(b)** 设 $F: (\text{Sch}/S)^{\text{op}} \to \text{Set}$ 是一个模函子（moduli functor）。

证明：$F$ 可表当且仅当存在 $S$-概形 $M$ 和**泛族（universal family）** $\xi \in F(M)$，使得对任意 $X \in \text{Sch}/S$ 和 $f \in F(X)$，存在唯一的 $g: X \to M$ 使得 $F(g)(\xi) = f$。

**(c)** **应用**：考虑函子
$$F(X) = \{\text{椭圆曲线 } E \to X \text{ 带截断 } 0\}/\cong$$

解释为什么 $F$ 的可表性等价于存在精细模空间（fine moduli space）$\mathcal{M}_{1,1}$。

---

## 解题思路

### 思路概述

本题涉及**现代代数几何的基础语言**：
- **Yoneda引理** - 范畴论的核心定理
- **可表函子** - 几何对象的本质定义
- **模问题** - 代数几何的驱动力

### 概念图

```
几何对象 ←────→ 函子
    │              │
    │              │
    ▼              ▼
  概形 X      h_X = Hom(-, X)
              由X"代表"的函子
              
模问题:
"参数化某类几何对象"
    │
    ▼
  函子 F: Sch^op → Set
  X ↦ {X上的对象族}
    │
    ▼
  可表? → 存在精细模空间
  不可表? → 只能用叠（stack）
```

---

## 详细解答

### (a) Yoneda引理

**定理**（Yoneda Lemma）：

设 $\mathcal{C}$ 是局部小范畴，$F: \mathcal{C}^{\text{op}} \to \text{Set}$ 是函子，$X \in \mathcal{C}$。

则：
$$\operatorname{Nat}(h_X, F) \cong F(X)$$

且这是自然于 $X$ 和 $F$ 的。

**证明**：

**构造映射** $\Phi: \operatorname{Nat}(h_X, F) \to F(X)$：

对自然变换 $\alpha: h_X \to F$，定义 $\Phi(\alpha) = \alpha_X(\text{id}_X) \in F(X)$。

**构造逆映射** $\Psi: F(X) \to \operatorname{Nat}(h_X, F)$：

对 $u \in F(X)$，定义自然变换 $\Psi(u): h_X \to F$：

对 $Y \in \mathcal{C}$，$\Psi(u)_Y: h_X(Y) = \operatorname{Hom}(Y, X) \to F(Y)$ 为：
$$\Psi(u)_Y(f) = F(f)(u) \in F(Y)$$

**验证自然性**：对 $g: Z \to Y$，需验证：
$$\Psi(u)_Z \circ h_X(g) = F(g) \circ \Psi(u)_Y$$

即对 $f: Y \to X$：
$$F(f \circ g)(u) = F(g)(F(f)(u))$$

这是函子性。

**验证互逆**：
- $\Phi(\Psi(u)) = \Psi(u)_X(\text{id}_X) = F(\text{id}_X)(u) = u$ ✓
- 对 $\alpha: h_X \to F$，需验证 $\Psi(\Phi(\alpha)) = \alpha$

对 $f: Y \to X$，$\Psi(\Phi(\alpha))_Y(f) = F(f)(\alpha_X(\text{id}_X)) = \alpha_Y(h_X(f)(\text{id}_X)) = \alpha_Y(f)$。✓

**推论**：Yoneda嵌入 $h: \mathcal{C} \to \text{PSh}(\mathcal{C})$ 是完全忠实的。

$$\operatorname{Nat}(h_X, h_Y) \cong h_Y(X) = \operatorname{Hom}(X, Y)$$∎

### (b) 可表性与泛族

**定理**：函子 $F: (\text{Sch}/S)^{\text{op}} \to \text{Set}$ 可表 $\Leftrightarrow$ 存在泛族。

**证明**：

**$(\Rightarrow)$** 设 $F \cong h_M$，即 $F(X) \cong \operatorname{Hom}_S(X, M)$ 自然于 $X$。

取 $\xi \in F(M)$ 对应 $\text{id}_M \in \operatorname{Hom}_S(M, M)$。

对任意 $X$ 和 $f \in F(X)$，设 $g: X \to M$ 对应于 $f$（通过同构）。

则 $F(g)(\xi)$ 对应 $h_M(g)(\text{id}_M) = \text{id}_M \circ g = g$，即对应 $f$。

唯一性由同构的单射性保证。

**$(\Leftarrow)$** 设存在泛族 $\xi \in F(M)$。

定义自然变换 $\alpha: h_M \to F$：对 $g: X \to M$，$\alpha_X(g) = F(g)(\xi) \in F(X)$。

泛性质说：对任意 $f \in F(X)$，存在唯一 $g$ 使 $\alpha_X(g) = f$。

即 $\alpha_X$ 是双射，故 $\alpha$ 是自然同构。∎

### (c) 椭圆曲线模空间

**椭圆曲线函子**：

$$F(X) = \{(E \to X, 0: X \to E)\} / \cong$$

其中 $E \to X$ 是带单位截断的椭圆曲线（光滑、真、相对维数1的群概形）。

**精细模空间**：

$F$ 可表 $\Leftrightarrow$ 存在 $S$-概形 $\mathcal{M}_{1,1}$ 和泛椭圆曲线 $\mathcal{E} \to \mathcal{M}_{1,1}$，使得：

对任意椭圆曲线 $E \to X$，存在唯一 $g: X \to \mathcal{M}_{1,1}$ 使得 $E \cong g^*\mathcal{E}$。

**现实情况**：

- 当考虑带标架（level structure）的椭圆曲线时，可表
- 无标架的原始问题：$F$ 不可表（由 $j$-不变量看出：椭圆曲线有自同构）
- 解决方法：使用 Deligne-Mumford 叠（stack）$\mathcal{M}_{1,1}$

---

## 关键概念

### Yoneda哲学

> "对象由其与其他对象的关系完全决定"

| 概念 | 含义 |
|------|------|
| $h_X$ | $X$ 的"外部观点" - 所有到 $X$ 的映射 |
| Yoneda引理 | 自然变换 $\cong$ 元素 |
| 可表函子 | $F \cong h_M$ - $F$ 有"几何化身" $M$ |

### 模问题

**粗模空间 (Coarse Moduli)**：
- $M$ 是概形
- 存在"泛"映射 $F \to h_M$（不是同构）
- 几何点对应：$F(\text{Spec } k)/\cong \cong M(k)$

**精细模空间 (Fine Moduli)**：
- $F$ 可表
- 存在泛族
- 更强的条件

**叠 (Stack)**：
- 当自同构存在时，函子不可表
- 叠允许"带自同构的对象"
- 代数叠（Deligne-Mumford 或 Artin）处理模问题

---

## 重要例子

### 可表函子的例子

| 函子 | 代表 | 说明 |
|------|------|------|
| $X \mapsto \Gamma(X, \mathcal{O}_X)$ | $\mathbb{A}^1$ | 仿射直线 |
| $X \mapsto \Gamma(X, \mathcal{O}_X)^\times$ | $\mathbb{G}_m$ | 乘法群 |
| $X \mapsto \operatorname{GL}_n(\Gamma(X, \mathcal{O}_X))$ | $\operatorname{GL}_n$ | 一般线性群 |
| $X \mapsto \{\text{线丛商 } \mathcal{O}_X^{n+1} \twoheadrightarrow \mathcal{L}\}$ | $\mathbb{P}^n$ | 射影空间 |

### 不可表函子的例子

| 函子 | 问题 | 解决方法 |
|------|------|----------|
| 椭圆曲线（无标架） | 存在非平凡自同构 | 使用叠 $\mathcal{M}_{1,1}$ |
| 向量丛（秩固定） | 需要固定额外的稳定性条件 | 使用 Quot 概形 |
| 曲线（亏格固定） | $M_g$ 只在 $g \geq 2$ 是 Deligne-Mumford 叠 | 叠/粗模空间 |

---

## 变式练习

### 变式 1: 可表函子的唯一性

证明：若 $F \cong h_M$ 且 $F \cong h_{M'}$，则 $M \cong M'$（在同构意义下唯一）。

**提示**：利用Yoneda引理，$h_M \cong h_{M'}$ 给出 $\operatorname{Hom}(-, M) \cong \operatorname{Hom}(-, M')$，特别地在 $M$ 处取值。

### 变式 2: Hilbert概形的存在

陈述Hilbert概形的存在定理：对射影概形 $X$，函子
$$F(T) = \{\text{闭子概形 } Z \subset X \times T, \text{平坦于 } T\}$$
是可表的。

### 变式 3: 可表性与极限

证明：可表函子保持所有极限（左正合），而可表性本身涉及余极限。

---

## 常见错误

| 错误 | 纠正 |
|------|------|
| 混淆自然变换与集合映射 | Yoneda引理给出的是自然变换 |
| 认为所有模问题可表 | 自同构的存在往往阻碍可表性 |
| 忽略基底 | 可表性是相对于基底范畴的 |

---

## 学习建议

1. **理解Yoneda哲学**：对象由其关系决定
2. **练习函子语言**：现代代数几何的基础
3. **研究模问题的例子**：从可表到不可表的各种情况

---

**文档位置**: `docs/13-代数几何/习题/AG-VK-005-可表函子.md`  
**创建日期**: 2026-04-10  
**最后更新**: 2026-04-10
