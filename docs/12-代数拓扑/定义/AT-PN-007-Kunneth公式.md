---
msc_primary: 55A99
university: Princeton
synonym: [Kunneth Formula, Kunneth定理, 积空间同调]
type: 定义
level: L3-理论建构层
difficulty: ⭐⭐⭐⭐⭐
concept_dependency: [张量积, Tor函子, 同调群]
prerequisite_concepts: [同调群, 张量积, Ext函子, Tor函子]
prerequisite_theorems: [万有系数定理, 代数Kunneth公式]
course_context: MAT 365 Topology
msc2010: [55N10, 55U25, 18G15]
related_concepts: [万有系数定理, 上同调的Kunneth公式, 纤维丛]
---

# AT-PN-007: Kunneth公式 (Kunneth Formula)

> **来源**: Princeton MAT 365 (Topology) | Hatcher Chapter 3, Section B, p. 274-275
> **级别**: 本科高阶/研究生初级
> **领域**: 代数拓扑 · 同调论

---

## 定义

### 几何Kunneth公式（同调）

**定理（Kunneth Formula）**：设 $X, Y$ 是拓扑空间，且 $H_i(X)$ 是有限生成自由Abel群（或系数域）。则存在自然短正合序列：

$$0 \to \bigoplus_{i+j=n} H_i(X) \otimes H_j(Y) \to H_n(X \times Y) \to \bigoplus_{i+j=n-1} \text{Tor}(H_i(X), H_j(Y)) \to 0$$

且该序列分裂（非自然）。因此：

$$H_n(X \times Y) \cong \bigoplus_{i+j=n} H_i(X) \otimes H_j(Y) \oplus \bigoplus_{i+j=n-1} \text{Tor}(H_i(X), H_j(Y))$$

### 几何Kunneth公式（上同调）

**定理**：在上同调中，存在环同构（系数为域 $F$ 时）：

$$H^*(X \times Y; F) \cong H^*(X; F) \otimes_F H^*(Y; F)$$

作为**分次** $F$-代数，右端配备：

- $(a \otimes b)(c \otimes d) = (-1)^{|b||c|} ac \otimes bd$（分次乘法）

### 代数Kunneth公式

**定理**：设 $(C_*, d_C)$ 和 $(D_*, d_D)$ 是自由链复形。则存在自然短正合序列：

$$0 \to \bigoplus_{i+j=n} H_i(C) \otimes H_j(D) \to H_n(C \otimes D) \to \bigoplus_{i+j=n-1} \text{Tor}(H_i(C), H_j(D)) \to 0$$

---

## 例子

### 例1：环面 $T^2 = S^1 \times S^1$

**计算**：$H_0(S^1) = H_1(S^1) = \mathbb{Z}$，其他为0。

$$H_0(T^2) = H_0(S^1) \otimes H_0(S^1) = \mathbb{Z} \otimes \mathbb{Z} = \mathbb{Z}$$

$$H_1(T^2) = (H_1 \otimes H_0) \oplus (H_0 \otimes H_1) = \mathbb{Z} \oplus \mathbb{Z}$$

$$H_2(T^2) = H_1(S^1) \otimes H_1(S^1) = \mathbb{Z} \otimes \mathbb{Z} = \mathbb{Z}$$

与已知结果一致。

### 例2：高维环面 $T^n = (S^1)^n$

**定理**：$H_k(T^n) = \mathbb{Z}^{\binom{n}{k}}$

**证明**：由Kunneth公式归纳，$H_*(T^n) = H_*(S^1)^{\otimes n}$。$\square$

### 例3：积空间 $S^2 \times S^3$

**计算**：

- $H_0 = \mathbb{Z}$
- $H_2 = \mathbb{Z}$（来自 $H_2(S^2) \otimes H_0(S^3)$）
- $H_3 = \mathbb{Z}$（来自 $H_0(S^2) \otimes H_3(S^3)$）
- $H_5 = \mathbb{Z}$（来自 $H_2(S^2) \otimes H_3(S^3)$）

### 例4：带挠系数的情况

设 $X = \mathbb{R}P^2$，$Y = \mathbb{R}P^2$。则 $H_1(X) = H_1(Y) = \mathbb{Z}/2$。

$$\text{Tor}(H_1(X), H_1(Y)) = \text{Tor}(\mathbb{Z}/2, \mathbb{Z}/2) = \mathbb{Z}/2$$

因此在 $H_2(X \times Y)$ 中出现Tor项。

---

## 性质

### 分裂性

**注**：Kunneth序列分裂（作为Abel群），但分裂不自然。这意味着虽然 $H_n(X \times Y)$ 作为群同构于直和，但没有典范的选择。

### 域系数的情形

**定理**：若 $F$ 是域，则：

$$H_n(X \times Y; F) \cong \bigoplus_{i+j=n} H_i(X; F) \otimes_F H_j(Y; F)$$

（无Tor项，因为域上模都是自由的）

### 相对Kunneth公式

**定理**：对空间对 $(X, A)$ 和 $(Y, B)$，有类似的相对Kunneth公式。

### 与杯积的关系

Kunneth公式与上同调的杯积密切相关：外积 $H^*(X) \otimes H^*(Y) \to H^*(X \times Y)$ 是环同态。

---

## FormalMath对应

### 主要文档

- `docs/05-拓扑学/02-代数拓扑.md` — 积空间同调
- `docs/00-习题示例反例库/拓扑/TOP-054-Künneth公式.md` — 计算练习

### 概念映射

| Princeton MAT 365 | FormalMath |
|------------------|------------|
| Kunneth公式 | `代数拓扑/Kunneth公式` |
| 张量积 | `同调代数/张量积` |
| Tor函子 | `同调代数/Tor函子` |

### Lean 4形式化参考

```lean
-- Tor和Ext函子是导出函子
-- 张量积在同调代数中有广泛实现
import Mathlib.Algebra.Homology.Homology

-- 链复形的张量积
variable {C D : ChainComplex (Module R)}
#check C ⊗ D  -- 链复形的张量积
```

### 交叉引用

- **前序定义**: AT-PN-004 (奇异同调), AT-PN-005 (胞腔同调)
- **相关概念**: 万有系数定理
- **后续应用**: AT-PN-008 (示性类的计算)

---

## Hatcher参考

- **章节**: Chapter 3, Section B, "The General Kunneth Formula", p. 274-275
- **关键内容**：
  - 几何Kunneth公式 (p. 274)
  - 相对Kunneth公式
  - 与万有系数定理的关系
- **关键习题**:
  - Exercise 3.B.1: 计算 $\mathbb{R}P^m \times \mathbb{R}P^n$ 的同调
  - Exercise 3.B.4: 利用Kunneth公式计算 $H^*(\Omega S^{n+1})$

---

## 总结

Kunneth公式提供了计算积空间同调的系统性方法，将复杂的几何问题转化为代数的张量积计算。

**关键要点**：

1. Kunneth公式将 $H_*(X \times Y)$ 与 $H_*(X)$ 和 $H_*(Y)$ 联系起来
2. 包含张量积项和Tor修正项
3. 域系数时无Tor项
4. 是计算复杂空间同调的有力工具
