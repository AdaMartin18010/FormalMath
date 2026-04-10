---
university: Princeton
synonym: [Homotopy Equivalence, 同伦型, 形变收缩]
type: 定义
level: L3-理论建构层
difficulty: ⭐⭐
concept_dependency: [拓扑空间, 连续映射, 同伦]
prerequisite_concepts: [拓扑空间, 连续映射]
prerequisite_theorems: []
course_context: MAT 365 Topology
msc2010: [55P10, 55P05]
related_concepts: [形变收缩, 同伦型, 可缩空间]
---

# AT-PN-001: 同伦等价 (Homotopy Equivalence)

> **来源**: Princeton MAT 365 (Topology) | Hatcher Chapter 0, p. 3-4
> **级别**: 本科高阶/研究生初级
> **领域**: 代数拓扑 · 同伦论

---

## 定义

### 正式定义

设 $X$ 和 $Y$ 是拓扑空间。连续映射 $f: X \to Y$ 称为**同伦等价**（homotopy equivalence），如果存在连续映射 $g: Y \to X$（称为 $f$ 的**同伦逆**），使得：

$$g \circ f \simeq \text{id}_X \quad \text{且} \quad f \circ g \simeq \text{id}_Y$$

即复合映射同伦于恒等映射。如果存在同伦等价 $f: X \to Y$，则称空间 $X$ 和 $Y$ 具有相同的**同伦型**（homotopy type），记作 $X \simeq Y$。

### 形变收缩（强同伦等价）

子空间 $A \subset X$ 称为 $X$ 的**形变收缩核**（deformation retract），如果存在**收缩**（retraction）$r: X \to A$（即 $r|_A = \text{id}_A$）使得 $i \circ r \simeq \text{id}_X$，其中 $i: A \hookrightarrow X$ 是包含映射。

**强形变收缩**：如果上述同伦 $H: X \times [0,1] \to X$ 可以选取使得 $H(a, t) = a$ 对所有 $a \in A$ 和 $t \in [0,1]$ 成立。

---

## 例子

### 例1：欧氏空间与单点

**命题**：$\mathbb{R}^n$ 可缩（contractible），即 $\mathbb{R}^n \simeq \{pt\}$。

**证明**：定义 $f: \mathbb{R}^n \to \{0\}$ 为常值映射，$g: \{0\} \to \mathbb{R}^n$ 为 $g(0) = 0$。

则 $f \circ g = \text{id}_{\{0\}}$，而 $g \circ f: \mathbb{R}^n \to \mathbb{R}^n$ 是常值映射 $x \mapsto 0$。

同伦 $H(x, t) = tx$ 连接 $g \circ f$ 与 $\text{id}_{\mathbb{R}^n}$。 $\square$

### 例2：穿孔平面与圆周

**命题**：$\mathbb{R}^2 \setminus \{0\} \simeq S^1$。

**证明**：定义 $r: \mathbb{R}^2 \setminus \{0\} \to S^1$ 为 $r(x) = x/\|x\|$（径向投影）。

这是收缩映射，且 $i \circ r \simeq \text{id}$ 通过同伦 $H(x, t) = (1-t)x + t \cdot x/\|x\|$。 $\square$

### 例3：8字图与穿孔双平面

**命题**：$\mathbb{R}^2 \setminus \{p, q\}$（两点穿孔平面）同伦等价于8字图（两个圆周在一点相交）。

这说明同伦等价保持"洞"的数量但不保持维数。

### 例4：莫比乌斯带与圆周

**命题**：莫比乌斯带 $M$ 强形变收缩于其中线圆周，故 $M \simeq S^1$。

---

## 性质

### 基本性质

**性质1（自反性）**：$X \simeq X$

**性质2（对称性）**：$X \simeq Y \Rightarrow Y \simeq X$

**性质3（传递性）**：$X \simeq Y$ 且 $Y \simeq Z$ $\Rightarrow$ $X \simeq Z$

因此同伦型是拓扑空间的等价关系。

### 同伦不变性

**定理**：同伦等价诱导：
- 基本群的同构：$\pi_1(X) \cong \pi_1(Y)$
- 同调群的同构：$H_n(X) \cong H_n(Y)$ 对所有 $n$
- 上同调环的同构：$H^*(X) \cong H^*(Y)$ 作为分次环

### 形变收缩 vs 同伦等价

| 概念 | 条件 | 强度 |
|------|------|------|
| 同伦等价 | $g \circ f \simeq \text{id}_X$，$f \circ g \simeq \text{id}_Y$ | 弱 |
| 形变收缩 | $A \subset X$，$i \circ r \simeq \text{id}_X$ | 中 |
| 强形变收缩 | 同上，且同伦保持 $A$ 不动 | 强 |

**注**：存在同伦等价但不是形变收缩的例子（需要映射不是嵌入）。

---

## FormalMath对应

### 主要文档

- `docs/05-拓扑学/02-代数拓扑.md` — 同伦论基础章节
- `docs/00-习题示例反例库/拓扑/TOP-009-同胚的判定.md` — 相关练习

### 概念映射

| Princeton MAT 365 | FormalMath |
|------------------|------------|
| 同伦等价 | `同伦论/同伦等价` |
| 形变收缩 | `同伦论/形变收缩` |
| 同伦型 | `同伦论/同伦型` |
| 可缩空间 | `拓扑空间/可缩性` |

### Lean 4形式化参考

```lean
-- 同伦等价的形式化概念（概念性）
structure HomotopyEquivalence (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] where
  toFun : C(X, Y)  -- 连续映射
  invFun : C(Y, X)  -- 同伦逆
  left_inv : Homotopy (invFun.comp toFun) id  -- 左逆同伦
  right_inv : Homotopy (toFun.comp invFun) id  -- 右逆同伦
```

### 交叉引用

- **相关定义**: AT-PN-002 (基本群), AT-PN-010 (同伦群)
- **依赖概念**: 拓扑空间、连续映射
- **后续概念**: 同调论的所有不变量都是同伦不变量

---

## Hatcher参考

- **章节**: Chapter 0, "Some Underlying Geometric Notions", p. 3-4
- **关键习题**: 
  - Exercise 0.1: 证明 $\mathbb{R}^n \setminus \{0\} \simeq S^{n-1}$
  - Exercise 0.2: 构造同伦等价的例子
- **延伸阅读**: Chapter 0 还包含关于胞腔复形和单纯复形的基本概念

---

## 总结

同伦等价是代数拓扑中最核心的等价关系，它比同胚弱，但保留了所有代数不变量（基本群、同调群等）。理解同伦等价与形变收缩的区别是学习代数拓扑的第一步。

**关键要点**：
1. 同伦等价 = 存在双向同伦逆
2. 形变收缩 = 子空间包含的强形式
3. 同伦等价保持所有代数拓扑不变量
4. 可缩空间 = 同伦等价于单点的空间
