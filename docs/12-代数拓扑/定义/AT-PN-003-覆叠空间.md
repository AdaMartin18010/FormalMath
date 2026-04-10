---
university: Princeton
synonym: [Covering Space, 覆叠映射, 万有覆叠]
type: 定义
level: L3-理论建构层
difficulty: ⭐⭐⭐⭐
concept_dependency: [拓扑空间, 连续映射, 基本群]
prerequisite_concepts: [基本群, 道路连通, 局部道路连通]
prerequisite_theorems: [同伦提升性质]
course_context: MAT 365 Topology
msc2010: [57M10, 55R05, 55Q05]
related_concepts: [覆叠变换, 万有覆叠, 单值化定理]
---

# AT-PN-003: 覆叠空间 (Covering Space)

> **来源**: Princeton MAT 365 (Topology) | Hatcher Chapter 1, Section 3, p. 56-63
> **级别**: 本科高阶/研究生初级
> **领域**: 代数拓扑 · 同伦论

---

## 定义

### 覆叠映射

设 $p: \tilde{X} \to X$ 是连续满射。$p$ 称为**覆叠映射**（covering map），如果对任意 $x \in X$，存在邻域 $U$（称为**均匀覆叠邻域**），使得：

$$p^{-1}(U) = \bigsqcup_{\alpha \in \Lambda} V_\alpha$$

其中每个 $V_\alpha$ 是 $\tilde{X}$ 中的开集，且 $p|_{V_\alpha}: V_\alpha \to U$ 是同胚。

此时，$\tilde{X}$ 称为 $X$ 的**覆叠空间**（covering space），对每个 $x \in X$，$p^{-1}(x)$ 称为**纤维**（fiber）。

### 覆叠的层数

若所有纤维都有相同的基数 $n$（可能是无限的），称覆叠为**$n$-层覆叠**（$n$-sheeted covering）。

### 万有覆叠

覆叠 $p: \tilde{X} \to X$ 称为**万有覆叠**（universal covering），如果 $\tilde{X}$ 是单连通的。

---

## 例子

### 例1：指数映射

**命题**：$p: \mathbb{R} \to S^1$，$p(t) = e^{2\pi i t}$ 是覆叠映射。

**验证**：对 $z = e^{2\pi i t_0} \in S^1$，取 $U = S^1 \setminus \{-z\}$。则 $p^{-1}(U) = \bigsqcup_{n \in \mathbb{Z}} (t_0 + n - 1/2, t_0 + n + 1/2)$，每个区间同胚于 $U$。

这是 $\infty$-层覆叠，且 $\mathbb{R}$ 单连通，故这是万有覆叠。

### 例2：幂映射

**命题**：$p: S^1 \to S^1$，$p(z) = z^n$（$n \in \mathbb{Z}^+$）是 $n$-层覆叠。

**纤维**：$p^{-1}(1) = \{e^{2\pi i k/n} : k = 0, 1, \ldots, n-1\}$，共 $n$ 个点。

### 例3：球面到射影空间

**命题**：商映射 $p: S^n \to \mathbb{R}P^n$（将对径点等同）是2层覆叠。

**验证**：$p^{-1}([x]) = \{x, -x\}$。对充分小的邻域 $U$，$p^{-1}(U) = V_+ \sqcup V_-$。

由于 $S^n$（$n \geq 2$）单连通，这是万有覆叠。

### 例4：8字图的覆叠

8字图 $B = S^1 \vee S^1$ 的万有覆叠是4-正则树（每个顶点度数为4）。

这是因为 $\pi_1(B) = F_2$（两个生成元的自由群），覆叠对应于子群。

---

## 性质

### 提升性质

**道路提升性质**：设 $p: \tilde{X} \to X$ 是覆叠，$\gamma: [0, 1] \to X$ 是道路，$\tilde{x}_0 \in p^{-1}(\gamma(0))$。则存在唯一提升 $\tilde{\gamma}: [0, 1] \to \tilde{X}$ 使得 $p \circ \tilde{\gamma} = \gamma$ 且 $\tilde{\gamma}(0) = \tilde{x}_0$。

**同伦提升性质**：设 $H: [0, 1] \times [0, 1] \to X$ 是同伦，$\tilde{H}(0, 0) = \tilde{x}_0$ 给定。则存在唯一提升 $\tilde{H}$ 使 $p \circ \tilde{H} = H$。

### 诱导同态的单射性

**定理**：覆叠映射 $p: \tilde{X} \to X$ 诱导单射 $p_*: \pi_1(\tilde{X}, \tilde{x}_0) \hookrightarrow \pi_1(X, x_0)$。

**证明**：若 $p_*([\tilde{\gamma}]) = e$，则 $p \circ \tilde{\gamma} \simeq e_{x_0}$。由同伦提升，$\tilde{\gamma} \simeq e_{\tilde{x}_0}$。$\square$

### 覆叠的分类（Galois对应）

**定理**：设 $X$ 道路连通、局部道路连通、半局部单连通。则：

$$\{\text{覆叠 } p: \tilde{X} \to X\}/\text{同构} \longleftrightarrow \{\pi_1(X, x_0) \text{ 的子群}\}/\text{共轭}$$

对应由 $p \mapsto p_*\pi_1(\tilde{X})$ 给出。

**特殊情况**：
- 万有覆叠 $\leftrightarrow$ 平凡子群
- 连通覆叠 $\leftrightarrow$ 子群
- 正规覆叠（Galois覆叠）$\leftrightarrow$ 正规子群

### 万有覆叠的存在性

**定理**：若 $X$ 道路连通、局部道路连通、半局部单连通，则万有覆叠存在。

**构造**：设 $x_0 \in X$。定义

$$\tilde{X} = \{[\gamma] : \gamma \text{ 是道路，} \gamma(0) = x_0\}/\sim$$

其中 $[\gamma]$ 表示终点相同且道路同伦的等价类。$p([\gamma]) = \gamma(1)$。

---

## FormalMath对应

### 主要文档

- `docs/05-拓扑学/02-代数拓扑.md` — 覆叠空间理论
- `docs/00-习题示例反例库/拓扑/TOP-019-覆叠空间理论.md` — 计算练习

### 概念映射

| Princeton MAT 365 | FormalMath |
|------------------|------------|
| 覆叠空间 | `代数拓扑/覆叠空间` |
| 万有覆叠 | `代数拓扑/万有覆叠` |
| 覆叠变换 | `代数拓扑/覆叠变换` |
| 提升 | `代数拓扑/提升性质` |

### Lean 4形式化参考

```lean
-- 覆叠空间概念框架
structure CoveringMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] 
  (p : X → Y) : Prop where
  continuous : Continuous p
  surjective : Surjective p
  locally_trivial : ∀ y : Y, ∃ U : Neighborhood y, 
    IsEvenlyCovered p U  -- p⁻¹(U) 是不交开集的并
```

### 交叉引用

- **前序定义**: AT-PN-002 (基本群)
- **后续定义**: AT-PN-010 (同伦群)
- **相关定理**: Galois对应、单值化定理

---

## Hatcher参考

- **章节**: Chapter 1, Section 3, "Covering Spaces", p. 56-63
- **关键内容**：
  - 覆叠映射的定义 (p. 56)
  - 提升性质 (p. 60-61)
  - 万有覆叠的构造 (p. 63-65)
- **关键习题**:
  - Exercise 1.3.7: 构造8字图的万有覆叠
  - Exercise 1.3.10: 证明覆叠的分类定理
  - Exercise 1.3.12: 覆叠变换的计算

---

## 总结

覆叠空间理论建立了空间的拓扑性质与基本群的代数性质之间的深刻联系。

**关键要点**：
1. 覆叠映射是局部同胚的满射
2. 提升性质是覆叠空间的核心工具
3. 覆叠分类 $\leftrightarrow$ 基本群的子群分类（Galois对应）
4. 万有覆叠对应于平凡子群
5. 基本群通过覆叠空间"几何实现"
