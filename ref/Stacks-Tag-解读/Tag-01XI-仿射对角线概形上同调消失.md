# Stacks Project Tag 01XI - 仿射对角线概形上同调消失

## 1. Tag基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 01XI |
| **章节位置** | Chapter 30: Cohomology of Schemes > Section 30.2: Čech Cohomology of Schemes |
| **数学领域** | 代数几何 / 概形上同调 |
| **文档类型** | 引理 (Lemma) |
| **重要性** | ⭐⭐⭐⭐ (计算上同调的基础工具) |
| **相关Tags** | 01XH, 01XJ, 01XK (Čech上同调系列) |

---

## 2. 定理原文

### 英文原文 (Stacks Project)

> **Lemma 30.2.4.** Let $X$ be a scheme with affine diagonal. Let $\mathcal{F}$ be a quasi-coherent sheaf on $X$. Let $\mathcal{U} : X = \bigcup_{i \in I} U_i$ be an affine open covering. Assume $H^p(U_{i_0 \ldots i_q}, \mathcal{F}) = 0$ for all $p > 0$, all $q$, and all $i_0, \ldots, i_q \in I$. Then the map
>
> $$\check{H}^q(\mathcal{U}, \mathcal{F}) \longrightarrow H^q(X, \mathcal{F})$$
>
> is an isomorphism for all $q$.

### 中文翻译

> **引理 30.2.4.** 设 $X$ 是具有仿射对角线的概形。设 $\mathcal{F}$ 是 $X$ 上的拟凝聚层。设 $\mathcal{U} : X = \bigcup_{i \in I} U_i$ 是仿射开覆盖。假设对所有 $p > 0$、所有 $q$ 以及所有 $i_0, \ldots, i_q \in I$ 都有 $H^p(U_{i_0 \ldots i_q}, \mathcal{F}) = 0$。则映射
>
> $$\check{H}^q(\mathcal{U}, \mathcal{F}) \longrightarrow H^q(X, \mathcal{F})$$
>
> 对所有 $q$ 都是同构。

---

## 3. 概念依赖图

```
仿射对角线概形的Čech上同调计算 (01XI)
│
├── 前置概念
│   ├── 概形 (Scheme)
│   ├── 拟凝聚层 (Quasi-coherent Sheaf)
│   ├── 仿射对角线 (Affine Diagonal)
│   │   └── Δ: X → X × X 是仿射态射
│   ├── 仿射开覆盖 (Affine Open Covering)
│   └── Čech上同调 (Čech Cohomology)
│
├── 关键条件
│   ├── 高阶上同调消失: H^p(U_{i0...iq}, F) = 0 (p > 0)
│   └── 仿射对角线保证 U_{i0...iq} 是仿射的
│
├── 核心结论
│   └── Čech上同调 ≅ 层上同调
│
└── 应用
    ├── 射影空间的上同调计算
    ├── 仿射概形的上同调消失
    └── 分离概形的上同调理论
```

### 依赖关系详解

| 概念 | 说明 | 在FormalMath中的位置 |
|------|------|---------------------|
| 仿射对角线 | $\Delta: X \to X \times X$ 是仿射态射 | `concept/代数几何/分离概形.md` |
| 拟凝聚层 | 局部上形如 $\widetilde{M}$ 的层 | `concept/代数几何/拟凝聚层.md` |
| Čech上同调 | 用覆盖计算的Čech复形 | `concept/层论/Čech上同调.md` |
| 层上同调 | 导出函子 $R\Gamma(X, -)$ | `concept/层论/层上同调.md` |
| 仿射交 | $U_{i_0} \cap \cdots \cap U_{i_q}$ | 由仿射对角线保证 |

---

## 4. 证明概要

### 核心观察

**关键引理：** 若 $X$ 有仿射对角线，则任意仿射开集的有限交仍是仿射的。

**证明：** 考虑图表：

$$U_{i_0} \cap \cdots \cap U_{i_q} \cong U_{i_0} \times_X \cdots \times_X U_{i_q} \hookrightarrow U_{i_0} \times \cdots \times U_{i_q}$$

这可以分解为：

$$X \xrightarrow{\Delta} X \times X \xrightarrow{\text{pr}} U_{i_0} \times \cdots \times U_{i_q}$$

由于 $\Delta$ 是仿射的，且仿射态射的纤维积保持仿射性，故有限交是仿射的。∎

### 主定理证明

**Step 1: 建立Čech-层谱序列**

存在收敛到层上同调的谱序列：

$$E_2^{p,q} = \check{H}^p(\mathcal{U}, \underline{H}^q(\mathcal{F})) \Rightarrow H^{p+q}(X, \mathcal{F})$$

其中 $\underline{H}^q(\mathcal{F})$ 是上同调预层：$U \mapsto H^q(U, \mathcal{F})$。

**Step 2: 应用消失条件**

由假设，对所有仿射开集 $V = U_{i_0 \ldots i_q}$：

$$H^p(V, \mathcal{F}) = 0, \quad p > 0$$

因此 $\underline{H}^q(\mathcal{F})(U_{i_0 \ldots i_p}) = 0$ 对 $q > 0$。

**Step 3: 谱序列退化**

- $E_2^{p,q} = 0$ 对 $q > 0$
- 只剩 $q = 0$ 行：$E_2^{p,0} = \check{H}^p(\mathcal{U}, \mathcal{F})$
- 谱序列在 $E_2$ 退化

**Step 4: 边缘同态**

退化给出边缘同态：

$$\check{H}^q(\mathcal{U}, \mathcal{F}) = E_2^{q,0} \twoheadrightarrow E_\infty^{q,0} = H^q(X, \mathcal{F})$$

由于无扩张问题，这是同构。∎

---

## 5. 与FormalMath的对应关系

### FormalMath相关文档

| 文档路径 | 内容对应 | 完成状态 |
|----------|----------|----------|
| `concept/代数几何/分离概形.md` | 仿射对角线概念 | ✅ 已完成 |
| `concept/代数几何/拟凝聚层.md` | 层的基本理论 | ✅ 已完成 |
| `concept/层论/Čech上同调.md` | 计算工具 | 🚧 部分完成 |
| `concept/层论/层上同调.md` | 导出函子定义 | ✅ 已完成 |
| `concept/代数几何/概形上同调.md` | 综合应用 | 🚧 进行中 |

### 概念映射

```yaml
Stacks Project Tag: 01XI
FormalMath概念:
  - path: "concept/代数几何/分离概形.md"
    sections:
      - "仿射对角线"
      - "有限交的仿射性"
    relation: "核心假设"

  - path: "concept/层论/Čech上同调.md"
    sections:
      - "Čech复形"
      - "与层上同调的关系"
    relation: "计算工具"

  - path: "concept/代数几何/仿射概形.md"
    relation: "H^i(X, F) = 0 (i > 0) 对拟凝聚层"
```

---

## 6. 应用与重要性

### 核心应用

#### 1. 仿射概形的上同调消失

**定理 (Tag 01XB):** 若 $X$ 是仿射概形，$\mathcal{F}$ 是拟凝聚层，则：

$$H^i(X, \mathcal{F}) = 0, \quad i > 0$$

**证明概要：** 取平凡覆盖 $\mathcal{U} = \{X\}$，Čech复形只有一项，直接得 $H^i = 0$ ($i > 0$)。

#### 2. 射影空间的上同调计算

使用标准仿射覆盖 $\mathcal{U} = \{D_+(X_i)\}$，$\mathbb{P}^n$ 有仿射对角线，可应用Čech计算。

**经典结果：**

$$H^i(\mathbb{P}^n_k, \mathcal{O}(m)) = \begin{cases} k[x_0,\ldots,x_n]_m & i = 0 \\ 0 & 0 < i < n \\ \text{dual} & i = n \end{cases}$$

#### 3. Serre消失定理

对于 $X$ 上的丰富线丛 $\mathcal{L}$，存在 $n_0$ 使得：

$$H^i(X, \mathcal{F} \otimes \mathcal{L}^{\otimes n}) = 0, \quad i > 0, n \geq n_0$$

Čech计算是证明的关键步骤。

### 重要性评估

| 方面 | 重要性说明 |
|------|-----------|
| 计算层面 | 提供具体的算法计算层上同调 |
| 理论层面 | 连接代数（Čech）与几何（层上同调） |
| 教学层面 | 学习概形上同调的必经之路 |
| 应用层面 | 曲线、曲面的Riemann-Roch定理证明 |

---

## 7. 与其他资源的关联

### nLab 对应条目

| nLab页面 | URL | 对应内容 |
|----------|-----|----------|
| Čech cohomology | https://ncatlab.org/nlab/show/%C4%8Cech+cohomology | 更一般的拓扑视角 |
| scheme | https://ncatlab.org/nlab/show/scheme | 代数几何基础 |
| quasi-coherent sheaf | https://ncatlab.org/nlab/show/quasi-coherent+sheaf | 层的性质 |

### 经典教材

| 教材 | 章节 | 特色 |
|------|------|------|
| Hartshorne | Chapter III, §4 | 经典处理，含详细计算 |
| Liu's AG | Chapter 5 | 较现代的表述 |
| Vakil's FOAG | §18-20 | 强调直觉和例子 |
| EGA III | §1 | 最一般形式 |

### 补充说明

**为什么需要仿射对角线？**

- **分离概形：** 保证对角线 $\Delta$ 是闭浸入
- **仿射对角线更强：** 保证有限交保持仿射性
- **反例：** 非分离概形（如带双原点的直线）中，仿射开集的交可能非仿射

---

## 8. Lean4形式化展望

### 当前形式化状态

| 项目 | 状态 | 链接/说明 |
|------|------|-----------|
| mathlib4 (Schemes) | 🚧 进行中 | 基础概形理论 |
| mathlib4 (Sheaf Cohomology) | 🚧 早期阶段 | 层上同调框架 |
| **具体本Tag** | ❌ 未开始 | 依赖前述基础 |

### mathlib4相关进展

- **Schemes:** 已有定义，包括仿射概形、分离性
- **Quasi-coherent sheaves:** 定义存在，性质开发中
- **Cech cohomology:** 拓扑版本存在，代数几何版本待开发

### 形式化挑战与策略

| 挑战 | 难度 | 策略 |
|------|------|------|
| 仿射对角线定义 | ⭐⭐ | 利用纤维积和仿射态射 |
| 有限交的仿射性 | ⭐⭐⭐ | 需要良好的纤维积API |
| Čech复形构造 | ⭐⭐⭐ | 参考拓扑版本推广 |
| 谱序列 | ⭐⭐⭐⭐⭐ | mathlib4正在开发 |

### 推荐形式化路线图

#### 阶段1：基础架构

- [ ] 完善分离概形的API
- [ ] 定义仿射对角线
- [ ] 证明有限交保持仿射性

#### 阶段2：Čech理论

- [ ] 概形上的Čech复形
- [ ] Čech上同调函子
- [ ] 与层上同调的比较映射

#### 阶段3：谱序列

- [ ] 双复形和上同调谱序列
- [ ] Čech-to-导出谱序列
- [ ] 退化条件的形式化

#### 阶段4：应用

- [ ] 仿射概形的上同调消失
- [ ] 射影空间的Čech计算
- [ ] Serre消失定理

### Lean4代码框架

```lean4
-- 仿射对角线的定义
class HasAffineDiagonal (X : Scheme) : Prop where
  diagonal_affine : IsAffineMorphism (Scheme.diagonal X)

-- 有限交保持仿射性
lemma affine_intersection {X : Scheme} [HasAffineDiagonal X]
    {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    IsAffineOpen (U ⊓ V) := by
  -- 利用对角线和纤维积
  sorry

-- 多交版本
lemma affine_finite_intersection {X : Scheme} [HasAffineDiagonal X]
    {ι : Type*} [Finite ι] (U : ι → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) :
    IsAffineOpen (⨅ i, U i) := by
  sorry

-- 主定理：Čech上同调计算层上同调
theorem Cech_cohomology_iso_sheaf_cohomology
    {X : Scheme} [HasAffineDiagonal X]
    (F : QCohSheaf X) (U : AffineOpenCover X)
    (hF : ∀ (q : ℕ) (i : Fin (q+1) → U.J),
      ∀ p > 0, Hp p (U.intersection i) F = 0) :
    ∀ q, CechCohomology U F q ≅ SheafCohomology X F q := by
  sorry
```

---

## 参考链接

- **Stacks Project Tag 01XI:** https://stacks.math.columbia.edu/tag/01XI
- **Stacks Project Section 30.2:** https://stacks.math.columbia.edu/tag/01XB
- **mathlib4 Schemes:** https://leanprover-community.github.io/api/latest/Mathlib-AlgebraicGeometry.html
- **Hartshorne AG:** Chapter III, Theorem 4.5

---

*文档创建日期：2026年4月*
*FormalMath Stacks Project Tag解读系列*
