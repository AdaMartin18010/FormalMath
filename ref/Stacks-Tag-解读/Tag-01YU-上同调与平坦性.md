# Stacks Project Tag 01YU - 上同调与平坦性（Cohomology and flatness）

## 1. Tag基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 01YU |
| **英文名称** | Cohomology and flatness |
| **中文名称** | 上同调与平坦性 |
| **所属章节** | Chapter 30: Cohomology of Sheaves (层的上同调) |
| **数学领域** | 代数几何、交换代数 |
| **难度等级** | 研究生水平 |

### 1.1 位置信息

- **URL**: https://stacks.math.columbia.edu/tag/01YU
- **章节**: 30.20 Cohomology and flatness
- **前置Tags**: 01YS (平坦基变换), 01YB (上同调与基变换), 01XS (平坦态射)

---

## 2. 定理/定义原文

### 2.1 上同调与平坦性定理

**设定**:

- $f: X \to S$ 是概形态射
- $\mathcal{F}$ 是 $X$ 上的凝聚层（或更一般的复形）
- 研究 $R^i f_* \mathcal{F}$ 的平坦性

**引理 30.20.4（Cohomology and Flatness - 基本版本）**:

设 $f: X \to S$ 是紧合态射，$S$ 局部Noether，$\mathcal{F}$ 是 $X$ 上的凝聚层且在 $S$ 上平坦。则以下条件等价：

1. $R^i f_* \mathcal{F}$ 是局部自由的（即向量丛）
2. 函数 $s \mapsto \dim_{\kappa(s)} H^i(X_s, \mathcal{F}_s)$ 是局部常值的
3. 基变换映射 $(R^i f_* \mathcal{F})_s \otimes \kappa(s) \to H^i(X_s, \mathcal{F}_s)$ 对所有 $s \in S$ 是同构

### 2.2 复形版本

**定理 30.20.5（Cohomology and Flatness - 复形版本）**:

设 $f: X \to S$ 紧合，$S$ 局部Noether，$K \in D_{\text{coh}}^b(X)$。假设 $K$ 在 $S$ 上具有有限Tor维数。则：

$Rf_* K$ 在 $S$ 上完美（perfect）当且仅当 $K$ 在每个纤维 $X_s$ 上的上同调维数有界。

### 2.3 Tor独立性

**定义 - Tor独立性**:

设 $f: X \to S$ 和 $g: S' \to S$ 是概形态射。称 $f$ 和 $g$ 是**Tor-独立**的，如果对所有 $x \in X$，$s' \in S'$ 使得 $f(x) = g(s') = s$，有：

$$\text{Tor}_i^{\mathcal{O}_{S,s}}(\mathcal{O}_{X,x}, \mathcal{O}_{S',s'}) = 0$$

对所有 $i > 0$ 成立。

**引理**: 若 $g$ 平坦，则 $f$ 和 $g$ 自动Tor-独立。

---

## 3. 概念依赖图

```
                    ┌─────────────────┐
                    │  概形 X/S       │
                    │  态射 f: X→S   │
                    └────────┬────────┘
                             │
              ┌──────────────┼──────────────┐
              ▼              ▼              ▼
       ┌────────────┐ ┌────────────┐ ┌────────────┐
       │ 凝聚层 ℱ   │ │ 平坦性     │ │ 高阶直像  │
       │ Flat/S    │ │ 条件       │ │  R^i f_* ℱ│
       └─────┬──────┘ └─────┬──────┘ └─────┬──────┘
             │              │              │
             └──────────────┼──────────────┘
                            │
                            ▼
                    ┌───────────────┐
                    │  纤维上同调   │
                    │ H^i(X_s, ℱ_s) │
                    └───────┬───────┘
                            │
                            ▼
                    ┌───────────────┐
                    │ 上同调与      │◄────────────┐
                    │ 平坦性定理    │             │
                    │              │             │
                    │ 等价条件：   │             │
                    │ 1. R^i f_* ℱ │ 局部自由    │
                    │ 2. 维数局部常 │             │
                    │ 3. 基变换同构 │             │
                    └───────┬───────┘             │
                            │                     │
              ┌─────────────┼─────────────┐       │
              ▼             ▼             ▼       │
       ┌──────────┐  ┌──────────┐  ┌──────────┐   │
       │ Grauert  │  │ 局部常值 │  │ 向量丛   │   │
       │ 定理     │  │ 性定理   │  │ 判定     │   │
       └──────────┘  └──────────┘  └──────────┘   │
                                                  │
                    ┌─────────────────┐           │
                    │  Tor独立性      │───────────┘
                    │ Tor_i = 0 (i>0) │
                    └─────────────────┘
```

### 3.1 详细依赖链

```
交换代数基础
    ├── 平坦模与平坦环同态
    ├── Tor函子
    └── 局部自由模 = 投射模 = 向量丛
        ↓
层论基础
    ├── 凝聚层的平坦性
    ├── 层的Tor函子
    └── 局部自由层
        ↓
层上同调
    ├── 高阶直像层 R^i f_*
    ├── 纤维上同调 H^i(X_s, ℱ_s)
    └── 基变换映射
        ↓
上同调与平坦性 ◄── 本Tag
    ├── 平坦性等价条件
    ├── Grauert定理
    └── Tor独立性
```

---

## 4. 证明概要

### 4.1 基本版本的证明

**引理 30.20.4 的证明**:

**$(1) \Rightarrow (3)$**:

- 若 $R^i f_* \mathcal{F}$ 局部自由，则：
  $$(R^i f_* \mathcal{F})_s \otimes \kappa(s) \cong H^i(X_s, \mathcal{F}_s)$$
- 由平坦基变换（01YS），基变换映射是同构

**$(3) \Rightarrow (2)$**:

- 若基变换映射是同构，则：
  $$\dim H^i(X_s, \mathcal{F}_s) = \text{rank}(R^i f_* \mathcal{F})_s$$
- 秩函数局部常值

**$(2) \Rightarrow (1)$**:

- 这是最难的部分，使用Nakayama引理
- 关键点：构造局部自由层的显式生成元

### 4.2 关键引理

**引理（Nakayama型）**:

设 $M$ 是Noether局部环 $(A, \mathfrak{m})$ 上的有限模，且 $M/\mathfrak{m}M$ 是 $A/\mathfrak{m}$ 上 $r$ 维向量空间。则 $M$ 可由 $r$ 个元素生成。

若 $M$ 平坦且维数函数局部常值，则 $M$ 局部自由。

### 4.3 复形版本的证明思路

**定理 30.20.5 的证明策略**:

1. **完美复形**: 局部拟同构于有界局部自由复形

2. **Tor维数条件**: 保证纤维维数有界

3. **归纳法**: 对复形的振幅（amplitude）归纳

4. **关键点**: 结合Künneth公式和Nakayama技术

---

## 5. 与FormalMath对应

### 5.1 对应概念映射

| Stacks Project | FormalMath对应 | 文件路径 |
|----------------|----------------|----------|
| 平坦模 | 平坦模 | `concept/交换代数/平坦模.md` |
| 局部自由层 | 局部自由层/向量丛 | `concept/代数几何/向量丛.md` |
| Tor函子 | Tor函子 | `concept/同调代数/Tor函子.md` |
| 高阶直像 | 高阶直像层 | `concept/代数几何/高阶直像层.md` |
| 完美复形 | 完美复形 | `concept/同调代数/完美复形.md` |

### 5.2 Lean4形式化方向

```lean4
-- 上同调与平坦性的Lean4可能形式
import Mathlib.AlgebraicGeometry.Cohomology

-- 纤维上同调维数
def fiberCohomologyDim {X S : Scheme} (f : X ⟶ S)
    (F : CoherentSheaf X) (i : ℕ) (s : S) : ℕ :=
  Module.rank (X.fiber s).residueField
    (Scheme.cohomology i (X.fiber s) (F.restrict (X.fiber s)))

-- 上同调与平坦性定理
theorem cohomology_and_flatness {X S : Scheme} (f : X ⟶ S)
    [IsProper f] [LocallyNoetherian S]
    (F : CoherentSheaf X) [F.FlatOver S] (i : ℕ) :
    (∀ (s : S), ∃ (n : ℕ), ∀ (t : S), t ∈ s.neighborhood →
      fiberCohomologyDim f F i t = n) ↔
    (IsLocallyFree (R i f.pushforward F)) := by
  sorry
```

### 5.3 在知识体系中的位置

```
代数几何/层上同调
    ├── 平坦性理论
    │       ├── 平坦模
    │       ├── 平坦态射
    │       └── Tor独立性
    ├── 层上同调
    │       ├── 高阶直像层
    │       └── 纤维上同调
    └── 上同调与平坦性 ◄── 本Tag
            ├── Grauert定理
            ├── 局部自由判定
            └── 向量丛理论
```

---

## 6. 应用与重要性

### 6.1 核心应用

1. **向量丛的构造**
   - 从上同调构造向量丛
   - Picard概形的局部结构

2. **模空间理论**
   - 判定模空间的平滑性
   - 相对维度计算

3. **形变理论**
   - 上同调群的形变
   - Hodge理论的应用

### 6.2 具体应用场景

| 应用场景 | 结果 | 重要性 |
|----------|------|--------|
| **Hodge丛** | 周期映射的向量丛 | 复几何 |
| **Determinant bundle** | 行列式线丛 | 模空间理论 |
| **Picard概形** | Picard群的概形结构 | Abelian簇理论 |
| **Hilbert概形** | 平坦族的上同调 | 模空间紧化 |

### 6.3 历史背景

- **H. Grauert (1960)**: 复解析情形的半连续性定理
- **A. Grothendieck (EGA III)**: 代数几何的系统发展
- **M. Artin**: 代数空间中的应用

### 6.4 现代发展

- **导出代数几何**: 高阶上同调与平坦性
- **非交换几何**: 矩阵因子范畴中的应用
- **算术几何**: p-进Hodge理论

---

## 7. 与其他资源关联

### 7.1 Stacks Project内部关联

| 相关Tag | 名称 | 关系 |
|---------|------|------|
| 01YS | 平坦基变换 | 基础定理 |
| 01YB | 上同调与基变换 | 推广版本 |
| 01XS | 平坦态射 | 基础概念 |
| 08HP | 导出张量积 | 导出版本工具 |
| 08H4 | 导出Hom | 相关构造 |

### 7.2 外部资源

**教科书**:

- Hartshorne: "Algebraic Geometry" (第三章, §12)
- Vakil: "The Rising Sea" (第29章)
- Le Potier: "Lectures on Vector Bundles"

**原始论文**:

- Grauert, H. "Ein Theorem der analytischen Garbentheorie"
- Mumford: "Abelian Varieties" (Chapter II)

**现代综述**:

- Huybrechts-Lehn: "The Geometry of Moduli Spaces of Sheaves"

### 7.3 相关软件

- **Macaulay2**: 层上同调与平坦性计算
- **SageMath**: 代数几何计算
- **Magma**: 向量丛计算

---

## 8. Lean4形式化展望

### 8.1 当前形式化状态

```
Mathlib4状态:
✅ 平坦模理论
✅ 向量丛基础
✅ Tor函子
🔄 层上同调
⬜ 高阶直像层
⬜ 上同调与平坦性
```

### 8.2 形式化路线图

**阶段1: 层上同调计算** (预计18个月)

- 高阶直像层的完整理论
- 纤维上同调的形式化

**阶段2: Grauert定理** (预计24个月)

```lean4
-- Grauert半连续性定理
theorem grauert_semicontinuity {X S : Scheme} (f : X ⟶ S)
    [IsProper f] [LocallyNoetherian S]
    (F : CoherentSheaf X) [F.FlatOver S] (i : ℕ) :
    IsUpperSemicontinuous (fiberCohomologyDim f F i) := by
  sorry
```

**阶段3: 局部自由判定** (预计30个月)

```lean4
-- 局部自由判定准则
theorem locally_free_criterion {X S : Scheme} (f : X ⟶ S)
    [IsProper f] [LocallyNoetherian S]
    (F : CoherentSheaf X) [F.FlatOver S] (i : ℕ) :
    IsLocallyFree (R i f.pushforward F) ↔
    (∀ (s : S), IsIso (baseChangeMap f (Spec.map (residueField s)) F i)) := by
  sorry
```

### 8.3 技术挑战

1. **上半连续性**: 拓扑空间中函数的上半连续性
2. **秩函数**: 凝聚层的秩函数的形式化
3. **局部自由判定**: 有效算法

### 8.4 相关形式化项目

- **mathlib4#vector-bundles**: 向量丛理论
- **mathlib4#moduli-spaces**: 模空间理论
- **Hodge Theory Formalization**: Hodge理论

---

## 附录: 关键公式速查

| 概念 | 公式 |
|------|------|
| **平坦基变换** | $g^* R^i f_* \mathcal{F} \cong R^i f'_* (g')^* \mathcal{F}$ |
| **纤维上同调** | $H^i(X_s, \mathcal{F}_s) = (R^i f_* \mathcal{F})_s \otimes \kappa(s)$ |
| **局部自由等价** | $R^i f_* \mathcal{F}$ 局部自由 $\Leftrightarrow$ $\dim H^i(X_s, \mathcal{F}_s)$ 局部常值 |
| **Tor独立性** | $\text{Tor}_i^{\mathcal{O}_{S,s}}(\mathcal{O}_{X,x}, \mathcal{O}_{S',s'}) = 0$ ($i > 0$) |

---

**文档版本**: 1.0
**创建日期**: 2026-04-10
**最后更新**: 2026-04-10
**作者**: FormalMath Knowledge System
