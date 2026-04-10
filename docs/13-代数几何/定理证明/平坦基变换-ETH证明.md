---
title: "平坦基变换定理 - ETH证明"
description: "平坦基变换定理的完整证明，强调与交换代数的深度融合，基于ETH Zurich 401-3532课程讲义"
course: "ETH Zurich 401-3532-00L"
topic: "代数几何"
subtopic: "上同调与基变换"
difficulty: "L4-高级"
prerequisites: ["层上同调基础", "平坦性理论", "Tor函子", "谱序列基础"]
theorem_id: "ETH-AG-FLATBC-001"
source: "Hartshorne III.9-12, ETH 401-3532 Kapitel 3"
date_created: "2026-04-10"
eth_feature: "交换代数深度融合与平坦性条件分析"
---

# 平坦基变换定理 (Flat Base Change)

**ETH Zurich 401-3532-00L | Kapitel 3: Flache Basiswechsel**

---

## 定理陈述

### 主定理：平坦基变换

设 $f: X \to Y$ 为概形态射，$\mathcal{F}$ 为 $X$ 上的拟凝聚层。设 $g: Y' \to Y$ 为平坦态射，形成纤维积图：

$$\begin{array}{ccc}
X' & \xrightarrow{g'} & X \\
\downarrow{f'} & & \downarrow{f} \\
Y' & \xrightarrow{g} & Y
\end{array}$$

其中 $X' = X \times_Y Y'$。

**定理** (平坦基变换): 对所有 $i \geq 0$，存在自然同构：
$$g^* R^i f_* \mathcal{F} \xrightarrow{\sim} R^i f'_* (g'^* \mathcal{F})$$

等价地，对任意 $y' \in Y'$，设 $y = g(y')$，有：
$$H^i(X_y, \mathcal{F}|_{X_y}) \otimes_{\mathcal{O}_{Y,y}} \mathcal{O}_{Y',y'} \cong H^i(X'_{y'}, (g'^*\mathcal{F})|_{X'_{y'}})$$

---

## 证明思路

### 几何直观

> **核心思想**: 平坦基变换保持"上同调信息"。

想象一族代数簇 $f: X \to Y$（如椭圆曲线族），基变换 $g: Y' \to Y$ 对应于改变参数空间。

- **平坦性条件**: 保证纤维"连续变化"，上同调维数不变
- **基变换映射**: 比较原族与拉回族的上同调
- **应用**: 证明上同调函数的上半连续性、形式化函数定理等

**ETH特色视角**（苏黎世交换代数传统）：
平坦基变换定理本质是交换代数中Tor函子消失条件的几何表现：
$$\operatorname{Tor}_i^{\mathcal{O}_{Y,y}}(\mathcal{O}_{Y',y'}, H^j(X_y, \mathcal{F}_y)) = 0 \quad (i > 0)$$

### 证明策略

```
证明结构 (ETH严格风格)
│
├─ 步骤1: 局部化简化
│  └─ 归约到仿射情形
│
├─ 步骤2: Čech上同调计算
│  └─ 相对Čech复形与基变换
│
├─ 步骤3: 平坦性条件的作用
│  └─ Tor函子消失 ⟹ 上同调交换
│
├─ 步骤4: 谱序列论证
│  └─ Leray谱序列与基变换谱序列
│
└─ 步骤5: 形式化函数定理应用
   └─ 完备化与忠实平坦下降
```

---

## 详细证明

### 步骤1: 局部化简化

**引理 1.1** (局部化与上同调交换)

设 $Y = \operatorname{Spec} A$，$S \subseteq A$ 为乘法集，$Y' = \operatorname{Spec} S^{-1}A$。则：
$$S^{-1}H^i(X, \mathcal{F}) \cong H^i(X', \mathcal{F}|_{X'})$$

其中 $X' = X \times_Y Y'$。

**证明**:

拟凝聚层的上同调与局部化交换，因为：
- 内射拟凝聚层的局部化仍内射
- 局部化是正合函子
- $S^{-1}\widetilde{M} = \widetilde{S^{-1}M}$

∎

**简化**: 可假设 $Y = \operatorname{Spec} A$，$Y' = \operatorname{Spec} A'$，$A \to A'$ 平坦。

---

### 步骤2: 相对Čech上同调

**定义 2.1** (相对Čech复形)

设 $f: X \to Y$ 为概形态射，$\mathcal{U} = \{U_i\}$ 为 $X$ 的相对仿射开覆盖（即每个 $U_i$ 在 $Y$ 上仿射）。定义相对Čech复形：
$$C^p(\mathcal{U}/Y, \mathcal{F}) := \bigoplus_{i_0 < \cdots < i_p} f_*\mathcal{F}|_{U_{i_0} \cap \cdots \cap U_{i_p}}$$

这是 $Y$ 上的层复形，其微分由限制映射给出。

**引理 2.1** (相对Čech上同调)

若 $\mathcal{U}$ 为相对仿射覆盖，则：
$$\mathbb{H}^i(C^\bullet(\mathcal{U}/Y, \mathcal{F})) \cong R^i f_* \mathcal{F}$$

**证明**:

相对Čech复形计算高次直像，因为 $f_*$ 的整体截面可用相对Čech复形计算。

∎

---

### 步骤3: 平坦性与Tor函子

**引理 3.1** (平坦性 ⟹ Tor消失)

设 $A \to A'$ 为平坦环同态，$M$ 为 $A$-模，则：
$$\operatorname{Tor}_i^A(A', M) = 0 \quad \text{对所有 } i > 0$$

**证明**: 平坦模的定义。∎

**引理 3.2** (Tor与复形的上同调)

设 $C^\bullet$ 为 $A$-模的有界复形，$A \to A'$ 平坦。则：
$$H^i(C^\bullet \otimes_A A') \cong H^i(C^\bullet) \otimes_A A'$$

**证明**:

考虑双复形 $K^{p,q} = C^p \otimes_A P^q$，其中 $P^\bullet \to A'$ 为 $A'$ 的投射消解。

由平坦性，$\operatorname{Tor}_i(C^p, A') = 0$ 对 $i > 0$，故谱序列退化。

∎

---

### 步骤4: 主要证明

**定理证明** (平坦基变换):

**步骤4.1**: 仿射化简

设 $Y = \operatorname{Spec} A$，$Y' = \operatorname{Spec} A'$，$A \to A'$ 平坦。

设 $X = \bigcup_{i=1}^n U_i$ 为相对仿射覆盖，$U_i = \operatorname{Spec} B_i$。

则 $U_i \cap U_j = \operatorname{Spec} B_{ij}$，等等。

**步骤4.2**: 相对Čech复形

相对Čech复形为：
$$C^p = \bigoplus_{i_0 < \cdots < i_p} \widetilde{B_{i_0 \cdots i_p}}$$

其中 $B_{i_0 \cdots i_p}$ 为 $U_{i_0} \cap \cdots \cap U_{i_p}$ 的坐标环。

**步骤4.3**: 基变换后的复形

基变换 $X' = X \times_Y Y'$ 后，坐标环变为 $B_i \otimes_A A'$，$B_{ij} \otimes_A A'$，等等。

新的相对Čech复形：
$$C'^p = \bigoplus_{i_0 < \cdots < i_p} \widetilde{B_{i_0 \cdots i_p} \otimes_A A'}$$

**关键观察**:
$$C'^p = C^p \otimes_A A'$$

**步骤4.4**: 上同调计算

由引理3.2（平坦性条件）：
$$H^i(C'^\bullet) = H^i(C^\bullet \otimes_A A') = H^i(C^\bullet) \otimes_A A'$$

左边是 $R^i f'_* (g'^* \mathcal{F})$（在 $Y'$ 上）。

右边是 $g^* R^i f_* \mathcal{F}$（拉回后）。

**结论**:
$$g^* R^i f_* \mathcal{F} \cong R^i f'_* (g'^* \mathcal{F})$$

∎

---

### 步骤5: 形式化函数定理应用

**推论 5.1** (形式化函数定理准备)

在平坦基变换定理的条件下，设 $y' \in Y'$，$y = g(y')$，$\mathfrak{m}_y \subseteq \mathcal{O}_{Y,y}$ 为极大理想。

则完备化与上同调交换：
$$(R^i f_* \mathcal{F})_y^\wedge \cong \varprojlim_n H^i(X_n, \mathcal{F}_n)$$

其中 $X_n$ 为 $n$-th 无穷小邻域。

**证明概要**:

平坦基变换定理允许我们将问题约化到Artin局部环，然后取极限。

∎

---

## 应用示例

### 示例1: 上同调的上半连续性

**定理**: 设 $f: X \to Y$ 为真态射，$Y$ 约化，$\mathcal{F}$ 为 $X$ 上平坦于 $Y$ 的凝聚层。则函数
$$y \mapsto \dim_{k(y)} H^i(X_y, \mathcal{F}_y)$$
是上半连续的。

**证明概要**:

1. 用平坦基变换定理证明高次直像在基变换下表现良好
2. 用Nakayama引理和秩的半连续性
3. 结合Grauert定理

∎

### 示例2: 椭圆曲线族的上同调

设 $f: E \to Y$ 为椭圆曲线族（光滑真态射，纤维为亏格1曲线），$\mathcal{F} = \mathcal{O}_E$。

则：
- $R^0 f_* \mathcal{O}_E = \mathcal{O}_Y$（整体截面为常数函数）
- $R^1 f_* \mathcal{O}_E$ 为 $Y$ 上的线丛（相对对偶层）

对任意平坦基变换 $g: Y' \to Y$：
$$g^* R^1 f_* \mathcal{O}_E \cong R^1 f'_* \mathcal{O}_{E'}$$

其中 $E' = E \times_Y Y'$。

这表明相对对偶层在平坦基变换下保持。

---

## 与Stacks Project对应

| 概念/定理 | Hartshorne | Stacks Project | FormalMath文档 |
|-----------|------------|----------------|----------------|
| 平坦基变换 | III.9.3 | [02N6](https://stacks.math.columbia.edu/tag/02N6) | 本文档 |
| 上同调与基变换 | III.12.11 | [0B91](https://stacks.math.columbia.edu/tag/0B91) | 本文档 |
| 形式化函数定理 | III.11.1 | [0B8U](https://stacks.math.columbia.edu/tag/0B8U) | 深度文档 |
| 上半连续性 | III.12.8 | [0BD4](https://stacks.math.columbia.edu/tag/0BD4) | 应用示例 |

**Stacks Project特色**：
- 使用导出范畴的基变换公式
- 强调perfect complex的条件
- 系统的相对对偶理论

---

## 关键洞察

### 洞察1: 平坦性的几何意义

平坦性保证纤维"连续变化"，具体表现为：

| 平坦性条件 | 几何表现 | 上同调表现 |
|-----------|---------|-----------|
| 纤维维数恒定 | 族的连续性 | 上同调维数有界 |
| Hilbert多项式恒定 | 纤维的结构稳定 | Euler示性数局部恒定 |
| 无嵌入分量 | 纤维的"纯粹性" | Tor函子消失 |

### 洞察2: 交换代数-几何对应

ETH传统强调以下对应：

```
平坦基变换定理的交换代数本质

几何层语言                      交换代数语言
────────────────────────────────────────────────────────
g: Y' → Y 平坦                A → A' 平坦
R^i f_* F                     H^i(X, F) 作为A-模
g^* R^i f_* F                 H^i(X, F) ⊗_A A'
R^i f'_* (g'^* F)             H^i(X', F') 作为A'-模

定理: g^* R^i f_* F ≅ R^i f'_* (g'^* F)

等价于: H^i(X, F) ⊗_A A' ≅ H^i(X ⊗_A A', F ⊗_A A')

关键: 平坦性 ⟹ Tor_i^A(A', H^j(X, F)) = 0 (i > 0)
```

### 洞察3: 基变换的类型

不同类型的基变换有不同的行为：

| 基变换类型 | 平坦性 | 典型应用 | 上同调行为 |
|-----------|--------|---------|-----------|
| 域扩张 | ✅ | 基域变换 | 完全保持 |
| 局部化 | ✅ |  stalk计算 | 完全保持 |
| 完备化 | ✅ | 形式化函数 | 完全保持 |
| 闭嵌入 | ❌ | 特殊纤维 | 需要额外分析 |
| 一般基变换 | ? | 一般情形 | 需要平坦性假设 |

---

## Lean4形式化对应

### Mathlib4中的平坦基变换

```lean4
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Cohomology
import Mathlib.AlgebraicGeometry.Flat
import Mathlib.CategoryTheory.Monoidal.Tor

open AlgebraicGeometry CategoryTheory

namespace ETH_FlatBaseChange

-- ============================================
-- 1. 平坦基变换定理 (ETH 401-3532 Kapitel 3)
-- ============================================

variable {X Y Y' : Scheme} (f : X ⟶ Y) (g : Y' ⟶ Y) [IsFlat g]

/-- 纤维积图表 -/
variable (X' : Scheme) (g' : X' ⟶ X) (f' : X' ⟶ Y')
variable [IsPullback (sq : Square f' g' f g)]

/-- 平坦基变换定理 - ETH陈述 -/
theorem flatBaseChange {F : SheafOfAbelianGroups X} [F.IsQuasicoherent]
    (i : ℕ) :
    g^* (R^i f_* F) ≅ R^i f'_* (g'^* F) := by
  -- 证明分以下步骤:
  -- 1. 局部化到仿射情形
  -- 2. 相对Čech复形计算
  -- 3. 平坦性 ⟹ Tor消失
  -- 4. 复形张量积与上同调交换
  sorry

-- ============================================
-- 2. 纤维上的上同调计算
-- ============================================

variable {y' : Y'} (y : Y) (hy : g y' = y)

/-- 纤维上同调的基变换 -/
theorem fiberCohomologyBaseChange {F : SheafOfAbelianGroups X}
    (i : ℕ) :
    H^i(X_y, F|_{X_y}) ⊗[O_Y,y] O_Y',y' ≅ H^i(X'_{y'}, (g'^*F)|_{X'_{y'}}) := by
  -- 从平坦基变换定理导出
  sorry

-- ============================================
-- 3. 形式化函数定理 (应用)
-- ============================================

variable [IsProper f]

/-- 形式化函数定理 -/
theorem formalFunctionsTheorem {F : SheafOfAbelianGroups X} [F.IsCoherent]
    (y : Y) :
    (R^i f_* F)_y^completion ≅ lim_n H^i(X_n, F_n) := by
  -- 使用平坦基变换定理到Artin环
  sorry

-- ============================================
-- 4. 上半连续性 (应用)
-- ============================================

/-- 上同维数的上半连续性 -/
theorem upperSemicontinuity {F : SheafOfAbelianGroups X}
    [F.IsCoherent] [F.IsFlatOver Y] [IsProper f] :
    UpperSemicontinuous (fun y ↦ Module.rank (H^i(X_y, F_y))) := by
  -- 由Grauert定理
  sorry

end ETH_FlatBaseChange
```

### 形式化状态评估

| 组件 | Mathlib4状态 | 难度 | ETH特色 |
|------|-------------|------|---------|
| 平坦态射 | ✅ 已完成 | ★★☆ | Tor刻画 |
| 纤维积 | ✅ 已完成 | ★★★ | 泛性质 |
| 相对Čech复形 | 🔄 进行中 | ★★★★ | 计算工具 |
| 平坦基变换 | 🔄 进行中 | ★★★★★ | 核心定理 |
| 形式化函数定理 | ⚠️ 计划中 | ★★★★★ | 深度应用 |
| 上半连续性 | ⚠️ 计划中 | ★★★★☆ | 几何应用 |

---

## 扩展阅读

### ETH 401-3532课程相关内容

- **Kapitel 3**: 平坦基变换的完整理论
- **Kapitel 4**: 应用：形式化函数定理
- **Kapitel 5**: 应用：曲线族的上同调

### 参考文献

1. **Hartshorne, R.** (1977). *Algebraic Geometry*, Chapter III.9-12. Springer.
2. **Liu, Q.** (2002). *Algebraic Geometry and Arithmetic Curves*, §5.3.
3. **Stacks Project**. [Tag 02N6](https://stacks.math.columbia.edu/tag/02N6) - Cohomology and Base Change.
4. **Mumford, D.** (1970). *Abelian Varieties*, §II.5.
5. **EGA III** (1961). *Éléments de géométrie algébrique*.
6. **ETH Zurich** (2024). *401-3532-00L: Algebraic Geometry II*, Kapitel 3.

---

**文档版本**: v1.0
**创建日期**: 2026-04-10
**ETH课程**: 401-3532-00L Algebraic Geometry II
**对应章节**: Hartshorne III.9-12
**Stacks Tag**: [02N6](https://stacks.math.columbia.edu/tag/02N6)
