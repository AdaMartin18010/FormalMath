# Stacks Tag 01XK - 凝聚层性质

## 1. Tag基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 01XK |
| **概念名称** | 凝聚层基本性质 (Coherent Sheaves - Basic Properties) |
| **所属章节** | Chapter 30: Coherent Sheaves on Schemes, Section 30.4 |
| **概念类型** | 引理/性质 (Lemma/Properties) |
| ** Stacks原文** | Lemma 30.4.6 及相关内容 |

---

## 2. 定理/定义原文

**引理陈述（Tag 01XK 相关内容）：**

设 $f: X \to S$ 是概形的拟紧、拟分离态射。设 $\mathcal{F}$ 是 $X$ 上的拟凝聚层。则：

1. 正向像层 $f_*\mathcal{F}$ 是 $S$ 上的拟凝聚层。

2. 若 $S$ 是仿射的，则对任意 $q \geq 0$：
$$H^q(X, \mathcal{F}) = H^0(S, R^qf_*\mathcal{F})$$

3. 若 $S$ 是仿射且 $f$ 是凝聚态射，$\mathcal{F}$ 是凝聚层，则 $R^qf_*\mathcal{F}$ 也是凝聚层。

**英文原文（核心部分）：**
> Let $f : X \to S$ be a morphism of schemes. Assume that $f$ is quasi-separated and quasi-compact. Assume $S$ is affine. For any quasi-coherent $\mathcal{O}_X$-module $\mathcal{F}$ we have $H^q(X, \mathcal{F}) = H^0(S, R^qf_*\mathcal{F})$ for all $q$.

---

## 3. 概念依赖图

```
Tag 01XK: 凝聚层性质
│
├── 前置概念
│   ├── 凝聚层 (Coherent Sheaf) [Tag 01XZ]
│   ├── 拟凝聚层 (Quasi-coherent Sheaf) [Tag 01LA]
│   ├── 概形态射 [Tag 01Q2]
│   ├── 拟紧/拟分离态射 [Tag 01KU/01KW]
│   ├── 高阶正向像 $R^qf_*$ [Tag 01DM]
│   └── Leray谱序列 [Tag 01FP]
│
├── 核心性质
│   ├── 正向像保持拟凝聚性
│   ├── 凝聚态射保持凝聚性
│   ├── 仿射基下的上同调计算
│   └── 凝聚层的上同调有限性
│
├── 证明工具
│   ├── Cech上同调 [Tag 01EO]
│   ├── Leray谱序列 [Tag 01FP]
│   ├── 仿射覆盖技巧
│   └── 下降理论
│
└── 后续应用
    ├── 半连续性定理 [Tag 02O8]
    ├── 基变换定理 [Tag 02N6]
    ├── 比较定理
    └── 代数几何基本定理
```

---

## 4. 证明概要

### 4.1 正向像的拟凝聚性

**定理：** 设 $f: X \to S$ 是拟紧、拟分离的态射，$\mathcal{F}$ 是拟凝聚层，则 $f_*\mathcal{F}$ 拟凝聚。

**证明要点：**

**步骤1：** 问题局部化

由于拟凝聚性是局部性质，可设 $S = \text{Spec}(A)$ 仿射。

**步骤2：** 仿射覆盖

设 $X = U_1 \cup \cdots \cup U_n$ 是有限仿射开覆盖（由拟紧性）。

**步骤3：** 利用Cech复形

$\Gamma(X, \mathcal{F}) = \check{H}^0(\{U_i\}, \mathcal{F})$ 可由Cech复形计算。

**步骤4：** 验证模结构

证明 $\Gamma(X, \mathcal{F})$ 有自然的 $A$-模结构，且与限制映射相容。

### 4.2 上同调等式

**定理：** 若 $S$ 仿射，则 $H^q(X, \mathcal{F}) = H^0(S, R^qf_*\mathcal{F})$。

**证明（利用Leray谱序列）：**

**步骤1：** 写出Leray谱序列

$$E_2^{p,q} = H^p(S, R^qf_*\mathcal{F}) \Rightarrow H^{p+q}(X, \mathcal{F})$$

**步骤2：** 利用 $S$ 仿射的性质

因 $S$ 仿射，$H^p(S, \mathcal{G}) = 0$ 对所有 $p > 0$ 和拟凝聚层 $\mathcal{G}$。

**步骤3：** 谱序列退化

$E_2^{p,q} = 0$ 对 $p > 0$，所以谱序列在 $E_2$ 处退化。

**步骤4：** 得到结论

$$H^n(X, \mathcal{F}) = E_2^{0,n} = H^0(S, R^nf_*\mathcal{F})$$

### 4.3 凝聚层的保持

**定理：** 若 $f$ 是凝聚态射（proper），$\mathcal{F}$ 凝聚，则 $R^qf_*\mathcal{F}$ 凝聚。

**这是Grothendieck的凝聚定理，是代数几何的基本定理之一。**

**证明思路：**

1. 问题可局部化到 $S$ 仿射
2. 利用Noetherian归纳法
3. 利用Chow引理约化到射影态射
4. 射影态射情形用射影空间的上同调计算

---

## 5. 与FormalMath对应

### 5.1 概念映射

| Stacks Project概念 | FormalMath对应内容 | 文件路径 |
|-------------------|-------------------|----------|
| 凝聚层 | CoherentSheaf | `concept/代数几何/凝聚层.md` |
| 拟凝聚层 | QuasiCoherentSheaf | `concept/代数几何/拟凝聚层.md` |
| 高阶正向像 | HigherDirectImage | `concept/层论/高阶正向像.md` |
| 凝聚态射 | ProperMorphism | `concept/代数几何/态射性质.md` |
| Leray谱序列 | LeraySpectralSequence | `concept/同调代数/谱序列.md` |

### 5.2 知识体系位置

```
FormalMath知识体系
├── 层论
│   ├── 拟凝聚层
│   └── 凝聚层 ←── Tag 01XK
│
├── 代数几何
│   ├── 概形态射
│   │   ├── 拟紧/拟分离
│   │   └── 凝聚态射
│   │
│   └── 上同调理论
│       ├── 层上同调
│       ├── 高阶正向像
│       └── 凝聚定理 ←── Tag 01XK的核心
```

### 5.3 学习路径建议

```
学习路径：
层论基础
    ├── 拟凝聚层
    └── 凝聚层 ←── Tag 01XK的前置
            ↓
概形态射
    ├── 基本性质
    ├── 拟紧/拟分离
    └── 凝聚态射
            ↓
上同调理论
    ├── 层上同调
    ├── Leray谱序列 ←── 证明工具
    └── 凝聚层性质 ←── Tag 01XK
```

---

## 6. 应用与重要性

### 6.1 理论重要性

**代数几何的柱石：**

凝聚层的性质是代数几何的核心内容。Grothendieck的凝聚定理是**现代代数几何的基石之一**。

**核心作用：**
1. **上同调有限性**：凝聚层在凝聚态射下的高阶正向像仍凝聚
2. **半连续性**：纤维维数的半连续性定理的基础
3. **比较定理**：不同上同调理论的比较

### 6.2 实际应用场景

#### 场景1：Riemann-Roch定理

对于曲线 $C$ 上的线丛 $L$，Riemann-Roch定理：
$$\chi(L) = \deg(L) + 1 - g$$

证明依赖于凝聚层上同调的有限性。

#### 场景2：参量空间的存在性

Hilbert概形、Picard概形的存在性证明都依赖于凝聚定理。

#### 场景3：模空间的紧化

利用凝聚态射的性质，可以将模空间紧化。

### 6.3 具体例子

**例1：射影空间的上同调**

设 $X = \mathbb{P}^n_k$，$\mathcal{O}(m)$ 是扭层，则：
- $H^0(X, \mathcal{O}(m)) = k[x_0, \ldots, x_n]_m$（$m$次齐次多项式）
- $H^n(X, \mathcal{O}(m)) = k[x_0, \ldots, x_n]_{-m-n-1}^*$
- 其他情形为零

**例2：曲线的上同调**

设 $C$ 是亏格 $g$ 的射影曲线，则：
$$\dim H^0(C, \mathcal{O}_C) = 1, \quad \dim H^1(C, \mathcal{O}_C) = g$$

### 6.4 现代发展

- **导出凝聚层**：$D^b_{coh}(X)$ 的等价性
- **傅里叶-穆凯里变换**：凝聚层的导出等价
- **稳定性条件**：凝聚层的稳定性

---

## 7. 与其他资源关联

### 7.1 Stacks Project内部关联

| 相关Tag | 关系类型 | 说明 |
|--------|---------|------|
| **Tag 01XZ** (凝聚层定义) | 基础概念 | 凝聚层的定义 |
| **Tag 01LA** (拟凝聚层) | 弱化版本 | 正向像保持拟凝聚性 |
| **Tag 01FP** (Leray谱序列) | 证明工具 | 上同调等式的证明 |
| **Tag 01KU/01KW** (拟紧/拟分离) | 前提条件 | 性质成立的条件 |
| **Tag 02O8** (半连续性) | 后续应用 | 凝聚定理的应用 |
| **Tag 02N6** (基变换) | 后续应用 | 凝聚定理的应用 |

### 7.2 外部参考资源

**经典教材：**

1. **Hartshorne, Algebraic Geometry**
   - Chapter III, §5: 凝聚层的高阶正向像
   - 定理5.2：凝聚定理

2. **EGA III** (Grothendieck)
   - 凝聚定理的原始论述
   - 最权威的参考

3. **Vakil, Foundations of Algebraic Geometry**
   - §18.9: 凝聚定理
   - 现代、详细的阐述

4. **Liu, Algebraic Geometry and Arithmetic Curves**
   - Chapter 5: 凝聚层与上同调

**在线资源：**
- [Stacks Project 第30章](https://stacks.math.columbia.edu/tag/01XK)
- [nLab: coherent sheaf](https://ncatlab.org/nlab/show/coherent+sheaf)

---

## 8. Lean4形式化展望

### 8.1 形式化难度评估

| 方面 | 难度 | 说明 |
|------|------|------|
| 概念复杂度 | ★★★★★ | 涉及层论、上同调、凝聚性 |
| 证明技术 | ★★★★★ | 需要谱序列和覆盖技巧 |
| 依赖链条 | ★★★★★ | 需要完整的代数几何基础 |
| 预计工作量 | 很大 | 需要6-12个月 |

### 8.2 mathlib4现状

**当前已有基础：**
```
mathlib4
├── AlgebraicGeometry
│   ├── Scheme ✅
│   ├── QuasiCoherentSheaf 🔄 开发中
│   └── CoherentSheaf 📝 计划中
│
└── CategoryTheory
    ├── Abelian ✅
    └── Sites (层论) ✅
```

### 8.3 形式化路线图

**阶段1：凝聚层定义 (2个月)**

```lean
import Mathlib.AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

-- 凝聚层的定义
def IsCoherent {X : Scheme} (F : SheafOfModules X) : Prop where
  of_finite_type : F.OfFiniteType
  subsheaf_of_finite_type : ∀ (G : Subsheaf F), G.OfFiniteType → G.IsFinitePresentation

-- 拟凝聚层
def IsQuasiCoherent {X : Scheme} (F : SheafOfModules X) : Prop := ...

end AlgebraicGeometry
```

**阶段2：高阶正向像 (3个月)**

```lean
-- 高阶正向像的定义
def higherDirectImage (f : X ⟶ Y) (q : ℕ) (F : SheafOfModules X) : 
    SheafOfModules Y := ...

-- 拟凝聚性保持
theorem quasiCoherent_preserved_under_direct_image 
    {f : X ⟶ Y} [IsQuasiCompact f] [IsQuasiSeparated f]
    {F : SheafOfModules X} [F.IsQuasiCoherent] :
    (f.directImage F).IsQuasiCoherent := by
  sorry
```

**阶段3：凝聚定理 (4-6个月)**

```lean
-- 凝聚定理
theorem coherence_theorem {f : X ⟶ Y} [IsProper f]
    {F : SheafOfModules X} [F.IsCoherent] (q : ℕ) :
    (higherDirectImage f q F).IsCoherent := by
  sorry

-- Leray谱序列的应用
theorem leray_spectral_sequence_affine_base {f : X ⟶ Y} 
    [IsAffine Y] [IsQuasiCompact f] [IsQuasiSeparated f]
    {F : SheafOfModules X} [F.IsQuasiCoherent] (q : ℕ) :
    let RqF := higherDirectImage f q F
    Isomorphic (sheafCohomology q X F) (globalSections Y RqF) := by
  sorry
```

### 8.4 技术挑战与解决方案

| 挑战 | 解决方案 |
|------|---------|
| 凝聚层的局部判定 | 使用仿射开覆盖的等价条件 |
| 高阶正向像的计算 | 利用Cech上同调或谱序列 |
| 凝聚定理的证明 | 参考EGA的系统证明 |
| 与现有代码的整合 | 逐步扩展拟凝聚层的代码 |

---

## 附录

### A. 符号速查表

| 符号 | 含义 | LaTeX |
|------|------|-------|
| $\mathcal{F}$ | 凝聚层 | `\mathcal{F}` |
| $f_*\mathcal{F}$ | 正向像层 | `f_*\mathcal{F}` |
| $R^qf_*\mathcal{F}$ | 高阶正向像 | `R^qf_*\mathcal{F}` |
| $H^q(X, \mathcal{F})$ | 层上同调 | `H^q(X, \mathcal{F})` |
| $\mathcal{O}_X$ | 结构层 | `\mathcal{O}_X` |

### B. 凝聚层 vs 拟凝聚层

| 性质 | 凝聚层 | 拟凝聚层 |
|------|--------|---------|
| 局部有限生成 | ✓ | ✓ |
| 关系层有限生成 | ✓ | 不一定 |
| 在凝聚态射下 | 保持 | 保持 |
| 在一般态射下 | 不一定保持 | 保持（拟紧+拟分离） |
| 例子 | 向量丛的截面层 | 任意模的相伴层 |

---

*文档版本: 1.0*  
*创建日期: 2026年4月*  
*对应Stacks Project版本: 2024.02*
