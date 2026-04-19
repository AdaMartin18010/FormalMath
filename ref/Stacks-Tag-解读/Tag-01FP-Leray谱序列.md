---
msc_primary: 00A99
msc_secondary:
  - 97A99
---

# Stacks Tag 01FP - Leray谱序列

## 1. Tag基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 01FP |
| **定理名称** | Leray谱序列 (Leray Spectral Sequence) |
| **所属章节** | Chapter 20: Cohomology of Sheaves, Section 20.14 |
| **定理类型** | 引理 (Lemma) |
| ** Stacks原文** | Lemma 20.14.5 |

---

## 2. 定理原文

**定理陈述：**

设 $f: X \to Y$ 是环化空间的态射，$\mathcal{F}$ 是 $X$ 上的 $\mathcal{O}_X$-模。则存在一个谱序列：

$$E_2^{p,q} = H^p(Y, R^qf_*\mathcal{F}) \Rightarrow H^{p+q}(X, \mathcal{F})$$

**英文原文：**
> Let $f : X \to Y$ be a morphism of ringed spaces. Let $\mathcal{F}$ be an $\mathcal{O}_X$-module. There is a spectral sequence with $E_2$-page $E_2^{p,q} = H^p(Y, R^qf_*\mathcal{F})$ converging to $H^{p+q}(X, \mathcal{F})$.

**推广形式（Relative Leray谱序列）：**

对于 $g: Y \to Z$ 和 $\mathcal{F} \in \text{Mod}(\mathcal{O}_X)$，有：
$$E_2^{p,q} = R^pg_*(R^qf_*\mathcal{F}) \Rightarrow R^{p+q}(g \circ f)_*\mathcal{F}$$

---

## 3. 概念依赖图

```
Tag 01FP: Leray谱序列
│
├── 前置概念
│   ├── 环化空间态射 $f: X \to Y$ [Tag 009M]
│   ├── 层上同调 $H^*(X, \mathcal{F})$ [Tag 01FV]
│   ├── 高阶正向像 $R^qf_*$ [Tag 01DM]
│   ├── 导出函子复合 [Tag 01F5]
│   └── 谱序列一般理论 [Tag 010H]
│
├── 依赖引理
│   ├── Lemma 20.13.7 (导出函子复合公式)
│   ├── Grothendieck谱序列构造
│   ├── 内射分解的存在性 [Tag 013T]
│   └── 双复形谱序列 [Tag 010J]
│
├── 等价表述
│   ├── $Rf_*$ 保持内射对象
│   ├── $E_2^{p,q} = R^p\Gamma(Y, R^qf_*\mathcal{F})$
│   └── $E_\infty^{p,q} = \text{Gr}^p H^{p+q}(X, \mathcal{F})$
│
└── 后续应用
    ├── 谱序列收敛 [Tag 01FQ]
    ├── 纤维丛上同调计算
    ├── 比较定理
    └── 上同调下降理论
```

---

## 4. 证明概要

### 4.1 核心思想

Leray谱序列本质上是**Grothendieck谱序列**在层上同调中的具体实现：

$$R(G \circ F) = RG \circ RF \quad \text{由谱序列联系}$$

其中：
- $F = f_*$ (层正向像)
- $G = \Gamma(Y, -)$ (全局截面函子)
- $G \circ F = \Gamma(X, -)$ (因为 $\Gamma(Y, f_*\mathcal{F}) = \Gamma(X, \mathcal{F})$)

### 4.2 详细证明步骤

**步骤1：构造双复形**

取 $\mathcal{F}$ 的内射分解 $\mathcal{F} \to \mathcal{I}^\bullet$，构造双复形：
$$C^{p,q} = \Gamma(Y, f_*\mathcal{I}^q) \text{ 的双重复形}$$

更精细地，使用**Cartan-Eilenberg分解**构造双复形。

**步骤2：两种谱序列的构造**

对于双复形 $C^{\bullet, \bullet}$，有两种自然谱序列：

**第一谱序列（按$q$过滤）：**
- $'E_1^{p,q} = H^q(C^{p, \bullet}) = H^q(\Gamma(Y, f_*\mathcal{I}^\bullet))$
- 这给出层上同调的直接计算

**第二谱序列（按$p$过滤）：**
- $''E_1^{p,q} = H^p(C^{\bullet, q})$
- 利用 $f_*$ 将内射映为 $\Gamma(Y, -)$-零调的对象

**步骤3：计算 $E_2$页**

$$''E_2^{p,q} = H^p(Y, R^qf_*\mathcal{F})$$

这是因为：
1. $R^qf_*\mathcal{F}$ 是 $f_*\mathcal{I}^\bullet$ 的第$q$个上同调层
2. 由层的内射分解计算 $H^p(Y, -)$

**步骤4：收敛性**

两个谱序列都收敛到同一目标：
$$H^n(\text{Tot}(C^{\bullet, \bullet})) = H^n(X, \mathcal{F})$$

### 4.3 边缘同态

谱序列给出重要的**边缘同态**（Edge Homomorphisms）：

1. **低次边缘映射：**
   $$H^p(Y, f_*\mathcal{F}) \to H^p(X, \mathcal{F})$$
   
2. **高次边缘映射：**
   $$H^q(X, \mathcal{F}) \to H^0(Y, R^qf_*\mathcal{F}) = \Gamma(Y, R^qf_*\mathcal{F})$$

### 4.4 五项正合列

由谱序列可导出低维的正合列：
$$0 \to H^1(Y, f_*\mathcal{F}) \to H^1(X, \mathcal{F}) \to H^0(Y, R^1f_*\mathcal{F}) \to H^2(Y, f_*\mathcal{F}) \to H^2(X, \mathcal{F})$$

---

## 5. 与FormalMath对应

### 5.1 概念映射

| Stacks Project概念 | FormalMath对应内容 | 文件路径 |
|-------------------|-------------------|----------|
| 谱序列 $(E_r, d_r)$ | Spectral Sequence定义 | `concept/同调代数/谱序列.md` |
| 层上同调 $H^*(X, \mathcal{F})$ | Sheaf Cohomology | `concept/层论/层上同调.md` |
| 高阶正向像 $R^qf_*$ | Higher Direct Image | `concept/层论/高阶正向像.md` |
| 收敛性 $\Rightarrow$ | Convergence of Spectral Sequence | `concept/同调代数/谱序列收敛.md` |
| 双复形 | Double Complex | `concept/同调代数/双复形.md` |

### 5.2 知识体系位置

```
FormalMath知识体系
├── 同调代数
│   ├── 谱序列理论
│   │   ├── 定义与基本性质 ←── Tag 01FP
│   │   ├── Grothendieck谱序列
│   │   └── 收敛性
│   │
│   └── 导出函子
│       └── 复合公式 [Tag 01F5]
│
└── 代数几何
    └── 层上同调
        ├── 基本理论
        └── Leray谱序列 ←── 核心应用
```

### 5.3 学习路径建议

```
学习路径：
环化空间 → 层论基础 → 层上同调 → 导出函子 → 谱序列基础 → Leray谱序列
    ↓                                                    ↓
    └────────────────────────────────────────────────────┘
                    导出函子复合公式 [Tag 01F5]
```

---

## 6. 应用与重要性

### 6.1 理论重要性

**历史地位：**
- **Leray** (1946) 在研究层论和谱序列时首次引入
- **Grothendieck** 将其推广到抽象导出函子框架
- 现代代数几何的**标准工具**

**核心作用：**
1. **分解复杂计算**：将 $X$ 的上同调分解为 $Y$ 和纤维上的计算
2. **连接局部与整体**：$R^qf_*$ 是局部信息，$H^p(Y, -)$ 是整体积分
3. **计算策略**："先沿纤维，再沿基" 或反之

### 6.2 具体应用场景

#### 场景1：纤维丛上同调

设 $\pi: E \to B$ 是纤维丛，纤维为 $F$，则：
$$E_2^{p,q} = H^p(B, \mathcal{H}^q(F)) \Rightarrow H^{p+q}(E)$$

其中 $\mathcal{H}^q(F)$ 是上同调层的局部系统。

**例：Hopf纤维化** $S^3 \to S^2$，纤维 $S^1$：
- $E_2^{p,q} = H^p(S^2, H^q(S^1))$
- 计算可得 $H^*(S^3)$

#### 场景2：概形的相对上同调

对于概形态射 $f: X \to S$，研究 $R^qf_*\mathcal{F}$ 的性质：
- 半连续性定理
- 基变换定理
- 平展态射的比较定理

#### 场景3：投影公式

与**投影公式**（Projection Formula）结合使用：
$$Rf_*(\mathcal{F} \otimes^L f^*\mathcal{G}) = Rf_*\mathcal{F} \otimes^L \mathcal{G}$$

### 6.3 计算策略表

| 问题类型 | 谱序列使用策略 | 期望结果 |
|---------|--------------|---------|
| 计算 $H^*(X)$ | 找合适的 $f: X \to Y$ | 利用 $Y$ 和纤维的已知信息 |
| 证明消失性 | 证明 $E_2$ 页大部分为零 | 推出 $H^n(X) = 0$ |
| 计算维数 | 计算 $E_\infty$ 页非零项 | 得到 $H^n(X)$ 的维数 |
| 比较上同调 | 构造合适的态射 | 建立两个理论的比较 |

### 6.4 现代发展

- **导出来回形式** (Derived Adjunction Formulas)
- **扭曲Leray谱序列** (Twisted Leray Spectral Sequence)
- ** motivic Leray谱序列**：在motivic上同调中的版本
- **p进Leray谱序列**：在p进上同调理论中的应用

---

## 7. 与其他资源关联

### 7.1 Stacks Project内部关联

| 相关Tag | 关系类型 | 说明 |
|--------|---------|------|
| **Tag 01F5** (导出函子复合) | 理论基础 | 构造谱序列的函子复合公式 |
| **Tag 01FQ** (谱序列收敛) | 技术补充 | 收敛性的详细讨论 |
| **Tag 013T** (内射分解) | 构造工具 | 谱序列构造的基础 |
| **Tag 01DM** (高阶正向像) | 核心概念 | 谱序列的 $E_2$ 项 |
| **Tag 01FV** (层上同调) | 目标对象 | 谱序列收敛的对象 |
| **Tag 010H** (谱序列一般理论) | 通用框架 | 一般谱序列理论 |

### 7.2 外部参考资源

**经典教材：**

1. **Godement, Topologie Algébrique et Théorie des Faisceaux**
   - 第II章：层上同调与谱序列
   - Leray谱序列的经典论述

2. **Griffiths-Harris, Principles of Algebraic Geometry**
   - Chapter 3, §5: 复流形上的谱序列
   - 包含大量计算示例

3. **Voisin, Hodge Theory and Complex Algebraic Geometry**
   - Chapter 4: 谱序列在Hodge理论中的应用

**专题文章：**

- **Grothendieck, Tôhoku Paper** (1957): 导出函子和谱序列的奠基之作
- **Deligne, Théorie de Hodge I, II**: 混合Hodge结构的谱序列应用

**在线资源：**
- [nLab: Leray spectral sequence](https://ncatlab.org/nlab/show/Leray+spectral+sequence)
- [Stacks Project 第20章](https://stacks.math.columbia.edu/tag/01FP)

### 7.3 计算工具

| 工具 | 功能 | 示例 |
|------|------|------|
| **Macaulay2** | 层上同调计算 | `HH^i` 命令 |
| **SageMath** | 谱序列计算 | `spectral_sequence` 模块 |
| **Singular** | 交换代数计算 | 局部上同调 |

---

## 8. Lean4形式化展望

### 8.1 形式化难度评估

| 方面 | 难度 | 说明 |
|------|------|------|
| 概念复杂度 | ★★★★★ | 涉及谱序列、层论、导出范畴 |
| 证明技术 | ★★★★☆ | 双复形技术和谱序列收敛 |
| 依赖链条 | ★★★★★ | 需要完整的同调代数基础 |
| 预计工作量 | 大 | 需要6-12个月 |

### 8.2 mathlib4现状

**当前已有基础：**
```
mathlib4
├── Algebra
│   └── Homology (同调代数) ✅
│       ├── Homology.lean
│       ├── ShortComplex.lean
│       └── Single.lean
│
└── CategoryTheory
    ├── Abelian (阿贝尔范畴) ✅
    ├── SpectralSequence 📝 计划中
    └── HomologicalComplex ✅
```

**需要的补充：**
1. 谱序列的一般框架
2. 层的阿贝尔范畴结构
3. 内射分解的函子性
4. 双复形及其全复形
5. 过滤复形的谱序列

### 8.3 形式化路线图

**阶段1：谱序列基础 (3-4个月)**

```lean
-- 谱序列的定义
structure SpectralSequence (C : Type*) [Category C] [Abelian C] where
  page : ℕ → ℤ → ℤ → C  -- E_r^{p,q}
  differential (r : ℕ) : page r ⟶ page r (1)  -- d_r
  condition : ∀ r p q, (differential r ≫ differential r) = 0
  iso : page (r+1) ≅ homology (differential r)  -- E_{r+1} = H(E_r)

-- 收敛性定义
structure ConvergenceTo (E : SpectralSequence C) (H : ℤ → C) where
  filtration : ∀ n, Filtration (H n)
  iso : ∀ p q, E.page ∞ p q ≅ filtration.grade p (H (p+q))
```

**阶段2：双复形谱序列 (2-3个月)**

```lean
-- 双复形
structure DoubleComplex (C : Type*) [Category C] [Abelian C] where
  obj : ℤ → ℤ → C
  horizontal_diff : ∀ i j, obj i j ⟶ obj (i+1) j
  vertical_diff : ∀ i j, obj i j ⟶ obj i (j+1)
  -- 反交换条件
  anticomm : ∀ i j, horizontal_diff i j ≫ vertical_diff (i+1) j = 
                    - (vertical_diff i j ≫ horizontal_diff i (j+1))

-- 双复形的两种谱序列
def firstSpectralSequence (D : DoubleComplex C) : SpectralSequence C := ...
def secondSpectralSequence (D : DoubleComplex C) : SpectralSequence C := ...
```

**阶段3：Leray谱序列 (2-3个月)**

```lean
-- 层的高阶正向像
def higherDirectImage (f : X ⟶ Y) (q : ℕ) : Sheaf X ⥤ Sheaf Y := ...

-- Leray谱序列
def leraySpectralSequence (f : X ⟶ Y) (F : Sheaf X) : 
  SpectralSequence Ab where
  page 2 p q := (higherDirectImage f q ⋙ sheafCohomology p) F
  -- 构造细节...
  
theorem lerayConvergence (f : X ⟶ Y) (F : Sheaf X) :
  leraySpectralSequence f F ≅ sheafCohomology (p+q) F := ...
```

### 8.4 技术挑战与解决方案

| 挑战 | 解决方案 |
|------|---------|
| 谱序列的索引复杂性 | 使用依赖类型精确索引 |
| 收敛性的集合论问题 | 使用过滤对象的形式化 |
| 双复形的符号问题 | 明确区分水平/垂直微分 |
| 与现有层论代码整合 | 逐步扩展已有框架 |

### 8.5 与其他形式化项目的联系

- **UniMath**: 有导出范畴的形式化基础
- **HoTT-Agda**: 谱序列的同伦类型论视角
- **Lean-Stacks**: Stacks Project的形式化项目（计划中）

---

## 附录

### A. 符号速查表

| 符号 | 含义 | 说明 |
|------|------|------|
| $E_r^{p,q}$ | 谱序列的第$r$页 | $p$为过滤度，$q$为补全度 |
| $d_r$ | 第$r$页微分 | $d_r: E_r^{p,q} \to E_r^{p+r, q-r+1}$ |
| $\Rightarrow$ | 收敛 | 谱序列收敛到目标 |
| $R^qf_*$ | 第$q$高阶正向像 | 右导出函子 |
| $H^p(Y, \mathcal{G})$ | 层上同调 | 右导出函子 $R^p\Gamma(Y, \mathcal{G})$ |
| $\text{Tot}(C^{\bullet,\bullet})$ | 双复形的全复形 | 对角线和 |

### B. 典型计算示例

**计算射影直线的结构层上同调：**

设 $f: \mathbb{P}^1_k \to \text{Spec}(k)$，则：
- $E_2^{p,q} = H^p(\text{Spec}(k), R^qf_*\mathcal{O})$ 
- $R^qf_*\mathcal{O} = H^q(\mathbb{P}^1_k, \mathcal{O})$ 的常值层
- 谱序列退化给出：$H^0 = k$, $H^1 = 0$

---

*文档版本: 1.0*  
*创建日期: 2026年4月*  
*对应Stacks Project版本: 2024.02*
