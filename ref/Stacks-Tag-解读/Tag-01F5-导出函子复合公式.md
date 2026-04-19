---
msc_primary: 00A99
msc_secondary:
  - 97A99
---

# Stacks Tag 01F5 - 导出函子复合公式

## 1. Tag基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 01F5 |
| **定理名称** | 导出函子复合公式 (Composition of Derived Functors) |
| **所属章节** | Chapter 20: Cohomology of Sheaves, Section 20.13 |
| **定理类型** | 引理 (Lemma) |
| ** Stacks原文** | Lemma 20.13.7 |

---

## 2. 定理原文

**定理陈述：**

设 $f: X \to Y$ 和 $g: Y \to Z$ 是环化空间的态射，则有：

$$Rg_* \circ Rf_* = R(g \circ f)_*$$

作为从 $D^{+}(X)$ 到 $D^{+}(Z)$ 的函子。

**英文原文：**
> The total derived functor of a composition is the composition of the total derived functors.
> 
> Let $f : X \to Y$ and $g : Y \to Z$ be morphisms of ringed spaces. In this case $Rg_* \circ Rf_* = R(g \circ f)_*$ as functors from $D^{+}(X) \to D^{+}(Z)$.

---

## 3. 概念依赖图

```
Tag 01F5: 导出函子复合公式
│
├── 前置概念
│   ├── 环化空间 (Ringed Space) [Tag 009M]
│   ├── 层正向像 (Direct Image Sheaf) $f_*$ [Tag 009K]
│   ├── 导出范畴 $D^{+}(X)$ [Tag 013H]
│   ├── 导出函子 $Rf_*$ [Tag 013U]
│   └── 态射复合 $(g \circ f)_*$ [Tag 00AK]
│
├── 依赖引理
│   ├── Derived Categories, Lemma 13.22.1
│   ├── Sheaves, Lemma 6.21.2 (层正向像的函子性)
│   ├── Lemma 20.11.10 (内射对象的性质)
│   └── Lemma 20.7.3 (高阶正向像)
│
└── 后续应用
    ├── Leray谱序列 [Tag 01FP]
    ├── 谱序列收敛 [Tag 01FQ]
    └── 凝聚层上同调 [Tag 01XK]
```

---

## 4. 证明概要

**证明思路：**

该证明的核心思想是应用导出范畴的一般理论（Derived Categories, Lemma 13.22.1），验证导出函子复合的两个关键条件：

### 步骤1：验证函子复合的等式

首先，对于普通层函子（非导出），我们有明显的等式：
$$g_* \circ f_* = (g \circ f)_*$$

这由层的正向像的定义直接得到——两次连续推前等价于复合推前。

### 步骤2：验证 $f_*\mathcal{I}$ 是 $g_*$-零调的

这是证明的技术核心。需要证明：若 $\mathcal{I}$ 是 $X$ 上的内射层，则 $f_*\mathcal{I}$ 对 $g_*$ 是零调的（acyclic），即：

$$R^i g_*(f_*\mathcal{I}) = 0, \quad \forall i > 0$$

**证明要点：**
- 由 Lemma 20.11.10，$f_*\mathcal{I}$ 是 $Y$ 上的软弱层（flasque）
- 软弱层对任意正向像函子都是零调的
- 结合 Lemma 20.7.3 对高阶正向像的描述

### 步骤3：应用通用导出函子定理

根据导出范畴理论，若 $F$ 和 $G$ 是两个左正合函子，且 $F$ 将内射对象映为 $G$-零调对象，则有：
$$R(G \circ F) = RG \circ RF$$

这正是我们所要证明的结论。

---

## 5. 与FormalMath对应

### 5.1 概念映射

| Stacks Project概念 | FormalMath对应内容 | 文件路径 |
|-------------------|-------------------|----------|
| 环化空间 $(X, \mathcal{O}_X)$ | RingedSpace定义 | `concept/代数几何/环化空间.md` |
| 层正向像 $f_*$ | pushforward定义 | `concept/层论/正向像与逆像.md` |
| 导出范畴 $D^{+}(X)$ | 有界下复形导出范畴 | `concept/同调代数/导出范畴.md` |
| 导出函子 $Rf_*$ | 右导出函子构造 | `concept/同调代数/导出函子.md` |
| 内射层 | Injective Sheaf | `concept/层论/内射层.md` |

### 5.2 知识体系位置

```
FormalMath知识体系
├── 代数几何
│   └── 环化空间与态射
│       ├── 层范畴 ←── Tag 01F5 所在领域
│       ├── 导出函子
│       └── 上同调理论
│
└── 同调代数
    └── 导出范畴
        ├── 导出函子复合
        └── 谱序列
```

### 5.3 学习路径建议

1. **前置知识**：环化空间 → 层论基础 → 阿贝尔范畴 → 导出范畴
2. **当前内容**：导出函子复合公式
3. **后续深入**：Leray谱序列 → 高阶正向像 → 凝聚层上同调

---

## 6. 应用与重要性

### 6.1 理论重要性

**核心地位：**
- 此定理是**层上同调理论**的基石之一
- 它是构造**Leray谱序列**的基础
- 在**相对上同调**和**纤维丛上同调**计算中不可或缺

### 6.2 具体应用场景

| 应用领域 | 具体应用 |
|---------|---------|
| **Leray谱序列** | 用于计算 $H^*(X, \mathcal{F})$ 通过 $H^*(Y, R^qf_*(\mathcal{F}))$ |
| **纤维丛上同调** | 若 $f: X \to Y$ 是纤维丛，计算全空间上同调 |
| **比较定理** | 连接不同拓扑下的上同调理论 |
| **基变换** | 研究 $R^qf_*$ 在基变换下的行为 |

### 6.3 实际计算示例

**例：射影空间的结构层上同调**

设 $f: \mathbb{P}^n_k \to \text{Spec}(k)$ 是结构态射，则：
$$R\Gamma(\mathbb{P}^n_k, \mathcal{O}) = Rf_*\mathcal{O}_{\mathbb{P}^n_k}$$

由导出函子复合公式，这是 $k$ 上的一个复形，其同调给出上同调群 $H^q(\mathbb{P}^n_k, \mathcal{O})$。

### 6.4 现代发展

- **增强导出范畴** (Enhanced Derived Categories)：在更精细的框架下重新表述
- **$\infty$-范畴**：导出函子复合在 $\infty$-范畴层面更为自然
- **导出代数几何**：在DAG框架下的推广

---

## 7. 与其他资源关联

### 7.1 Stacks Project内部关联

| 相关Tag | 关系类型 | 说明 |
|--------|---------|------|
| **Tag 01FP** (Leray谱序列) | 直接应用 | 该公式的谱序列版本 |
| **Tag 01FQ** (谱序列收敛) | 理论延续 | 谱序列的收敛性质 |
| **Tag 013U** (投影分解) | 对偶理论 | 导出函子的另一种计算方式 |
| **Tag 013T** (内射分解) | 技术基础 | 导出函子的构造方法 |
| **Tag 00AK** (层范畴) | 基础概念 | 函子定义的场所 |

### 7.2 外部参考资源

**经典教材：**
1. **Hartshorne, Algebraic Geometry**
   - Chapter III, §8: 导出函子复合与Leray谱序列
   - 习题 8.1-8.5 涉及相关计算

2. **Gelfand-Manin, Methods of Homological Algebra**
   - Chapter III: 导出范畴中的复合定理
   - 详细讨论了导出函子复合的一般理论

3. **Weibel, An Introduction to Homological Algebra**
   - Chapter 10: Grothendieck谱序列
   - 导出函子复合是其特例

**在线资源：**
- [Kerodon](https://kerodon.net/): Jacob Lurie的导出代数几何讲义
- [nLab: derived functor](https://ncatlab.org/nlab/show/derived+functor)
- [MathOverflow相关讨论](https://mathoverflow.net/questions/tagged/derived-functors)

### 7.3 相关数学软件

| 软件/库 | 功能 | 相关链接 |
|--------|------|---------|
| **Macaulay2** | 层上同调计算 | `coherentSheaf` 包 |
| **SageMath** | 代数几何计算 | `schemes` 模块 |
| **Lean 4** | 形式化验证 | `mathlib4` 的代数几何部分 |

---

## 8. Lean4形式化展望

### 8.1 形式化难度评估

| 方面 | 难度 | 说明 |
|------|------|------|
| 概念复杂度 | ★★★★☆ | 涉及导出范畴、层论、同调代数 |
| 证明技术 | ★★★☆☆ | 主要是验证零调性条件 |
| 依赖链条 | ★★★★★ | 需要完整的层论和导出范畴基础 |
| 预计工作量 | 中等偏大 | 需要3-6个月全职工作 |

### 8.2 mathlib4现状

**当前已有基础：**
```
mathlib4
├── CategoryTheory
│   ├── Abelian (阿贝尔范畴) ✅
│   ├── Derived (导出范畴) 🔄 开发中
│   └── Homological (同调代数) ✅
│
└── AlgebraicGeometry
    ├── Scheme (概形) ✅
    ├── Sheaf (层) 🔄 部分实现
    └── Cohomology (上同调) 📝 计划中
```

**需要补充的组件：**
1. 环化空间的完整形式化
2. 层范畴的阿贝尔结构
3. 足够内射对象的存在性
4. 导出函子的通用构造
5. 零调对象的判定定理

### 8.3 形式化策略建议

**阶段1：基础构建 (1-2个月)**
```lean
-- 环化空间的形式化
structure RingedSpace where
  carrier : Type u
  [top : TopologicalSpace carrier]
  structureSheaf : Sheaf Ring carrier

-- 层正向像的函子性
noncomputable def pushforward (f : X ⟶ Y) : Sheaf Ab X ⥤ Sheaf Ab Y := ...
```

**阶段2：导出函子构造 (2-3个月)**
```lean
-- 导出范畴的定义
def DerivedCategory (A : Type*) [Abelian A] : Type _ := ...

-- 右导出函子
noncomputable def rightDerivedFunctor (F : A ⥤ B) [EnoughInjectives A] : 
  DerivedCategory A ⥤ DerivedCategory B := ...
```

**阶段3：定理证明 (1个月)**
```lean
-- 核心定理：导出函子复合公式
theorem composition_of_derived_functors 
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (rightDerivedFunctor (pushforward g)) ⋙ 
    (rightDerivedFunctor (pushforward f)) = 
    rightDerivedFunctor (pushforward (g ≫ f)) := by
  -- 证明依赖于零调性验证
  sorry
```

### 8.4 预期挑战与解决方案

| 挑战 | 解决方案 |
|------|---------|
| 导出范畴的集合论问题 | 使用宇宙提升 (universe lifting) |
| 层范畴的内射分解 | 先形式化模层的特殊情况 |
| 谱序列的处理 | 在导出范畴框架下间接处理 |
| 与现有代数几何代码整合 | 参考现有的Scheme实现 |

### 8.5 相关Lean4项目参考

- [schemes-tactics](https://github.com/leanprover-community/mathlib4/tree/master/Mathlib/AlgebraicGeometry): Mathlib4的代数几何部分
- [lean-ga](https://github.com/eric-wieser/lean-ga): 几何代数的形式化
- [formalising-mathematics-2024](https://github.com/ImperialCollegeLondon/formalising-mathematics-2024): 帝国理工的形式化数学课程

---

## 附录：符号速查表

| 符号 | 含义 | LaTeX |
|------|------|-------|
| $f_*$ | 层正向像（推前） | `f_*` |
| $Rf_*$ | 导出正向像函子 | `Rf_*` |
| $D^{+}(X)$ | 有界下导出范畴 | `D^{+}(X)` |
| $R^qf_*$ | 第$q$高阶正向像 | `R^qf_*` |
| $\text{Spec}(R)$ | 环的素谱 | `\text{Spec}` |
| $\mathcal{I}$ | 内射层 | `\mathcal{I}` |
| $\mathfrak{p}$ | 素理想 | `\mathfrak{p}` |

---

*文档版本: 1.0*  
*创建日期: 2026年4月*  
*最后更新: 2026年4月*  
*对应Stacks Project版本: 2024.02*
