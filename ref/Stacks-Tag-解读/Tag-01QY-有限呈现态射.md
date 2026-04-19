---
msc_primary: 00A99
msc_secondary:
  - 97A99
---

# Stacks Tag 01QY - 有限呈现态射

## 1. Tag基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 01QY |
| **概念名称** | 有限呈现态射 (Morphisms of Finite Presentation) |
| **所属章节** | Chapter 29: Morphisms of Schemes, Section 29.21 |
| **概念类型** | 定义 (Definition) |
| ** Stacks原文** | Definition 29.21.1 |

---

## 2. 定义原文

**定义陈述：**

设 $f: X \to S$ 是概形的态射。

1. 称 $f$ 在点 $x \in X$ 是**局部有限呈现**的（locally of finite presentation），如果存在 $x$ 的一个仿射开邻域 $\text{Spec}(A) = U \subset X$ 和 $f(x)$ 的一个仿射开邻域 $\text{Spec}(R) = V \subset S$，使得 $f(U) \subset V$ 且诱导的环同态 $R \to A$ 是有限呈现的。

2. 称 $f$ 是**局部有限呈现**的，如果它在每个点 $x \in X$ 都是局部有限呈现的。

3. 称 $f$ 是**有限呈现**的，如果它是局部有限呈现、拟紧且拟分离的。

**英文原文：**
> Let $f : X \to S$ be a morphism of schemes.
> 
> 1. We say that $f$ is *locally of finite presentation at $x$* if there exists an affine open neighbourhood $\mathop{\mathrm{Spec}}(A) = U \subset X$ of $x$ and an affine open $\mathop{\mathrm{Spec}}(R) = V \subset S$ with $f(U) \subset V$ such that the induced ring map $R \to A$ is of finite presentation.
> 
> 2. We say that $f$ is *locally of finite presentation* if it is locally of finite presentation at every point of $X$.
> 
> 3. We say that $f$ is *of finite presentation* if it is locally of finite presentation, quasi-compact and quasi-separated.

---

## 3. 概念依赖图

```
Tag 01QY: 有限呈现态射
│
├── 前置概念
│   ├── 概形 (Scheme) [Tag 006V]
│   ├── 概形态射 [Tag 01Q2]
│   ├── 仿射开覆盖 [Tag 006W]
│   ├── 有限呈现环同态 [Tag 00EP]
│   ├── 拟紧态射 [Tag 01KU]
│   └── 拟分离态射 [Tag 01KW]
│
├── 等价刻画
│   ├── 局部：仿射局部有限呈现
│   ├── 整体：有限呈现 = 局部有限呈现 + 拟紧 + 拟分离
│   └── 开浸入情形：开浸入自动局部有限呈现
│
├── 重要性质
│   ├── 在基变换下稳定 [Tag 01QZ]
│   ├── 在复合下稳定 [Tag 01R0]
│   ├── 对靶标局部 [Tag 01R2]
│   └── 下降性质 [Tag 02KR]
│
└── 后续应用
    ├── 极限方法 [Tag 01ZB]
    ├──  constructible 性质 [Tag 054J]
    └── 平坦下降 [Tag 02L6]
```

---

## 4. 证明概要（等价性证明）

### 4.1 局部定义的相容性

**引理：** 定义是良定的，即不依赖于仿射开集的选择。

**证明思路：**

设 $x \in X$ 有两个仿射开邻域 $U = \text{Spec}(A)$ 和 $U' = \text{Spec}(A')$，都映射到 $V = \text{Spec}(R) \subset S$。

**步骤1：** $U \cap U'$ 可由基本开集覆盖
$$U \cap U' = \bigcup_{i=1}^n D(f_i) = \bigcup_{j=1}^m D(g_j)$$

其中 $f_i \in A$，$g_j \in A'$。

**步骤2：** 利用局部化的有限呈现性

若 $R \to A$ 有限呈现，则对任意 $f \in A$，$R \to A_f$ 也是有限呈现。

**步骤3：** 传递性

若 $R \to A'$ 在覆盖 $U \cap U'$ 的某点处与有限呈现环局部同构，则整体也是有限呈现。

### 4.2 有限呈现的组合刻画

**命题：** $f: X \to S$ 有限呈现当且仅当：
1. 局部有限呈现
2. 拟紧（准紧）
3. 拟分离

**证明要点：**

- **拟紧**：$X$ 可被有限个仿射开集 $U_i = \text{Spec}(A_i)$ 覆盖，且每个 $A_i$ 在对应的 $R_i$ 上有限呈现
- **拟分离**：对角线 $\Delta: X \to X \times_S X$ 是拟紧的

**为什么需要这三个条件：**

| 条件 | 作用 |
|------|------|
| 局部有限呈现 | 局部代数性质："有限个生成元和关系" |
| 拟紧 | 整体有限性：有限个仿射覆盖 |
| 拟分离 | 技术性条件：保证对角线 behaves well |

### 4.3 与有限型态射的关系

**回顾：** 有限型态射 $f: X \to S$ 要求：
- 局部有限型：$R \to A$ 有限型（有限生成）
- 拟紧

**关键区别：**

有限型：$A = R[x_1, \ldots, x_n]/\mathfrak{a}$（有限生成）  
有限呈现：$A = R[x_1, \ldots, x_n]/(f_1, \ldots, f_m)$（有限生成 + 有限关系）

**关系链：**
$$
\text{有限呈现} \Rightarrow \text{有限型} \Rightarrow \text{局部有限型}
$$

---

## 5. 与FormalMath对应

### 5.1 概念映射

| Stacks Project概念 | FormalMath对应内容 | 文件路径 |
|-------------------|-------------------|----------|
| 有限呈现环同态 | RingHom.FinitePresentation | `concept/交换代数/有限呈现.md` |
| 概形态射 | Scheme.Hom | `concept/代数几何/概形.md` |
| 拟紧态射 | QuasiCompact | `concept/代数几何/拟紧态射.md` |
| 拟分离态射 | QuasiSeparated | `concept/代数几何/拟分离态射.md` |
| 局部性质 | LocalProperty | `concept/代数几何/态射性质.md` |

### 5.2 知识体系位置

```
FormalMath知识体系
├── 交换代数
│   └── 环同态的有限性条件
│       ├── 有限型 (Finite Type) ←── 较弱
│       └── 有限呈现 (Finite Presentation) ←── Tag 01QY
│
└── 代数几何
    └── 概形态射的性质
        ├── 局部性质：局部有限呈现
        ├── 整体性质：有限呈现
        └── 有限性层次：有限 ⟹ 仿射 ⟹ 有限型 ⟹ 局部有限型
```

### 5.3 学习路径建议

```
学习路径：
交换代数基础
    ├── 有限生成模
    ├── 有限呈现模 ←── 代数基础
    └── 有限呈现环同态 ←── 核心概念
            ↓
代数几何
    ├── 概形与态射
    ├── 有限型态射 ←── 对比学习
    └── 有限呈现态射 ←── Tag 01QY
```

---

## 6. 应用与重要性

### 6.1 理论重要性

**极限方法的核心：**

有限呈现态射最重要的理论价值在于其与**极限**（极限/余极限）的关系：

**定理：** 设 $S = \varprojlim S_\lambda$ 是概形的余极限（滤余极限），则：

$$\text{Mor}_S(X, Y) = \varinjlim \text{Mor}_{S_\lambda}(X_\lambda, Y_\lambda)$$

对有限呈现态射成立。

**为什么这很重要：**
1. **逼近原理**：复杂概形可被有限型概形逼近
2. **下降理论**：性质可从极限下降到有限层
3. ** constructible 集**：在代数闭域上的 constructible 性质

### 6.2 实际应用场景

#### 场景1：Noetherian情形的简化

**命题：** 若 $S$ 是局部Noetherian概形，则：

$$f \text{ 局部有限型} \Leftrightarrow f \text{ 局部有限呈现}$$

**原因：** 在Noetherian环上，有限生成自动蕴含有限关系。

#### 场景2：平坦下降

有限呈现态射在**平坦下降**中表现良好：

若 $S' \to S$ 是忠实平坦且拟紧，则许多关于 $f: X \to S$ 的问题可约化到基变换 $f': X' \to S'$。

#### 场景3：Hilbert概形构造

Hilbert概形 $Hilb_{P}(\mathbb{P}^n)$ 参数化 $\mathbb{P}^n$ 中具有固定Hilbert多项式 $P$ 的闭子概形，其存在性证明依赖于：
- 有限呈现条件
- 平坦性
- 极限方法

### 6.3 现代发展

- **代数空间的有限呈现**：扩展到代数空间范畴
- **导出代数几何**：在DAG框架下的类似概念
- **刚性解析几何**：在p进几何中的应用

---

## 7. 与其他资源关联

### 7.1 Stacks Project内部关联

| 相关Tag | 关系类型 | 说明 |
|--------|---------|------|
| **Tag 00EP** (有限呈现环同态) | 代数基础 | 定义的代数核心 |
| **Tag 01R1** (局部有限型态射) | 弱化版本 | 去掉"有限关系"条件 |
| **Tag 01KU** (拟紧态射) | 组合条件 | 有限呈现的定义组成部分 |
| **Tag 01KW** (拟分离态射) | 组合条件 | 有限呈现的定义组成部分 |
| **Tag 01QZ** (基变换稳定性) | 性质 | 有限呈现对基变换稳定 |
| **Tag 01R0** (复合稳定性) | 性质 | 有限呈现在复合下稳定 |
| **Tag 01ZB** (极限方法) | 应用 | 有限呈现的核心应用 |

### 7.2 外部参考资源

**经典教材：**

1. **EGA IV$_3$, §8** (Grothendieck)
   - 有限呈现态射的最权威论述
   - 极限方法的系统发展

2. **Hartshorne, Algebraic Geometry**
   - Exercise II.3.13: 有限型与有限呈现的区别
   - 主要在Noetherian情形下讨论

3. **Vakil, Foundations of Algebraic Geometry**
   - §10.3: 有限性条件
   - 以极限方法为重点的现代阐述

4. **Görtz-Wedhorn, Algebraic Geometry I**
   - Chapter 10: 有限性条件
   - 详细讨论了各种有限性层次

**专题文章：**

- **Thomason, Trobaugh**: K-理论中的极限方法
- **Conrad**: 非Noetherian情形的代数几何讲义

### 7.3 计算工具

| 工具 | 功能 | 示例 |
|------|------|------|
| **Macaulay2** | 计算有限呈现 | `presentation` 命令 |
| **SageMath** | 概形计算 | 有限性判断 |
| **Singular** | Gröbner基计算 | 理想生成元最小化 |

---

## 8. Lean4形式化展望

### 8.1 形式化难度评估

| 方面 | 难度 | 说明 |
|------|------|------|
| 概念复杂度 | ★★★☆☆ | 涉及环论、概形、范畴论 |
| 证明技术 | ★★★☆☆ | 主要是局部-整体论证 |
| 依赖链条 | ★★★★☆ | 需要完整的概形基础 |
| 预计工作量 | 中等 | 需要2-4个月 |

### 8.2 mathlib4现状

**当前已有基础：**
```
mathlib4
├── RingTheory
│   ├── FiniteType (有限型) ✅
│   └── FinitePresentation (有限呈现) ✅
│
└── AlgebraicGeometry
    ├── Scheme ✅
    ├── MorphismProperty 🔄 开发中
    └── QuasiCompact / QuasiSeparated 🔄 开发中
```

**已有的相关定义：**

```lean
-- 环的有限呈现同态
structure RingHom.FinitePresentation {R S : Type*} [CommRing R] [CommRing S] 
    (f : R →+* S) : Prop where
  -- 存在有限生成元和有限关系
  exists_finset : ∃ (s : Finset S), ...
  
-- 概形的拟紧性
def IsQuasiCompact {X Y : Scheme} (f : X ⟶ Y) : Prop := ...

-- 概形的拟分离性  
def IsQuasiSeparated {X Y : Scheme} (f : X ⟶ Y) : Prop := ...
```

### 8.3 形式化路线图

**阶段1：有限呈现态射的定义 (1个月)**

```lean
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.RingTheory.FinitePresentation

namespace AlgebraicGeometry

-- 局部有限呈现的定义
def LocallyOfFinitePresentationAt {X Y : Scheme} (f : X ⟶ Y) 
    (x : X) : Prop :=
  ∃ (U : Opens X) (V : Opens Y), 
    x ∈ U ∧ f '' U ⊆ V ∧ 
    IsAffineOpen U ∧ IsAffineOpen V ∧
    (f.app V).hom.FinitePresentation

-- 局部有限呈现态射
def LocallyOfFinitePresentation {X Y : Scheme} (f : X ⟶ Y) : Prop :=
  ∀ x : X, LocallyOfFinitePresentationAt f x

-- 有限呈现态射
def IsFinitePresentation {X Y : Scheme} (f : X ⟶ Y) : Prop :=
  LocallyOfFinitePresentation f ∧ IsQuasiCompact f ∧ IsQuasiSeparated f

end AlgebraicGeometry
```

**阶段2：基本性质证明 (1-2个月)**

```lean
-- 基变换稳定性
theorem finitePresentation_stable_under_base_change 
    {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [IsFinitePresentation f] :
    IsFinitePresentation (pullback.fst f g) := by
  sorry

-- 复合稳定性
theorem finitePresentation_stable_under_composition
    {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsFinitePresentation f] [IsFinitePresentation g] :
    IsFinitePresentation (f ≫ g) := by
  sorry

-- 对靶标局部
theorem finitePresentation_local_of_target
    {X Y : Scheme} (f : X ⟶ Y) (𝒰 : Y.OpenCover) :
    (∀ i, IsFinitePresentation (pullback.snd f (𝒰.map i))) →
    IsFinitePresentation f := by
  sorry
```

**阶段3：极限方法 (1-2个月)**

```lean
-- 极限逼近定理
theorem approximation_by_finite_presentation
    {S : Scheme} (hs : IsAffine S) 
    (X : Scheme) (f : X ⟶ S) [IsLocallyOfFiniteType f] :
    ∃ (S' : Scheme) (g : S' ⟶ S) (X' : Scheme) (f' : X' ⟶ S'),
      IsFinitePresentation g ∧ IsFinitePresentation f' ∧
      X ≅ pullback f g := by
  sorry
```

### 8.4 技术挑战与解决方案

| 挑战 | 解决方案 |
|------|---------|
| 局部性质的形式化 | 使用 `∀ x, ∃ U` 模式的谓词 |
| 仿射开集的选取 | 使用类型类推断 `IsAffineOpen` |
| 环同态的转换 | 利用 `f.app` 和伴随函子 |
| 拟分离性的证明 | 参考EGA或Vakil的构造 |

### 8.5 与其他形式化项目的联系

- **Lean-Stacks**: Stacks Project的形式化项目
- **mathlib4-AG**: mathlib4的代数几何扩展
- **ForMath**: 欧盟形式化数学项目

---

## 附录

### A. 符号速查表

| 符号/术语 | 含义 | 备注 |
|----------|------|------|
| 有限呈现 (finite presentation) | 有限生成 + 有限关系 | 比有限型强 |
| 拟紧 (quasi-compact) | 紧致性条件（无Hausdorff） | 任意开覆盖有有限子覆盖 |
| 拟分离 (quasi-separated) | 对角线拟紧 | 技术性条件 |
| 局部 (locally) | 每点处成立 | 局部性质 |
| $R \to A$ | 环同态 | $A$ 是 $R$-代数 |

### B. 有限性层次表

| 性质 | 代数条件 | 概形态射 | 重要性 |
|------|---------|---------|--------|
| 有限 (finite) | $A$ 是有限 $R$-模 | 仿射 + 整体有限 | ★★★★★ |
| 仿射 (affine) | $A$ 是 $R$-代数 | 原像仿射 | ★★★★☆ |
| 有限型 (finite type) | $A$ 有限生成 $R$-代数 | 局部有限型 + 拟紧 | ★★★★★ |
| 有限呈现 (finite presentation) | $A$ 有限呈现 $R$-代数 | 局部有限呈现 + 拟紧 + 拟分离 | ★★★★★ |
| 局部有限型 | 局部有限生成 | 每点仿射局部有限型 | ★★★★☆ |

---

*文档版本: 1.0*  
*创建日期: 2026年4月*  
*对应Stacks Project版本: 2024.02*
