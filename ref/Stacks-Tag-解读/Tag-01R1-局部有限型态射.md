# Stacks Tag 01R1 - 局部有限型态射

## 1. Tag基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 01R1 |
| **概念名称** | 局部有限型态射 (Morphisms Locally of Finite Type) |
| **所属章节** | Chapter 29: Morphisms of Schemes, Section 29.15 |
| **概念类型** | 定义 (Definition) |
| ** Stacks原文** | Definition 29.15.1 |

---

## 2. 定义原文

**定义陈述：**

设 $f: X \to S$ 是概形的态射。

1. 称 $f$ 在点 $x \in X$ 是**局部有限型**的（locally of finite type），如果存在 $x$ 的一个仿射开邻域 $\text{Spec}(A) = U \subset X$ 和 $f(x)$ 的一个仿射开邻域 $\text{Spec}(R) = V \subset S$，使得 $f(U) \subset V$ 且诱导的环同态 $R \to A$ 是有限型的。

2. 称 $f$ 是**局部有限型**的，如果它在每个点 $x \in X$ 都是局部有限型的。

3. 称 $f$ 是**有限型**的，如果它是局部有限型且拟紧的。

**英文原文：**
> Let $f : X \to S$ be a morphism of schemes.
> 
> 1. We say that $f$ is *locally of finite type at $x$* if there exists an affine open neighbourhood $\mathop{\mathrm{Spec}}(A) = U \subset X$ of $x$ and an affine open $\mathop{\mathrm{Spec}}(R) = V \subset S$ with $f(U) \subset V$ such that the induced ring map $R \to A$ is of finite type.
> 
> 2. We say that $f$ is *locally of finite type* if it is locally of finite type at every point of $X$.
> 
> 3. We say that $f$ is *of finite type* if it is locally of finite type and quasi-compact.

---

## 3. 概念依赖图

```
Tag 01R1: 局部有限型态射
│
├── 前置概念
│   ├── 概形 (Scheme) [Tag 006V]
│   ├── 概形态射 [Tag 01Q2]
│   ├── 仿射开集 [Tag 006W]
│   ├── 有限型环同态 [Tag 00EV]
│   ├── 拟紧态射 [Tag 01KU]
│   └── 局部性质 [Tag 0062]
│
├── 等价刻画
│   ├── 局部：仿射局部有限型
│   ├── 整体：有限型 = 局部有限型 + 拟紧
│   └── 判别准则：对角线性质等
│
├── 重要性质
│   ├── 对基变换稳定 [Tag 01R2]
│   ├── 对复合稳定 [Tag 01R3]
│   ├── 对靶标局部 [Tag 01R4]
│   └── 有限性层次的核心
│
└── 后续应用
    ├── 有限呈现态射 [Tag 01QY]
    ├── 光滑态射 [Tag 01V5]
    ├── 态射的维数理论 [Tag 02FS]
    └── 有限性判定
```

---

## 4. 证明概要（基本性质）

### 4.1 定义的良定性

**引理：** 局部有限型的定义不依赖于仿射开集的选取。

**证明：**

设 $x \in U \cap U'$，其中 $U = \text{Spec}(A)$，$U' = \text{Spec}(A')$ 都是 $x$ 的仿射开邻域，且都映射到 $V = \text{Spec}(R) \subset S$。

**步骤1：** 取基本开覆盖

$U \cap U'$ 可表示为：
$$U \cap U' = \bigcup_{i=1}^n D(f_i) = \bigcup_{j=1}^m D(g_j)$$

其中 $f_i \in A$，$g_j \in A'$。

**步骤2：** 利用局部化的性质

若 $R \to A$ 有限型，则对任意 $f \in A$，$R \to A_f$ 也是有限型。

**步骤3：** 验证相容性

若 $R \to A$ 有限型，则 $R \to A'$ 在交 $U \cap U'$ 上诱导的环同态也是有限型。

### 4.2 局部有限型与整体有限型

**命题：** $f: X \to S$ 是有限型的当且仅当：
1. 它是局部有限型的
2. 它是拟紧的

**证明要点：**

- **$(\Rightarrow)$** 显然：有限型定义要求这两个条件
- **$(\Leftarrow)$** 由拟紧性，$X$ 可被有限个仿射开集 $U_i = \text{Spec}(A_i)$ 覆盖，每个 $A_i$ 在对应的 $R_i$ 上有限型

### 4.3 纤维的有限型性

**命题：** 若 $f: X \to S$ 是局部有限型的，则对任意 $s \in S$，纤维 $X_s$ 是域 $k(s)$ 上的局部有限型概形。

**证明：**

纤维 $X_s = X \times_S \text{Spec}(k(s))$ 的构造保持有限型性：

若 $R \to A$ 有限型，则对任意素理想 $\mathfrak{p} \subset R$，$k(\mathfrak{p}) \to A \otimes_R k(\mathfrak{p})$ 也是有限型。

---

## 5. 与FormalMath对应

### 5.1 概念映射

| Stacks Project概念 | FormalMath对应内容 | 文件路径 |
|-------------------|-------------------|----------|
| 有限型环同态 | RingHom.FiniteType | `concept/交换代数/有限型.md` |
| 局部有限型态射 | LocallyOfFiniteType | `concept/代数几何/态射性质.md` |
| 有限型态射 | OfFiniteType | `concept/代数几何/态射性质.md` |
| 拟紧态射 | QuasiCompact | `concept/代数几何/拟紧态射.md` |
| 纤维 | Scheme.fiber | `concept/代数几何/纤维.md` |

### 5.2 知识体系位置

```
FormalMath知识体系
├── 交换代数
│   └── 环同态的有限性
│       ├── 整环同态 (Integral) ←── 最强
│       ├── 有限同态 (Finite)
│       ├── 有限呈现 (Finite Presentation)
│       └── 有限型 (Finite Type) ←── Tag 01R1
│
└── 代数几何
    └── 概形态射
        ├── 有限性条件
        │   ├── 有限型 ←── 最常用
        │   └── 有限呈现 ←── Noetherian情形等价
        └── 光滑性/平展性
```

### 5.3 学习路径建议

```
学习路径：
环同态基础
    ├── 有限生成代数 ←── 代数基础
    └── 有限型环同态 ←── 核心概念
            ↓
概形
    ├── 态射基本性质
    ├── 局部有限型 ←── Tag 01R1
    └── 有限型 ←── 常用整体条件
```

---

## 6. 应用与重要性

### 6.1 理论重要性

**最基础的有限性条件：**

局部有限型（和有限型）是概形态射的**最基础、最常用**的有限性条件。几乎所有"好"的态射都满足这个条件。

**重要性体现：**
1. **Chevalley定理**：有限型态射的像是 constructible 的
2. **半连续性定理**：纤维维数的半连续性
3. **Hilbert零点定理的推广**：在概形上的形式

### 6.2 实际应用场景

#### 场景1：经典代数簇

所有经典代数簇（affine varieties, projective varieties）到基域的态射都是有限型的。

**例：**
- 仿射空间 $\mathbb{A}^n_k \to \text{Spec}(k)$ 是有限型的
- 射影空间 $\mathbb{P}^n_k \to \text{Spec}(k)$ 是有限型的
- 任何拟射影簇 $X \to \text{Spec}(k)$ 是有限型的

#### 场景2：维数理论

有限型态射允许定义**相对维数**：

**定义：** 设 $f: X \to S$ 是局部有限型的，$x \in X$，$s = f(x)$。$f$ 在 $x$ 处的相对维数定义为：
$$\dim_x f = \dim_x(X_s) + \text{tr.deg}(k(x)/k(s))$$

#### 场景3：Noetherian性质传递

**命题：** 若 $S$ 是局部Noetherian的，$f: X \to S$ 是局部有限型的，则 $X$ 也是局部Noetherian的。

这在实际计算中极其重要——可以将Noetherian性质从基传递到总空间。

### 6.3 与其他性质的关系

**有限性层次的包含关系：**

$$
\begin{array}{ccccc}
\text{有限} & \Rightarrow & \text{仿射} & \Rightarrow & \\
& & \Downarrow & & \\
\text{拟有限} & & \text{有限型} & & \text{局部有限型} \\
& & \Uparrow & & \\
\text{有限呈现} & \Rightarrow & & &
\end{array}
$$

**光滑态射的层次：**

光滑态射 $\Rightarrow$ 局部有限型 + 平坦 + 相对维数局部常数

### 6.4 现代发展

- **fppf/étale拓扑**：在平坦拓扑下研究有限型态射
- **代数空间**：扩展到代数空间范畴
- **Artin逼近**：有限型态射的逼近理论

---

## 7. 与其他资源关联

### 7.1 Stacks Project内部关联

| 相关Tag | 关系类型 | 说明 |
|--------|---------|------|
| **Tag 00EV** (有限型环同态) | 代数基础 | 定义的代数核心 |
| **Tag 01QY** (有限呈现) | 强化版本 | 加"有限关系"条件 |
| **Tag 01KU** (拟紧) | 组合条件 | 从局部到整体的关键 |
| **Tag 01V5** (光滑态射) | 应用 | 光滑 = 有限型 + 平坦 + ... |
| **Tag 02FS** (维数理论) | 应用 | 相对维数定义需要有限型 |
| **Tag 01ZB** (Chevalley定理) | 应用 | 有限型态射的像是constructible |

### 7.2 外部参考资源

**经典教材：**

1. **Hartshorne, Algebraic Geometry**
   - Chapter II, §3: 概形态射的基本性质
   - 重点讨论有限型态射

2. **Vakil, Foundations of Algebraic Geometry**
   - §7.3: 态射的有限性条件
   - 现代、详细、丰富的例子

3. **Görtz-Wedhorn, Algebraic Geometry I**
   - Chapter 4: 概形的基本性质
   - 系统性论述各种有限性条件

4. **Liu, Algebraic Geometry and Arithmetic Curves**
   - Chapter 3: 态射
   - 算术几何视角

**在线资源：**
- [Stacks Project 第29章](https://stacks.math.columbia.edu/tag/01R1)
- [nLab: finite type](https://ncatlab.org/nlab/show/finite+type)

---

## 8. Lean4形式化展望

### 8.1 形式化难度评估

| 方面 | 难度 | 说明 |
|------|------|------|
| 概念复杂度 | ★★★☆☆ | 概念清晰，依赖适度 |
| 证明技术 | ★★☆☆☆ | 主要是验证性证明 |
| 依赖链条 | ★★★☆☆ | 需要概形和环论基础 |
| 预计工作量 | 中等 | 需要1-2个月 |

### 8.2 mathlib4现状

**当前已有基础：**
```
mathlib4
├── RingTheory
│   └── FiniteType (有限型) ✅
│
└── AlgebraicGeometry
    ├── Scheme ✅
    ├── QuasiCompact ✅
    └── MorphismProperty 🔄 开发中
```

### 8.3 形式化路线图

**阶段1：基本定义 (2周)**

```lean
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.RingTheory.FiniteType

namespace AlgebraicGeometry

-- 局部有限型的定义
def LocallyOfFiniteTypeAt {X Y : Scheme} (f : X ⟶ Y) (x : X) : Prop :=
  ∃ (U : Opens X) (V : Opens Y),
    x ∈ U ∧ f '' U ⊆ V ∧ 
    IsAffineOpen U ∧ IsAffineOpen V ∧
    (f.app V).hom.FiniteType

-- 局部有限型态射
def LocallyOfFiniteType {X Y : Scheme} (f : X ⟶ Y) : Prop :=
  ∀ x : X, LocallyOfFiniteTypeAt f x

-- 有限型态射
def IsFiniteType {X Y : Scheme} (f : X ⟶ Y) : Prop :=
  LocallyOfFiniteType f ∧ IsQuasiCompact f

end AlgebraicGeometry
```

**阶段2：基本性质 (3-4周)**

```lean
-- 基变换稳定性
theorem finiteType_stable_under_base_change 
    {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [IsFiniteType f] :
    IsFiniteType (pullback.fst f g) := by
  sorry

-- 复合稳定性
theorem finiteType_stable_under_composition
    {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsFiniteType f] [IsFiniteType g] :
    IsFiniteType (f ≫ g) := by
  sorry

-- 纤维的有限型性
theorem finiteType_fiber {X Y : Scheme} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (y : Y) : 
    LocallyOfFiniteType (fiber f y) := by
  sorry
```

**阶段3：Chevalley定理 (4-6周)**

```lean
-- constructible集
def IsConstructible {X : Scheme} (S : Set X) : Prop := ...

-- Chevalley定理
theorem chevalley_theorem {X Y : Scheme} (f : X ⟶ Y) [IsFiniteType f] :
    ∀ (U : Opens X), IsConstructible (f '' U) := by
  sorry
```

### 8.4 技术挑战

| 挑战 | 解决方案 |
|------|---------|
| 局部性质的统一处理 | 使用 `MorphismProperty` 类型类 |
| 纤维的定义 | 使用纤维积的构造 |
| constructible集 | 先定义局部闭集，再定义constructible |

### 8.5 测试示例

```lean
-- 仿射空间是有限型的
example : IsFiniteType (Scheme.Spec (Polynomial (Fin n) k) ⟶ Spec k) := by
  sorry

-- 射影空间是有限型的
example : IsFiniteType (projectiveSpace n k ⟶ Spec k) := by
  sorry
```

---

## 附录

### A. 符号速查表

| 符号/术语 | 含义 | 英文 |
|----------|------|------|
| 有限型 | 有限生成代数 | of finite type |
| 拟紧 | 任意开覆盖有有限子覆盖 | quasi-compact |
| 纤维 | $X \times_S \text{Spec}(k(s))$ | fiber |
| constructible | 有限个局部闭集的并 | constructible |

### B. 有限性条件对比表

| 性质 | 环同态条件 | 概形条件 | Noetherian情形 |
|------|----------|---------|---------------|
| 有限 | 有限模 | 仿射 + 整体有限 | 自动有限型 |
| 有限型 | 有限生成代数 | 局部有限型 + 拟紧 | 最常用 |
| 有限呈现 | 有限生成 + 有限关系 | 有限型 + 拟分离 | = 有限型 |
| 局部有限型 | 局部有限生成 | 每点处 | Noetherian传递 |

---

*文档版本: 1.0*  
*创建日期: 2026年4月*  
*对应Stacks Project版本: 2024.02*
