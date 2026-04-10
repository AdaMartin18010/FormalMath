# Stacks Project Tag 00EB - 局部化（Localization）

## 1. Tag基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 00EB |
| **英文名称** | Localization |
| **中文名称** | 局部化 |
| **所属章节** | Chapter 10: Commutative Algebra (交换代数) |
| **数学领域** | 交换代数、环论 |
| **难度等级** | 本科高年级/研究生初级 |

### 1.1 位置信息

- **URL**: https://stacks.math.columbia.edu/tag/00EB
- **章节**: 10.9 Localization
- **前置Tags**: 00E0 (环), 00E1 (理想)

---

## 2. 定理/定义原文

### 2.1 乘闭子集的局部化

**定义 10.9.1 - 乘闭子集（Multiplicative Subset）**:

设 $R$ 是环，子集 $S \subseteq R$ 称为**乘闭的（multiplicative）**，如果：

1. $1 \in S$
2. 若 $a, b \in S$，则 $ab \in S$

**定义 10.9.2 - 局部化环**:

设 $R$ 是环，$S \subseteq R$ 是乘闭子集。$R$ 关于 $S$ 的**局部化（localization）**是一个环 $S^{-1}R$ 连同环同态 $R \to S^{-1}R$，满足：

1. **泛性质**: 对任意环 $A$ 和同态 $\phi: R \to A$，若 $\phi(s)$ 在 $A$ 中可逆对所有 $s \in S$，则存在唯一的同态 $S^{-1}R \to A$ 使得图表交换。

2. **显式构造**: $S^{-1}R$ 的元素是形式分数 $\frac{r}{s}$（其中 $r \in R, s \in S$），模等价关系：
   $$\frac{r}{s} = \frac{r'}{s'} \Leftrightarrow \exists t \in S: t(rs' - r's) = 0$$

### 2.2 特殊情形

**情形1: 素理想的局部化**

设 $\mathfrak{p} \subseteq R$ 是素理想，$S = R \setminus \mathfrak{p}$ 是乘闭的。记：
$$R_{\mathfrak{p}} = S^{-1}R$$

这是 $R$ 在 $\mathfrak{p}$ 处的**局部化**，是一个局部环，极大理想为 $\mathfrak{p}R_{\mathfrak{p}}$。

**情形2: 元素的局部化**

设 $f \in R$，$S = \{f^n \mid n \geq 0\}$。记：
$$R_f = S^{-1}R$$

这是 $R$ 关于 $f$ 的**局部化**，同构于 $R[x]/(xf - 1)$。

### 2.3 局部化的基本性质

**引理 10.9.3**:

1. $R \to S^{-1}R$ 是同态，$S$ 中元素映到单位
2. $\ker(R \to S^{-1}R) = \{r \in R \mid \exists s \in S: sr = 0\}$
3. 若 $R$ 是整环且 $0 \notin S$，则 $R \to S^{-1}R$ 是单射
4. 若 $S$ 包含所有非零因子，则 $S^{-1}R$ 是 $R$ 的全商环

**引理 10.9.4 - 理想的对应**:

局部化诱导 $R$ 中与 $S$ 不交的素理想和 $S^{-1}R$ 的素理想之间的一一对应：
$$\{\mathfrak{p} \subseteq R \mid \mathfrak{p} \cap S = \emptyset, \mathfrak{p} \text{ 素}\} \leftrightarrow \{\mathfrak{q} \subseteq S^{-1}R \mid \mathfrak{q} \text{ 素}\}$$

---

## 3. 概念依赖图

```
                    ┌─────────────────┐
                    │      环 R       │
                    └────────┬────────┘
                             │
              ┌──────────────┼──────────────┐
              ▼              ▼              ▼
       ┌────────────┐ ┌────────────┐ ┌────────────┐
       │  零因子    │ │  素理想    │ │ 乘闭子集 S │
       │            │ │    𝔭      │ │ 1∈S, ab∈S │
       └────────────┘ └─────┬──────┘ └─────┬──────┘
                            │              │
                            └──────────────┘
                                           │
                                           ▼
                    ┌───────────────────────┐
                    │     局部化环 S⁻¹R     │
                    │                       │
                    │  元素: r/s, r∈R, s∈S │
                    │  等价: t(rs'-r's)=0   │
                    └───────────┬───────────┘
                                │
              ┌─────────────────┼─────────────────┐
              ▼                 ▼                 ▼
       ┌────────────┐   ┌────────────┐   ┌────────────┐
       │  素理想𝔭   │   │  元素 f    │   │  全商环   │
       │  局部化    │   │  局部化    │   │            │
       │  R_𝔭      │   │  R_f      │   │  Frac(R)  │
       │ (局部环)  │   │ (仿射开)  │   │ (整环情形)│
       └─────┬──────┘   └─────┬──────┘   └─────┬──────┘
             │                │                │
             └────────────────┴────────────────┘
                                │
                                ▼
                    ┌───────────────────┐
                    │    局部化性质     │
                    │  • 理想对应      │
                    │  • 正合性        │
                    │  • 平坦性        │
                    └───────────────────┘
```

### 3.1 详细依赖链

```
抽象代数基础
    ├── 环的定义
    ├── 理想理论
    │       ├── 素理想
    │       ├── 极大理想
    │       └── 根理想
    └── 环同态
        ↓
局部化理论
    ├── 乘闭子集定义
    ├── 局部化环构造
    │       ├── 泛性质
    │       └── 显式构造
    ├── 特殊局部化
    │       ├── R_𝔭 (素理想局部化)
    │       ├── R_f (元素局部化)
    │       └── Frac(R) (分式域)
    └── 局部化性质 ◄── 本Tag核心
            ├── 理想对应
            ├── 正合性
            └── 平坦性
```

---

## 4. 证明概要

### 4.1 局部化环的存在性证明

**构造**:

1. **集合**: $\{(r, s) \mid r \in R, s \in S\}$

2. **等价关系**: $(r, s) \sim (r', s')$ 当且仅当存在 $t \in S$ 使得 $t(rs' - r's) = 0$

3. **验证等价关系**:
   - 自反性: 取 $t = 1$
   - 对称性: 显然
   - 传递性: 关键步骤
     - 设 $(r, s) \sim (r', s')$，$(r', s') \sim (r'', s'')$
     - 则 $t(rs' - r's) = 0$，$t'(r's'' - r''s') = 0$
     - 则 $t t' s' (r s'' - r'' s) = 0$
     - 由于 $t t' s' \in S$，得 $(r, s) \sim (r'', s'')$

4. **环结构**: 分数的加法和乘法
   - $\frac{r}{s} + \frac{r'}{s'} = \frac{rs' + r's}{ss'}$
   - $\frac{r}{s} \cdot \frac{r'}{s'} = \frac{rr'}{ss'}$

### 4.2 泛性质的证明

**定理**: 局部化 $R \to S^{-1}R$ 满足泛性质。

**证明**:

1. 给定 $\phi: R \to A$ 使得 $\phi(s)$ 可逆对所有 $s \in S$

2. **定义映射** $\psi: S^{-1}R \to A$:
   $$\psi\left(\frac{r}{s}\right) = \phi(r) \cdot \phi(s)^{-1}$$

3. **良定性**: 若 $\frac{r}{s} = \frac{r'}{s'}$，则 $t(rs' - r's) = 0$
   - 故 $\phi(t)(\phi(r)\phi(s') - \phi(r')\phi(s)) = 0$
   - 由于 $\phi(t)$ 可逆，得 $\phi(r)\phi(s)^{-1} = \phi(r')\phi(s')^{-1}$

4. **同态性质**: 直接验证

5. **唯一性**: 由定义唯一确定

### 4.3 理想对应定理证明

**引理 10.9.4 的证明**:

1. **映射构造**:
   - 对 $R$ 的理想 $I$，定义 $S^{-1}I = \{\frac{a}{s} \mid a \in I, s \in S\}$
   - 对 $S^{-1}R$ 的理想 $J$，定义 $I = \phi^{-1}(J)$

2. **素理想对应**:
   - 若 $\mathfrak{p} \subseteq R$ 素且 $\mathfrak{p} \cap S = \emptyset$
   - 则 $S^{-1}\mathfrak{p}$ 是 $S^{-1}R$ 的素理想
   - 反之亦然

---

## 5. 与FormalMath对应

### 5.1 对应概念映射

| Stacks Project | FormalMath对应 | 文件路径 |
|----------------|----------------|----------|
| 环 | 环 | `concept/抽象代数/环.md` |
| 素理想 | 素理想 | `concept/交换代数/素理想.md` |
| 乘闭子集 | 乘闭子集 | `concept/交换代数/局部化.md` |
| 局部化环 | 局部化 | `concept/交换代数/局部化.md` |
| 局部环 | 局部环 | `concept/交换代数/局部环.md` |
| 分式域 | 分式域 | `concept/抽象代数/域.md` |

### 5.2 Lean4形式化

```lean4
-- 局部化的Lean4形式化（已存在于Mathlib4）
import Mathlib.RingTheory.Localization.Basic

-- 乘闭子集
variable {R : Type*} [CommRing R] (S : Submonoid R)

-- 局部化环
def Localization := Localization S

-- 局部化映射
def Localization.of : R →+* Localization S :=
  algebraMap R (Localization S)

-- 泛性质
def Localization.lift {A : Type*} [CommRing A] (g : R →+* A)
    (hg : ∀ s ∈ S, IsUnit (g s)) : Localization S →+* A :=
  IsLocalization.lift hg

-- 素理想局部化
def Localization.AtPrime {R : Type*} [CommRing R] (P : Ideal R) [P.IsPrime] :
    Type _ :=
  Localization (Ideal.primeCompl P)
```

### 5.3 在知识体系中的位置

```
代数学/交换代数
    ├── 环论基础
    │       ├── 环的定义
    │       ├── 理想理论
    │       └── 商环
    ├── 交换代数核心
    │       ├── 局部化 ◄── 本Tag
    │       │       ├── 乘闭子集
    │       │       ├── 局部化环
    │       │       └── 性质与应用
    │       ├── Noether环
    │       └── 整扩张
    └── 代数几何基础
            ├── 仿射概形
            ├── 层的局部化
            └── 茎（stalk）
```

---

## 6. 应用与重要性

### 6.1 核心应用

1. **交换代数**
   - 局部性质的研究
   - 支集与维数理论
   - 相伴素理想

2. **代数几何**
   - 概形的局部结构
   - 结构层的茎
   - 有理函数域

3. **代数数论**
   - p-进数构造
   - 赋值理论
   - Dedekind整环

### 6.2 具体应用实例

| 应用领域 | 具体应用 |
|----------|----------|
| **概形理论** | $\text{Spec}(R_f) = D(f) \subseteq \text{Spec}(R)$ |
| **层论** | 结构层 $\mathcal{O}_{\text{Spec}(R), \mathfrak{p}} = R_{\mathfrak{p}}$ |
| **有理映射** | 分式域 $\text{Frac}(R)$ 是有理函数域 |
| **维数理论** | $\dim(R_{\mathfrak{p}}) = \text{ht}(\mathfrak{p})$ |

### 6.3 历史背景

- **E. Noether**: 抽象代数的奠基人
- **W. Krull**: 局部环理论的系统发展
- **C. Chevalley**: 局部化在代数几何中的应用

### 6.4 现代发展

- **导出局部化**: 三角范畴的局部化
- **非交换局部化**: 非交换环的局部化理论
- **高维代数**: ∞-范畴中的局部化

---

## 7. 与其他资源关联

### 7.1 Stacks Project内部关联

| 相关Tag | 名称 | 关系 |
|---------|------|------|
| 00EC | 模的局部化 | 直接推广 |
| 00E0 | 环 | 基础概念 |
| 01HS | 概形 | 几何应用 |
| 01I5 | 结构层 | 层论应用 |
| 00H7 | 平坦性 | 局部化性质 |

### 7.2 外部资源

**教科书**:

- Atiyah-Macdonald: "Introduction to Commutative Algebra" (第三章)
- Eisenbud: "Commutative Algebra" (第二章)
- Matsumura: "Commutative Ring Theory" (第四章)

**在线资源**:

- Keith Conrad: "Expository papers on localization"
- nLab: https://ncatlab.org/nlab/show/localization+of+a+ring

**课程讲义**:

- Harvard Math 221: Commutative Algebra
- MIT 18.705: Commutative Algebra

### 7.3 相关计算工具

- **SageMath**: 环的局部化计算
- **Macaulay2**: 交换代数计算
- **Singular**: Gröbner基与局部化

---

## 8. Lean4形式化展望

### 8.1 当前形式化状态

```
Mathlib4状态:
✅ 环与理想理论
✅ 局部化基础 (IsLocalization)
✅ 素理想局部化
✅ 元素局部化
✅ 局部化性质
```

Mathlib4已经有非常完整的局部化理论！

### 8.2 Mathlib4中的关键定义

```lean4
-- 局部化的泛性质
class IsLocalization (S : Submonoid R) (Q : Type*) [CommSemiring Q]
    [Algebra R Q] : Prop where
  inverts : ∀ s ∈ S, IsUnit (algebraMap R Q s)
  surj : ∀ q : Q, ∃ r s, q = algebraMap R Q r *
    (IsUnit.liftRight (inverts s.2) s).unit⁻¹.val
  exists_of_eq : ∀ r₁ r₂, algebraMap R Q r₁ = algebraMap R Q r₂ →
    ∃ s ∈ S, s * r₁ = s * r₂

-- 局部化环的构造
def Localization := OreLocalization (S := S) (R := R) (· * ·)
```

### 8.3 进一步形式化方向

虽然基础局部化理论已经很完善，仍有扩展空间：

1. **非交换局部化**: Ore条件与局部化
2. **导出局部化**: 三角范畴的局部化
3. **高维局部化**: ∞-范畴版本

---

## 附录: 关键公式速查

| 概念 | 公式/定义 |
|------|-----------|
| **乘闭子集** | $1 \in S$，$a,b \in S \Rightarrow ab \in S$ |
| **局部化** | $S^{-1}R = \{r/s \mid r \in R, s \in S\}/\sim$ |
| **等价关系** | $\frac{r}{s} = \frac{r'}{s'} \Leftrightarrow \exists t \in S: t(rs' - r's) = 0$ |
| **素理想局部化** | $R_{\mathfrak{p}} = (R \setminus \mathfrak{p})^{-1}R$ |
| **元素局部化** | $R_f = \{f^n \mid n \geq 0\}^{-1}R$ |
| **分式域** | $\text{Frac}(R) = (R \setminus \{0\})^{-1}R$（整环情形） |

---

**文档版本**: 1.0
**创建日期**: 2026-04-10
**最后更新**: 2026-04-10
**作者**: FormalMath Knowledge System
