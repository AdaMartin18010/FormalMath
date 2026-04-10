# Stacks Project Tag 00EB - 局部化

## 1. Tag基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 00EB |
| **定义名称** | 局部化 (Localization) |
| **所属章节** | Section 10.9 - Localization (Commutative Algebra) |
| **数学领域** | 交换代数、环论 |
| **Stacks Project链接** | https://stacks.math.columbia.edu/tag/00EB |

## 2. 定理/定义原文

**定义 (Tag 00EB):**

设 $R$ 是环（交换幺环），$S \subseteq R$ 是**乘性子集**，即满足：
- $1 \in S$
- $s, t \in S \implies st \in S$

则 $R$ 关于 $S$ 的**局部化** $S^{-1}R$ 定义为：

$$S^{-1}R = \{(r, s) \mid r \in R, s \in S\} / \sim$$

其中等价关系 $\sim$ 定义为：
$$(r, s) \sim (r', s') \iff \exists t \in S : t(rs' - r's) = 0$$

记 $r/s$ 为 $(r, s)$ 的等价类，则 $S^{-1}R$ 构成环，运算为：
- 加法: $\frac{r}{s} + \frac{r'}{s'} = \frac{rs' + r's}{ss'}$
- 乘法: $\frac{r}{s} \cdot \frac{r'}{s'} = \frac{rr'}{ss'}$

**典范映射:**

$$\phi: R \longrightarrow S^{-1}R, \quad r \mapsto \frac{r}{1}$$

**万有性质:**

对任意环同态 $\psi: R \to A$，若 $\psi(S) \subseteq A^\times$（$\psi$ 将 $S$ 中元素映为单位），则存在唯一的 $\bar{\psi}: S^{-1}R \to A$ 使得 $\psi = \bar{\psi} \circ \phi$。

## 3. 概念依赖图

```
局部化 (Tag 00EB)
│
├── 核心前置概念
│   ├── 交换环 (Tag 00DT)
│   ├── 乘性子集 (Tag 00E9)
│   ├── 单位群 (Tag 00DX)
│   └── 环同态 (Tag 00E2)
│
├── 特殊局部化
│   ├── 素理想的局部化 (Tag 00E7)
│   ├── 元素的局部化 R_f (Tag 00E6)
│   ├── 全商环 (Tag 02C5)
│   └── 分式域 (Tag 00EW)
│
├── 范畴论视角
│   ├── 泛性质/万有性质 (Tag 0049)
│   └── 始对象 (Tag 002I)
│
└── 后继应用
    ├── 模的局部化 (Tag 00EC)
    ├── 局部环 (Tag 07BH)
    ├── 仿射概形 (Tag 01H8)
    └── 层论/茎 (Tag 007L)
```

## 4. 证明概要

**验证 $S^{-1}R$ 是环:**

**Step 1: 验证等价关系**
- **自反性:** $(r,s) \sim (r,s)$，取 $t=1$
- **对称性:** 若 $t(rs'-r's)=0$，则 $t(r's-rs')=0$
- **传递性:** 若 $t(rs'-r's)=0$ 且 $t'(r's''-r''s')=0$，则
  $$tt's''(rs''-r''s) = t's'' \cdot t(rs'-r's) + ts \cdot t'(r's''-r''s') = 0$$

**Step 2: 验证运算良定性**
- 若 $\frac{r}{s} = \frac{r_1}{s_1}$，$\frac{r'}{s'} = \frac{r'_1}{s'_1}$
- 需验证 $\frac{rs'+r's}{ss'} = \frac{r_1s'_1+r'_1s_1}{s_1s'_1}$
- 利用 $t(rs_1-r_1s)=0$ 和 $t'(r's'_1-r'_1s')=0$ 推导

**Step 3: 验证环公理**
- 结合律、交换律、分配律由 $R$ 继承
- 零元: $0/1$，单位元: $1/1$
- 加法逆元: $-\frac{r}{s} = \frac{-r}{s}$

**万有性质的证明:**

**存在性:** 定义 $\bar{\psi}(r/s) = \psi(r)\psi(s)^{-1}$
- 良定性: 若 $t(rs'-r's)=0$，则 $\psi(t)(\psi(r)\psi(s')-\psi(r')\psi(s))=0$
- 由于 $\psi(t)$ 可逆，得 $\psi(r)\psi(s)^{-1} = \psi(r')\psi(s')^{-1}$

**唯一性:** 由 $\bar{\psi}(r/1) = \psi(r)$ 和 $\bar{\psi}(1/s) = \psi(s)^{-1}$ 确定

## 5. 与FormalMath对应

| Stacks Project概念 | FormalMath对应内容 | 文档路径 |
|-------------------|-------------------|----------|
| 环的局部化 | 交换代数/局部化 | `concept/commutative_algebra/localization.md` |
| 乘性子集 | 交换代数/乘性子集 | `concept/commutative_algebra/multiplicative_set.md` |
| 分式域 | 域论/分式域 | `concept/field_theory/field_of_fractions.md` |
| 局部环 | 交换代数/局部环 | `concept/commutative_algebra/local_ring.md` |

**当前对齐状态:**
- 🟢 **良好对齐** - 局部化是交换代数的基础内容，FormalMath有完整覆盖

**建议补充内容:**
```markdown
## 局部化详解

### 定义
设 $R$ 交换环，$S$ 乘性子集，$S^{-1}R$ 是 $R$ 关于 $S$ 的局部化：
$$S^{-1}R = \{r/s : r \in R, s \in S\}/\sim$$
其中 $r/s \sim r'/s' \Leftrightarrow \exists t \in S: t(rs'-r's)=0$

### 万有性质
$$
\xymatrix{
R \ar[r]^\phi \ar[dr]_\psi & S^{-1}R \ar@{-->}[d]^{\exists! \bar{\psi}} \\
& A
}
$$
若 $\psi(S) \subseteq A^\times$，则存在唯一的 $\bar{\psi}$ 使图交换。

### 重要例子
1. **整环的分式域:** $S = R \setminus \{0\}$
2. **素理想的局部化:** $S = R \setminus \mathfrak{p}$
3. **元素局部化:** $S = \{f^n : n \geq 0\}$

### 性质
- $\phi: R \to S^{-1}R$ 是同态
- $S^{-1}R$ 中 $S$ 的元素成为单位
- $\ker\phi = \{r : \exists s \in S, sr = 0\}$
```

## 6. 应用与重要性

**核心应用场景:**

### 1. 局部环的构造
- 对素理想 $\mathfrak{p}$，$R_{\mathfrak{p}}$ 是局部环
- 唯一极大理想: $\mathfrak{p}R_{\mathfrak{p}}$
- 是代数几何中"在点处局部化"的基础

### 2. 分式域
- 整环 $R$ 的局部化 $S^{-1}R$（$S = R \setminus \{0\}$）是域
- 称为 $R$ 的分式域 $\text{Frac}(R)$

### 3. 代数几何
- **仿射概形:** $\text{Spec}(S^{-1}R) \cong D(S) \subseteq \text{Spec}(R)$
- **层论:** 结构层的茎是局部化: $\mathcal{O}_{X,x} = \mathcal{O}_X(U)_{\mathfrak{m}_x}$

### 4. 模的局部化 (Tag 00EC)
- 构造 $S^{-1}M = S^{-1}R \otimes_R M$
- 正合性: $S^{-1}(-)$ 是正合函子

### 5. 平坦性
- $S^{-1}R$ 是平坦 $R$-模
- 局部化是正合函子，保持正合列

**重要性评级:** ⭐⭐⭐⭐⭐ (5/5)

局部化是交换代数中最基本、最常用构造之一，是连接整体与局部性质的桥梁。

## 7. 与其他资源关联

### Stacks Project内部关联
| 相关Tag | 关联描述 |
|---------|----------|
| Tag 00EC | 模的局部化 |
| Tag 00E6 | 元素局部化 $R_f$ |
| Tag 00E7 | 素理想的局部化 |
| Tag 07BH | 局部环 |
| Tag 02C5 | 全商环 |
| Tag 00EW | 分式域 |

### 外部资源

**经典教材:**
1. **Atiyah & Macdonald** "Introduction to Commutative Algebra"
   - 第3章: Rings and Modules of Fractions
   - 最经典的处理

2. **Matsumura, H.** "Commutative Ring Theory"
   - §4: 局部化的深入讨论

3. **Eisenbud, D.** "Commutative Algebra with a View Toward Algebraic Geometry"
   - 第2章: Localization

**现代教材:**
- **Dummit & Foote** "Abstract Algebra"
- **Lang, S.** "Algebra"
- **Reid, M.** "Undergraduate Commutative Algebra"

### 相关概念
- **Ore condition**: 非交换局部化的条件
- **Saturation**: 乘性子集的饱和化
- **Total quotient ring**: 零因子情形的一般化

## 8. Lean4形式化展望

### 形式化难度评估: ⭐⭐☆☆☆ (2/5)

**主要挑战:**
1. **等价关系的验证** - 需仔细处理零因子情形
2. **运算良定性** - 分数运算的良好定义性
3. **万有性质** - 范畴论层面的泛性质

**Lean4实现路线:**

```lean4
-- Mathlib已有完整实现！
import Mathlib

-- 乘性子集
variable {R : Type*} [CommRing R]

-- 局部化已在Mathlib中完整形式化
#check Localization  -- 局部化类型构造子
#check IsLocalization  -- 局部化的类型类

-- 使用示例
def example_localization (S : Submonoid R) :=
  Localization S

-- 万有性质 (Mathlib中)
#check IsLocalization.lift
-- 若 $f: R \to A$ 将 $S$ 映为单位，则存在唯一的 $\bar{f}: S^{-1}R \to A$

-- 分式域 (整环情形)
def FractionRing (R : Type*) [CommRing R] [IsDomain R] :=
  FractionRing R

-- 素理想的局部化
example (P : Ideal R) [P.IsPrime] :
    IsLocalRing (Localization (Ideal.primeCompl P)) := by
  infer_instance  -- 自动证明
```

**Mathlib现状:**
- `Localization` 类型构造子已完整实现
- `IsLocalization` 类型类封装了局部化的特征性质
- 分式域 `FractionRing` 已有定义
- 局部环、素理想局部化等推论都已形式化

**形式化优先级:** COMPLETED ✅
- Mathlib已有完整的局部化理论
- 可直接使用现有API
- 建议关注更高层的应用（如层论中的茎）

---

**文档编制日期:** 2026年4月  
**作者:** FormalMath项目团队  
**版本:** 1.0
