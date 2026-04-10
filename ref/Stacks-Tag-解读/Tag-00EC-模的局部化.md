# Stacks Project Tag 00EC - 模的局部化

## 1. Tag基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 00EC |
| **定义名称** | 模的局部化 (Localization of Modules) |
| **所属章节** | Section 10.9 - Localization (Commutative Algebra) |
| **数学领域** | 交换代数、同调代数、模论 |
| **Stacks Project链接** | https://stacks.math.columbia.edu/tag/00EC |

## 2. 定理/定义原文

**定义 (Tag 00EC):**

设 $R$ 是环，$S \subseteq R$ 是乘性子集，$M$ 是 $R$-模。则 $M$ 关于 $S$ 的**局部化** $S^{-1}M$ 定义为：

$$S^{-1}M = \{(m, s) \mid m \in M, s \in S\} / \sim$$

其中等价关系 $\sim$ 定义为：
$$(m, s) \sim (m', s') \iff \exists t \in S : t(s'm - sm') = 0$$

记 $m/s$ 为 $(m, s)$ 的等价类，则 $S^{-1}M$ 构成 $S^{-1}R$-模，运算为：
- 加法: $\frac{m}{s} + \frac{m'}{s'} = \frac{s'm + sm'}{ss'}$
- 数乘: $\frac{r}{s} \cdot \frac{m}{s'} = \frac{rm}{ss'}$

**等价构造:**

$$S^{-1}M \;\cong\; S^{-1}R \otimes_R M$$

**典范映射:**

$$\phi_M: M \longrightarrow S^{-1}M, \quad m \mapsto \frac{m}{1}$$

**万有性质:**

对任意 $S^{-1}R$-模 $N$ 和 $R$-线性映射 $f: M \to N$，存在唯一的 $S^{-1}R$-线性映射 $\bar{f}: S^{-1}M \to N$ 使得 $f = \bar{f} \circ \phi_M$。

## 3. 概念依赖图

```
模的局部化 (Tag 00EC)
│
├── 核心前置概念
│   ├── 环的局部化 (Tag 00EB)
│   ├── 乘性子集 (Tag 00E9)
│   ├── R-模 (Tag 00DZ)
│   └── 张量积 (Tag 00DD)
│
├── 函子性质
│   ├── 正合函子 (Tag 00HD)
│   ├── 张量积函子 (Tag 00N1)
│   └── 伴随函子 (Tag 003L)
│
├── 特殊局部化
│   ├── 素理想的局部化 M_p (Tag 00E7)
│   ├── 元素局部化 M_f (Tag 00E6)
│   └── 茎 M_x (层论)
│
└── 后继应用
    ├── 局部性质 (Tag 00EU)
    ├── 平坦性 (Tag 00MB)
    ├── 支撑集 (Tag 00L2)
    └── 拟凝聚层 (Tag 01LA)
```

## 4. 证明概要

**验证 $S^{-1}M$ 是 $S^{-1}R$-模:**

**Step 1: 等价关系的验证**
- 与环的局部化类似，利用 $S$ 的乘性封闭性

**Step 2: 运算良定性**
- 加法良定: 若 $m/s = m_1/s_1$，$m'/s' = m'_1/s'_1$
- 需验证 $(s'm + sm')/(ss') = (s'_1m_1 + s_1m'_1)/(s_1s'_1)$
- 利用 $t(sm_1 - s_1m) = 0$ 和 $t'(s'm'_1 - s'_1m') = 0$

**Step 3: 模公理验证**
- $(S^{-1}M, +)$ 是Abel群
- $S^{-1}R$ 的作用满足模公理

**张量积同构的证明:**

**构造映射:**
$$\Phi: S^{-1}M \to S^{-1}R \otimes_R M, \quad \frac{m}{s} \mapsto \frac{1}{s} \otimes m$$

**逆映射:**
$$\Psi: S^{-1}R \otimes_R M \to S^{-1}M, \quad \frac{r}{s} \otimes m \mapsto \frac{rm}{s}$$

**验证:**
- 两个映射互逆
- 保持 $S^{-1}R$-模结构

**正合性证明:**

**定理:** 局部化函子 $S^{-1}(-): R\text{-Mod} \to S^{-1}R\text{-Mod}$ 是正合的。

**证明:**
- $S^{-1}(-) \cong S^{-1}R \otimes_R -$
- $S^{-1}R$ 是平坦 $R$-模
- 张量积与平坦模保持正合性

## 5. 与FormalMath对应

| Stacks Project概念 | FormalMath对应内容 | 文档路径 |
|-------------------|-------------------|----------|
| 模的局部化 | 交换代数/模的局部化 | `concept/commutative_algebra/localization_module.md` |
| 张量积构造 | 同调代数/张量积 | `concept/homological_algebra/tensor_product.md` |
| 正合函子 | 同调代数/正合函子 | `concept/homological_algebra/exact_functor.md` |
| 平坦模 | 同调代数/平坦模 | `concept/homological_algebra/flat_module.md` |

**当前对齐状态:**
- 🟢 **良好对齐** - 模的局部化是标准内容，FormalMath有完整覆盖

**建议补充内容:**
```markdown
## 模的局部化详解

### 定义
设 $M$ 是 $R$-模，$S$ 乘性子集：
$$S^{-1}M = \{m/s : m \in M, s \in S\}/\sim$$
其中 $m/s \sim m'/s' \Leftrightarrow \exists t \in S: t(s'm-sm')=0$

### 等价刻画
$$S^{-1}M \cong S^{-1}R \otimes_R M$$

### 万有性质
$$
\xymatrix{
M \ar[r]^{\phi_M} \ar[dr]_f & S^{-1}M \ar@{-->}[d]^{\exists! \bar{f}} \\
& N
}
$$
对任意 $S^{-1}R$-模 $N$ 和 $R$-线性 $f$，存在唯一的 $S^{-1}R$-线性 $\bar{f}$。

### 正合性
$S^{-1}(-)$ 是正合函子，因为：
- $S^{-1}R$ 是平坦 $R$-模
- $S^{-1}(-) = S^{-1}R \otimes_R -$

### 应用
- 局部性质的研究
- 层论中的茎
- 代数几何中的拟凝聚层
```

## 6. 应用与重要性

**核心应用场景:**

### 1. 局部性质的研究
- 模的性质"是局部的"若可在局部化后检验
- 例: 平坦性、有限生成性、投射性都是局部性质

### 2. 层论中的茎
- 层 $\mathcal{F}$ 在点 $x$ 的茎：$\mathcal{F}_x = \varinjlim_{U \ni x} \mathcal{F}(U)$
- 对于仿射概形上的拟凝聚层，茎即模的局部化

### 3. 代数几何
- **拟凝聚层:** $\widetilde{S^{-1}M} \cong (\tilde{M})|_{D(S)}$
- **局部自由性:** $M$ 局部自由 $\Leftrightarrow$ $M_{\mathfrak{p}}$ 自由（对所有素理想）

### 4. 支撑集的计算
- $\text{Supp}(S^{-1}M) = \text{Supp}(M) \cap \text{Spec}(S^{-1}R)$
- 用于研究模的零点集

### 5. 同调代数
- 局部化保持投射性、内射性（在一定条件下）
- 导出函子与局部化的交换性

**重要性评级:** ⭐⭐⭐⭐⭐ (5/5)

模的局部化是交换代数的核心工具，是连接代数与几何（通过层论）的桥梁。

## 7. 与其他资源关联

### Stacks Project内部关联
| 相关Tag | 关联描述 |
|---------|----------|
| Tag 00EB | 环的局部化（基础） |
| Tag 00EU | 局部性质 |
| Tag 00MB | 平坦性 |
| Tag 01LA | 拟凝聚层 |
| Tag 00HD | 正合函子 |

### 外部资源

**经典教材:**
1. **Atiyah & Macdonald** "Introduction to Commutative Algebra"
   - 第3章: Modules of fractions
   - 正合性的完整证明

2. **Matsumura, H.** "Commutative Ring Theory"
   - §4: 局部化的深入应用

3. **Eisenbud, D.** "Commutative Algebra"
   - 第2.1节: 模的局部化

**现代教材:**
- **Dummit & Foote** "Abstract Algebra"
- **Rotman, J.** "An Introduction to Homological Algebra"

### 相关概念
- **Flatness**: 局部化是正合的核心原因
- **Support**: 模的支撑集
- **Associated primes**: 相伴素理想

## 8. Lean4形式化展望

### 形式化难度评估: ⭐⭐☆☆☆ (2/5)

**主要挑战:**
1. **张量积的同构** - 双向映射的构造与验证
2. **正合性的证明** - 需要平坦模的理论
3. **万有性质** - 泛性质的范畴论表述

**Lean4实现路线:**

```lean4
-- Mathlib已有完整实现！
import Mathlib

-- 模的局部化
variable {R : Type*} [CommRing R] {S : Submonoid R} {M : Type*} [AddCommGroup M] [Module R M]

-- 局部化模
#check LocalizedModule S M  -- S^{-1}M 的构造

-- 作为张量积的同构
#check (LocalizedModule.liftEquiv S M).toEquiv
-- LocalizedModule S M ≅ Localization S ⊗[R] M

-- 正合性
#check LocalizedModule.exact
-- 局部化保持正合列

-- 使用示例：层论中的茎
section StalkExample

variable {X : Type*} [TopologicalSpace X] (F : Presheaf Ab X) (x : X)

-- 茎的定义
#check F.stalk x
-- 作为余极限: colim_{U \ni x} F(U)

-- 对于仿射概形上的拟凝聚层
example {R : CommRingCat} (M : Module R ℝ) (P : PrimeSpectrum R) :
    (quasiCoherentSheaf M).stalk P ≅ LocalizedModule (PrimeSpectrum.compl P) M := by
  sorry  -- 需要层论的形式化

end StalkExample
```

**Mathlib现状:**
- `LocalizedModule` 已完整实现
- 张量积同构已有证明
- 正合性已形式化
- 层论中的茎需要更多工作

**形式化优先级:** MOSTLY COMPLETED 🟡
- 纯代数部分已在Mathlib中完成
- 需要与层论、代数几何的结合
- 建议关注拟凝聚层的应用

---

**文档编制日期:** 2026年4月  
**作者:** FormalMath项目团队  
**版本:** 1.0
