---
msc_primary: 00A99
msc_secondary:
  - 97A99
---

# Stacks Project Tag 02V0 - 平坦模（Flat Modules）

## 1. Tag基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 02V0 |
| **章节** | Chapter 10: Commutative Algebra, Section 10.39 |
| **类型** | 定义 (Definition) + 引理 (Lemma) |
| **重要性** | ★★★★★ (核心概念) |
| **位置** | Algebra, Definition 10.39.1 |

## 2. 定理/定义原文

### 英文原文

**Definition 10.39.1.** Let $R$ be a ring and $M$ an $R$-module.

1. We say that $M$ is **flat** over $R$ or **$R$-flat** if the functor $-\otimes_R M : \text{Mod}_R \to \text{Mod}_R$ is exact.

2. A morphism of rings $f : R \to S$ is said to be **flat** if $S$ is flat as an $R$-module.

3. If $R$ is a domain, an $R$-module $M$ is said to be **torsion free** if for all $x \in M$ and $r \in R$, $rx = 0$ implies $r = 0$ or $x = 0$.

### 中文翻译

**定义 10.39.1.** 设 $R$ 是环，$M$ 是 $R$-模。

1. 称 $M$ 在 $R$ 上是**平坦的**（flat），或**$R$-平坦**的，如果函子 $-\otimes_R M : \text{Mod}_R \to \text{Mod}_R$ 是正合的。

2. 环同态 $f : R \to S$ 称为**平坦的**，如果 $S$ 作为 $R$-模是平坦的。

3. 若 $R$ 是整环，$R$-模 $M$ 称为**无挠的**（torsion free），如果对所有 $x \in M$ 和 $r \in R$，$rx = 0$ 蕴含 $r = 0$ 或 $x = 0$。

## 3. 概念依赖图

```
                    平坦模 (Flat Module)
                           |
          +----------------+----------------+
          |                |                |
    张量积正合性        环同态平坦         无挠性
    (Tensor Product   (Flat Ring        (Torsion Free)
     Exactness)       Homomorphism)
          |                |                |
          +----------------+----------------+
                           |
                局部性质与判别准则
                           |
       +-------------------+-------------------+
       |                   |                   |
   Tor函子判别          局部自由           正则序列
   (Tor vanishing)    (Locally Free)    (Regular Seq)
```

**前置概念：**
- 张量积（Tensor Products）
- 正合函子（Exact Functors）
- 短正合序列（Short Exact Sequences）
- Tor函子（Tor Functors）

**依赖此概念：**
- 平坦态射（Flat Morphisms）
- 忠实平坦下降（Faithfully Flat Descent）
- 形变理论（Deformation Theory）
- 相交理论中的Tor公式

## 4. 证明概要

### 4.1 基本判别法

**引理 10.39.2:** 以下等价：
1. $M$ 是平坦的
2. 对任意单射 $N' \hookrightarrow N$，$N' \otimes M \to N \otimes M$ 是单射
3. $\text{Tor}_1^R(N, M) = 0$ 对所有 $N$

**证明思路：**
- (1)⇔(2): 由定义，平坦性要求 $-\otimes M$ 保持所有单射
- (2)⇔(3): Tor函子的定义性质

### 4.2 局部性质

**引理 10.39.18:** 设 $R \to S$ 是平坦环同态，$M$ 是 $R$-模。则：
- $M$ 平坦（在 $R$ 上）$\Leftrightarrow$ $M \otimes_R S$ 平坦（在 $S$ 上）

**应用：** 平坦性可以局部检验（在素理想上）。

### 4.3 局部自由与平坦

**引理 10.78.2:** 有限展示模 $M$ 平坦 $\Leftrightarrow$ $M$ 局部自由。

这是极其重要的结论：在诺特环上，有限生成平坦模 = 局部自由模 = 向量丛的截面。

## 5. 与FormalMath的对应关系

| FormalMath概念 | Stacks Project对应 | Lean4/mathlib4 |
|----------------|-------------------|----------------|
| `Module` | $R$-模 $M$ | `Module R M` ✓ |
| `TensorProduct` | $N \otimes_R M$ | `TensorProduct` ✓ |
| `Flat` | 平坦模 | `Module.Flat` ✓ |
| `Tor` | Tor函子 | `Tor` (部分) |
| `LocallyFree` | 局部自由 | `Module.LocallyFree` |

**mathlib4对应代码：**
```lean
-- 平坦模的定义
class Module.Flat (R : Type*) [Semiring R] (M : Type*) 
    [AddCommMonoid M] [Module R M] : Prop where
  -- 张量积函子右正合（左正合自动）
  rightExact : ∀ ⦃N N' N''⦄, 
    Function.Exact (N' →ₗ[R] N) (N →ₗ[R] N'') → 
    Function.Exact (N' ⊗[R] M →ₗ[R] N ⊗[R] M) (N ⊗[R] M →ₗ[R] N'' ⊗[R] M)

-- 环同态平坦
class Algebra.Flat (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] : Prop where
  flat : Module.Flat R S
```

## 6. 应用与重要性

### 6.1 代数几何中的平坦性

**几何意义：**

平坦态射 $f : X \to Y$ 可以理解为"连续变化"的概形族。纤维的维数在平坦态射下是局部常值的。

**关键定理：**

- **平坦性开性：** 若 $f$ 固有且平坦，则Hilbert多项式沿纤维局部常值
- **忠实平坦下降：** 平坦覆盖可用于下降数据

### 6.2 与光滑性的关系

| 性质 | 关系 |
|------|------|
| 光滑态射 | 平坦 + 局部有限展示 + 几何正则纤维 |
| 平展态射 | 平坦 + 非分歧 + 局部有限展示 |
| 开浸入 | 平坦（实际上是局部同构）|

### 6.3 重要例子

| 模/同态 | 平坦性 | 说明 |
|---------|--------|------|
$R^n$ (自由模) | ✓ 平坦 | 自由⇒平坦 |
$\mathbb{Q}$ 作为 $\mathbb{Z}$-模 | ✓ 平坦 | 无挠Abel群平坦 |
$\mathbb{Z}/n\mathbb{Z}$ | ✗ 非平坦 | 有挠 |
$k[x,y]/(xy)$ | ✗ 非平坦 | 几何上有奇点 |
$R \to R[x]$ | ✓ 平坦 | 多项式扩张 |
$R \to R_f$ (局部化) | ✓ 平坦 | 局部化平坦 |

### 6.4 维数理论

**定理:** 设 $R \to S$ 是平坦环同态，$\mathfrak{p} \subset R$ 是素理想。则：

$$\dim(S_{\mathfrak{p}}) = \dim(R_{\mathfrak{p}}) + \dim(S_{\mathfrak{p}} / \mathfrak{p}S_{\mathfrak{p}})$$

这是平坦性保持"纤维结构"的定量描述。

## 7. 与其他资源的关联

| 资源 | 章节 | 关联内容 |
|------|------|---------|
| Atiyah-Macdonald | Ch.2, 3 | 平坦模的基础理论 |
| Matsumura | Ch.7 | 交换代数中的平坦性 |
| Hartshorne | III.9 | 平坦态射与上同调 |
| Hartshorne | III.12 | 光滑态射的平坦性 |
| Stacks | Tag 02W1 | 平坦性判别 |
| Stacks | Tag 00MB | 忠实平坦性 |

**Stacks Project交叉引用：**
- Tag 02W1: 平坦性判别
- Tag 00MB: 忠实平坦性
- Tag 00MC: 平坦下降
- Tag 02V2: 平坦模的Tor判别

## 8. Lean4形式化展望

### 8.1 当前状态

```lean
-- mathlib4中已有定义
class Module.Flat (R : Type*) [Semiring R] (M : Type*) 
    [AddCommMonoid M] [Module R M] : Prop

-- 基本性质
theorem Module.Flat.lTensor_exact : 
    Flat R M → Function.Exact f g → 
    Function.Exact (f.lTensor M) (g.lTensor M)

-- 环同态平坦
class Algebra.Flat (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
```

### 8.2 待形式化内容

```lean
-- Tor判别法
theorem Module.flat_iff_tor_zero {R : Type*} [Ring R] {M : Type*} 
    [AddCommGroup M] [Module R M] :
    Module.Flat R M ↔ ∀ N, Tor₁ R N M = 0 := sorry

-- 局部自由⇔平坦+有限展示
theorem Module.locallyFree_iff_flat_finitePresentation [IsNoetherianRing R]
    [Module.FinitePresentation R M] :
    Module.LocallyFree R M ↔ Module.Flat R M := sorry

-- 平坦性的局部检验
theorem Module.flat_iff_localization : 
    Module.Flat R M ↔ ∀ p : PrimeSpectrum R, 
    Module.Flat (Localization.AtPrime p) (LocalizedModule p M) := sorry
```

### 8.3 形式化路线图

```
阶段1: 基础定义 ✓
  └── Module.Flat类型类
  └── 基本正合性

阶段2: 判别法 (进行中)
  └── Tor判别
  └── 单射保持判别
  └── 正合序列判别

阶段3: 局部性质 (计划中)
  └── 局部化保持
  └── 平坦性局部检验

阶段4: 应用 (计划中)
  └── 平坦下降
  └── 形变理论
  └── Hilbert概形
```

---

**文档版本：** Round 36  
**创建日期：** 2026-04-09
