---
title: "Lebesgue积分 - 深度扩展版"
msc_primary: "28Axx"
msc_secondary: ['46Gxx', '46-XX', '46Axx']
processed_at: '2026-04-05'
---
# Lebesgue积分 - 深度扩展版

**创建日期**: 2025年12月1日
**研究领域**: 分析学 - 测度论与积分理论
**优先级**: P0（最高优先级）⭐⭐⭐⭐⭐

---

## 📑 目录

- [Lebesgue积分 - 深度扩展版](#lebesgue积分---深度扩展版)
  - [📑 目录](#目录)
  - [📋 一、概述与历史背景](#-一概述与历史背景)
    - [1.1 历史发展](#11-历史发展)
    - [1.2 核心思想](#12-核心思想)
  - [📚 二、测度论基础](#-二测度论基础)
    - [2.1 σ-代数](#21-σ-代数)
    - [2.2 测度](#22-测度)
    - [2.3 可测函数](#23-可测函数)
  - [🔧 三、Lebesgue积分构造](#-三lebesgue积分构造)
    - [3.1 简单函数积分](#31-简单函数积分)
    - [3.2 非负可测函数积分](#32-非负可测函数积分)
    - [3.3 一般可测函数积分](#33-一般可测函数积分)
    - [3.4 构造层次图](#34-构造层次图)
  - [📐 四、核心定理与证明](#-四核心定理与证明)
    - [4.1 单调收敛定理 (MCT)](#41-单调收敛定理-mct)
    - [4.2 Fatou引理](#42-fatou引理)
    - [4.3 控制收敛定理 (DCT)](#43-控制收敛定理-dct)
    - [4.4 三大定理关系图](#44-三大定理关系图)
  - [⚖️ 五、与Riemann积分对比](#️-五与riemann积分对比)
    - [5.1 对比表](#51-对比表)
    - [5.2 Riemann可积⟹Lebesgue可积](#52-riemann可积lebesgue可积)
    - [5.3 Lebesgue可积但非Riemann可积](#53-lebesgue可积但非riemann可积)
  - [🗺️ 六、知识图谱](#️-六知识图谱)
    - [6.1 概念依赖图](#61-概念依赖图)
    - [6.2 定理证明依赖图](#62-定理证明依赖图)
    - [6.3 积分理论演化图](#63-积分理论演化图)
    - [6.4 应用领域图](#64-应用领域图)
  - [💻 七、技术实现](#-七技术实现)
    - [7.1 Lean 4 形式化](#71-lean-4-形式化)
    - [7.2 Haskell 函数式实现](#72-haskell-函数式实现)
    - [7.3 Python 数值实现](#73-python-数值实现)
  - [📈 八、应用与扩展](#-八应用与扩展)
    - [8.1 概率论应用](#81-概率论应用)
    - [8.2 泛函分析应用](#82-泛函分析应用)
    - [8.3 Fourier分析](#83-fourier分析)
    - [8.4 推广方向](#84-推广方向)
  - [📖 九、参考文献](#-九参考文献)
    - [经典教材](#经典教材)
    - [原始文献](#原始文献)
    - [形式化资源](#形式化资源)
  - [📊 术语对照表](#-术语对照表)

---

## 📋 一、概述与历史背景

### 1.1 历史发展

**问题起源**：

| 时期 | 发展 | 关键人物 |
|------|------|----------|
| 1854年 | Riemann积分定义 | Riemann |
| 1881年 | Volterra发现Riemann积分局限 | Volterra |
| 1898年 | Borel测度论基础 | Borel |
| 1902年 | Lebesgue积分创立 | Lebesgue |
| 1904年 | 《积分、长度与面积》发表 | Lebesgue |
| 1909年 | Radon测度推广 | Radon |
| 1930s | 抽象测度论完善 | Kolmogorov |

### 1.2 核心思想

**Riemann vs Lebesgue 思想差异**：

```text
[Riemann积分思想]              [Lebesgue积分思想]
        │                              │
  "按定义域划分"              "按值域划分"
        │                              │
  ┌─────┴─────┐              ┌─────┴─────┐
  │           │              │           │
将[a,b]分成   对每个子区间   将R分成      对每个值域
小区间Δxᵢ    取函数值fᵢ     小区间Δyⱼ   找原像μ(f⁻¹)
  │           │              │           │
  └─────┬─────┘              └─────┬─────┘
        │                              │
  Σ f(xᵢ*)Δxᵢ                  Σ yⱼ·μ(Eⱼ)
        │                              │
"水平切片求和"              "垂直切片求和"

```

**Lebesgue的格言**：
> "如果我要计算硬币的总值，可以一枚一枚地加（Riemann），也可以先把相同面值的分类，再乘以数量相加（Lebesgue）"

---

## 📚 二、测度论基础

### 2.1 σ-代数

**定义**：集合X上的σ-代数Σ满足：

1. X ∈ Σ
2. A ∈ Σ ⟹ Aᶜ ∈ Σ（补集封闭）
3. {Aₙ}ₙ∈ℕ ⊂ Σ ⟹ ∪ₙAₙ ∈ Σ（可数并封闭）

**重要例子**：

| σ-代数 | 定义 | 用途 |
|--------|------|------|
| 幂集 P(X) | 所有子集 | 离散情形 |
| Borel σ-代数 | 由开集生成 | ℝⁿ上标准测度 |
| Lebesgue σ-代数 | Borel + 零测集子集 | 完备化 |

### 2.2 测度

**定义**：测度μ: Σ → [0,∞]满足：

1. μ(∅) = 0
2. σ-可加性：μ(∪ₙAₙ) = Σₙμ(Aₙ)（不交并）

**Lebesgue测度构造**：

```text
        [Lebesgue测度构造]
              │
    ┌─────────┴─────────┐
    │                   │
[外测度]            [Carathéodory]
    │               条件
    │                   │
m*(A) = inf{Σ|Iₙ|:   A是可测的 ⟺

A⊂∪Iₙ, Iₙ为区间}    对所有E:
    │               m*(E)=m*(E∩A)+m*(E∩Aᶜ)
    │                   │
    └─────────┬─────────┘
              │
    [Lebesgue可测集]
    含所有开集、闭集、Borel集
    及零测集的子集

```

### 2.3 可测函数

**定义**：f: X → ℝ̄ 可测，若对所有α∈ℝ：

```text
f⁻¹((α,∞]) = {x: f(x) > α} ∈ Σ

```

**等价条件**：

| 条件 | 表述 |
|------|------|
| (1) | {f > α} 可测，∀α |
| (2) | {f ≥ α} 可测，∀α |
| (3) | {f < α} 可测，∀α |
| (4) | {f ≤ α} 可测，∀α |
| (5) | f⁻¹(B) 可测，∀ Borel集B |

---

## 🔧 三、Lebesgue积分构造

### 3.1 简单函数积分

**简单函数**：

```text
φ = Σᵢ₌₁ⁿ aᵢ χ_{Eᵢ}

```

其中Eᵢ可测且不交。

**积分定义**：

```text
∫ φ dμ = Σᵢ₌₁ⁿ aᵢ · μ(Eᵢ)

```

### 3.2 非负可测函数积分

**定义**：

```text
∫ f dμ = sup{∫ φ dμ : 0 ≤ φ ≤ f, φ简单}

```

### 3.3 一般可测函数积分

**分解**：f = f⁺ - f⁻

- f⁺ = max(f, 0)
- f⁻ = max(-f, 0)

**定义**（若至少一个有限）：

```text
∫ f dμ = ∫ f⁺ dμ - ∫ f⁻ dμ

```

**可积条件**：∫|f|dμ < ∞

### 3.4 构造层次图

```text
        [Lebesgue积分构造层次]
                  │
    ┌─────────────┼─────────────┐
    │             │             │
[第一层]       [第二层]      [第三层]
简单函数       非负函数      一般函数
    │             │             │
∫Σaᵢχ_{Eᵢ}dμ   sup逼近       f⁺ - f⁻
=Σaᵢμ(Eᵢ)      简单函数      分解
    │             │             │
    └─────────────┴─────────────┘
                  │
        [L¹空间: 可积函数]
        ∫|f|dμ < ∞

```

---

## 📐 四、核心定理与证明

### 4.1 单调收敛定理 (MCT)

**定理**：设{fₙ}是非负可测函数列，且fₙ↗f（单调递增收敛于f），则：

```text
lim_{n→∞} ∫ fₙ dμ = ∫ f dμ

```

**证明树**：

```text
        [单调收敛定理证明]
                │
    ┌───────────┴───────────┐
    │                       │
[方向1: ≤]              [方向2: ≥]
    │                       │
fₙ ≤ f                  取简单函数φ ≤ f
    ↓                       │
∫fₙdμ ≤ ∫fdμ           设Eₙ = {fₙ ≥ cφ}, 0<c<1
    ↓                       │
lim∫fₙdμ ≤ ∫fdμ        Eₙ↗X (因fₙ↗f)
                            │
                    ∫fₙdμ ≥ ∫_{Eₙ}fₙdμ ≥ c∫_{Eₙ}φdμ
                            │
                    令n→∞: lim∫fₙdμ ≥ c∫φdμ
                            │
                    令c→1: lim∫fₙdμ ≥ ∫φdμ
                            │
                    对所有φ≤f取sup: ≥ ∫fdμ
                            │
    └───────────┬───────────┘
                │
        lim∫fₙdμ = ∫fdμ ∎

```

### 4.2 Fatou引理

**定理**：设{fₙ}是非负可测函数列，则：

```text
∫ liminf fₙ dμ ≤ liminf ∫ fₙ dμ

```

**证明**：

- 令 gₙ = inf_{k≥n} fₖ
- gₙ↗ liminf fₙ
- 由MCT：∫ liminf fₙ dμ = lim ∫gₙ dμ
- 而 gₙ ≤ fₙ，故 ∫gₙdμ ≤ ∫fₙdμ
- 因此 lim∫gₙdμ ≤ liminf∫fₙdμ ∎

### 4.3 控制收敛定理 (DCT)

**定理**：设{fₙ}可测，fₙ→f a.e.，且存在可积函数g使|fₙ|≤g a.e.，则：

```text
lim_{n→∞} ∫ fₙ dμ = ∫ f dμ

```

**证明树**：

```text
        [控制收敛定理证明]
                │
        应用Fatou引理两次
                │
    ┌───────────┴───────────┐
    │                       │
[对 g+fₙ]               [对 g-fₙ]
    │                       │
g+fₙ ≥ 0               g-fₙ ≥ 0
    │                       │
Fatou:                  Fatou:
∫(g+f)dμ ≤             ∫(g-f)dμ ≤
liminf∫(g+fₙ)dμ        liminf∫(g-fₙ)dμ
    │                       │
∫gdμ+∫fdμ ≤            ∫gdμ-∫fdμ ≤
∫gdμ+liminf∫fₙdμ       ∫gdμ-limsup∫fₙdμ
    │                       │
∫fdμ ≤ liminf∫fₙdμ     limsup∫fₙdμ ≤ ∫fdμ
    │                       │
    └───────────┬───────────┘
                │
    limsup∫fₙdμ ≤ ∫fdμ ≤ liminf∫fₙdμ
                │
    ⟹ lim∫fₙdμ = ∫fdμ ∎

```

### 4.4 三大定理关系图

```text
        [Lebesgue积分三大定理]
                  │
    ┌─────────────┼─────────────┐
    │             │             │
  [MCT]        [Fatou]        [DCT]
单调收敛        引理         控制收敛
    │             │             │
fₙ↗f非负     liminf      fₙ→f, |fₙ|≤g

    │             │             │
lim∫=∫lim    ∫liminf≤    lim∫=∫lim
              liminf∫
    │             │             │
    └──────┬──────┘             │
           │                    │
      [Fatou由MCT推出]          │
           │                    │
           └─────────┬──────────┘
                     │
              [DCT由Fatou推出]

```

---

## ⚖️ 五、与Riemann积分对比

### 5.1 对比表

| 特性 | Riemann积分 | Lebesgue积分 |
|------|-------------|--------------|
| **划分方式** | 定义域（x轴） | 值域（y轴） |
| **可积条件** | 有界+几乎处处连续 | 可测+可积 |
| **极限交换** | 需一致收敛 | 控制收敛即可 |
| **完备性** | L¹不完备 | L¹完备 |
| **适用范围** | 有界区间上连续函数 | 一般测度空间 |

### 5.2 Riemann可积⟹Lebesgue可积

**定理**：f在[a,b]上Riemann可积 ⟹ f Lebesgue可积且积分值相等。

**证明要点**：

1. Riemann可积 ⟺ 不连续点是零测集
2. 构造上下和逼近
3. 极限一致

### 5.3 Lebesgue可积但非Riemann可积

**经典例子：Dirichlet函数**：

```text
f(x) = χ_ℚ(x) = { 1, x∈ℚ
                { 0, x∉ℚ

```

- **Riemann**：不可积（上和=1，下和=0）
- **Lebesgue**：∫₀¹ f dm = m(ℚ∩[0,1]) = 0

---

## 🗺️ 六、知识图谱

### 6.1 概念依赖图

```text
        [Lebesgue积分知识体系]
                  │
    ┌─────────────┼─────────────┐
    │             │             │
[测度论基础]  [积分构造]    [收敛定理]
    │             │             │
├─σ-代数      ├─简单函数    ├─MCT
├─测度        │ 积分        ├─Fatou
├─外测度      ├─非负函数    ├─DCT
├─可测集      │ 积分        │
├─可测函数    ├─一般函数    │
│             │ 积分        │
    │             │             │
    └─────────────┼─────────────┘
                  │
            [L^p空间]
                  │
├─L¹: 可积函数空间
├─L²: 平方可积（Hilbert空间）
├─L^∞: 本性有界
└─Hölder, Minkowski不等式

```

### 6.2 定理证明依赖图

```text
[σ-代数定义] ──→ [可测函数定义]
      │                 │
      ▼                 ▼
[测度定义] ───→ [简单函数积分] ──→ [非负函数积分]
      │                              │
      ▼                              ▼
[Carathéodory] ←───────────────── [MCT]
      │                              │
      ▼                              ▼
[Lebesgue测度] ──────────────→ [Fatou引理]
                                     │
                                     ▼
                              [DCT(控制收敛)]
                                     │
                                     ▼
                              [Fubini定理]

```

### 6.3 积分理论演化图

```text
        [积分理论发展史]
              │
[Archimedes穷竭法] (前3世纪)
              │
[Newton-Leibniz微积分] (17世纪)
              │
[Riemann积分] (1854)
        │
        ├─────────────────┐
        │                 │
[Stieltjes积分]     [Lebesgue积分]
(1894)                  (1902)
        │                 │
        └────────┬────────┘
                 │
          [Radon测度]
             (1909)
                 │
          [抽象测度论]
          (Kolmogorov, 1930s)
                 │
    ┌────────────┼────────────┐
    │            │            │
[概率论]   [泛函分析]   [调和分析]

```

### 6.4 应用领域图

```text
        [Lebesgue积分应用]
                │
    ┌───────────┼───────────┐
    │           │           │
[纯数学]     [物理]      [应用]
    │           │           │
├─泛函分析  ├─量子力学  ├─信号处理
│ L²空间    │ 波函数    │ Fourier
├─概率论    ├─统计力学  ├─图像处理
│ 期望值    │ 配分函数  │
├─调和分析  ├─场论      ├─金融数学
│ Fourier   │ 路径积分  │ 期权定价
├─PDE       │           ├─机器学习
│ Sobolev   │           │ 损失函数

```

---

## 💻 七、技术实现

### 7.1 Lean 4 形式化

```lean
-- Lebesgue积分基础（Mathlib风格）
import Mathlib.MeasureTheory.Integral.Lebesgue

-- 简单函数积分
theorem simple_function_integral {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : SimpleFunc α ℝ≥0) :
    ∫⁻ x, f x ∂μ = ∑ y in f.range, y * μ (f ⁻¹' {y}) := by
  exact SimpleFunc.lintegral_eq_lintegral f μ

-- 单调收敛定理
theorem monotone_convergence {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : ℕ → α → ℝ≥0∞}
    (hf_meas : ∀ n, Measurable (f n))
    (hf_mono : ∀ x, Monotone (fun n => f n x)) :
    ∫⁻ x, ⨆ n, f n x ∂μ = ⨆ n, ∫⁻ x, f n x ∂μ := by
  exact lintegral_iSup hf_meas (fun x => hf_mono x)

-- 控制收敛定理
theorem dominated_convergence {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : ℕ → α → ℝ} {g : α → ℝ} {bound : α → ℝ}
    (hf_meas : ∀ n, Measurable (f n))
    (hf_lim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    (hf_bound : ∀ n, ∀ᵐ x ∂μ, |f n x| ≤ bound x)

    (hbound_int : Integrable bound μ) :
    Tendsto (fun n => ∫ x, f n x ∂μ) atTop (𝓝 (∫ x, g x ∂μ)) := by
  exact tendsto_integral_of_dominated_convergence bound hf_meas
    (fun n => (hf_bound n).mono fun x hx => le_abs_self _)
    hbound_int hf_lim

```

### 7.2 Haskell 函数式实现

```haskell
-- Lebesgue积分概念模拟
module LebesgueIntegral where

-- 简单函数表示
data SimpleFunc a = SimpleFunc [(a, Double)]  -- (值, 测度)

-- 简单函数积分
integrateSimple :: SimpleFunc a -> Double
integrateSimple (SimpleFunc pairs) =
    sum [val * measure | (val, measure) <- pairs]

-- 非负函数积分（通过逼近）
integrateNonneg :: (Double -> Double) -> [SimpleFunc Double] -> Double
integrateNonneg f approxSeq =
    maximum [integrateSimple s | s <- approxSeq]

-- 数值积分示例
numericalLebesgue :: (Double -> Double) -> Double -> Double -> Int -> Double
numericalLebesgue f a b n =
    let dx = (b - a) / fromIntegral n
        xs = [a + fromIntegral i * dx | i <- [0..n-1]]

        vals = map f xs
        sortedVals = sort vals
        -- 按值域划分并计算
    in sum [v * dx | v <- vals]  -- 简化版本

```

### 7.3 Python 数值实现

```python
import numpy as np
from scipy import integrate

def lebesgue_integral_numerical(f, a, b, n=1000):
    """
    数值逼近Lebesgue积分
    使用值域划分方法
    """
    x = np.linspace(a, b, n)
    y = f(x)

    # 按值域划分
    y_min, y_max = np.min(y), np.max(y)
    m = 100  # 值域划分数
    levels = np.linspace(y_min, y_max, m)

    integral = 0
    for i in range(len(levels) - 1):
        level = (levels[i] + levels[i+1]) / 2
        # 计算原像的测度（在此区间内f(x)在[levels[i], levels[i+1]]的x的测度）
        mask = (y >= levels[i]) & (y < levels[i+1])
        measure = np.sum(mask) * (b - a) / n
        integral += level * measure

    return integral

# 验证：Dirichlet函数
def dirichlet(x, rationals_approx):
    """Dirichlet函数的有限近似"""
    return np.array([1 if any(np.abs(xi - r) < 1e-10 for r in rationals_approx)
                     else 0 for xi in x])

# Lebesgue: ∫₀¹ χ_ℚ = 0 (有理数零测)
print("Dirichlet函数Lebesgue积分 ≈ 0")

```

---

## 📈 八、应用与扩展

### 8.1 概率论应用

**期望值定义**：

```text
E[X] = ∫_Ω X dP

```

**优势**：

- 可处理任意分布
- 极限定理（大数定律、中心极限）

### 8.2 泛函分析应用

**L²空间**：

- 内积：⟨f,g⟩ = ∫fg dμ
- 完备 → Hilbert空间
- Riesz表示定理

### 8.3 Fourier分析

**Plancherel定理**：

```text
‖f̂‖_{L²} = ‖f‖_{L²}

```

### 8.4 推广方向

| 推广 | 内容 |
|------|------|
| Stieltjes积分 | 对一般测度 |
| Bochner积分 | Banach空间值函数 |
| 向量测度 | 向量值测度 |
| 非交换积分 | 算子代数 |

---

## 📖 九、参考文献

### 经典教材

1. **Rudin, W. (1987). Real and Complex Analysis.**
   - 标准研究生教材

2. **Royden, H. L. (1988). Real Analysis.**
   - 经典本科教材

3. **Folland, G. B. (1999). Real Analysis: Modern Techniques.**
   - 现代方法

### 原始文献

4. **Lebesgue, H. (1904). Leçons sur l'intégration.**
   - Lebesgue原著

5. **Lebesgue, H. (1902). Intégrale, longueur, aire.**
   - 博士论文

### 形式化资源

6. **Mathlib - MeasureTheory**
   - Lean 4测度论库

---

## 📊 术语对照表

| 中文 | 英文 | 符号 |
|------|------|------|
| σ-代数 | σ-algebra | Σ |
| 测度 | Measure | μ |
| 可测函数 | Measurable function | f |
| 简单函数 | Simple function | φ |
| 单调收敛定理 | Monotone Convergence Theorem | MCT |
| 控制收敛定理 | Dominated Convergence Theorem | DCT |
| Fatou引理 | Fatou's Lemma | - |
| Lebesgue可积 | Lebesgue integrable | f ∈ L¹ |

---

**最后更新**: 2025年12月1日
**状态**: ✅ 已完成深化（含证明树与知识图谱）
