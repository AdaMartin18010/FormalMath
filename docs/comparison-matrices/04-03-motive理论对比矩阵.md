---
msc_primary: 00

  - 00A99
title: Motive理论对比矩阵
processed_at: '2026-04-05'
---
# Motive理论对比矩阵

> **摘要**：本文档系统对比motive理论中的各类构造，包括Grothendieck motive、Chow motive、Nori motive、Voevodsky motive等，从构造方法、性质、关系和应用等多维度进行分析，帮助读者理解这一深刻统一理论的核心思想。

---

## 目录

1. [Motive理论概述](#motive理论概述)
2. [纯Motive vs 混合Motive](#纯motive-vs-混合motive)
3. [Grothendieck纯Motive](#grothendieck纯motive)
4. [Voevodsky混合Motive](#voevodsky混合motive)
5. [Nori Motive](#nori-motive)
6. [Motive与其他理论的关系](#motive与其他理论的关系)

---

## Motive理论概述

### 什么是Motive

**Grothendieck的愿景**：存在一种"普适上同调理论"，使得：
- 每个代数簇 X 对应一个 motive M(X)
- 各种上同调理论（Betti、de Rham、ℓ进）都是 M(X) 的"实现"
- motive 范畴是各种几何范畴的"公分母"

**直观理解**：

```

代数簇 X ──→ Motive M(X)
   ↓              ↓
H^*_Betti    H^*_motive 的"实现"
H^*_deRham      ↓
H^*_ℓ-adic   ← 各种上同调理论

```

### Motive理论分类

| 类型 | 构造者 | 对象 | 系数 | 主要特征 |
|-----|-------|-----|-----|---------|
| **Grothendieck纯Motive** | Grothendieck | 光滑射影簇 | ℚ | 代数圈、数值等价 |
| **Chow Motive** | - | 同上 | ℚ | Chow群、有理等价 |
| **Murre Motive** | Murre | 同上 | ℚ | Chow-Künneth分解 |
| **Voevodsky Motive** | Voevodsky | 所有簇 | ℤ | 三角范畴、A¹-同伦 |
| **Nori Motive** | Nori | 所有簇 | ℚ | 万有阿贝尔范畴 |
| **Ayoub Motive** | Ayoub | 所有簇 | ℚ | 导出范畴 |

---

## 纯Motive vs 混合Motive

### 基本对比

| 性质 | 纯Motive | 混合Motive |
|-----|---------|-----------|
| **来源** | 光滑射影簇 | 所有代数簇 |
| **结构** | 半单（猜想） | 有权重滤过 |
| **范畴** | 阿贝尔范畴（猜想） | 阿贝尔/三角范畴 |
| **实现** | 纯Hodge结构/ℓ进表示 | 混合Hodge结构/ℓ进表示 |
| **构造完成度** | 部分完成（数值等价） | Voevodsky完成（DM） |
| **标准猜想** | 需要Grothendieck标准猜想 | 部分避免 |

### 纯Motive的动机

**Poincaré对偶**：对光滑射影簇 X，dim = n：
$$H^i(X) \times H^{2n-i}(X) \to H^{2n}(X) \cong \mathbb{Q}(-n)$$

**Künneth分解**：
$$H^*(X \times Y) = \bigoplus_{i+j=*} H^i(X) \otimes H^j(Y)$$

**纯Motive的想法**：将代数簇分解为"上同调切片"的直和。

### 混合Motive的动机

**问题**：非紧或非光滑簇的上同调有**权重滤过**：

$$W_0 \subseteq W_1 \subseteq ... \subseteq W_{2n} = H^*(X)$$

**gr_i^W H^*(X)** 是纯的（权 i）。

**混合Motive**：捕捉这种权重结构。

---

## Grothendieck纯Motive

### 构造步骤

```

Step 1: 对应范畴 Corr(k)
  - 对象：光滑射影簇
  - 态射：Corrⁱ(X,Y) = CH^{dim X + i}(X × Y)

Step 2: 添加幂等元分裂
  - 对投影算子 e: X → X（e² = e）分裂
  - 得到有效纯Motive范畴

Step 3: 添加Tate motive的逆
  - ℚ(1) = L = ℙ¹ \ {pt}
  - ℚ(n) = ℚ(1)^{⊗n}
  - 得到纯Motive范畴 ChowEff(k)

Step 4: 取伪Abel完备化（Grothendieck构造）
  - 或取数值等价商（已证明半单）

```

### 三种等价关系

| 等价关系 | 定义 | 性质 | 结果范畴 |
|---------|-----|-----|---------|
| **有理等价** | Chow群 | 容易计算 | Chow Motive |
| **同调等价** | H^*中的类 | 依赖于上同调 | - |
| **数值等价** | 与所有dim交为0 | 猜测=同调 | 数值Motive（半单） |

**标准猜想**：
- **猜想D**：同调等价 = 数值等价
- **猜想C**：Künneth分量是代数圈
- **猜想B**：Lefschetz算子给出同构

### 纯Motive的结构

**有限性**：设 X 是光滑射影簇。

$$M(X) = \bigoplus_{i=0}^{2n} M^i(X)(-?)$$

其中 $M^i(X)$ 对应 $H^i(X)$。

**Tate motive**：
- ℚ = M(pt)：平凡motive
- ℚ(1)：Tate motive（权 -2）
- ℚ(n) = ℚ(1)^{⊗n}（权 -2n）

**Lefschetz motive**：L = ℚ(-1) = M¹(ℙ¹)。

---

## Voevodsky混合Motive

### 构造概要

```

Step 1: 光滑对应范畴 SmCor(k)
  - 对象：光滑簇
  - 态射：有限对应（代数圈）

Step 2: 链复形范畴
  - 复形的不变量处理
  
Step 3: 三种局部化
  a) Nisnevich局部化
  b) A¹-同伦不变化（类似拓扑同伦）
  c) 商去复形（移去不必要结构）

Step 4: 得到 DM(k)（三角范畴）
  - 对象：混合motive
  - 满足六函子形式体系

```

### Voevodsky范畴的性质

| 性质 | 说明 | 意义 |
|-----|-----|-----|
| **三角范畴** | 有平移和 distinguished triangles | 导出函子形式 |
| **张量结构** | ⊗ 和对偶 | 代数结构 |
| **Tate扭转** | M(n) = M ⊗ ℤ(n) | 权重变化 |
| **紧生成** | 光滑簇生成 | 可计算 |
| **实现函子** | 到各上同调理论 | 统一性 |

### 重要对象

| 对象 | 符号 | 意义 |
|-----|-----|-----|
| **Motive of X** | M(X) | 簇的motive |
| **Tate motive** | ℤ(1) | Lefschetz motive |
| **Motivic上同调** | H^i_M(X, ℤ(j)) | 推广Chow群 |
| **Motivic复形** | ℤ(n) | 层复形 |

### Motivic上同调

**定义**：$H^i_M(X, \mathbb{Z}(j)) = \text{Hom}_{DM}(M(X), \mathbb{Z}(j)[i])$

**与其他理论的关系**：

| 理论 | motivic解释 | 关系 |
|-----|------------|-----|
| **Chow群** | H^{2n}_M(X, ℤ(n)) | CH^n(X) ≅ H^{2n}_M |
| **Milnor K-理论** | H^n_M(F, ℤ(n)) | K^M_n(F) ≅ H^n_M |
| **étale上同调** | H^i_M(X, ℤ/n) → H^i_ét(X, μ_n^{⊗j}) | 实现 |
| **代数K-理论** | 谱序列 | Atiyah-Hirzebruch型 |

---

## Nori Motive

### 构造方法

**Nori的核心思想**：从"好"的上同调理论（如奇异上同调）出发，通过**万有阿贝尔范畴**构造motive。

**步骤**：

```

Step 1: 定义图表 D = "好对" (X, Y, i)
  - X 代数簇，Y ⊆ X 闭子集，i 整数
  - 模拟相对上同调 H^i(X, Y)

Step 2: 给定表示 T: D → ℤ-Mod（如奇异上同调）

Step 3: 构造万有阿贝尔范畴 C(T)
  - 包含 D 的"图"（diagram）
  - 反映 T 的所有关系

Step 4: Nori motive = C(T) 的对象

```

### Nori范畴的性质

| 性质 | 说明 | 与Voevodsky比较 |
|-----|-----|----------------|
| **阿贝尔范畴** | 核和余核存在 | Voevodsky是三角范畴 |
| **万有性** | 最小包含给定表示 | DM包含更多 |
| **权结构** | 有自然的权滤过 | 类似 |
| **实现** | 构造性 | 需要额外证明 |

### Nori motive的结构

**关键定理**：Nori motive的范畴是**中性Tannakian范畴**。

**Galois群**：
$$G_{mot}(k) = \text{Aut}^\otimes(H^*_B: MM(k) → \text{Vec}_\mathbb{Q})$$

称为**motivic Galois群**。

**猜想**：$G_{mot}(k)$ 反映所有代数圈的信息。

---

## Motive与其他理论的关系

### 与Hodge理论的关系

| 理论 | 对象 | 与Motive的关系 |
|-----|-----|--------------|
| **Hodge结构** | Hodge分解 | 纯motive → Hodge结构 |
| **混合Hodge结构** | 权重滤过 | 混合motive → MHS |
| **Hodge猜想** | H^{p,p}中的类是代数圈 | 等价于motive的实现满射 |

**Hodge实现**：
$$\text{real}_H: MM(k) → \text{MHS}$$

### 与ℓ进理论的关系

| 理论 | 对象 | 与Motive的关系 |
|-----|-----|--------------|
| **ℓ进表示** | Gal(k̄/k)作用 | 纯motive → ℓ进表示 |
| **Tate猜想** | 不动子空间 = 代数圈 | 等价于实现本质满 |

**ℓ进实现**：
$$\text{real}_\ell: MM(k) → \text{Rep}_\ell(Gal)$$

### 与K-理论的关系

**Bloch-Kato猜想 / 范循环猜想**（Voevodsky证明）：
$$H^i_M(X, \mathbb{Z}/n) \cong H^i_\text{ét}(X, \mu_n^{\otimes j})$$

**意义**：桥接motivic上同调与étale上同调，是motive理论的中心结果。

### Motive与标准猜想

| 猜想 | 内容 | 现状 |
|-----|-----|-----|
| **标准猜想D** | 同调=数值等价 | 开放 |
| **标准猜想C** | Künneth分量代数 | 开放 |
| **标准猜想B** | Lefschetz类型 | 开放 |
| **Hodge猜想** | H^{p,p}类代数 | 开放（百万问题） |
| **Tate猜想** | ℓ进循环类代数 | 开放 |

**关系**：

```

标准猜想 + Hodge猜想 ──→ 纯motive的阿贝尔性
                   │
                   v
              所有上同调理论的统一

```

---

## 总结表：Motive理论选择指南

| 问题 | 推荐理论 | 关键工具 |
|-----|---------|---------|
| 光滑射影簇 | Grothendieck纯Motive | 代数圈、数值等价 |
| 一般簇 | Voevodsky混合Motive | DM范畴、A¹-同伦 |
| 具体计算 | Nori Motive | 图范畴、万有构造 |
| 与上同调联系 | 实现函子 | 各种比较定理 |
| Bloch-Kato | Motivic上同调 | 范循环猜想 |

---

**参考MSC编码**: 14C15 (Chow群与环), 14C25 (代数圈), 14C35 (应用 of 代数圈到动机理论), 14F42 (motivic上同调; 概形的motive), 19E15 (代数K-理论中的代数圈)
