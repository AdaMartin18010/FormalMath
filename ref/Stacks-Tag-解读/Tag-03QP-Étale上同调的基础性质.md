# Stacks Project Tag 03QP - Étale上同调的基础性质

## 1. 基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 03QP |
| **英文名称** | Étale Cohomology - Basic Properties |
| **所属章节** | Theorem on Formal Functions (Chapter 52) |
| **主题分类** | 代数几何 - 上同调理论 |
| **创建日期** | 2026-04-10 |
| **版本** | v1.0 |

---

## 2. 核心概念与定义

### 2.1 Étale上同调概述

**Étale上同调**（Étale Cohomology）是代数几何中一种重要的上同调理论，由Alexander Grothendieck在1960年代发展，用于在任意概形上建立类似于奇异上同调的理论。

### 2.2 关键定义

**定义 2.2.1**（Étale拓扑）
设 $X$ 是一个概形。$X$ 的**Étale位形**（Étale Site）$X_{\text{ét}}$ 定义如下：
- 对象：$X$ 的Étale态射 $U \to X$
- 覆盖：集合族 $\{U_i \to U\}$ 使得 $\coprod U_i \to U$ 是满射

**定义 2.2.2**（Étale层）
$X_{\text{ét}}$ 上的**层**（Sheaf）是一个反变函子 $\mathcal{F}: X_{\text{ét}}^{\text{op}} \to \text{Sets}$（或Abel群等），满足层条件：对任意覆盖 $\{U_i \to U\}$，序列

$$\mathcal{F}(U) \to \prod_i \mathcal{F}(U_i) \rightrightarrows \prod_{i,j} \mathcal{F}(U_i \times_U U_j)$$

是正合的。

**定义 2.2.3**（Étale上同调群）
对于Abel群层 $\mathcal{F} \in \text{Ab}(X_{\text{ét}})$，其**$q$阶Étale上同调群**定义为：

$$H^q_{\text{ét}}(X, \mathcal{F}) := R^q\Gamma(X, \mathcal{F})$$

其中 $\Gamma(X, -)$ 是整体截面函子。

---

## 3. 主要结果与定理

### 3.1 基本性质定理

**定理 3.1.1**（Tag 03QP）
Étale上同调满足以下基本性质：

**(a) 长正合序列**
对于短正合序列 $0 \to \mathcal{F}' \to \mathcal{F} \to \mathcal{F}'' \to 0$，存在自然的长正合序列：

$$\cdots \to H^q_{\text{ét}}(X, \mathcal{F}') \to H^q_{\text{ét}}(X, \mathcal{F}) \to H^q_{\text{ét}}(X, \mathcal{F}'') \xrightarrow{\delta} H^{q+1}_{\text{ét}}(X, \mathcal{F}') \to \cdots$$

**(b) 维数消失**
若 $X$ 是维度 $\leq d$ 的诺特概形，则对任意 $q > d$ 和任意挠层 $\mathcal{F}$，有：

$$H^q_{\text{ét}}(X, \mathcal{F}) = 0$$

**(c) 群上同调**
对于域 $k$ 和 $G_k = \text{Gal}(k^{\text{sep}}/k)$，有：

$$H^q_{\text{ét}}(\text{Spec}(k), \mathcal{F}) \cong H^q(G_k, \mathcal{F}_{k^{\text{sep}}})$$

### 3.2 比较定理

**定理 3.2.1**（与奇异上同调的比较）
设 $X$ 是复代数簇，$\mathcal{F}$ 是局部常值有限Abel群层，则：

$$H^q_{\text{ét}}(X, \mathcal{F}) \cong H^q_{\text{sing}}(X(\mathbb{C}), \mathcal{F})$$

其中右侧是经典的奇异上同调。

---

## 4. 证明思路

### 4.1 长正合序列的证明

**步骤1**：导出函子性质
- 整体截面函子 $\Gamma(X, -)$ 是左正合函子
- 高阶导出函子 $R^q\Gamma(X, -)$ 自动给出长正合序列

**步骤2**：内射分解
- 任何Abel群层都有内射分解
- 导出函子与内射分解的选择无关

### 4.2 维数消失的证明

**关键引理**（Artin-Schreier）：
对于光滑射影曲线 $X/\mathbb{F}_p$ 和常值层 $\mathbb{Z}/p\mathbb{Z}$，有：

$$H^q_{\text{ét}}(X, \mathbb{Z}/p\mathbb{Z}) = 0, \quad q > 1$$

**归纳论证**：
- 使用超覆盖（hypercovering）技术
- 将高维问题约化到低维情形

---

## 5. 应用与例子

### 5.1 具体计算

**例子 5.1.1**（曲线的上同调）
设 $C$ 是代数闭域 $k$ 上的光滑射影曲线，亏格为 $g$。

对于常值层 $\mathbb{Z}/n\mathbb{Z}$（$n$ 与 $\text{char}(k)$ 互素）：

| $q$ | $H^q_{\text{ét}}(C, \mathbb{Z}/n\mathbb{Z})$ |
|-----|------------------------------------------|
| 0 | $\mathbb{Z}/n\mathbb{Z}$ |
| 1 | $(\mathbb{Z}/n\mathbb{Z})^{2g}$ |
| 2 | $\mathbb{Z}/n\mathbb{Z}$ |
| $\geq 3$ | $0$ |

### 5.2 Weil猜想中的应用

Étale上同调在Weil猜想的证明中发挥核心作用：

- **Lefschetz不动点公式**：用于计算Frobenius的不动点数
- **Poincaré对偶**：建立上同调群之间的完美配对
- **Riemann假设**：通过特征值的估计实现

### 5.3 算术应用

**应用 5.3.1**（Brauer群）
对于域 $k$，有同构：

$$\text{Br}(k) \cong H^2_{\text{ét}}(\text{Spec}(k), \mathbb{G}_m)$$

这联系了中心单代数的理论与上同调。

---

## 6. 与其他概念的关系

### 6.1 上同调理论的比较

```
                    Étale上同调
                         │
         ┌───────────────┼───────────────┐
         │               │               │
         ▼               ▼               ▼
  Zariski上同调    晶体上同调      奇异上同调
  (更粗糙)         (p-进情形)      (复几何)
         │               │               │
         └───────────────┴───────────────┘
                         │
                    动机上同调
                  (统一理论)
```

### 6.2 与平展上同调的关系

- **平展上同调**（Flat Cohomology）：处理更一般的群概形
- **Étale上同调**：平展上同调的特例（对于光滑群概形）

### 6.3 导出范畴视角

在导出范畴 $D^+(X_{\text{ét}})$ 中：
- $R\Gamma(X, -)$ 是整体截面的导出函子
- $Rf_*$ 是高阶直像函子
- 存在六种Grothendieck运算的完整形式

---

## 7. 参考文献

### 7.1 原始文献

1. **Grothendieck, A.** (1960s). *SGA 4: Théorie des topos et cohomologie étale des schémas*
   - Séminaire de Géométrie Algébrique du Bois-Marie
   - Étale上同调的基础文献

2. **Deligne, P.** (1977). *SGA 4½: Cohomologie étale*
   - 更简洁的处理方式
   - 包含Weil猜想的证明

### 7.2 教科书

3. **Milne, J.S.** (1980). *Étale Cohomology*
   - Princeton University Press
   - 标准参考书

4. **Tamme, G.** (1994). *Introduction to Étale Cohomology*
   - Springer Universitext
   - 入门友好

### 7.3 在线资源

5. **Stacks Project**: [Tag 03QP](https://stacks.math.columbia.edu/tag/03QP)
6. **Kerodon**: [Étale Cohomology](https://kerodon.net/)

---

## 8. 相关Tags

### 8.1 直接相关

| Tag | 主题 | 关系 |
|-----|------|------|
| [03QU](#tag-03qu) | Étale上同调的函子性 | 后继结果 |
| [03QY](#tag-03qy) | Étale上同调与极限交换 | 技术工具 |
| [03T0](#tag-03t0) | 适当基变换定理 | 核心定理 |
| [03T3](#tag-03t3) | 光滑基变换 | 相关技术 |

### 8.2 进阶主题

| Tag | 主题 | 说明 |
|-----|------|------|
| [0F11](#tag-0f11) | 黎曼-希尔伯特对应 | $\ell$-进理论 |
| [0F12](#tag-0f12) | 权重理论 | Deligne理论 |
| [0F13](#tag-0f13) | 交截上同调 | 奇异情形 |

### 8.3 前置知识

| Tag | 主题 | 说明 |
|-----|------|------|
| [02FE](#tag-02fe) | 位形与层论 | 基础概念 |
| [00UZ](#tag-00uz) | 导出函子 | 同调代数 |
| [01FQ](#tag-01fq) | 概形基础 | 几何背景 |

---

## 附录：符号说明

| 符号 | 含义 |
|------|------|
| $X_{\text{ét}}$ | Étale位形 |
| $H^q_{\text{ét}}$ | Étale上同调群 |
| $\mathcal{F}, \mathcal{G}$ | 层（通常指Abel群层） |
| $R^q f_*$ | 高阶直像函子 |
| $\mathbb{Z}/n\mathbb{Z}$ | 常值层 |
| $\mathbb{G}_m$ | 乘法群层 |

---

*本文档由FormalMath项目生成，最后更新：2026-04-10*
