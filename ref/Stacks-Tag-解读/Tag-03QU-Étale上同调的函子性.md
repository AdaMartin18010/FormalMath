---
msc_primary: 00A99
msc_secondary:
  - 97A99
---

# Stacks Project Tag 03QU - Étale上同调的函子性

## 1. 基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 03QU |
| **英文名称** | Étale Cohomology - Functoriality |
| **所属章节** | Theorem on Formal Functions |
| **主题分类** | 代数几何 - 上同调函子性 |
| **创建日期** | 2026-04-10 |
| **版本** | v1.0 |

---

## 2. 核心概念与定义

### 2.1 函子性概述

**函子性**（Functoriality）是上同调理论的核心特征，描述了上同调群如何随概形的态射而变化。Étale上同调具有丰富而微妙的函子性结构。

### 2.2 关键定义

**定义 2.2.1**（逆像函子）
设 $f: X \to Y$ 是概形态射，**逆像函子** $f^{-1}: \text{Ab}(Y_{\text{ét}}) \to \text{Ab}(X_{\text{ét}})$ 定义为：

$$(f^{-1}\mathcal{G})(U) = \text{colim}_{V} \mathcal{G}(V)$$

其中极限取遍所有满足 $f(U) \subseteq V$ 的交换图。

**定义 2.2.2**（逆像层 $f^*$）
对于Abel群层，**逆像层**定义为：

$$f^*\mathcal{G} := f^{-1}\mathcal{G} \otimes_{f^{-1}\mathcal{O}_Y} \mathcal{O}_X$$

**定义 2.2.3**（正像函子）
**正像函子** $f_*: \text{Ab}(X_{\text{ét}}) \to \text{Ab}(Y_{\text{ét}})$ 定义为：

$$(f_*\mathcal{F})(V) := \mathcal{F}(X \times_Y V)$$

### 2.3 伴随关系

**命题 2.3.1**
$(f^{-1}, f_*)$ 构成伴随对：

$$\text{Hom}_{X_{\text{ét}}}(f^{-1}\mathcal{G}, \mathcal{F}) \cong \text{Hom}_{Y_{\text{ét}}}(\mathcal{G}, f_*\mathcal{F})$$

---

## 3. 主要结果与定理

### 3.1 基本函子性定理

**定理 3.1.1**（Tag 03QU）
Étale上同调的函子性满足以下性质：

**(a) 复合性**
对于 $X \xrightarrow{f} Y \xrightarrow{g} Z$，有：

$$(g \circ f)^{-1} \cong f^{-1} \circ g^{-1}, \quad (g \circ f)_* \cong g_* \circ f_*$$

**(b) 高阶直像的长正合序列**
对于短正合序列 $0 \to \mathcal{F}' \to \mathcal{F} \to \mathcal{F}'' \to 0$，有长正合序列：

$$\cdots \to R^q f_*\mathcal{F}' \to R^q f_*\mathcal{F} \to R^q f_*\mathcal{F}'' \to R^{q+1}f_*\mathcal{F}' \to \cdots$$

**(c) 导出伴随**
$(Lf^*, Rf_*)$ 在导出范畴中形成伴随：

$$\text{Hom}_{D(X_{\text{ét}})}(Lf^*\mathcal{G}^\bullet, \mathcal{F}^\bullet) \cong \text{Hom}_{D(Y_{\text{ét}})}(\mathcal{G}^\bullet, Rf_*\mathcal{F}^\bullet)$$

### 3.2 特殊态射的性质

**定理 3.2.1**（适当态射）
设 $f: X \to Y$ 是**适当**（proper）态射，则：

**(i)** $R^q f_*$ 保持凝聚性（对于凝聚层）

**(ii)** 高阶直像与基变换交换（在特定条件下）

**(iii)** 纤维上的上同调控制整体性质

**定理 3.2.2**（平滑态射）
设 $f: X \to Y$ 是**光滑**（smooth）态射，则：

**(i)** $R^q f_*$ 与基变换交换

**(ii)** 存在相对Poincaré对偶

**(iii)** 局部上同调由纤维决定

### 3.3 Leray谱序列

**定理 3.3.1**
对于 $X \xrightarrow{f} Y \to \text{Spec}(k)$，存在**Leray谱序列**：

$$E_2^{p,q} = H^p_{\text{ét}}(Y, R^q f_*\mathcal{F}) \Rightarrow H^{p+q}_{\text{ét}}(X, \mathcal{F})$$

这允许通过纤维的上同调计算整体的上同调。

---

## 4. 证明思路

### 4.1 逆像函子的构造

**步骤1**：预层构造
- 对预层 $\mathcal{G}$，定义 $f_p\mathcal{G}(U) = \text{colim} \mathcal{G}(V)$
- 验证这是良定义的预层

**步骤2**：层化
- 对预层进行层化得到 $f^{-1}\mathcal{G} = (f_p\mathcal{G})^+$
- 验证层化保持所需性质

### 4.2 高阶直像的存在性

**关键观察**：
- $f_*$ 是左正合函子（作为左伴随的右伴随）
- Abel群层的范畴有足够的内射对象
- 因此可以定义右导出函子 $R^q f_*$

**技术引理**：
内射层在 $f_*$ 下的像不一定是内射的，需要**flasque**或**柔软**层的介入。

### 4.3 适当基变换的证明

**Cartan-Serre方法**：
1. 约化到仿射情形
2. 使用Čech上同调计算
3. 应用Noetherian归纳法
4. 利用适当态射的紧性性质

---

## 5. 应用与例子

### 5.1 纤维化的上同调计算

**例子 5.1.1**（纤维化曲面）
设 $f: S \to C$ 是纤维化曲面，纤维亏格为 $g$。

则Leray谱序列给出：

$$E_2^{p,q} = H^p_{\text{ét}}(C, R^q f_*\mathbb{Q}_\ell) \Rightarrow H^{p+q}_{\text{ét}}(S, \mathbb{Q}_\ell)$$

其中 $R^1 f_*\mathbb{Q}_\ell$ 对应于Jacobian的Tate模。

### 5.2 平展下降

**例子 5.2.1**（下降上同调类）
设 $\{U_i \to X\}$ 是Étale覆盖，$
abla$ 是下降数据。

函子性允许我们将 $X$ 上的上同调类与覆盖上的相容系统等同：

$$H^q_{\text{ét}}(X, \mathcal{F}) \cong \check{H}^q(\{U_i\}, \mathcal{F})$$

### 5.3 Galois上同调

**应用 5.3.1**（谱序列退化）
对于域扩张 $L/K$ 和 $G = \text{Gal}(L/K)$，有：

$$H^p(G, H^q_{\text{ét}}(X_L, \mathcal{F})) \Rightarrow H^{p+q}_{\text{ét}}(X, \mathcal{F})$$

这联系了Galois上同调与几何上同调。

### 5.4 动机实现

**例子 5.4.1**（交截上同调）
对于奇异簇的交截上同调，$Rf_*$ 的分解定理给出：

$$Rf_*\text{IC}_X \cong \bigoplus_i \text{IC}_{Y_i}(\mathcal{L}_i)[d_i]$$

这是Weil猜想证明的关键步骤。

---

## 6. 与其他概念的关系

### 6.1 与导出范畴的融合

```
    经典上同调              导出范畴语言
         │                        │
         ▼                        ▼
    H^q(X, F)            RΓ(X, F^•) ∈ D(Ab)
         │                        │
         │     ┌──────────────────┘
         │     │
         ▼     ▼
    R^q f_* F            Rf_* F^• ∈ D(Y)
         │                        │
         └────────┬───────────────┘
                  ▼
           六种Grothendieck运算
```

### 6.2 与D-模理论的联系

- **Riemann-Hilbert对应**：$Rf_*$ 对应于 $D$-模的解复形的直像
- **de Rham上同调**：$Rf_*$ 在de Rham情形对应于相对de Rham上同调

### 6.3 与算术几何的联系

| 几何概念 | 算术类比 |
|---------|---------|
| $Rf_*\mathbb{Q}_\ell$ | $\ell$-进表示 |
| 局部单值群 | Galois表示 |
| 高阶直像的茎 | 上同调的纤维 |

---

## 7. 参考文献

### 7.1 原始文献

1. **Grothendieck, A.** (1960s). *SGA 4: Théorie des topos et cohomologie étale des schémas*
   - 函子性的系统发展

2. **Deligne, P.** (1977). *SGA 4½: Cohomologie étale*
   - 简洁且完整的处理

3. **Deligne, P.** (1980). *La conjecture de Weil II*
   - Pub. Math. IHÉS 52
   - 权重理论的建立

### 7.2 现代参考

4. **Milne, J.S.** (1980). *Étale Cohomology*
   - 第III-V章

5. **Kashiwara, M. & Schapira, P.** (1990). *Sheaves on Manifolds*
   - 导出范畴的视角

### 7.3 在线资源

6. **Stacks Project**: [Tag 03QU](https://stacks.math.columbia.edu/tag/03QU)
7. **Kerodon**: [Cohomology](https://kerodon.net/)

---

## 8. 相关Tags

### 8.1 直接相关

| Tag | 主题 | 关系 |
|-----|------|------|
| [03QP](#tag-03qp) | Étale上同调基础 | 前置知识 |
| [03QY](#tag-03qy) | 上同调与极限 | 技术工具 |
| [03T0](#tag-03t0) | 适当基变换 | 核心应用 |
| [0D4T](#tag-0d4t) | 光滑基变换 | 对偶结果 |

### 8.2 进阶主题

| Tag | 主题 | 说明 |
|-----|------|------|
| [0F1N](#tag-0f1n) | 附近循环函子 | 单值群理论 |
| [0F1P](#tag-0f1p) | 消失循环函子 | 奇异纤维分析 |
| [0F1Q](#tag-0f1q) | 分解定理 | 交截上同调 |

### 8.3 应用实例

| Tag | 主题 | 说明 |
|-----|------|------|
| [0A3R](#tag-0a3r) | Weil猜想 | 原始动机 |
| [0A3S](#tag-0a3s) | Lefschetz不动点 | 计数应用 |
| [0A3T](#tag-0a3t) | 黎曼假设 | 特征值估计 |

---

## 附录：关键公式速查

| 公式 | 名称 | 说明 |
|------|------|------|
| $(g \circ f)_* = g_* \circ f_*$ | 正像复合 | 协变函子性 |
| $(g \circ f)^{-1} = f^{-1} \circ g^{-1}$ | 逆像复合 | 反变函子性 |
| $\text{Hom}(f^{-1}\mathcal{G}, \mathcal{F}) \cong \text{Hom}(\mathcal{G}, f_*\mathcal{F})$ | 伴随性 | 核心关系 |
| $E_2^{p,q} = H^p(Y, R^q f_*\mathcal{F}) \Rightarrow H^{p+q}(X, \mathcal{F})$ | Leray谱序列 | 计算工具 |

---

*本文档由FormalMath项目生成，最后更新：2026-04-10*
