---
msc_primary: 00A99
msc_secondary:
  - 97A99
---

# Stacks Project Tag 0F1B - p进比较定理

## 1. 基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 0F1B |
| **英文名称** | p-adic Comparison Theorems |
| **所属章节** | p-adic Hodge Theory |
| **主题分类** | 算术几何 - 比较同构 |
| **创建日期** | 2026-04-10 |
| **版本** | v1.0 |

---

## 2. 核心概念与定义

### 2.1 比较定理的哲学

**核心问题**：如何统一理解同一个代数簇的不同上同调理论？

比较定理建立了p进域上代数簇的étale上同调与微分几何上同调之间的深刻联系，是算术几何的基石。

### 2.2 主要比较同构

**定义 2.2.1**（de Rham比较同构）
设 $X/K$ 光滑真，比较同构为：
$$\iota_{\text{dR}}: H^n_{\text{ét}}(X_{\bar{K}}, \mathbb{Q}_p) \otimes_{\mathbb{Q}_p} \mathbb{B}_{\text{dR}} \xrightarrow{\sim} H^n_{\text{dR}}(X/K) \otimes_K \mathbb{B}_{\text{dR}}$$

**定义 2.2.2**（晶体比较同构）
对好约化簇：
$$\iota_{\text{cris}}: H^n_{\text{ét}}(X_{\bar{K}}, \mathbb{Q}_p) \otimes_{\mathbb{Q}_p} \mathbb{B}_{\text{cris}} \xrightarrow{\sim} H^n_{\text{cris}}(\mathcal{X}_k/W(k)) \otimes_{K_0} \mathbb{B}_{\text{cris}}$$

**定义 2.2.3**（半稳定比较同构）
对半稳定约化簇：
$$\iota_{\text{st}}: H^n_{\text{ét}}(X_{\bar{K}}, \mathbb{Q}_p) \otimes_{\mathbb{Q}_p} \mathbb{B}_{\text{st}} \xrightarrow{\sim} H^n_{\text{st}}(X/K) \otimes_K \mathbb{B}_{\text{st}}$$

### 2.3 比较同构的性质

**定义 2.3.1**（Galois等变性）
比较同构 $\iota$ 是 $G_K$-等变的，即与Galois群作用交换。

**定义 2.3.2**（Filtration保持）
de Rham比较保持Hodge filtration：
$$\text{Fil}^i H^n_{\text{dR}} \otimes \mathbb{B}_{\text{dR}} = \text{Fil}^i(H^n_{\text{ét}} \otimes \mathbb{B}_{\text{dR}})$$

**定义 2.3.3**（Frobenius等变性）
晶体比较与 $\varphi$ 交换：
$$\iota_{\text{cris}} \circ \varphi_{\text{ét}} = \varphi_{\text{cris}} \circ \iota_{\text{cris}}$$

### 2.4 积分比较

**定义 2.4.1**（积分p进Hodge理论）
Bhatt-Morrow-Scholze建立：
$$R\Gamma_{\mathfrak{S}}(X) \otimes^{\mathbb{L}}_{\mathfrak{S}} A_{\text{inf}} \cong R\Gamma_{\text{ét}}(X, \mathbb{Z}_p) \otimes^{\mathbb{L}}_{\mathbb{Z}_p} A_{\text{inf}}$$

---

## 3. 主要结果与定理

### 3.1 de Rham比较定理

**定理 3.1.1**（Tag 0F1B）
设 $X/K$ 是光滑真概形，则存在自然同构：
$$H^n_{\text{ét}}(X_{\bar{K}}, \mathbb{Q}_p) \otimes_{\mathbb{Q}_p} \mathbb{B}_{\text{dR}} \cong H^n_{\text{dR}}(X/K) \otimes_K \mathbb{B}_{\text{dR}}$$
满足：
- **Galois等变性**：与 $G_K$ 作用交换
- **Filtration保持**：$\text{Fil}^i$ 对应
- **维数守恒**：$\dim_{\mathbb{Q}_p} = \dim_K$

**推论 3.1.2**（Hodge-Tate分解）
存在 $G_K$-等变分级同构：
$$H^n_{\text{ét}}(X_{\bar{K}}, \mathbb{Q}_p) \otimes_{\mathbb{Q}_p} \mathbb{C}_p \cong \bigoplus_{i+j=n} H^j(X, \Omega^i_{X/K}) \otimes_K \mathbb{C}_p(-i)$$

### 3.2 晶体比较定理

**定理 3.2.1**（Faltings, Tsuji）
设 $X$ 有好约化模型 $\mathcal{X}/\mathcal{O}_K$，则：
$$H^n_{\text{ét}}(X_{\bar{K}}, \mathbb{Q}_p) \otimes_{\mathbb{Q}_p} \mathbb{B}_{\text{cris}} \cong H^n_{\text{cris}}(\mathcal{X}_k/W(k)) \otimes_{K_0} \mathbb{B}_{\text{cris}}$$

**推论 3.2.2**（Frobenius本征值）
Frobenius在 $H^n_{\text{cris}}$ 上的本征值是代数整数，且满足Archimedean估值条件。

### 3.3 半稳定比较定理

**定理 3.3.1**（Tsuji, Niziol）
对半稳定约化簇，存在同构：
$$H^n_{\text{ét}}(X_{\bar{K}}, \mathbb{Q}_p) \otimes_{\mathbb{Q}_p} \mathbb{B}_{\text{st}} \cong H^n_{\text{st}}(X/K) \otimes_K \mathbb{B}_{\text{st}}$$
兼容 $\varphi, N$ 和 filtration结构。

**推论 3.3.2**（单值化定理）
单值算子 $N$ 确定退化行为：
$$N \text{ 幂零} \Leftrightarrow \text{一致收敛}$$

### 3.4 统一比较定理

**定理 3.4.1**（Bhatt-Morrow-Scholze, 2018）
存在导出范畴中的比较同构：
$$R\Gamma_{\mathfrak{S}}(X) \cong R\Gamma_{\text{ét}}(X, \mathbb{Z}_p) \otimes^{\mathbb{L}}_{\mathbb{Z}_p} \mathfrak{S}$$

这统一了所有经典比较定理。

---

## 4. 证明思路

### 4.1 经典证明路线

**步骤1**：几乎纯性（Almost Purity）
- Fontaine的几乎 étale 扩张理论
- Faltings的几乎纯性定理

**步骤2**：Poincaré引理
- p进版本的de Rham复形
- 使用pro-étale拓扑

**步骤3**：下降论证
- 从通用情形下降到具体簇
- 使用适当的纤维积

### 4.2 Bhatt-Morrow-Scholze方法

**创新点**：使用完美胚空间和棱镜上同调

**步骤1**：构造棱镜上同调 $R\Gamma_{\mathfrak{S}}(X)$

**步骤2**：证明 $A_{\text{inf}}$-比较

**步骤3**：通过模不同理想得到经典比较

### 4.3 关键技术

**引理 4.3.1**（忠实平坦下降）
映射 $A_{\text{inf}} \to \mathbb{B}_{\text{dR}}^+$ 忠实平坦。

**引理 4.3.2**（几乎数学）
在几乎数学框架下，很多精确序列变得分裂。

---

## 5. 应用与例子

### 5.1 Tate曲线

**例子 5.1.1**
设 $E_q = \mathbb{G}_m/q^{\mathbb{Z}}$ 是Tate曲线，$q \in K^\times$，$|q| < 1$。

比较同构明确给出：
$$H^1_{\text{ét}}(E_q, \mathbb{Q}_p) \cong \text{Hom}(q^{\mathbb{Z}}, \mathbb{Q}_p(1)) \oplus \mathbb{Q}_p$$

### 5.2 模曲线的比较

**例子 5.1.2**
对于模曲线 $X(N)/\mathbb{Q}_p$，比较定理给出：
$$H^1_{\text{ét}}(X(N)_{\overline{\mathbb{Q}}_p}, \mathbb{Q}_p) \cong \bigoplus_{f} V_f$$
其中 $V_f$ 是模形式 $f$ 的p进Galois表示。

### 5.3 代数循环的p进Hodge猜想

**应用 5.3.1**（Tate猜想）
比较定理蕴含Tate猜想的p进版本：
$$\text{NS}(X) \otimes \mathbb{Q}_p \cong H^2_{\text{ét}}(X_{\bar{K}}, \mathbb{Q}_p(1))^{G_K}$$

### 5.4 Iwasawa理论

**应用 5.4.1**（Bloch-Kato猜想）
比较定理是证明Bloch-Kato指数公式的关键工具。

---

## 6. 与其他概念的关系

### 6.1 各种上同调理论的统一

```
        Étale上同调
              │
              │ 比较同构
              ▼
    ┌─────────┴─────────┐
    │                   │
    ▼                   ▼
de Rham上同调    晶体上同调
    │                   │
    │ 退化              │ Frobenius
    ▼                   ▼
Hodge上同调      牛顿多边形
```

### 6.2 与经典Hodge理论的对比

| 特征 | 经典Hodge理论 | p进比较定理 |
|------|--------------|------------|
| 基域 | $\mathbb{C}$ | $p$进域 $K$ |
| Betti上同调 | $H^n(X^{\text{an}}, \mathbb{Z})$ | $H^n_{\text{ét}}(X, \mathbb{Z}_p)$ |
| 周期环 | $\mathbb{C}$ | $\mathbb{B}_{\text{dR}}$ |
| 比较类型 | 解析-代数 | Galois-微分 |
| 工具 | 调和形式 | 几乎纯性 |

### 6.3 与动机理论的关联

**联系**：比较定理是构造混合动机的关键
$$H^n_{\mathcal{M}}(X) := \text{系统 } (H^n_{\text{ét}}, H^n_{\text{dR}}, H^n_{\text{cris}}, \text{比较})$$

### 6.4 导出几何视角

**现代观点**：比较同构在导出代数几何中更自然
$$R\Gamma_{\text{ét}}(X) \in D(\mathbb{Z}_p), \quad R\Gamma_{\text{dR}}(X) \in D(K)$$
比较是导出范畴的等价。

---

## 7. 参考文献

### 7.1 经典文献

1. **Faltings, G.** (1988). *Crystalline cohomology and p-adic Galois-representations*
   - 几乎纯性方法

2. **Faltings, G.** (1989). *p-adic Hodge theory*
   - J. Amer. Math. Soc.

3. **Tsuji, T.** (1999). *p-adic étale cohomology and crystalline cohomology*
   - Ann. Sci. Éc. Norm. Sup.

### 7.2 积分理论

4. **Bhatt, B., Morrow, M., Scholze, P.** (2018). *Integral p-adic Hodge theory*
   - Publ. Math. IHÉS 128
   - 里程碑工作

5. **Bhatt, B., Scholze, P.** (2019). *Prisms and prismatic cohomology*
   - 统一框架

### 7.3 综述文献

6. **Brinon, O., Conrad, B.** (2009). *CMI Summer School notes on p-adic Hodge theory*
   - 优秀入门材料

7. **Moonen, B.** (2012). *From p-divisible groups to prismatic cohomology*
   - 历史发展

### 7.4 在线资源

8. **Stacks Project**: [Tag 0F1B](https://stacks.math.columbia.edu/tag/0F1B)
9. **Scholze's Notes**: Perfectoid Spaces and Applications

---

## 8. 相关Tags

### 8.1 直接相关

| Tag | 主题 | 关系 |
|-----|------|------|
| [0F1A](#tag-0f1a) | p进Hodge理论基础 | 前置理论 |
| [0B2C](#tag-0b2c) | 完美胚空间 | 现代工具 |
| [0BS6](#tag-0bs6) | 棱镜上同调 | 统一框架 |

### 8.2 周期环

| Tag | 主题 | 说明 |
|-----|------|------|
| [0F1C](#tag-0f1c) | $\mathbb{B}_{\text{dR}}$ | de Rham周期 |
| [0F1D](#tag-0f1d) | $\mathbb{B}_{\text{cris}}$ | 晶体周期 |
| [0F1E](#tag-0f1e) | $\mathbb{B}_{\text{st}}$ | 半稳定周期 |

### 8.3 应用

| Tag | 主题 | 说明 |
|-----|------|------|
| [0F1F](#tag-0f1f) | p进Langlands | 表示论应用 |
| [0F5A](#tag-0f5a) | 混合动机 | 哲学基础 |

---

## 附录：前沿性与形式化

### A.1 前沿性说明

**为什么这是前沿？**

1. **2018突破**：Bhatt-Morrow-Scholze的积分p进Hodge理论彻底改变了该领域

2. **棱镜革命**：所有比较定理成为棱镜上同调的特例

3. **数论应用**：p进Langlands对应、Iwasawa理论的核心工具

### A.2 未解决问题

- **Fontaine-Lafaille理论**的完全理解
- **p进局部Langlands**的完整对应
- **高维簇**的积分比较

### A.3 Lean4形式化现状

| 组件 | 状态 | 预计难度 |
|------|------|---------|
| 基本定义 | ❌ 待建设 | ★★★☆☆ |
| 周期环构造 | ❌ 待建设 | ★★★★★ |
| 比较同构陈述 | ❌ 待建设 | ★★★★☆ |
| 特殊情形证明 | ❌ 待建设 | ★★★★★ |
| 完整证明 | ❌ 待建设 | ★★★★★ |

---

*本文档由FormalMath项目生成，最后更新：2026-04-10*
