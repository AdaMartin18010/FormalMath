---
msc_primary: 00A99
msc_secondary:
  - 97A99
---

# Stacks Project Tag 0F1A - p进Hodge理论基础

## 1. 基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 0F1A |
| **英文名称** | Foundations of p-adic Hodge Theory |
| **所属章节** | p-adic Hodge Theory |
| **主题分类** | 算术几何 - p进霍奇理论 |
| **创建日期** | 2026-04-10 |
| **版本** | v1.0 |

---

## 2. 核心概念与定义

### 2.1 历史背景与动机

**p进Hodge理论**是研究p进域上代数簇的「p进」与「算术」性质之间深刻联系的数学分支。它起源于Tate在1960年代对p进域上椭圆曲线的研究，旨在建立p进表示与微分形式之间的对应。

**核心问题**：设 $K/\mathbb{Q}_p$ 是p进域，$X/K$ 是光滑真概形，如何理解étale上同调群 $H^n_{\text{ét}}(X_{\bar{K}}, \mathbb{Q}_p)$ 的几何信息？

### 2.2 基本周期环

**定义 2.2.1**（p进复数域 $\mathbb{C}_p$）
$p$进复数域定义为代数闭包 $\overline{\mathbb{Q}}_p$ 的完备化：
$$\mathbb{C}_p := \widehat{\overline{\mathbb{Q}}}_p$$
它是代数闭的、完备的、非阿基米德赋值域。

**定义 2.2.2**（基本周期环 $\mathbb{B}_{\text{dR}}$）
de Rham周期环是Fontaine构造的离散赋值环：
$$\mathbb{B}_{\text{dR}}^+ := \varprojlim_n W(R)[1/p]/(\ker\theta)^n$$
其中 $R$ 是完美胚环，$\theta: W(R) \to \mathcal{O}_{\mathbb{C}_p}$ 是Fontaine映射。

**定义 2.2.3**（Hodge-Tate周期环）
$$\mathbb{B}_{\text{HT}} := \bigoplus_{n \in \mathbb{Z}} \mathbb{C}_p(n)$$
其中 $\mathbb{C}_p(n)$ 是Tate扭动。

**定义 2.2.4**（晶体周期环 $\mathbb{B}_{\text{cris}}$）
$$\mathbb{B}_{\text{cris}}^+ := \{\sum_{n=0}^\infty a_n \frac{\omega^n}{n!} : a_n \in W(R)[1/p] \to 0\}$$
带有Frobenius作用 $\varphi$ 和Filtration。

**定义 2.2.5**（半稳定周期环 $\mathbb{B}_{\text{st}}$）
$$\mathbb{B}_{\text{st}} := \mathbb{B}_{\text{cris}}[t]$$
其中 $t$ 是形式变量，对应单值化作用。

### 2.3 p进表示的分类

**定义 2.3.1**（de Rham表示）
$p$进Galois表示 $V$ 称为**de Rham**的，如果：
$$\dim_K D_{\text{dR}}(V) = \dim_{\mathbb{Q}_p} V$$
其中 $D_{\text{dR}}(V) := (\mathbb{B}_{\text{dR}} \otimes_{\mathbb{Q}_p} V)^{G_K}$。

**定义 2.3.2**（半稳定表示）
$V$ 称为**半稳定**（semistable）的，如果：
$$\dim_K D_{\text{st}}(V) = \dim_{\mathbb{Q}_p} V$$
其中 $D_{\text{st}}(V) := (\mathbb{B}_{\text{st}} \otimes_{\mathbb{Q}_p} V)^{G_K}$。

**定义 2.3.3**（晶体表示）
$V$ 称为**晶体**（crystalline）的，如果：
$$\dim_K D_{\text{cris}}(V) = \dim_{\mathbb{Q}_p} V$$
其中 $D_{\text{cris}}(V) := (\mathbb{B}_{\text{cris}} \otimes_{\mathbb{Q}_p} V)^{G_K}$。

### 2.4 $(\varphi, \Gamma)$-模

**定义 2.4.1**（Robba环）
$$\mathcal{R} := \{\sum_{n \in \mathbb{Z}} a_n X^n : a_n \in K, \text{收敛于 } 0 < |X| < 1\}$$

**定义 2.4.2**（$(\varphi, \Gamma)$-模）
有限自由 $\mathcal{R}$-模 $D$ 配备：
- Frobenius $\varphi: D \to D$（半线性）
- $\Gamma = \text{Gal}(K(\zeta_{p^\infty})/K)$ 连续作用
满足相容性条件。

**定理 2.4.3**（Fontaine, Cherbonnier-Colmez）
存在范畴等价：
$$\{\text{连续 } p\text{进表示}\} \cong \{\text{étale } (\varphi, \Gamma)\text{-模}\}$$

---

## 3. 主要结果与定理

### 3.1 de Rham比较同构

**定理 3.1.1**（Tag 0F1A - p进Hodge理论基础）
设 $X/K$ 是光滑真概形，则存在自然的 $G_K$-等变同构：
$$H^n_{\text{ét}}(X_{\bar{K}}, \mathbb{Q}_p) \otimes_{\mathbb{Q}_p} \mathbb{B}_{\text{dR}} \cong H^n_{\text{dR}}(X/K) \otimes_K \mathbb{B}_{\text{dR}}$$

**推论 3.1.2**（Hodge-Tate分解）
$$H^n_{\text{ét}}(X_{\bar{K}}, \mathbb{Q}_p) \otimes_{\mathbb{Q}_p} \mathbb{C}_p \cong \bigoplus_{i+j=n} H^i(X, \Omega^j_{X/K}) \otimes_K \mathbb{C}_p(-j)$$

### 3.2 晶体比较同构

**定理 3.2.1**（Fontaine-Messing, Faltings, Tsuji）
若 $X$ 有光滑模型 $\mathcal{X}$ 于 $W(k)$，则：
$$H^n_{\text{ét}}(X_{\bar{K}}, \mathbb{Q}_p) \otimes_{\mathbb{Q}_p} \mathbb{B}_{\text{cris}} \cong H^n_{\text{cris}}(\mathcal{X}_k/W(k))[1/p] \otimes_{K_0} \mathbb{B}_{\text{cris}}$$

### 3.3 半稳定比较同构

**定理 3.3.1**（Tsuji, Niziol）
对于一般光滑真簇：
$$H^n_{\text{ét}}(X_{\bar{K}}, \mathbb{Q}_p) \otimes_{\mathbb{Q}_p} \mathbb{B}_{\text{st}} \cong H^n_{\text{st}}(X) \otimes_{K} \mathbb{B}_{\text{st}}$$
其中 $H^n_{\text{st}}(X)$ 是半稳定上同调。

### 3.4 阿贝尔簇的特殊情形

**定理 3.4.1**（Tate, de Shalit）
对于阿贝尔簇 $A/K$，有：
$$H^1_{\text{ét}}(A_{\bar{K}}, \mathbb{Q}_p) \cong V_p(A) := T_p(A) \otimes_{\mathbb{Z}_p} \mathbb{Q}_p$$
这是p进Tate模的张量积。

---

## 4. 证明思路

### 4.1 周期环的构造

**步骤1**：完美胚环 $R$
$$R := \varprojlim_{x \mapsto x^p} \mathcal{O}_{\mathbb{C}_p}/p$$
这是特征 $p$ 的完备赋值完美环。

**步骤2**：Witt向量
$$W(R) = \text{Witt vectors of } R$$
带有Frobenius提升 $\varphi$。

**步骤3**：Fontaine映射
$$\theta: W(R) \to \mathcal{O}_{\mathbb{C}_p}, \quad (x_0, x_1, \ldots) \mapsto \sum_{n=0}^\infty p^n x_n^{(n)}$$

**步骤4**：完备化得 $\mathbb{B}_{\text{dR}}^+$

### 4.2 比较同构的证明策略

**策略**：使用Poincaré引理的p进类比

1. ** pro-étale拓扑**（Bhatt-Scholze）
2. **结构层**的完备化
3. **微分形式的p进完成**

### 4.3 关键引理

**引理 4.3.1**（几乎纯性）
对于有限平坦群概形 $G$，几乎序列：
$$0 \to G(\mathcal{O}_{\bar{K}}) \to G(\mathbb{C}_p) \to \text{Lie}(G) \otimes \mathbb{C}_p/G(\mathcal{O}_{\bar{K}}) \to 0$$

---

## 5. 应用与例子

### 5.1 椭圆曲线的p进周期

**例子 5.1.1**
设 $E/K$ 是椭圆曲线，$\omega$ 是不变微分形式，$\eta$ 是对偶周期。

p进周期积分为：
$$\int_\gamma \omega \in \mathbb{B}_{\text{dR}}$$
满足Legendre关系。

### 5.2 Fermat曲线的Hodge-Tate权

**例子 5.1.2**
对于 $X: x^n + y^n = z^n$，$H^1$ 的Hodge-Tate权由Jacobi和决定：
$$\text{HT weights} = \left\{\frac{a}{n} + \frac{b}{n} : a+b < n\right\}$$

### 5.3 模形式的p进L-函数

**应用 5.3.1**（p进Langlands纲领）
p进Hodge理论是p进局部Langlands对应的核心工具：
$$\{\text{p进表示}\} \longleftrightarrow \{\text{p进自守形式}\}$$

### 5.4 有理点判定

**应用 5.4.1**（Kim的Chabauty方法）
结合p进Hodge理论与Tannaka理论，给出曲线有理点的新算法。

---

## 6. 与其他概念的关系

### 6.1 经典Hodge理论的p进类比

| 经典Hodge理论 | p进Hodge理论 |
|--------------|-------------|
| $\mathbb{C}$ | $\mathbb{C}_p$ |
| Betti上同调 | étale上同调 |
| de Rham上同调 | p进de Rham上同调 |
| Hodge分解 | Hodge-Tate分解 |
| 周期积分 | p进周期积分 |
| Hodge结构 | $(\varphi, N)$-模 |

### 6.2 理论演进图

```
    Tate的p进除子理论 (1967)
            │
            ▼
    Fontaine的周期环 (1979-1982)
            │
            ▼
    晶体比较定理 (Faltings, Tsuji)
            │
            ▼
    $(\varphi, \Gamma)$-模理论
            │
            ▼
    Bhatt-Morrow-Scholze: p进Hodge理论的
    完美胚空间方法 (2018)
```

### 6.3 与完美胚理论的联系

**定理 6.3.1**（Bhatt-Morrow-Scholze）
在完美胚框架下，周期环有更自然的构造：
$$\mathbb{A}_{\text{inf}} := W(\mathcal{O}^\flat_{\mathbb{C}_p})$$

### 6.4 与棱镜上同调的关系

**展望 6.4.1**
p进Hodge理论是棱镜上同调在光滑情形下的特例：
$$\text{Prismatic cohomology} \leadsto \text{All comparison theorems}$$

---

## 7. 参考文献

### 7.1 奠基文献

1. **Tate, J.** (1967). *p-divisible groups*
   - Proc. Conf. Local Fields, Driebergen
   - 开创性工作

2. **Fontaine, J.-M.** (1982). *Sur certains types de représentations p-adiques du groupe de Galois d'un corps local*
   - 周期环的系统构造

3. **Fontaine, J.-M.** (1994). *Le corps des périodes p-adiques*
   - Astérisque 223
   - 全面综述

### 7.2 比较定理

4. **Faltings, G.** (1988). *p-adic Hodge theory*
   - J. Amer. Math. Soc.
   - 几乎纯性方法

5. **Tsuji, T.** (1999). *p-adic étale cohomology and crystalline cohomology*
   - Ann. Sci. Éc. Norm. Sup.
   - 半稳定比较

6. **Niziol, W.** (2008). *Semistable conjecture via K-theory*
   - Duke Math. J.

### 7.3 现代发展

7. **Bhatt, B., Morrow, M., Scholze, P.** (2018). *Integral p-adic Hodge theory*
   - Publ. Math. IHÉS
   - 完美胚方法

8. **Bhatt, B., Scholze, P.** (2019). *Prisms and prismatic cohomology*
   - 统一框架

9. **Colmez, P.** (2008). *Représentations triangulines de dimension 2*
   - $(\varphi, \Gamma)$-模

### 7.4 在线资源

10. **Stacks Project**: [Tag 0F1A](https://stacks.math.columbia.edu/tag/0F1A)
11. **Berkeley Lecture Notes**: Scholze的p进Hodge理论讲义

---

## 8. 相关Tags

### 8.1 直接相关

| Tag | 主题 | 关系 |
|-----|------|------|
| [0F1B](#tag-0f1b) | p进比较定理 | 核心定理 |
| [0B2C](#tag-0b2c) | 完美胚空间 | 现代基础 |
| [0B2D](#tag-0b2d) | 完美胚与倾斜 | 关键技术 |

### 8.2 周期环

| Tag | 主题 | 说明 |
|-----|------|------|
| [0F1C](#tag-0f1c) | $\mathbb{B}_{\text{dR}}$ 构造 | de Rham环 |
| [0F1D](#tag-0f1d) | $\mathbb{B}_{\text{cris}}$ 性质 | 晶体环 |
| [0F1E](#tag-0f1e) | $(\varphi, \Gamma)$-模 | 等价理论 |

### 8.3 应用主题

| Tag | 主题 | 说明 |
|-----|------|------|
| [0F1F](#tag-0f1f) | p进Langlands对应 | 数论应用 |
| [0F1G](#tag-0f1g) | p进L-函数 | Iwasawa理论 |
| [0BS6](#tag-0bs6) | 棱镜上同调 | 统一框架 |

---

## 附录：前沿性说明

### A.1 为什么这是前沿？

1. **2018年突破**：Bhatt-Morrow-Scholze的积分p进Hodge理论解决了Fontaine的百年难题

2. **棱镜革命**：棱镜上同调（2019）提供了p进Hodge理论的统一框架

3. **Langlands应用**：p进局部Langlands对应是当今最活跃的数论方向

### A.2 待解决问题

- **Fontaine-Lafaille猜想**（部分已解决）
- **局部-整体兼容性**
- **高维Abel簇的完整理论**

### A.3 Lean4形式化现状

| 组件 | 状态 | 难度 |
|------|------|------|
| p进数 $\mathbb{Q}_p$ | ✅ 基础 | ★★☆ |
| 周期环 | ❌ 待建设 | ★★★★★ |
| 比较同构 | ❌ 待建设 | ★★★★★ |
| 完美胚 | 🔄 进行中 | ★★★★☆ |
| 棱镜上同调 | ❌ 待建设 | ★★★★★ |

---

*本文档由FormalMath项目生成，最后更新：2026-04-10*
