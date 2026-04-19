---
msc_primary: 00A99
msc_secondary:
  - 97A99
---

# Stacks Project Tag 07GI - 晶体上同调定义

## 1. 基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 07GI |
| **英文名称** | Crystalline Cohomology - Definition |
| **所属章节** | Crystalline Cohomology |
| **主题分类** | 代数几何 - $p$-进上同调 |
| **创建日期** | 2026-04-10 |
| **版本** | v1.0 |

---

## 2. 核心概念与定义

### 2.1 晶体上同调的动机

**晶体上同调**（Crystalline Cohomology）由Alexander Grothendieck在1966年提出，由Pierre Berthelot发展完善，旨在为特征 $p > 0$ 的概形提供一种"好"的上同调理论。

**动机问题**：
- 在特征 $p$ 域上，Étale上同调在 $p$ 处消失（$H^i_{\text{ét}}(X, \mathbb{Z}/p\mathbb{Z}) = 0$ 对于 $i > \dim X + 1$）
- 需要一种能捕捉 $p$ 进信息的上同调理论
- de Rham上同调在特征 $p$ 时"太小"

### 2.2 关键定义

**定义 2.2.1**（PD厚化）
设 $S$ 是概形，$\mathcal{I} \subseteq \mathcal{O}_S$ 是理想层。一个**PD结构**（divided power structure）在 $\mathcal{I}$ 上是映射 $\gamma_n: \mathcal{I} \to \mathcal{O}_S$（$n \geq 0$），满足：
- $\gamma_0(x) = 1$，$\gamma_1(x) = x$
- $\gamma_n(x)\gamma_m(x) = \binom{n+m}{n}\gamma_{n+m}(x)$
- $\gamma_n(x+y) = \sum_{i=0}^n \gamma_i(x)\gamma_{n-i}(y)$
- $\gamma_n(\gamma_m(x)) = \frac{(nm)!}{(m!)^n n!}\gamma_{nm}(x)$

**定义 2.2.2**（晶体位形）
设 $X$ 是特征 $p$ 的概形，$S$ 是PD概形。$X$ 相对于 $S$ 的**晶体位形**（Crystalline Site）$\text{Cris}(X/S)$ 定义如下：
- **对象**：$U \hookrightarrow T$，其中 $U \subseteq X$ 是Zariski开集，$T$ 是 $S$ 上的PD厚化
- **态射**：使得下图交换的相容映射
- **覆盖**：Zariski覆盖

**定义 2.2.3**（晶体层）
$\text{Cris}(X/S)$ 上的**晶体层**（Crystal of $\mathcal{O}_{X/S}$-modules）是一个层 $\mathcal{F}$ 满足：

对每个态射 $(U' \hookrightarrow T') \to (U \hookrightarrow T)$，自然映射
$$f^*\mathcal{F}_T \to \mathcal{F}_{T'}$$
是同构。

### 2.3 晶体上同调的定义

**定义 2.3.1**（晶体上同调）
对于晶体层 $\mathcal{F}$，其**晶体上同调群**定义为：

$$H^i_{\text{cris}}(X/S, \mathcal{F}) := H^i(\text{Cris}(X/S), \mathcal{F})$$

当 $S = \text{Spec}(W(k))$（$W(k)$ 是Witt向量环）时，简记为 $H^i_{\text{cris}}(X/W)$。

---

## 3. 主要结果与定理

### 3.1 基本性质定理

**定理 3.1.1**（Tag 07GI）
晶体上同调具有以下基本性质：

**(a) 有限性**
设 $X$ 是 $k$ 上光滑真概形，则 $H^i_{\text{cris}}(X/W)$ 是有限生成 $W$-模。

**(b) 正合性**
对于短正合序列 $0 \to \mathcal{F}' \to \mathcal{F} \to \mathcal{F}'' \to 0$，存在长正合序列：

$$\cdots \to H^i_{\text{cris}}(X/S, \mathcal{F}') \to H^i_{\text{cris}}(X/S, \mathcal{F}) \to H^i_{\text{cris}}(X/S, \mathcal{F}'') \to \cdots$$

**(c) 函子性**
对于 $f: X \to Y$，存在拉回映射：

$$f^*: H^i_{\text{cris}}(Y/S) \to H^i_{\text{cris}}(X/S)$$

### 3.2 结构定理

**定理 3.2.1**（Frobenius作用）
绝对Frobenius $F_X: X \to X$ 诱导**Frobenius同态**：

$$F^*: H^i_{\text{cris}}(X/W) \to H^i_{\text{cris}}(X/W)$$

这是 $\sigma$-线性的，其中 $\sigma: W \to W$ 是Witt向量的Frobenius。

**定理 3.2.2**（晶体结构）
$H^i_{\text{cris}}(X/W)$ 具有以下结构：

- 有限生成 $W$-模
- 带有 $\sigma$-线性Frobenius $F$
- 带有 $W$-线性Verschiebung $V$ 满足 $FV = VF = p$
- 非典范地：$H^i_{\text{cris}}(X/W) \cong W^r \oplus (W/p^{n_j})$（挠部分）

### 3.3 比较定理

**定理 3.3.1**（与de Rham的比较）
设 $X$ 是 $W$ 上的光滑真概形，$X_k$ 是特殊纤维，则：

$$H^i_{\text{cris}}(X_k/W) \otimes_W K \cong H^i_{\text{dR}}(X_K/K)$$

其中 $K = \text{Frac}(W)$。

---

## 4. 证明思路

### 4.1 PD包络的构造

**步骤1**：普适PD厚化
- 对浸入 $X \hookrightarrow Y$，构造PD包络 $D_X(Y)$
- 这是接收PD结构的普适对象

**步骤2**：局部描述
- 对于 $X = \text{Spec}(A)$，$Y = \text{Spec}(B)$
- $D_X(Y) = B[\{x^{[n]}\}_{n \geq 1, x \in I}]/\text{PD关系}$

### 4.2 de Rham复形的晶体解释

**关键观察**：
晶体上同调可以用de Rham复形计算：

$$H^i_{\text{cris}}(X/S) = H^i(X, \Omega^\bullet_{X/S})$$

其中 $\Omega^\bullet_{X/S}$ 是晶体层的de Rham复形。

### 4.3 有限性证明

**Cartan-Serre论证**：
1. 约化到射影情形
2. 使用Čech上同调
3. 证明 $R^i f_{\text{cris}*}$ 保持凝聚性

---

## 5. 应用与例子

### 5.1 基本计算

**例子 5.1.1**（仿射空间）
$$H^i_{\text{cris}}(\mathbb{A}^n_k/W) = \begin{cases} W & i = 0 \\ 0 & i > 0 \end{cases}$$

**例子 5.1.2**（射影直线）
$$H^i_{\text{cris}}(\mathbb{P}^1_k/W) = \begin{cases} W & i = 0, 2 \\ 0 & i = 1 \text{ 或 } i > 2 \end{cases}$$

### 5.2 超奇异椭圆曲线

**例子 5.2.1**
设 $E$ 是超奇异椭圆曲线（特征 $p > 0$），则：

$$H^1_{\text{cris}}(E/W) \cong D$$

其中 $D$ 是Dieudonné模，满足：
- 秩为2的 $W$-模
- $F^2 = p$，$V^2 = p$
- 这编码了曲线的 $p$-可除群

### 5.3 刚性上同调的联系

**应用 5.3.1**
对于开簇，晶体上同调推广为**刚性上同调**（Rigid Cohomology）：

$$H^i_{\text{rig}}(X/K) = H^i_{\text{cris}}(\bar{X}/W) \otimes K / H^i_{\text{cris}}((\bar{X} \setminus X)/W) \otimes K$$

这是特征 $p$ 上的Weil上同调理论。

### 5.4 p-进Hodge理论

**应用 5.4.1**
晶体上同调是$p$-进Hodge理论的核心：

- **$C_{\text{cris}}$-比较**：$H^i_{\text{ét}}(X_{\bar{K}}, \mathbb{Q}_p) \otimes B_{\text{cris}} \cong H^i_{\text{cris}}(X_k/W) \otimes B_{\text{cris}}$
- 这揭示了Galois表示与晶体结构的深刻联系

---

## 6. 与其他概念的关系

### 6.1 $p$-进上同调理论的谱系

```
               晶体上同调
                    │
         ┌──────────┼──────────┐
         │          │          │
         ▼          ▼          ▼
    de Rham上同调  刚性上同调   收敛上同调
    (提升存在时)   (开簇推广)   (Washauser)
         │          │          │
         └──────────┼──────────┘
                    ▼
              p-进Hodge理论
                    │
         ┌──────────┴──────────┐
         ▼                     ▼
    半稳定上同调            log-晶体上同调
    (C_st-理论)            (边界情形)
```

### 6.2 与Dieudonné理论的关系

对于 $p$-可除群 $G$，有等价：

$$\{p\text{-可除群}/k\} \longleftrightarrow \{\text{Dieudonné模}\}$$

$$G \longmapsto \mathbb{D}(G) = \text{Ext}^1_{\text{cris}}(\mathbf{1}, G)$$

晶体上同调提供了这个对应的几何实现。

### 6.3 与Witt向量上同调的关系

**Bloch-Deligne-Illusie理论**：
对于光滑真簇 $X/k$，存在：

$$H^i(X, W\Omega^\bullet) \cong H^i_{\text{cris}}(X/W)$$

其中 $W\Omega^\bullet$ 是de Rham-Witt复形。

---

## 7. 参考文献

### 7.1 奠基文献

1. **Grothendieck, A.** (1966). *Letter to Tate*
   - 晶体上同调的原始想法

2. **Berthelot, P.** (1974). *Cohomologie cristalline des schémas de caractéristique $p > 0$*
   - Springer Lecture Notes 407
   - 系统理论建立

3. **Berthelot, P. & Ogus, A.** (1978). *Notes on Crystalline Cohomology*
   - Princeton University Press
   - 简洁的入门书

### 7.2 发展文献

4. **Messing, W.** (1972). *The crystals associated to Barsotti-Tate groups*
   - Springer Lecture Notes 264
   - Dieudonné理论的联系

5. **Illusie, L.** (1979). *Complexe de de Rham-Witt et cohomologie cristalline*
   - Ann. Sci. Éc. Norm. Sup.
   - de Rham-Witt复形

### 7.3 现代应用

6. **Fontaine, J.-M.** (1982). *Formes différentielles et modules de Tate*
   - $p$-进Hodge理论

7. **Tsuji, T.** (1999). *$p$-adic Hodge theory*
   - 比较定理的证明

### 7.4 在线资源

8. **Stacks Project**: [Tag 07GI](https://stacks.math.columbia.edu/tag/07GI)
9. **Stacks Project**: Chapter "Crystalline Cohomology"

---

## 8. 相关Tags

### 8.1 直接相关

| Tag | 主题 | 关系 |
|-----|------|------|
| [07GJ](#tag-07gj) | 晶体上同调与de Rham | 比较定理 |
| [07L3](#tag-07l3) | de Rham-Witt复形 | 计算工具 |
| [07MK](#tag-07mk) | PD结构 | 基础定义 |

### 8.2 $p$-进上同调

| Tag | 主题 | 说明 |
|-----|------|------|
| [0F4P](#tag-0f4p) | 刚性上同调 | 推广理论 |
| [0F4Q](#tag-0f4q) | 收敛上同调 | 相关理论 |
| [0F4R](#tag-0f4r) | log-晶体上同调 | 边界情形 |

### 8.3 应用领域

| Tag | 主题 | 说明 |
|-----|------|------|
| [0F11](#tag-0f11) | $p$-进Hodge理论 | 主要应用 |
| [0F12](#tag-0f12) | 半稳定约化 | 几何应用 |
| [0F13](#tag-0f13) | Dieudonné模 | 代数结构 |

---

## 附录：PD结构示例

### 多项式环的PD包络

对于 $A = \mathbb{Z}_p[x]$ 和 $I = (x)$，PD包络为：

$$D_I(A) = \mathbb{Z}_p[x, x^{[2]}, x^{[3]}, \ldots]/(x^{[n]}x^{[m]} = \binom{n+m}{n}x^{[n+m]})$$

### Witt向量的Frobenius

在 $W(k)$ 上，Frobenius作用：

$$\sigma(a_0, a_1, a_2, \ldots) = (a_0^p, a_1^p, a_2^p, \ldots)$$

这是 $\mathbb{Z}_p$-代数的自同态。

---

*本文档由FormalMath项目生成，最后更新：2026-04-10*
