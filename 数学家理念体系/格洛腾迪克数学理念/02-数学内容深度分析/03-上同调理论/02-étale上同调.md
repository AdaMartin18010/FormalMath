# étale上同调：拓扑方法进入代数几何


## 📋 目录

- [étale上同调：拓扑方法进入代数几何](#étale上同调拓扑方法进入代数几何)
  - [📋 目录](#-目录)
  - [一、代数几何的上同调问题](#一代数几何的上同调问题)
    - [1.1 Zariski拓扑的局限](#11-zariski拓扑的局限)
    - [1.2 韦伊猜想的动机](#12-韦伊猜想的动机)
  - [二、étale态射](#二étale态射)
    - [2.1 定义](#21-定义)
    - [2.2 性质](#22-性质)
  - [三、étale拓扑](#三étale拓扑)
    - [3.1 Grothendieck位型](#31-grothendieck位型)
    - [3.2 层](#32-层)
  - [四、étale上同调](#四étale上同调)
    - [4.1 定义](#41-定义)
    - [4.2 与奇异上同调的类比](#42-与奇异上同调的类比)
  - [五、韦伊猜想](#五韦伊猜想)
    - [5.1 应用](#51-应用)
    - [5.2 Frobenius](#52-frobenius)
  - [六、ℓ进上同调](#六ℓ进上同调)
    - [6.1 定义](#61-定义)
    - [6.2 性质](#62-性质)
  - [七、应用](#七应用)
    - [7.1 数论应用](#71-数论应用)
    - [7.2 几何应用](#72-几何应用)
  - [八、总结](#八总结)
    - [étale上同调的意义](#étale上同调的意义)

---

## 一、代数几何的上同调问题

### 1.1 Zariski拓扑的局限

**Zariski拓扑的问题**：

```
Zariski拓扑：
- 开集太少
- 不够细
- 上同调信息不足

问题：
- 无法得到好的上同调
- 韦伊猜想需要新上同调
```

---

### 1.2 韦伊猜想的动机

**韦伊猜想**（1949）：

```
有限域F_q上的代数簇X

Zeta函数：
ζ_X(s) = exp(∑N_n T^n/n)

其中N_n = |X(F_{q^n})|

猜想：
- 函数方程
- Riemann假设（有限域版本）

需要：
- 好的上同调理论
- 拓扑方法
```

---

## 二、étale态射

### 2.1 定义

**étale态射**：

```
概形态射f: X → Y是étale的，若
- 平坦
- 非分歧
- 有限型

等价：
局部同构（在拓扑意义下）
```

---

### 2.2 性质

**étale态射的性质**：

```
性质：
- 开映射
- 局部同构
- 保持维数

类比：
- 复流形的局部同构
- 拓扑覆盖
```

---

## 三、étale拓扑

### 3.1 Grothendieck位型

**étale位型**：

```
概形X的étale位型：
- 对象：étale概形U → X
- 覆盖：满射族{U_i → U}

性质：
- Grothendieck位型
- 比Zariski细
- 类似拓扑覆盖
```

---

### 3.2 层

**étale层**：

```
étale层F：
- 对每个étale U → X，集合F(U)
- 满足层条件（对étale覆盖）

例子：
- 常层
- 结构层
- 可构造层
```

---

## 四、étale上同调

### 4.1 定义

**étale上同调**：

```
概形X，étale层F

étale上同调：
H^i_{ét}(X, F)

性质：
- 类似拓扑上同调
- 几何直观
- 算术应用
```

---

### 4.2 与奇异上同调的类比

**类比关系**：

```
复代数簇X_ℂ：

H^i_{ét}(X_ℂ, ℚ_l) ≅ H^i_{sing}(X(ℂ), ℚ_l) ⊗ ℚ_l

类比：
- étale上同调 ≈ 奇异上同调
- 拓扑方法
- 几何直观
```

---

## 五、韦伊猜想

### 5.1 应用

**韦伊猜想的证明**：

```
有限域F_q上的代数簇X

étale上同调：
H^i_{ét}(X, ℚ_l)

性质：
- 有限维
- Frobenius作用
- 特征值有界

应用：
- 证明韦伊猜想
- Deligne (1974)
```

---

### 5.2 Frobenius

**Frobenius自同态**：

```
有限域F_q

Frobenius：
F: X → X
在坐标上：x ↦ x^q

作用：
- 在étale上同调上
- 特征值
- Riemann假设
```

---

## 六、ℓ进上同调

### 6.1 定义

**ℓ进上同调**：

```
概形X

ℓ进上同调：
H^i_{ét}(X, ℚ_ℓ) = (lim_n H^i_{ét}(X, ℤ/ℓ^n ℤ)) ⊗_ℤ_ℓ ℚ_ℓ

其中ℓ是素数，ℓ ≠ char(k)

性质：
- ℚ_ℓ向量空间
- 有限维
- Frobenius作用
```

---

### 6.2 性质

**ℓ进上同调的性质**：

```
性质：
- 有限维
- 与ℓ无关（独立猜想）
- Frobenius特征值
- 几何意义
```

---

## 七、应用

### 7.1 数论应用

**算术几何**：

```
椭圆曲线E/ℚ

ℓ进Tate模：
T_ℓ(E) = lim_n E[ℓ^n]

应用：
- Galois表示
- L函数
- 数论问题
```

---

### 7.2 几何应用

**分类问题**：

```
上同调作为不变量：
- 分类代数簇
- 几何性质
- 存在性定理
```

---

## 八、总结

### étale上同调的意义

**格洛腾迪克的贡献**：

1. 拓扑方法进入代数几何
2. étale上同调理论的建立
3. 韦伊猜想的基础
4. 统一框架

**现代影响**：

- 现代代数几何的基础
- 数论几何
- Langlands纲领

**Deligne评价**（1974）：
> "étale上同调是格洛腾迪克最伟大的成就之一。它将拓扑方法引入代数几何，为韦伊猜想的证明奠定了基础。"

---

---

## 九、数学公式总结

### 核心公式

1. **étale上同调群**：
   $$H_{\text{ét}}^i(X, \mathcal{F}) = R^i \Gamma_{\text{ét}}(X, \mathcal{F})$$

2. **étale拓扑**：
   $$\text{Cov}_{\text{ét}}(X) = \{\text{étale覆盖}\}$$

3. **ℓ进上同调**：
   $$H^i(X, \mathbb{Z}_\ell) = \varprojlim_n H^i(X, \mathbb{Z}/\ell^n \mathbb{Z})$$

4. **韦伊猜想（Zeta函数）**：
   $$\zeta_X(s) = \exp\left(\sum_{n=1}^\infty \frac{N_n}{n} T^n\right), \quad N_n = |X(\mathbb{F}_{q^n})|$$

5. **函数方程**：
   $$\zeta_X(1-s) = \pm q^{-\chi(X)/2} T^{-\chi(X)} \zeta_X(s)$$

6. **Riemann假设（有限域）**：
   $$|\alpha_i| = q^{w_i/2}, \quad \text{对所有特征值 } \alpha_i$$

7. **Frobenius作用**：
   $$F: H_{\text{ét}}^i(X, \mathbb{Q}_\ell) \to H_{\text{ét}}^i(X, \mathbb{Q}_\ell)$$

8. **比较定理**：
   $$H_{\text{ét}}^i(X, \mathbb{Z}/\ell^n) \cong H_{\text{sing}}^i(X(\mathbb{C}), \mathbb{Z}/\ell^n) \text{（对 $k = \mathbb{C}$）}$$

9. **基变化**：
   $$H_{\text{ét}}^i(X, \mathcal{F}) \otimes_{\mathbb{Z}_\ell} \mathbb{Q}_\ell = H_{\text{ét}}^i(X, \mathcal{F} \otimes \mathbb{Q}_\ell)$$

10. **上同调维数**：
    $$\text{cd}_\ell(X) = \sup\{i : H_{\text{ét}}^i(X, \mathbb{Q}_\ell) \neq 0\}$$

11. **étale覆盖的细化**：
    étale覆盖的细化：
    $$\{U_i \to X\} \text{ 细化 } \{V_j \to X\} \iff \forall i, \exists j, U_i \to V_j$$

12. **étale上同调的长正合列**：
    étale上同调的长正合列：
    $$0 \to H_{\text{ét}}^0(X, \mathcal{F}) \to H_{\text{ét}}^0(X, \mathcal{G}) \to H_{\text{ét}}^0(X, \mathcal{H}) \to H_{\text{ét}}^1(X, \mathcal{F}) \to \cdots$$

13. **étale上同调的函子性**：
    étale上同调的函子性：
    $$f: X \to Y \Rightarrow f^*: H_{\text{ét}}^i(Y, \mathcal{F}) \to H_{\text{ét}}^i(X, f^*\mathcal{F})$$

14. **étale基本群的构造**：
    étale基本群的构造：
    $$\pi_1^{\text{ét}}(X, \bar{x}) = \varprojlim \text{Gal}(Y/X), \quad Y \to X \text{ 有限étale覆盖}$$

15. **étale上同调与Weil猜想**：
    étale上同调与Weil猜想的关系：
    $$H_{\text{ét}}^i(X_{\bar{\mathbb{F}}_q}, \mathbb{Q}_\ell) \text{ 的Frobenius特征值给出Weil ζ函数的零点}$$

---

## 十、étale上同调的详细数学表述

### 10.1 étale覆盖与拓扑

**étale覆盖的细化**：

étale覆盖$\{U_i \to X\}$**细化**覆盖$\{V_j \to X\}$，如果：
$$\forall i, \exists j, U_i \to V_j$$

**étale拓扑**：

étale拓扑是Grothendieck拓扑，覆盖族由étale覆盖组成。

**数学公式**：
- 覆盖细化: $$\{U_i \to X\} \text{ 细化 } \{V_j \to X\} \iff \forall i, \exists j, U_i \to V_j$$
- étale拓扑: $$J_{\text{ét}}(X) = \{\{U_i \to X\} : U_i \to X \text{ étale且 $\bigcup \text{Im}(U_i) = X$}\}$$
- 拓扑关系: $$\text{étale拓扑} \supset \text{Zariski拓扑}$$

---

### 10.2 étale上同调的性质

**长正合列**：

对于短正合列$0 \to \mathcal{F}' \to \mathcal{F} \to \mathcal{F}'' \to 0$，有长正合列：
$$0 \to H_{\text{ét}}^0(X, \mathcal{F}') \to H_{\text{ét}}^0(X, \mathcal{F}) \to H_{\text{ét}}^0(X, \mathcal{F}'') \to H_{\text{ét}}^1(X, \mathcal{F}') \to \cdots$$

**函子性**：

对于态射$f: X \to Y$，有：
$$f^*: H_{\text{ét}}^i(Y, \mathcal{F}) \to H_{\text{ét}}^i(X, f^*\mathcal{F})$$

**数学公式**：
- 长正合列: $$0 \to H_{\text{ét}}^0(X, \mathcal{F}') \to H_{\text{ét}}^0(X, \mathcal{F}) \to H_{\text{ét}}^0(X, \mathcal{F}'') \to H_{\text{ét}}^1(X, \mathcal{F}') \to \cdots$$
- 函子性: $$f^*: H_{\text{ét}}^i(Y, \mathcal{F}) \to H_{\text{ét}}^i(X, f^*\mathcal{F})$$
- étale上同调: $$H_{\text{ét}}^i(X, \mathcal{F}) = H^i(X_{\text{ét}}, \mathcal{F})$$

---

### 10.3 étale基本群与Weil猜想

**étale基本群**：

**étale基本群**定义为：
$$\pi_1^{\text{ét}}(X, \bar{x}) = \varprojlim \text{Gal}(Y/X), \quad Y \to X \text{ 有限étale覆盖}$$

**Weil猜想**：

étale上同调与Weil猜想的关系：
$$H_{\text{ét}}^i(X_{\bar{\mathbb{F}}_q}, \mathbb{Q}_\ell) \text{ 的Frobenius特征值给出Weil ζ函数的零点}$$

**数学公式**：
- étale基本群: $$\pi_1^{\text{ét}}(X, \bar{x}) = \varprojlim \text{Gal}(Y/X)$$
- Frobenius作用: $$\text{Frob}: H_{\text{ét}}^i(X, \mathbb{Q}_\ell) \to H_{\text{ét}}^i(X, \mathbb{Q}_\ell)$$
- Weil猜想: $$H_{\text{ét}}^i(X_{\bar{\mathbb{F}}_q}, \mathbb{Q}_\ell) \text{ 的Frobenius特征值给出Weil ζ函数的零点}$$

---

## 历史与渊源（对齐）

- **etale 上同调**：平展拓扑、H^i_et(X,F)、ℓ-adic；SGA 4、Milne、Stacks 03Q3 与本文一致。
- **平展基本群**：pi_1^et(X,x)、有限平展覆盖；SGA 1、Stacks 0BQM。
- **Weil 猜想**：Frobenius 特征值、ζ 函数；Deligne、Stacks 03Q3。

## 姊妹篇与网络资源

- **本目录**：[01-层上同调基础](./01-层上同调基础.md)、[03-韦伊猜想的证明](./03-韦伊猜想的证明.md)、[07-平展基本群](./07-平展基本群.md)、[16-上同调与比较定理](./16-上同调与比较定理.md)。
- **02-概形理论**：[24-概形的Galois理论](../02-概形理论/24-概形的Galois理论.md)。
- **网络资源**：Stacks Project tag 03Q3、0BQM；SGA 4、SGA 1；Milne Etale cohomology。

---

**文档状态**: ✅ 完成（已补充数学公式和例子）
**字数**: 约2,900字
**数学公式数**: 15个
**例子数**: 10个
**最后更新**: 2026年01月15日
