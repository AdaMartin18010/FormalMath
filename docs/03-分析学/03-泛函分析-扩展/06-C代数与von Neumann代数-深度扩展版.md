---
msc_primary: 00

  - 00A99
  - 46L05
  - 46L10
  - 46L35
  - 46L87
  - 47L30
title: '12.06 C*-代数与von Neumann代数深度扩展版 / C*-Algebras and von Neumann Algebras: In-Depth
  Extensions'
processed_at: '2026-04-05'
---
msc_primary: "@"
msc_secondary: ['46L05', '46L10', '46L35', '46L87', '47L30']
---

# 12.06 C*-代数与von Neumann代数深度扩展版 / C*-Algebras and von Neumann Algebras: In-Depth Extensions

## 目录

- [12.06 C\*-代数与von Neumann代数深度扩展版 / C\*-Algebras and von Neumann Algebras: In-Depth Extensions](#1206-c-代数与von-neumann代数深度扩展版-c-algebras-and-von-neumann-algebras-in-depth-extensions)
  - [目录](#目录)
  - [12.06.1 概述 / Overview](#12061-概述-overview)
  - [12.06.2 Banach代数与谱理论 / Banach Algebras and Spectral Theory](#12062-banach代数与谱理论-banach-algebras-and-spectral-theory)
    - [12.06.2.1 Banach代数的定义与例子](#120621-banach代数的定义与例子)
    - [12.06.2.2 谱与预解式](#120622-谱与预解式)
    - [12.06.2.3 Gelfand表示](#120623-gelfand表示)
  - [12.06.3 C\*-代数基本理论 / C\*-Algebras](#12063-c-代数基本理论-c-algebras)
    - [12.06.3.1 C\*-代数的定义与基本性质](#120631-c-代数的定义与基本性质)
    - [12.06.3.2 交换C\*-代数的结构](#120632-交换c-代数的结构)
    - [12.06.3.3 正元与序结构](#120633-正元与序结构)
  - [12.06.4 GNS构造与表示理论 / GNS Construction](#12064-gns构造与表示理论-gns-construction)
    - [12.06.4.1 态与正线性泛函](#120641-态与正线性泛函)
    - [12.06.4.2 Gelfand-Naimark-Segal构造](#120642-gelfand-naimark-segal构造)
    - [12.06.4.3 通用表示定理](#120643-通用表示定理)
  - [12.06.5 von Neumann代数 / von Neumann Algebras](#12065-von-neumann代数-von-neumann-algebras)
    - [12.06.5.1 von Neumann代数的等价定义](#120651-von-neumann代数的等价定义)
    - [12.06.5.2 双交换子定理](#120652-双交换子定理)
    - [12.06.5.3 投影格与因子分解](#120653-投影格与因子分解)
  - [12.06.6 Murray-von Neumann因子分类 / Factor Classification](#12066-murray-von-neumann因子分类-factor-classification)
    - [12.06.6.1 因子的定义与类型](#120661-因子的定义与类型)
    - [12.06.6.2 迹与维数函数](#120662-迹与维数函数)
    - [12.06.6.3 现代发展：Tomita-Takesaki理论简述](#120663-现代发展tomita-takesaki理论简述)
  - [12.06.7 历史背景与数学物理应用 / Historical Development](#12067-历史背景与数学物理应用-historical-development)
  - [12.06.8 参考文献 / References](#12068-参考文献-references)

## 12.06.1 概述 / Overview

C*-代数和von Neumann代数是泛函分析中研究算子代数的两大学派，分别由Gelfand和von Neumann在20世纪30-40年代开创。C*-代数以其简洁的公理化定义和Gelfand-Naimark表示定理著称；von Neumann代数则以其在量子力学中的直接应用和深刻的因子分类理论闻名。

本章参考Murphy《C*-代数与算子理论》和Takesaki《算子代数理论》的经典体系，系统阐述Banach代数、C*-代数、von Neumann代数的基本理论，重点介绍GNS构造和Murray-von Neumann因子分类。

## 12.06.2 Banach代数与谱理论 / Banach Algebras and Spectral Theory

### 12.06.2.1 Banach代数的定义与例子

**定义 12.06.1（Banach代数）**：复Banach空间 $\mathcal{A}$ 称为**Banach代数**，如果其上定义了乘法运算 $(a, b) \mapsto ab$ 满足：

1. **结合律**：$(ab)c = a(bc)$
2. **分配律**：$a(b+c) = ab + ac$，$(a+b)c = ac + bc$
3. **数乘相容**：$\lambda(ab) = (\lambda a)b = a(\lambda b)$
4. **范数次乘性**：$\|ab\| \leq \|a\|\|b\|$

若存在元素 $e$ 使得 $ea = ae = a$ 对所有 $a \in \mathcal{A}$ 成立，且 $\|e\| = 1$，则称 $\mathcal{A}$ 是**含幺Banach代数**。

**定义 12.06.2（* -代数）**：Banach代数 $\mathcal{A}$ 称为**对合代数**（或* -代数），如果存在对合运算 $*: \mathcal{A} \to \mathcal{A}$，$a \mapsto a^*$ 满足：

1. $(a^*)^* = a$
2. $(ab)^* = b^*a^*$
3. $(\lambda a + \mu b)^* = \overline{\lambda}a^* + \overline{\mu}b^*$

**例子 12.06.1（连续函数代数）**：设 $X$ 是紧Hausdorff空间，$C(X)$ 是 $X$ 上连续复值函数空间，装备上确界范数 $\|f\|_\infty = \sup_{x \in X}|f(x)|$ 和逐点乘法，则是含幺交换Banach代数，对合为复共轭 $f^*(x) = \overline{f(x)}$。

**例子 12.06.2（有界算子代数）**：设 $H$ 是Hilbert空间，$\mathcal{L}(H)$ 是 $H$ 上有界线性算子全体，装备算子范数和复合乘法，则是含幺Banach代数，对合为伴随运算 $T^*$。

**例子 12.06.3（卷积代数）**：设 $G$ 是局部紧群，$\mu$ 是左Haar测度，$L^1(G)$ 装备卷积乘法：
$$(f * g)(x) = \int_G f(y)g(y^{-1}x)\, d\mu(y)$$

则是Banach代数，当 $G$ 非平凡时非交换。

### 12.06.2.2 谱与预解式

**定义 12.06.3（谱）**：设 $\mathcal{A}$ 是含幺Banach代数，$a \in \mathcal{A}$，**谱**定义为：
$$\sigma(a) = \{\lambda \in \mathbb{C} : a - \lambda e \text{ 在 } \mathcal{A} \text{ 中不可逆}\}$$

**预解集** $\rho(a) = \mathbb{C} \setminus \sigma(a)$，**预解式** $R(\lambda, a) = (a - \lambda e)^{-1}$。

**定理 12.06.1（谱的基本性质）**：

1. **非空性**：$\sigma(a) \neq \emptyset$
2. **紧性**：$\sigma(a)$ 是 $\mathbb{C}$ 的紧子集
3. **谱半径公式**（Gelfand-Beurling）：
$$r(a) = \sup_{\lambda \in \sigma(a)}|\lambda| = \lim_{n \to \infty} \|a^n\|^{1/n}$$

*证明思路*：非空性由Liouville定理推出——若谱为空，则预解式是整函数且在无穷远处趋于0，必恒为零，矛盾。谱半径公式利用复分析中的Cauchy-Hadamard公式。$\square$

**定理 12.06.2（谱映射定理）**：设 $a \in \mathcal{A}$，$f$ 在 $\sigma(a)$ 邻域全纯，则：
$$\sigma(f(a)) = f(\sigma(a))$$

其中 $f(a)$ 由Dunford-Riesz函数演算定义。

### 12.06.2.3 Gelfand表示

**定义 12.06.4（特征与极大理想）**：设 $\mathcal{A}$ 是交换Banach代数，非零同态 $\chi: \mathcal{A} \to \mathbb{C}$ 称为**特征**（character）。特征与极大理想一一对应：$\ker(\chi)$ 是极大理想。

**Gelfand谱**：所有特征的集合 $\hat{\mathcal{A}}$，装备弱*拓扑成为紧Hausdorff空间（当 $\mathcal{A}$ 含幺时）。

**定理 12.06.3（Gelfand表示）**：设 $\mathcal{A}$ 是交换Banach代数，定义**Gelfand变换** $\Gamma: \mathcal{A} \to C(\hat{\mathcal{A}})$ 为：
$$\Gamma(a)(\chi) = \chi(a)$$

则：

1. $\Gamma$ 是连续代数同态，$\|\Gamma(a)\|_\infty = r(a)$

2. $\sigma(a) = \{\chi(a) : \chi \in \hat{\mathcal{A}}\}$
3. 若 $\mathcal{A}$ 是C*-代数，则 $\Gamma$ 是等距* -同构

## 12.06.3 C*-代数基本理论 / C*-Algebras

### 12.06.3.1 C*-代数的定义与基本性质

**定义 12.06.5（C*-代数）**：Banach代数 $\mathcal{A}$ 称为**C*-代数**，如果它是* -代数且满足**C*-恒等式**：
$$\|a^*a\| = \|a\|^2, \quad \forall a \in \mathcal{A}$$

**基本性质**：

1. $\|a^*\| = \|a\|$
2. 若 $a = a^*$（自伴），则 $\|a^2\| = \|a\|^2$，$\|a\| = r(a)$
3. 若 $u^*u = uu^* = e$（酉元），则 $\sigma(u) \subset \mathbb{T} = \{z : |z| = 1\}$

**例子 12.06.4（矩阵代数）**：$M_n(\mathbb{C})$ 是有限维C*-代数，装备Hilbert-Schmidt内积诱导的范数。

**例子 12.06.5（紧算子代数）**：设 $H$ 是Hilbert空间，$\mathcal{K}(H)$ 是紧算子全体，则是 $\mathcal{L}(H)$ 的闭*-理想，是C*-代数。

### 12.06.3.2 交换C*-代数的结构

**定理 12.06.4（Gelfand-Naimark，交换情形）**：设 $\mathcal{A}$ 是含幺交换C*-代数，则Gelfand变换是等距* -同构：
$$\mathcal{A} \cong C(\hat{\mathcal{A}})$$

*证明思路*：关键是证明对自伴元 $a$，$\sigma(a) \subset \mathbb{R}$。设 $\chi$ 是特征，由C*-恒等式，$\chi(a^*) = \overline{\chi(a)}$。若 $a = a^*$，则 $\chi(a) = \overline{\chi(a)}$，即特征值实。再由谱半径公式，$\|\Gamma(a)\|_\infty = r(a) = \|a\|$。$\square$

**推论 12.06.1（函数演算）**：设 $\mathcal{A}$ 是C*-代数，$a \in \mathcal{A}$ 正规（即 $a^*a = aa^*$），则：
$$C^*(a) \cong C(\sigma(a))$$

其中 $C^*(a)$ 是由 $a$ 和 $e$ 生成的C*-子代数。

### 12.06.3.3 正元与序结构

**定义 12.06.6（正元）**：$a \in \mathcal{A}$ 称为**正元**，记 $a \geq 0$，如果 $a = a^*$ 且 $\sigma(a) \subset [0, \infty)$。

**命题 12.06.1**：以下等价：

1. $a \geq 0$
2. 存在 $b \in \mathcal{A}$ 使得 $a = b^*b$
3. 存在唯一的 $c \geq 0$ 使得 $c^2 = a$（记 $c = a^{1/2}$）

**序结构**：对自伴元 $a, b$，定义 $a \leq b$ 当且仅当 $b - a \geq 0$。这给出 $\mathcal{A}_{sa}$（自伴元全体）上的偏序。

## 12.06.4 GNS构造与表示理论 / GNS Construction

### 12.06.4.1 态与正线性泛函

**定义 12.06.7（正线性泛函）**：线性泛函 $\varphi: \mathcal{A} \to \mathbb{C}$ 称为**正**的，如果 $\varphi(a^*a) \geq 0$ 对所有 $a \in \mathcal{A}$ 成立。

**命题 12.06.2**：正线性泛函 $\varphi$ 满足Cauchy-Schwarz不等式：
$$|\varphi(b^*a)|^2 \leq \varphi(a^*a)\varphi(b^*b)$$

**定义 12.06.8（态）**：正线性泛函 $\varphi$ 称为**态**，如果 $\|\varphi\| = 1$（当 $\mathcal{A}$ 含幺时等价于 $\varphi(e) = 1$）。所有态的集合记为 $\mathcal{S}(\mathcal{A})$，是 $\mathcal{A}^*$ 的凸子集。

**定义 12.06.9（纯态）**：态 $\varphi$ 称为**纯态**，如果它不能表示为非平凡态的凸组合。纯态对应 $\mathcal{S}(\mathcal{A})$ 的极值点。

### 12.06.4.2 Gelfand-Naimark-Segal构造

**定理 12.06.5（GNS构造）**：设 $\mathcal{A}$ 是C*-代数，$\varphi$ 是 $\mathcal{A}$ 上的正线性泛函，则存在：

1. Hilbert空间 $H_\varphi$
2. - -表示 $\pi_\varphi: \mathcal{A} \to \mathcal{L}(H_\varphi)$
3. 循环向量 $\xi_\varphi \in H_\varphi$（即 $\overline{\pi_\varphi(\mathcal{A})\xi_\varphi} = H_\varphi$）

满足：
$$\varphi(a) = \langle \pi_\varphi(a)\xi_\varphi, \xi_\varphi \rangle$$

*构造方法*：在 $\mathcal{A}$ 上定义半内积 $\langle a, b \rangle_\varphi = \varphi(b^*a)$。由Cauchy-Schwarz，$N_\varphi = \{a : \varphi(a^*a) = 0\}$ 是左理想。在商空间 $\mathcal{A}/N_\varphi$ 上内积正定，完备化得 $H_\varphi$。定义 $\pi_\varphi(a)[b] = [ab]$，验证这是良定义的* -表示。$\square$

### 12.06.4.3 通用表示定理

**定理 12.06.6（Gelfand-Naimark，一般情形）**：每个C*-代数 $\mathcal{A}$ 都等距* -同构于某个Hilbert空间上有界算子代数的C*-子代数。

*证明思路*：考虑通用表示：
$$\pi_u = \bigoplus_{\varphi \in \mathcal{S}(\mathcal{A})} \pi_\varphi$$

需证 $\pi_u$ 是单射且等距。由Hahn-Banach和Krein-Milman，态分离点。$\square$

**定义 12.06.10（包络von Neumann代数）**：$\mathcal{A}^{**}$（Banach空间双重对偶）可赋予C*-代数结构，其泛表示的弱闭包是**包络von Neumann代数** $W^*(\mathcal{A})$。

## 12.06.5 von Neumann代数 / von Neumann Algebras

### 12.06.5.1 von Neumann代数的等价定义

**定义 12.06.11（von Neumann代数）**：设 $H$ 是Hilbert空间，$\mathcal{M} \subset \mathcal{L}(H)$ 称为**von Neumann代数**，如果：

1. 是含幺C*-子代数
2. 在弱算子拓扑（WOT）下闭

**等价刻画**：

- 在强算子拓扑（SOT）下闭
- 在超弱拓扑下闭
- 在超强拓扑下闭

### 12.06.5.2 双交换子定理

**定义 12.06.12（交换子）**：对 $\mathcal{S} \subset \mathcal{L}(H)$，定义：
$$\mathcal{S}' = \{T \in \mathcal{L}(H) : TS = ST, \, \forall S \in \mathcal{S}\}$$

$\mathcal{S}'$ 称为 $\mathcal{S}$ 的**交换子**（commutant），$\mathcal{S}''$ 称为**双交换子**。

**定理 12.06.7（von Neumann双交换子定理）**：设 $\mathcal{M} \subset \mathcal{L}(H)$ 是含幺自伴子代数（即C*-子代数），则以下条件等价：

1. $\mathcal{M}$ 是von Neumann代数
2. $\mathcal{M} = \mathcal{M}''$

*证明思路*：关键是证明若 $\mathcal{M} = \mathcal{M}''$，则 $\mathcal{M}$ 在SOT下闭。对任意 $T \in \overline{\mathcal{M}}^{SOT}$，需证 $T \in \mathcal{M}''$。利用 von Neumann的**双重交换技巧**和Cyclic向量存在性。$\square$

**推论 12.06.2**：$\mathcal{M}'$ 也是von Neumann代数，且 $\mathcal{M}''' = \mathcal{M}'$。

### 12.06.5.3 投影格与因子分解

**定义 12.06.13（投影）**：$p \in \mathcal{M}$ 称为**投影**，如果 $p = p^* = p^2$。

**投影格**：$\mathcal{M}$ 的所有投影记为 $\mathcal{P}(\mathcal{M})$，装备偏序 $p \leq q \Leftrightarrow pq = p$，构成**完备格**。

**定义 12.06.14（中心）**：$Z(\mathcal{M}) = \mathcal{M} \cap \mathcal{M}'$ 称为 $\mathcal{M}$ 的**中心**。若 $Z(\mathcal{M}) = \mathbb{C}I$，称 $\mathcal{M}$ 为**因子**（factor）。

**命题 12.06.3**：每个von Neumann代数都可唯一分解为因子的直积分（或直接积分）。

## 12.06.6 Murray-von Neumann因子分类 / Factor Classification

### 12.06.6.1 因子的定义与类型

**定义 12.06.15（等价投影）**：投影 $p, q \in \mathcal{P}(\mathcal{M})$ 称为**等价**，记 $p \sim q$，如果存在部分等距 $u \in \mathcal{M}$ 使得 $p = u^*u$，$q = uu^*$。

**定义 12.06.16（有限投影）**：投影 $p$ 称为**有限**的，如果 $q \leq p$ 且 $q \sim p$ 蕴含 $q = p$。否则称为**无限**的。

**定义 12.06.17（因子类型）**：设 $\mathcal{M}$ 是因子：

- **类型 I**：存在非零极小投影
- **类型 II$_1$**：存在非零有限投影，但无极小投影，单位元有限
- **类型 II$_\infty$**：存在非零有限投影，单位元无限
- **类型 III**：所有非零投影都是无限的

**定理 12.06.8（Murray-von Neumann分类）**：任何因子必属且仅属上述类型之一。

### 12.06.6.2 迹与维数函数

**定义 12.06.18（迹）**：映射 $\tau: \mathcal{M}_+ \to [0, \infty]$ 称为**迹**，如果：

1. $\tau(\lambda a + \mu b) = \lambda\tau(a) + \mu\tau(b)$（线性）
2. $\tau(a^*a) = \tau(aa^*)$（迹性质）

**定理 12.06.9**：

- 类型 I$_n$ 因子同构于 $M_n(\mathbb{C})$，有规范迹 $\tau = \frac{1}{n}\text{Tr}$
- 类型 I$_\infty$ 因子同构于 $\mathcal{L}(H)$，无有限迹
- 类型 II$_1$ 因子有唯一的正规化忠实正规迹
- 类型 II$_\infty$ 因子有忠实的半有限迹
- 类型 III 因子无半有限迹（除非平凡）

**维数函数**：对类型 II$_1$ 因子，$D(p) = \tau(p)$ 定义投影上的维数函数，取值于 $[0, 1]$。

### 12.06.6.3 现代发展：Tomita-Takesaki理论简述

**背景**：类型III因子在量子场论和统计力学中自然出现，但传统工具难以研究。

**定理 12.06.10（Tomita-Takesaki基本定理，简述）**：设 $\mathcal{M}$ 是von Neumann代数，$\Omega \in H$ 是循环且分离向量，定义模算子 $\Delta$ 和模共轭 $J$ 通过极分解 $S = J\Delta^{1/2}$，其中 $S(a\Omega) = a^*\Omega$。则：

1. $J\mathcal{M}J = \mathcal{M}'$
2. $\Delta^{it}\mathcal{M}\Delta^{-it} = \mathcal{M}$，$\forall t \in \mathbb{R}$

**类型III的进一步分类**：利用模自同构群 $\sigma_t^\varphi(a) = \Delta^{it}a\Delta^{-it}$，Connes将类型III细分为III$_\lambda$（$0 \leq \lambda \leq 1$）。

## 12.06.7 历史背景与数学物理应用 / Historical Development

**历史发展脉络**：

1. **矩阵力学的诞生（1925）**：Heisenberg创立矩阵力学，Born和Jordan认识到矩阵代数的重要性。

2. **von Neumann的奠基工作（1929-1936）**：von Neumann引入"算子环"（rings of operators）概念，证明双交换子定理，为量子力学建立严格数学基础。1936年与Murray发表因子分类的开创性工作。

3. **Gelfand的抽象方法（1940s）**：Gelfand和Naimark引入C*-代数概念，1943年证明交换C*-代数的表示定理。1947年Segal发展GNS构造。

4. **Tomita-Takesaki革命（1967-1970）**：Tomita发现模理论，Takesaki系统整理并证明基本定理，深刻改变了von Neumann代数的研究。

5. **Connes的非交换几何（1970s-1980s）**：Connes将C*-代数与微分几何结合，发展非交换几何，1982年获得Fields奖。

6. **量子场论应用（1980s至今）**：Haag-Kastler公理体系使用C*-代数描述量子场论；Jones的次因子理论连接算子代数与纽结理论。

**与数学物理的联系**：

- **量子力学**：可观测量构成C*-代数，物理态是代数上的态，GNS构造给出Hilbert空间实现
- **统计力学**：KMS条件刻画热平衡态，由Haag-Hugenholtz-Winnink引入
- **量子场论**：局部可观测量代数形成网（net），满足局域性公理
- **量子信息**：C*-代数框架统一经典和量子概率

**与其他分支的联系**：

- **K理论**：C*-代数的K群是拓扑不变量，联系指标理论
- **遍历理论**：测度保持系统的群C*-代数研究
- **纽结理论**：Jones多项式源于子因子理论

## 12.06.8 参考文献 / References

1. **Murphy, G. J.** (1990). *C*-Algebras and Operator Theory*. Academic Press. (MSC: @, @)

2. **Takesaki, M.** (1979, 2003). *Theory of Operator Algebras*, Vol. I, II, III. Springer. (MSC: @)

3. **Blackadar, B.** (2006). *Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*. Springer. (MSC: @)

4. **Kadison, R. V. & Ringrose, J. R.** (1983, 1986). *Fundamentals of the Theory of Operator Algebras*, Vol. I, II. Academic Press. (MSC: @)

5. **Connes, A.** (1994). *Noncommutative Geometry*. Academic Press. (MSC: 46L87, 58B34)

6. **Bratteli, O. & Robinson, D. W.** (1987, 1997). *Operator Algebras and Quantum Statistical Mechanics*, Vol. 1, 2 (2nd ed.). Springer. (MSC: 46L60, 82-02)

---

**相关文档**：

- [04-算子理论-深度扩展版](./04-算子理论-深度扩展版.md)
- [05-分布理论-深度扩展版](./05-分布理论-深度扩展版.md)
- [07-非交换几何-深度扩展版](./07-非交换几何-深度扩展版.md)
- [../11-高级数学/20-现代分析学前沿.md](./../../11-高级数学/20-现代分析学前沿.md)
