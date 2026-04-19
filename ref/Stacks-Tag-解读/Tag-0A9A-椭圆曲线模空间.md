---
msc_primary: 00A99
msc_secondary:
  - 97A99
---

# Stacks Project Tag 0A9A - 椭圆曲线的模空间

## 1. 基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 0A9A |
| **英文名称** | Moduli of Elliptic Curves |
| **所属章节** | Moduli of Curves |
| **主题分类** | 代数几何 - 模空间理论 |
| **创建日期** | 2026-04-10 |
| **版本** | v1.0 |

---

## 2. 核心概念与定义

### 2.1 椭圆曲线概述

**椭圆曲线**是亏格为1的代数曲线，带有指定的有理点。它们是代数几何、数论和密码学中的核心对象。

### 2.2 关键定义

**定义 2.2.1**（椭圆曲线）
在域 $K$ 上，**椭圆曲线** $(E, O)$ 由以下数据组成：
- 光滑射影曲线 $E/K$，亏格 $g(E) = 1$
- 指定点 $O \in E(K)$（原点）

**定义 2.2.2**（Weierstrass方程）
特征 $\neq 2, 3$ 时，椭圆曲线有Weierstrass方程：

$$E: y^2 = x^3 + ax + b, \quad a, b \in K$$

判别式 $\Delta = -16(4a^3 + 27b^2) \neq 0$ 保证光滑性。

**定义 2.2.3**（$j$-不变量）
椭圆曲线的**$j$-不变量**定义为：

$$j(E) = 1728 \frac{4a^3}{4a^3 + 27b^2}$$

这是粗模空间（coarse moduli space）的坐标。

**定义 2.2.4**（椭圆曲线的同构）
两条椭圆曲线 $(E_1, O_1)$ 和 $(E_2, O_2)$ **同构**，如果存在同构 $\phi: E_1 \to E_2$ 使得 $\phi(O_1) = O_2$。

对于Weierstrass方程，同构由 $(x, y) \mapsto (u^2x, u^3y)$ 给出，$u \in K^*$。

### 2.3 椭圆曲线的群结构

**定理 2.3.1**（群律）
椭圆曲线 $(E, O)$ 有自然的Abel群结构：
- 原点 $O$ 是单位元
- 三点共线之和为零：$P + Q + R = O$ 当且仅当 $P, Q, R$ 共线

**定理 2.3.2**（Mordell-Weil定理）
对于数域 $K$ 上的椭圆曲线 $E/K$：

$$E(K) \cong \mathbb{Z}^r \oplus E(K)_{\text{tors}}$$

其中 $r$ 是**秩**（rank），$E(K)_{\text{tors}}$ 是有限挠子群。

---

## 3. 主要结果与定理

### 3.1 模空间的存在性

**定理 3.1.1**（Tag 0A9A）
椭圆曲线的模空间具有以下性质：

**(a) 粗模空间**
存在**粗模空间**（coarse moduli space）：

$$M_{1,1} \cong \mathbb{A}^1_j$$

坐标为$j$-不变量。

**(b) 细模叠（Deligne-Mumford叠）**
存在Deligne-Mumford叠 $\mathcal{M}_{1,1}$ 精细参数化椭圆曲线：

$$\mathcal{M}_{1,1}(S) = \{(E \to S, e: S \to E)\}/\cong$$

**(c) 紧致化**
通过添加**尖点**（cuspidal cubic）紧致化：

$$\overline{M}_{1,1} \cong \mathbb{P}^1_j$$

### 3.2 模叠的结构

**定理 3.2.1**（通用椭圆曲线）
存在**通用椭圆曲线** $\mathcal{E} \to \mathcal{M}_{1,1}$，使得对任何椭圆曲线族 $E \to S$，存在唯一的Cartier图：

$$\begin{array}{ccc}
E & \to & \mathcal{E} \\
\downarrow & & \downarrow \\
S & \to & \mathcal{M}_{1,1}
\end{array}$$

**定理 3.2.2**（Hodge线丛）
模叠带有**Hodge线丛**：

$$\omega = \pi_* \Omega^1_{\mathcal{E}/\mathcal{M}_{1,1}}$$

权$k$模形式是其$k$次张量幂的截面：

$$M_k = H^0(\mathcal{M}_{1,1}, \omega^{\otimes k})$$

### 3.3 层结构与上同调

**定理 3.3.1**
$$H^0(\mathcal{M}_{1,1}, \omega^{\otimes k}) = \begin{cases} \mathbb{C} \cdot E_k & k \geq 4 \text{ 偶数} \\ 0 & \text{否则} \end{cases}$$

其中 $E_k$ 是正规化的Eisenstein级数。

**定理 3.3.2**（刚性）
对于 $k \geq 3$，$H^1(\mathcal{M}_{1,1}, \omega^{\otimes k}) = 0$。

---

## 4. 证明思路

### 4.1 模叠的构造

**步骤1**：Weierstrass方程的参数空间
- 考虑 $(a, b) \in \mathbb{A}^2$，条件 $\Delta \neq 0$
- 这是椭圆曲线的参数空间

**步骤2**：商去同构
- 同构群 $\mathbb{G}_m$ 作用：$(a, b) \mapsto (u^4a, u^6b)$
- 叠 $[(\mathbb{A}^2 \setminus \{\Delta=0\})/\mathbb{G}_m]$

**步骤3**：与上半平面的联系
- 解析上：$\mathcal{M}_{1,1}^{\text{an}} \cong [\mathbb{H}/SL_2(\mathbb{Z})]$
- 这是orbifold，有 $\mathbb{Z}/6\mathbb{Z}$ 和 $\mathbb{Z}/4\mathbb{Z}$ stabilizers

### 4.2 $j$-不变量的证明

**核心观察**：
$j$-不变量分类椭圆曲线在代数闭域上的同构类：

$$j(E_1) = j(E_2) \Leftrightarrow E_1 \cong E_2 \text{（代数闭域上）}$$

这是由于 $j$ 生成不变量环。

### 4.3 紧致化

**技术步骤**：
1. 添加尖点曲线（nodal cubic）
2. 验证稳定性条件
3. 检查Deligne-Mumford性质保持

---

## 5. 应用与例子

### 5.1 模形式的经典例子

**例子 5.1.1**（Eisenstein级数）
$$E_4(\tau) = 1 + 240\sum_{n=1}^\infty \sigma_3(n)q^n$$
$$E_6(\tau) = 1 - 504\sum_{n=1}^\infty \sigma_5(n)q^n$$

作为权4和权6的模形式。

**例子 5.1.2**（判别式）
$$\Delta(\tau) = \frac{E_4(\tau)^3 - E_6(\tau)^2}{1728} = q\prod_{n=1}^\infty (1-q^n)^{24}$$

是权12的尖点形式。

**例子 5.1.3**（$j$-函数）
$$j(\tau) = \frac{E_4(\tau)^3}{\Delta(\tau)} = q^{-1} + 744 + 196884q + \cdots$$

是权0的模函数，在无穷远有单极点。

### 5.2 复乘法（CM）

**应用 5.2.1**
椭圆曲线 $E$ 有**复乘法**，如果 $\text{End}(E) \supsetneq \mathbb{Z}$。

此时 $\text{End}(E) \otimes \mathbb{Q}$ 是虚二次域。

**定理**（Weber, Hasse, Deuring）：
- 若 $E$ 有CM by $\mathcal{O}_K$，则 $j(E)$ 是代数整数
- $K(j(E))$ 是Hilbert类域

### 5.3 密码学应用

**应用 5.3.1**（椭圆曲线密码学）
椭圆曲线群用于：
- **Diffie-Hellman密钥交换**
- **ECDSA签名**
- **配对密码学**（Weil配对、Tate配对）

安全性基于**椭圆曲线离散对数问题**（ECDLP）的困难性。

### 5.4 Fermat大定理的证明

**应用 5.4.1**（Wiles定理）
Frey曲线：若 $a^p + b^p = c^p$ 有解，构造椭圆曲线

$$E: y^2 = x(x-a^p)(x+b^p)$$

Ribet定理 + Wiles-Taylor定理证明这种曲线不可能模形式化，导出矛盾。

---

## 6. 与其他概念的关系

### 6.1 模空间的比较

```
    $\mathcal{M}_{1,1}$ (Deligne-Mumford叠)
           │
           │ forget stabilizers
           ▼
    $M_{1,1} = \mathbb{A}^1_j$ (粗模空间)
           │
           │ compactify
           ▼
    $\overline{M}_{1,1} = \mathbb{P}^1_j$
           │
           │ complex analytification
           ▼
    $[\mathbb{H}/SL_2(\mathbb{Z})]$ (orbifold)
```

### 6.2 与模形式的关系

| 几何 | 分析 |
|------|------|
| $\omega^{\otimes k}$ 的截面 | 权$k$模形式 |
| Hodge线丛 | 自守因子 |
| 尖点 | 无穷远点 |
| 抛物上同调 | 尖点形式 |

### 6.3 与高维Abel簇的关系

| 维数1（椭圆曲线） | 高维Abel簇 |
|----------------|-----------|
| $\mathcal{M}_{1,1}$ 是1维 | $\mathcal{A}_g$ 是 $\frac{g(g+1)}{2}$ 维 |
| 有粗模空间 | 一般只有粗模叠 |
| 模形式理论成熟 | Siegel模形式 |
| 自对偶 | 有对偶Abel簇 |

---

## 7. 参考文献

### 7.1 经典文献

1. **Silverman, J.H.** (1986). *The Arithmetic of Elliptic Curves*
   - Springer GTM 106
   - 椭圆曲线的标准教科书

2. **Silverman, J.H.** (1994). *Advanced Topics in the Arithmetic of Elliptic Curves*
   - Springer GTM 151
   - 复乘法、模曲线等

3. **Husemöller, D.** (2004). *Elliptic Curves*
   - Springer GTM 111
   - 入门友好

### 7.2 模形式

4. **Diamond, F. & Shurman, J.** (2005). *A First Course in Modular Forms*
   - Springer GTM 228

5. **Miyake, T.** (2006). *Modular Forms*
   - Springer

### 7.3 模空间

6. **Katz, N.M. & Mazur, B.** (1985). *Arithmetic Moduli of Elliptic Curves*
   - Princeton University Press
   - 模叠的详细构造

7. **Deligne, P. & Rapoport, M.** (1973). *Les schémas de modules de courbes elliptiques*
   - Springer LNM 349

### 7.4 在线资源

8. **Stacks Project**: [Tag 0A9A](https://stacks.math.columbia.edu/tag/0A9A)
9. **LMFDB**: [Elliptic Curves](https://www.lmfdb.org/EllipticCurve/Q/)

---

## 8. 相关Tags

### 8.1 直接相关

| Tag | 主题 | 关系 |
|-----|------|------|
| [0A99](#tag-0a99) | 模叠与模形式 | 理论框架 |
| [0A9B](#tag-0a9b) | 模形式的层 | 结构层 |
| [0E6J](#tag-0e6j) | 通用椭圆曲线 | 具体构造 |

### 8.2 椭圆曲线理论

| Tag | 主题 | 说明 |
|-----|------|------|
| [0E6K](#tag-0e6k) | Weierstrass方程 | 具体计算 |
| [0E6L](#tag-0e6l) | 群结构 | 代数结构 |
| [0E6M](#tag-0e6m) | 复乘法 | 数论应用 |

### 8.3 应用主题

| Tag | 主题 | 说明 |
|-----|------|------|
| [0E6N](#tag-0e6n) | 椭圆曲线密码学 | 实际应用 |
| [0E6O](#tag-0e6o) | 模曲线 | 算术几何 |
| [0E6P](#tag-0e6p) | Fermat大定理 | 历史应用 |

---

## 附录：椭圆曲线数据

### 同构类数量

对于有限域 $\mathbb{F}_q$，椭圆曲线的同构类数量约为 $2q$。

### 挠子群可能结构（Mazur定理）

对于 $E/\mathbb{Q}$，挠子群 $E(\mathbb{Q})_{\text{tors}}$ 只能是以下15种之一：

$$\mathbb{Z}/n\mathbb{Z}, \quad n = 1, 2, \ldots, 10, 12$$

$$\mathbb{Z}/2\mathbb{Z} \times \mathbb{Z}/2n\mathbb{Z}, \quad n = 1, 2, 3, 4$$

---

*本文档由FormalMath项目生成，最后更新：2026-04-10*
