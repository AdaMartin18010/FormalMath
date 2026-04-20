---
msc_primary: 17

  - 17B56
msc_secondary: ['18G99', '17B55']
keywords: ['Lie代数上同调', 'Chevalley-Eilenberg', '外代数', '中心扩张', 'Whitehead引理']
version: 1.0
---

# Lie代数上同调

**Lie代数的同调理论 — 从Chevalley-Eilenberg到表示论**

---

## 1. 概念深度解析

### 1.1 代数直观

**Lie代数上同调** $H^n(  hetacal g, M)$ 是群上同调的Lie代数版本。与群上同调类似，它通过不变量来刻画Lie代数的结构：

- $H^1$ 反映导子与内导子的差异（外自同构的信息）
- $H^2$ 分类Lie代数的中心扩张
- $H^3$ 与形变理论密切相关

**与de Rham上同调的联系**：若 $G$ 是紧Lie群，$  hetacal g$ 是其Lie代数，则存在同构：
$$H^n(  hetacal g;   hetacalmathbb{R})   hetacalcong H^n_{dR}(G;   hetacalmathbb{R})$$

这一同构的建立依赖于左不变微分形式：紧Lie群上的任何闭形式都同调于一个左不变形式，而左不变形式完全由其在单位元处的值决定，即由 $  hetacal g^*$ 中的元素决定。

**几何直观**：Lie代数上同调可以看作是"Lie群上同调在无穷小层面的表现"。群上同调中的上边缘算子对应于Lie代数上同调中的Chevalley-Eilenberg微分。

### 1.2 范畴论语境

$$H^n(  hetacal g, M) =   ext{Ext}^n_{U(  hetacal g)}(k, M)$$

其中 $U(  hetacal g)$ 是泛包络代数。

**为什么用泛包络代数？** Lie代数表示论的基本定理（Poincaré-Birkhoff-Witt定理）告诉我们，$U(  hetacal g)$ 的表示范畴与 $  hetacal g$ 的表示范畴等价。因此，Lie代数上同调可以看作是 $U(  hetacal g)$-模的导出函子上同调。

### 1.3 形式定义

#### 定义 1.1 (Chevalley-Eilenberg复形)

$$C^n(  hetacal g, M) =   ext{Hom}_k(  hetacalLambda^n   hetacal g, M)$$

微分 $  hetadelta: C^n(  hetacal g, M)   hetato C^{n+1}(  hetacal g, M)$ 定义为：
$$(  hetadelta   hetacalomega)(x_0, ..., x_n) =   hetasum_{i=0}^n (-1)^i x_i   hetacalcdot   hetacalomega(x_0, ...,   hetahat{x}_i, ..., x_n) +   hetasum_{i<j} (-1)^{i+j}   hetacalomega([x_i, x_j], x_0, ...,   hetahat{x}_i, ...,   hetahat{x}_j, ..., x_n)$$

**各项的含义**：

- 第一项：$  hetacal g$ 在 $M$ 上的作用
- 第二项：Lie括号的外代数结构

#### 定义 1.2 (Lie代数上同调群)

$$H^n(  hetacal g, M) =   hetaker(  hetadelta_n) /   ext{im}(  hetadelta_{n-1})$$

---

## 2. 属性与关系

### 2.1 低维解释

**定理 2.1**

- $H^0(  hetacal g, M) = M^{  hetacal g} = \{m   hetacalin M   hetamid x   hetacalcdot m = 0,   hetaforall x   hetacalin   hetacal g\}$
- $H^1(  hetacal g, M) =   ext{Der}(  hetacal g, M) /   ext{InnDer}(  hetacal g, M)$（导子模去内导子）
- $H^2(  hetacal g, M) = \{  ext{Lie代数扩张 } 0   hetato M   hetato   hetacalhat{g}   hetato   hetacal g   hetato 0\text{ 的等价类}\}$

**$H^1$ 的详细解释**：导子 $d:   hetacal g   hetato M$ 满足 Leibniz 法则：
$$d([x,y]) = x   hetacalcdot d(y) - y   hetacalcdot d(x)$$

内导子具有形式 $d_m(x) = x   hetacalcdot m$（$m   hetacalin M$ 固定）。$H^1 = 0$ 意味着所有导子都是内导子。

**$H^2$ 的详细解释**：给定2-上循环 $  hetacalomega   hetacalin Z^2(  hetacal g, M)$，可构造扩张 $  hetacalhat{g} =   hetacal g   hetacaloplus M$，其Lie括号为：
$$[(x, m), (y, n)] = ([x, y], x   hetacalcdot n - y   hetacalcdot m +   hetacalomega(x, y))$$

两个2-上循环定义等价扩张当且仅当它们相差一个上边缘。

### 2.2 Whitehead引理

**定理 2.2 (Whitehead)**
设 $  hetacal g$ 是半单Lie代数，$M$ 是有限维表示。
$$H^1(  hetacal g, M) = H^2(  hetacal g, M) = 0$$

**详细证明**：半单Lie代数的Weyl定理断言：任何有限维表示都是完全可约的。

**$H^1 = 0$ 的证明**：

1. 由Weyl定理，$M = M_1   hetacaloplus M_2$，其中 $M_1 = M^{  hetacal g}$（不变子空间），$M_2$ 没有非零不变向量
2. 对 $M_1$：导子 $d:   hetacal g   hetato M_1$ 满足 $d([x,y]) = 0$（因 $  hetacal g$ 在 $M_1$ 上作用平凡）
3. 由于 $[  hetacal g,   hetacal g] =   hetacal g$（半单性），$d = 0$
4. 对 $M_2$：需要更精细的论证（见Weyl's unitarian trick）

**推论**：半单Lie代数的所有有限维表示都是完全可约的。

### 2.3 与Lie群上同调的关系

**定理 2.3**：设 $G$ 是单连通Lie群，$  hetacal g$ 是其Lie代数，$M$ 是有限维表示。则：
$$H^n_{cts}(G, M)   hetacalcong H^n(  hetacal g, M)$$

其中左边是连续群上同调。

---

## 3. 深入示例

### 3.1 例子：$  hetacal g =   hetacalmathfrak{sl}_2(  hetacalmathbb{C})$ 的上同调

$  hetacalmathfrak{sl}_2(  hetacalmathbb{C})$ 有标准基 $\{e, f, h\}$，满足：
$$[h, e] = 2e,   hetatquad [h, f] = -2f,   hetatquad [e, f] = h$$

**计算 $H^*(  hetacalmathfrak{sl}_2,   hetacalmathbb{C})$（平凡表示）**：

由Whitehead引理，$H^1 = H^2 = 0$。

**$H^3$ 的计算**：考虑3-形式 $  hetacalomega(e, f, h) = 1$。验证这是上循环：
$$  hetadelta   hetacalomega(x_1, x_2, x_3, x_4) =   hetacalomega([x_1, x_2], x_3, x_4) -   hetacalomega([x_1, x_3], x_2, x_4) +   hetacalomega([x_1, x_4], x_2, x_3) +   hetacalomega([x_2, x_3], x_1, x_4) -   hetacalomega([x_2, x_4], x_1, x_3) +   hetacalomega([x_3, x_4], x_1, x_2)$$

由于 $  hetacalmathfrak{sl}_2$ 是3维的，唯一的非零3-形式是体积形式。通过对称性分析，可以证明 $H^3(  hetacalmathfrak{sl}_2,   hetacalmathbb{C}) =   hetacalmathbb{C}$。

**一般结果**：对半单Lie代数 $  hetacal g$，$H^3(  hetacal g,   hetacalmathbb{C})   hetacalneq 0$ 当且仅当 $  hetacal g$ 有单分量。$H^3$ 中的元素与 $  hetacal g$ 上的**不变对称双线性型**（Killing形式）密切相关。

### 3.2 例子：Heisenberg Lie代数

Heisenberg Lie代数 $  hetacal h_3$ 是3维幂零Lie代数，基为 $\{x, y, z\}$，满足：
$$[x, y] = z,   hetatquad [x, z] = [y, z] = 0$$

**计算 $H^2(  hetacal h_3,   hetacalmathbb{C})$**：

由于 $  hetacal h_3$ 不是半单的，Whitehead引理不适用。直接计算Chevalley-Eilenberg复形：

$C^2(  hetacal h_3,   hetacalmathbb{C})$ 由 $\{\thetacalomega_{xy}, \thetacalomega_{xz}, \thetacalomega_{yz}\}$ 张成，其中 $\thetacalomega_{ab}(a, b) = 1$。

上边缘 $  hetadelta: C^1   hetato C^2$：对 $f   hetacalin C^1$，
$$  hetadelta f(x, y) = -f([x, y]) = -f(z)$$

因此 $  ext{im}(  hetadelta) =   hetacalmathbb{C}   hetacalomega_{xy}$。

上循环条件 $  hetadelta   hetacalomega = 0$（在 $C^3$ 中，因 $  hetacal h_3$ 是3维的）：
$$  hetadelta   hetacalomega(x, y, z) =   hetacalomega([x, y], z) -   hetacalomega([x, z], y) +   hetacalomega([y, z], x) =   hetacalomega(z, z) = 0$$

因此所有2-形式都是上循环，$Z^2 = C^2   hetacalcong   hetacalmathbb{C}^3$。

$$H^2(  hetacal h_3,   hetacalmathbb{C}) = Z^2 / B^2 =   hetacalmathbb{C}^3 /   hetacalmathbb{C} =   hetacalmathbb{C}^2$$

**几何意义**：$H^2   hetacalneq 0$ 反映了Heisenberg Lie代数有非平凡的中心扩张。事实上，Heisenberg代数本身就是最经典的中心扩张例子。

---

## 4. 示例与习题

### 4.1 习题

#### 习题 1

计算 $H^*(  hetacalmathfrak{sl}_2,   hetacalmathbb{C})$。

**详细解答**：设 $\thetacal g =   hetacalmathfrak{sl}_2(  hetacalmathbb{C}})$，平凡表示。

**$H^0$**：$H^0 =   hetacalmathbb{C}^{  hetacal g} =   hetacalmathbb{C}$（常数）。

**$H^1$**：由Whitehead引理，$H^1 = 0$。

**$H^2$**：由Whitehead引理，$H^2 = 0$。

**$H^3$**：由前述分析，$H^3 =   hetacalmathbb{C}$，生成元为Killing形式诱导的体积形式。

**更高维**：对半单Lie代数，$H^n(  hetacal g,   hetacalmathbb{C})   hetacalcong (  hetacalLambda^n   hetacal g^*)^{  hetacal g}$（不变外形式）。对 $  hetacalmathfrak{sl}_2$，不变外形式只有 $1$（0次）和体积形式（3次），因此：
$$H^n(  hetacalmathfrak{sl}_2,   hetacalmathbb{C}) =   hetacalbegin{cases}   hetacalmathbb{C} & n = 0, 3 \\ 0 & n = 1, 2 \\ 0 & n   hetacalgeq 4   hetacalend{cases}$$

#### 习题 2

证明Whitehead引理。

**详细证明**：设 $  hetacal g$ 是半单Lie代数，$M$ 是有限维表示。

**$H^1 = 0$**：设 $d:   hetacal g   hetato M$ 是导子。定义Casimir算子 $C =   hetasum x_i x^i$（$\{x_i\}$ 是基，$\{x^i\}$ 是对偶基关于Killing形式）。

关键步骤：对半单Lie代数，Killing形式非退化。构造平均算子：
$$  hetavarphi =   hetaint_G g   hetacalcdot d(g^{-1}   hetacalcdot -) \, dg$$

（对紧形式积分）。可以证明 $d(x) = x   hetacalcdot m$ 对某个 $m   hetacalin M$。

**$H^2 = 0$**：类似地，用完全可约性将问题约化到平凡表示和非平凡不可约表示。对平凡表示，利用 $[  hetacal g,   hetacal g] =   hetacal g$；对非平凡表示，利用不变性。

#### 习题 3

证明 $H^n(  hetacal g, k)   hetacalcong H^n_{dR}(G)$ 对紧Lie群 $G$。

**详细证明**：设 $G$ 是紧Lie群。

**步骤1**：左不变形式。设 $  hetacalOmega^*(G)^G$ 是左不变微分形式复形。赋值映射 $  hetacalOmega^*(G)^G   hetato   hetacalLambda^*   hetacal g^*$ 是同构。

**步骤2**：de Rham上同调。$H^n_{dR}(G) = H^n(  hetacalOmega^*(G), d)$。

**步骤3**：平均化。对紧群，任何闭形式 $  hetacalomega$ 可以"平均化"为左不变形式：
$$  hetacalomega^G =   hetaint_G L_g^*   hetacalomega \, dg$$

其中 $L_g$ 是左平移。$  hetacalomega^G$ 与 $  hetacalomega$ 同调。

**步骤4**：Lie代数上同调。左不变形式的微分正是Chevalley-Eilenberg微分：
$$d  hetacalomega(x_0, ..., x_n) =   hetasum_{i<j} (-1)^{i+j}   hetacalomega([x_i, x_j], ...)$$

（无Lie导数项，因左不变性使 $x_i   hetacalcdot   hetacalomega = 0$）。

因此 $H^n_{dR}(G)   hetacalcong H^n(  hetacalLambda^*   hetacal g^*, d) = H^n(  hetacal g,   hetacalmathbb{R})$。$  hetacal square$

---

## 5. 形式化实现 (Lean 4)

```lean4
import Mathlib.Algebra.Lie.Cohomology

variable {k : Type*} [CommRing k] {g : Type*} [LieRing g] [LieAlgebra k g]
  {M : Type*} [AddCommGroup M] [Module k M] [LieRingModule g M] [LieModule k g M]

-- ============================================
-- Lie代数上同调
-- ============================================

def LieAlgebraCohomology (n : ℕ) : Type _ :=
  LieAlgebra.Cohomology k g M n
```

---

**维护者**: FormalMath项目组
**创建日期**: 2026年4月8日
**难度等级**: ⭐⭐⭐⭐
