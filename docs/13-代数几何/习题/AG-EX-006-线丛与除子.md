---
习题编号: AG-EX-006
标题: 线丛与除子
类型: 综合型
难度: ⭐⭐⭐
章节: Hartshorne Ch II/IV
对应课程: Harvard Math 232br
预计用时: 90-120分钟
msc: 14C20, 14C22
---

# AG-EX-006: 线丛与除子

## 题目

### 原题 (Hartshorne II.6.2 + IV.4.1)

设 $X$ 是光滑射影曲线。

**(a)** 证明Weil除子类群、Cartier除子类群和线丛群（Picard群）之间的自然同构:
$$\text{Cl}(X) \cong \text{CaCl}(X) \cong \text{Pic}(X)$$

**(b)** 对 $X = \mathbb{P}^1$，证明 $\text{Pic}(X) \cong \mathbb{Z}$，由 $\mathcal{O}(1)$ 生成。

**(c)** 设 $X$ 是椭圆曲线，描述 $\text{Pic}^0(X)$（度0线丛）的群结构。

### 应用题目

设 $X$ 是亏格 $g$ 的曲线，$L$ 是 $d$ 次线丛。

**(a)** 证明 $\deg: \text{Pic}(X) \to \mathbb{Z}$ 是群同态。

**(b)** 描述短正合列:
$$0 \to \text{Pic}^0(X) \to \text{Pic}(X) \xrightarrow{\deg} \mathbb{Z} \to 0$$

---

## 解答

### 主题目解答

#### (a) 三类除子群同构

**Step 1: Weil除子 $	o$ Cartier除子**

在光滑簇上，每个Weil除子是Cartier的（正则局部环是UFD）。

给定Weil除子 $D = \sum n_i [P_i]$，局部方程为:
- 在 $P_i$ 附近: 局部坐标 $t_i$，方程为 $t_i^{n_i} = 0$
- 在其他点: 方程为 $1 = 0$

**Step 2: Cartier除子 $	o$ 线丛**

给定Cartier除子 $\{(U_i, f_i)\}$，其中 $f_i \in k(X)^*$，且 $f_i/f_j \in \mathcal{O}^*(U_i \cap U_j)$。

构造线丛 $L$:
- 转移函数: $g_{ij} = f_i/f_j \in \mathcal{O}^*(U_i \cap U_j)$
- 满足余链条件: $g_{ij}g_{jk}g_{ki} = 1$

**Step 3: 线丛 $	o$ Weil除子**

给定线丛 $L$，取非零有理截面 $s \in H^0(X, L \otimes k(X))$。

定义: $(s) = \sum_{P \in X} \nu_P(s) \cdot [P]$

两个截面相差乘法单位，给出相同的除子类。

**Step 4: 验证互逆**

- $D \mapsto L(D) \mapsto (s_D) = D$ ✓
- $L \mapsto (s) \mapsto L((s)) \cong L$ ✓

---

#### (b) $\text{Pic}(\mathbb{P}^1) \cong \mathbb{Z}$

**证明**:

**Step 1**: 构造映射 $\phi: \mathbb{Z} \to \text{Pic}(\mathbb{P}^1)$，$n \mapsto \mathcal{O}(n)$。

**Step 2**: 证明满射。

设 $L$ 是 $\mathbb{P}^1$ 上的线丛，取非零有理截面 $s$。

$(s) = \sum n_i [P_i] - \sum m_j [Q_j]$（零点减极点）。

总次数: $\deg(s) = \sum n_i - \sum m_j = d$。

则 $L \cong \mathcal{O}(d)$。

**Step 3**: 证明单射。

若 $\mathcal{O}(n) \cong \mathcal{O}(m)$，则 $\mathcal{O}(n-m) \cong \mathcal{O}$。

$\mathcal{O}(k) \cong \mathcal{O}$ 当且仅当 $h^0(\mathcal{O}(k)) = h^0(\mathcal{O}) = 1$。

这需要 $k = 0$。

**结论**: $\text{Pic}(\mathbb{P}^1) \cong \mathbb{Z}$，由 $\mathcal{O}(1)$ 生成。

---

#### (c) 椭圆曲线的 $\text{Pic}^0(X)$

设 $E$ 是椭圆曲线，固定点 $P_0 \in E$。

**定理**: 映射 $\phi: E \to \text{Pic}^0(E)$，$P \mapsto \mathcal{O}(P - P_0)$ 是群同构。

**证明**:

**Step 1: 良定性**

$\deg(P - P_0) = 0$，故 $\mathcal{O}(P - P_0) \in \text{Pic}^0(E)$。

**Step 2: 单射**

若 $\mathcal{O}(P - P_0) \cong \mathcal{O}(Q - P_0)$，则 $\mathcal{O}(P) \cong \mathcal{O}(Q)$。

故存在 $f$ 使得 $(f) = Q - P$，即 $P \sim Q$。

在椭圆曲线上，$P \sim Q$ 当且仅当 $P = Q$（Abel-Jacobi）。

**Step 3: 满射**

设 $L \in \text{Pic}^0(E)$，则 $\deg(L) = 0$。

由Riemann-Roch:
$$h^0(L) - h^1(L) = 0 + 1 - 1 = 0$$

Serre对偶: $h^1(L) = h^0(L^{-1}) = h^0(K \otimes L^{-1}) = h^0(L^{-1})$（$K = \mathcal{O}$）。

若 $h^0(L) = 0$，则 $L \cong \mathcal{O}$（对应 $P = P_0$）。

若 $h^0(L) > 0$，则存在有效除子 $D \in |L|$，$\deg(D) = 0$，故 $D = P$ 是一点。

$\mathcal{O}(P - P_0) \cong L$，即 $P$ 是原像。

**Step 4: 群结构**

$E$ 的群法则: $P \oplus Q = R$ 其中 $P + Q \sim R + P_0$。

这对应于 $\text{Pic}^0(E)$ 的张量积: $\mathcal{O}(P - P_0) \otimes \mathcal{O}(Q - P_0) = \mathcal{O}(R - P_0)$。

**结论**: $\text{Pic}^0(E) \cong E$ 作为代数群。

---

### 应用题目解答

#### (a) 次数同态

**定义**: 对 $L \in \text{Pic}(X)$，$\deg(L) = \deg(D)$ 其中 $L \cong \mathcal{L}(D)$。

**证明同态性**:

设 $L_1 = \mathcal{L}(D_1)$, $L_2 = \mathcal{L}(D_2)$。

$$L_1 \otimes L_2 = \mathcal{L}(D_1) \otimes \mathcal{L}(D_2) = \mathcal{L}(D_1 + D_2)$$

$$\deg(L_1 \otimes L_2) = \deg(D_1 + D_2) = \deg(D_1) + \deg(D_2) = \deg(L_1) + \deg(L_2)$$

---

#### (b) 短正合列

**Step 1**: $\text{Pic}^0(X) = \ker(\deg)$。

**Step 2**: 构造分裂。

固定点 $P_0 \in X$，定义 $s: \mathbb{Z} \to \text{Pic}(X)$，$n \mapsto \mathcal{O}(nP_0)$。

则 $\deg(s(n)) = n$，故 $s$ 是分裂。

**Step 3**: 直和分解。

$$\text{Pic}(X) \cong \text{Pic}^0(X) \oplus \mathbb{Z}$$

**几何意义**: 
- $\text{Pic}^0(X)$: "连续"部分（Jacobi簇）
- $\mathbb{Z}$: "离散"部分（次数）

---

## 解题技巧

### 技巧1: 除子-线丛对应速查

```
┌─────────────────────────────────────────┐
│  D = Σ n_i[P_i]  ↔  L(D)               │
│                                         │
│  L(D)_P = {f ∈ k(X)* : (f) + D ≥ 0}    │
│           ∪ {0}                         │
│                                         │
│  H^0(X, L(D)) = L(D)(X) = L(D)          │
└─────────────────────────────────────────┘
```

### 技巧2: Picard群计算策略

1. **找生成元**: 通常由点或超平面生成
2. **找关系**: 线性等价给出关系
3. **验证**: 用Euler示性数或上同调

### 技巧3: 椭圆曲线的特殊性质

```
椭圆曲线 E:
├─ K_E = O_E (典范平凡)
├─ h^1(O_E) = 1
├─ Pic^0(E) ≅ E (群同构)
└─ 自同态环 End(E) 丰富
```

---

## 变式与推广

### 变式1: 一般曲线的Jacobi簇

设 $X$ 是亏格 $g$ 的曲线。

**问题**: 证明 $\text{Pic}^0(X)$ 是 $g$ 维Abel簇（Jacobi簇）。

---

### 变式2: 乘积空间的Picard群

计算 $\text{Pic}(\mathbb{P}^n \times \mathbb{P}^m)$。

**答案**: $\mathbb{Z} \oplus \mathbb{Z}$，由两个投影的拉回生成。

---

### 变式3: 挠子群

设 $E$ 是椭圆曲线，$E[n] = \{P \in E : nP = 0\}$。

**问题**: 证明 $E[n] \cong (\mathbb{Z}/n\mathbb{Z})^2$。

---

## 相关概念

| 概念 | 定义 | 符号 |
|:---|:---|:---:|
| Weil除子 | 余维1闭链的形式和 | $\text{Div}(X)$ |
| Cartier除子 | 局部方程定义的除子 | $\text{CaDiv}(X)$ |
| Picard群 | 线丛的同构类群 | $\text{Pic}(X)$ |
| Jacobi簇 | $\text{Pic}^0$ 的代数结构 | $J(X)$ |

## 参考文献

1. Hartshorne, R. *Algebraic Geometry*, Ch II, §6
2. Griffiths, Harris. *Principles of Algebraic Geometry*, Ch 2
3. Milne, J. *Abelian Varieties*

---

**创建日期**: 2026-04-10  
**难度**: ⭐⭐⭐  
**预计用时**: 90-120分钟
