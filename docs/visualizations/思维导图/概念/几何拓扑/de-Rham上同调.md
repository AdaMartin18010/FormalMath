---
msc_primary: 00

  - 00A99
title: de Rham上同调 (de Rham Cohomology)
processed_at: '2026-04-05'
---
msc_primary: "00A99"
msc_secondary: ['00-00']
---

# de Rham上同调 (de Rham Cohomology)

## 中心概念精确定义

**de Rham上同调**是光滑流形的代数拓扑不变量，通过微分形式定义，架起了分析与拓扑之间的桥梁。对光滑流形$M$，其$k$维de Rham上同调群定义为：

$$H^k_{dR}(M) = \frac{Z^k(M)}{B^k(M)} = \frac{\{\omega \in \Omega^k(M) : d\omega = 0\}}{\{d\eta : \eta \in \Omega^{k-1}(M)\}}$$

即**闭$k$-形式空间**模去**恰当$k$-形式空间**。

**核心思想**：闭形式是否在全局上为恰当形式的障碍反映了流形的拓扑结构。$H^k_{dR}(M) \neq 0$当且仅当存在$M$中$k$维的"洞"。

---

## 核心要素

### 1. de Rham复形

**微分形式复形**：
$$0 \to \Omega^0(M) \xrightarrow{d} \Omega^1(M) \xrightarrow{d} \cdots \xrightarrow{d} \Omega^n(M) \to 0$$

- 由$d^2 = 0$，这是**上链复形**（cochain complex）
- 上同调$H^k = \ker d_k / \text{im} \, d_{k-1}$

**de Rham上同调环**：$H^*_{dR}(M) = \bigoplus_k H^k_{dR}(M)$带有诱导的楔积：
$$[\omega] \wedge [\eta] = [\omega \wedge \eta]$$

构成分次交换代数：$[\alpha] \wedge [\beta] = (-1)^{kl}[\beta] \wedge [\alpha]$。

### 2. 同调群的结构

**0阶上同调**：$H^0_{dR}(M) \cong \mathbb{R}^{\pi_0(M)}$
- 闭0-形式是局部常值函数
- 连通分支数 = dim $H^0_{dR}(M)$

**最高阶上同调**：对紧致连通定向$n$-维流形：
$$H^n_{dR}(M) \cong \mathbb{R}$$
- 同构由积分给出：$[\omega] \mapsto \int_M \omega$

**Poincaré引理**：$H^k_{dR}(\mathbb{R}^n) = \begin{cases} \mathbb{R} & k = 0 \\ 0 & k > 0 \end{cases}$

### 3. Poincaré对偶

**定理**：设$M$是紧致定向$n$-维流形，则：
$$H^k_{dR}(M) \cong (H^{n-k}_{dR}(M))^*$$

**杯积配对**：
$$H^k_{dR}(M) \times H^{n-k}_{dR}(M) \to \mathbb{R}, \quad ([\omega], [\eta]) \mapsto \int_M \omega \wedge \eta$$

是非退化的。

**相交形式**：对$\dim M = 4k$，$H^{2k}_{dR}(M) \times H^{2k}_{dR}(M) \to \mathbb{R}$是_signature_的重要来源。

### 4. Künneth公式

**定理**：对光滑流形$M, N$：
$$H^k_{dR}(M \times N) \cong \bigoplus_{i+j=k} H^i_{dR}(M) \otimes H^j_{dR}(N)$$

**应用**：$H^*_{dR}(T^n) = H^*_{dR}(S^1)^{\otimes n} = \Lambda^*\mathbb{R}^n$

$n$-维环面有$\binom{n}{k}$个独立的$k$-维上同调类。

### 5. 诱导映射

**拉回映射**：光滑$f: M \to N$诱导：
$$f^*: H^k_{dR}(N) \to H^k_{dR}(M), \quad f^*[\omega] = [f^*\omega]$$

- 同伦不变性：$f \simeq g$则$f^* = g^*$
- 同伦等价诱导上同调同构
- 收缩核嵌入诱导单射

**Mayer-Vietoris序列**：对$M = U \cup V$：
$$\cdots \to H^k(M) \to H^k(U) \oplus H^k(V) \to H^k(U \cap V) \xrightarrow{\delta} H^{k+1}(M) \to \cdots$$

### 6. Hodge理论

**Laplace算子**：$\Delta = d\delta + \delta d$，其中$\delta = *d*$是余微分。

**Hodge定理**：在紧致定向Riemann流形上：
$$H^k_{dR}(M) \cong \mathcal{H}^k(M) = \{\omega : \Delta \omega = 0\}$$

即每上同调类有唯一的调和代表元。

---

## 性质与定理

### 定理1：de Rham定理

$$H^k_{dR}(M) \cong H^k_{\text{sing}}(M; \mathbb{R})$$

微分形式上同调与实系数的奇异上同调同构。积分配对$\langle \omega, c \rangle = \int_c \omega$给出同构。

### 定理2：Betti数与Euler示性数

$$b_k = \dim H^k_{dR}(M)$$称为第$k$个Betti数。

$$\chi(M) = \sum_{k=0}^n (-1)^k b_k = \sum_{k=0}^n (-1)^k \dim H^k_{dR}(M)$$

### 定理3：Lefschetz不动点定理

光滑$f: M \to M$的Lefschetz数：
$$L(f) = \sum_{k=0}^n (-1)^k \text{tr}(f^*: H^k_{dR}(M) \to H^k_{dR}(M))$$

若$L(f) \neq 0$，则$f$有不动点。

### 定理4：Thom同构与Gysin序列

对秩$k$定向向量丛$\pi: E \to M$：
$$H^i(E, E_0) \cong H^{i-k}(M)$$

导出球丛的Gysin长正合列。

### 定理5：Hard Lefschetz定理

对紧Kähler流形$(M, \omega)$：
$$L^{n-k}: H^k_{dR}(M) \xrightarrow{\cong} H^{2n-k}_{dR}(M), \quad L([\eta]) = [\omega \wedge \eta]$$

---

## 典型例子

### 例子1：球面$S^n$的上同调

$$H^k_{dR}(S^n) = \begin{cases} \mathbb{R} & k = 0, n \\ 0 & \text{otherwise} \end{cases}$$

- $H^0$由常数函数生成
- $H^n$由归一化体积形式生成
- 生成元可用极坐标显式构造

### 例子2：环面$T^n = (S^1)^n$

$$H^k_{dR}(T^n) \cong \mathbb{R}^{\binom{n}{k}}$$

由$d\theta_i$生成的外代数，$\theta_i \in [0, 2\pi]$是角坐标。

### 例子3：亏格$g$的定向闭曲面$\Sigma_g$

$$H^k_{dR}(\Sigma_g) = \begin{cases} \mathbb{R} & k = 0, 2 \\ \mathbb{R}^{2g} & k = 1 \\ 0 & \text{otherwise} \end{cases}$$

$H^1$的$2g$个生成元对应$g$个柄的经圈和纬圈。

---

## 关联概念

| 概念 | 关系 | 应用领域 |
|------|------|----------|
| **微分形式** | 定义基础 | 整体分析 |
| **奇异同调** | de Rham定理 | 代数拓扑 |
| **层上同调** | 推广形式 | 代数几何 |
| **指标定理** | 特征形式积分 | 数学物理 |
| **Morse理论** | 计算工具 | 动力系统 |
| **Hodge理论** | 调和形式代表 | 复几何 |

---

## Mermaid 思维导图

```mermaid
mindmap
  root((de Rham上同调<br/>de Rham Cohomology))
    定义
      Zᵏ闭形式
      Bᵏ恰当形式
      Hᵏ = Zᵏ/Bᵏ
      拓扑障碍
    基本性质
      H⁰ ≅ ℝ^π₀
      Hⁿ ≅ ℝ
      Poincaré引理
      同伦不变性
    Poincaré对偶
      Hᵏ ≅ (Hⁿ⁻ᵏ)*
      杯积配对
      相交形式
      符号差
    Künneth公式
      M × N的分解
      Tⁿ的计算
      外代数结构
    Mayer-Vietoris
      U ∪ V分解
      连接同态δ
      计算工具
    Hodge理论
      Δ = dδ + δd
      调和形式
      唯一代表元
      椭圆算子
    重要定理
      de Rham定理
      Betti数
      Euler示性数
      Lefschetz不动点

```

---

## 学术参考

**Princeton MAT 355**: de Rham cohomology as the bridge between differential forms and topology.

**MIT 18.905**: Singular cohomology and de Rham's theorem via integration.

**经典文献**：
- Bott & Tu, *Differential Forms in Algebraic Topology*
- Warner, F.W. *Foundations of Differentiable Manifolds and Lie Groups*
- Hatcher, A. *Algebraic Topology* (第3章)

---

*生成日期：2026年4月 | MSC2020: 58A12, 55N05, 14F40*
