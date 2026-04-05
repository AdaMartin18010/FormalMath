---
msc_primary: 00A99
msc_secondary:
- 00A99
title: Morse理论 (Morse Theory)
processed_at: '2026-04-05'
---
msc_primary: "00A99"
msc_secondary: ['00-XX']
---

# Morse理论 (Morse Theory)

## 中心概念精确定义

**Morse理论**研究光滑流形上函数临界点的拓扑信息，建立了分析与拓扑之间的深刻联系。**Morse函数**$f: M \to \mathbb{R}$是满足以下条件的函数：

1. **临界点非退化**：若$df(p) = 0$，则Hessian$H_f(p)$非奇异
2. **临界点有限**（或满足紧性条件）

**Morse指标**：临界点$p$的**指标**$\lambda(p)$是$H_f(p)$的负特征值个数。

**Morse引理**：在临界点$p$附近存在坐标使得：
$$f(x) = f(p) - x_1^2 - \cdots - x_\lambda^2 + x_{\lambda+1}^2 + \cdots + x_n^2$$

**核心思想**：流形的拓扑结构可通过Morse函数的临界点重构。

---

## 核心要素

### 1. Morse函数

**临界点**：$\text{Crit}(f) = \{p \in M : df_p = 0\}$

**非退化条件**：Hessian矩阵$\left(\frac{\partial^2 f}{\partial x^i \partial x^j}\right)_p$满秩。

**Morse指标**：$\lambda(p) = \#\{\text{负特征值 of } H_f(p)\} \in \{0, 1, \ldots, n\}$

**例子**：
- 高度函数在环面上：4个临界点（极小、两个鞍、极大）
- 指标分布：0, 1, 1, 2

### 2. 胞腔附着

**水平集拓扑变化**：当$c$经过临界点$p$（$f(p) = c$），$M^{c+\epsilon} = f^{-1}(-\infty, c+\epsilon]$相对于$M^{c-\epsilon}$附着$\lambda(p)$-维胞腔$e^{\lambda(p)}$。

**基本定理**：若$M^a$到$M^b$之间无临界点，则$M^a \simeq M^b$（同伦等价）。

**Morse不等式**：设$c_k$是指标$k$临界点个数，$b_k = \dim H_k(M)$：
- **弱Morse不等式**：$c_k \geq b_k$
- **强Morse不等式**：$\sum_{i=0}^k (-1)^{k-i}c_i \geq \sum_{i=0}^k (-1)^{k-i}b_i$
- **Euler关系**：$\sum (-1)^k c_k = \chi(M)$

### 3. CW结构

**定理**：紧流形具有CW结构，$k$-胞腔对应指标$k$临界点。

**构造**：
- 每个临界点$p$给出胞腔$e^{\lambda(p)}$
- 附着映射由梯度流线给出

**同伦型**：$M \simeq \bigvee_{\text{crit}(f)} S^{\lambda(p)}$（同伦意义下）。

### 4. 梯度流与稳定/不稳定流形

**梯度向量场**：$\nabla f$满足$g(\nabla f, X) = df(X)$。

**梯度流**：$\frac{d\gamma}{dt} = -\nabla f(\gamma(t))$

**稳定流形**：
$$W^s(p) = \{x \in M : \lim_{t \to +\infty} \phi_t(x) = p\}$$

**不稳定流形**：
$$W^u(p) = \{x \in M : \lim_{t \to -\infty} \phi_t(x) = p\}$$

**维数**：$\dim W^s(p) = n - \lambda(p)$，$\dim W^u(p) = \lambda(p)$

**横截条件**：Morse-Smale条件要求$W^u(p) \pitchfork W^s(q)$对所有$p, q$。

### 5. Morse同调

**链复形**：$C_k = \mathbb{Z}^{\#\{\text{指标}k\text{临界点}\}}$

**边界算子**：
$$\partial p = \sum_{q: \lambda(q) = k-1} \langle p, q \rangle \cdot q$$

其中$\langle p, q \rangle$计数从$p$到$q$的梯度流线数（模2或有向）。

**定理**：$H_*^{\text{Morse}}(M; f) \cong H_*^{\text{sing}}(M)$

### 6. Lusternik-Schnirelmann理论

**范畴（category）**：空间$X$的LS范畴$\text{cat}(X)$是覆盖$X$所需可缩开集的最小数目。

**临界点下界**：
$$\#\text{Crit}(f) \geq \text{cat}(M) \geq \text{cuplength}(M) + 1$$

**cup长**：$\text{cuplength} = \max\{k : \exists \alpha_1, \ldots, \alpha_k \in \tilde{H}^*(M), \alpha_1 \cup \cdots \cup \alpha_k \neq 0\}$

---

## 性质与定理

### 定理1：Morse引理

在临界点$p$附近存在坐标使$f$为二次标准形。

### 定理2：Reeb定理

若$M$上存在恰有两个临界点的Morse函数，则$M$同胚于球面。

### 定理3：Bott周期性（Morse理论证明）

基于路径空间上的能量泛函。

### 定理4：Morse不等式是最优的

当所有不等式取等号时，Morse函数称为**完美的**。

### 定理5：Floer理论的推广

到无限维情形（辛作用泛函、Chern-Simons泛函）。

---

## 典型例子

### 例子1：环面$T^2$的高度函数

- 极小点（底部）：指标0
- 两个鞍点：指标1
- 极大点（顶部）：指标2

$c_0 = 1, c_1 = 2, c_2 = 1$，$b_0 = 1, b_1 = 2, b_2 = 1$（满足Morse等式）

### 例子2：复射影空间$\mathbb{C}P^n$

函数$f([z_0:\cdots:z_n]) = \sum k|z_k|^2/\sum|z_k|^2$：

- $n+1$个临界点
- 指标为$0, 2, 4, \ldots, 2n$
- 完美的Morse函数

### 例子3：测地线的能量泛函

路径空间$\Omega(M; p, q)$上的能量泛函：
$$E(\gamma) = \int_0^1 g(\dot{\gamma}, \dot{\gamma}) dt$$

临界点是测地线，指标是共轭点数（带重数）。

---

## 关联概念

| 概念 | 关系 | 应用领域 |
|------|------|----------|
| **CW复形** | 胞腔分解 | 代数拓扑 |
| **同调论** | Morse同调 | 辛几何 |
| **Floer理论** | 无限维推广 | 低维拓扑 |
| **指标定理** | 热核方法 | 数学物理 |
| **动力系统** | 梯度流 | 动力系统 |
| **辛几何** | 作用泛函 | 弦理论 |

---

## Mermaid 思维导图

```mermaid
mindmap
  root((Morse理论<br/>Morse Theory))
    Morse函数
      非退化临界点
      Morse指标λ
      Morse引理
      有限临界点
    胞腔附着
      Mᶜ⁺ᵋ ≃ Mᶜ⁻ᵋ ∪ eᵝ
      CW结构
      同伦型
      拓扑变化
    Morse不等式
      ck ≥ bk
      强不等式
      χ(M) = Σ(-1)ᵏck
      完美Morse函数
    梯度流
      ∇f向量场
      稳定流形Ws
      不稳定流形Wu
      Morse-Smale条件
    Morse同调
      链复形Ck
      梯度流线计数
      ∂² = 0
      ≅ 奇异同调
    Lusternik-Schnirelmann
      cat(M)范畴
      cuplength
      临界点下界
      拓扑约束

```

---

## 学术参考

**Princeton MAT 355**: Morse theory as the bridge between critical point theory and topology.

**MIT 18.905**: Morse theory and the topology of manifolds via CW complexes.

**经典文献**：
- Milnor, J. *Morse Theory*
- Milnor, J. *Lectures on the h-Cobordism Theorem*
- Audin & Damian, *Morse Theory and Floer Homology*
- Schwarz, M. *Morse Homology*

---

*生成日期：2026年4月 | MSC2020: 58E05, 57R70, 58E10*
