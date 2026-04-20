---
msc_primary: 00A99
习题编号: AG-059
学科: 代数几何
知识点: 代数几何-高阶Chow群
难度: ⭐⭐⭐⭐⭐
预计时间: 55分钟
---

# 高阶 Chow 群

## 题目

**(a)** 定义 Bloch 的高阶 Chow 群。

**(b)** 证明高阶 Chow 群与 motivic 上同调的关系。

**(c)** 讨论循环映射和 Abel-Jacobi 映射。

---

## 解答

### (a) Bloch的高阶Chow群

#### 代数单形

**代数单形**：
$$\Delta^n = \text{Spec}\, k[t_0, \ldots, t_n]/(t_0 + \cdots + t_n - 1)$$

面映射：$\partial_i: \Delta^{n-1} \to \Delta^n$（设 $t_i = 0$）。

#### 高阶闭链

设 $X$ 是光滑簇。

$$z^p(X, n) = \{Z \subseteq X \times \Delta^n : Z \text{ 余维 } p \text{，与所有面正常相交}\}$$

**Bloch复形**：
$$\cdots \to z^p(X, 2) \xrightarrow{\partial} z^p(X, 1) \xrightarrow{\partial} z^p(X, 0) \to 0$$

其中 $\partial = \sum (-1)^i \partial_i^*$。

#### 高阶Chow群

$$CH^p(X, n) = H_n(z^p(X, \cdot))$$

**性质**：
- $CH^p(X, 0) = CH^p(X)$（经典Chow群）
- $CH^p(X, n) = 0$（$n > p$ 或 $n > \dim X$）

---

### (b) Motivic上同调

#### Voevodsky的构造

**定理**（Voevodsky）：
$$H^i_M(X, \mathbb{Z}(p)) = CH^p(X, 2p-i)$$

**Motivic上同调的性质**：
1. **Betti实现**：$H^i_M(X, \mathbb{Q}(p)) \to H^i_B(X, \mathbb{Q}(p))$
2. **étale实现**：$H^i_M(X, \mathbb{Z}/n) \to H^i_{\text{\'et}}(X, \mu_n^{\otimes p})$
3. **de Rham实现**：$H^i_M(X, \mathbb{Q}(p)) \to H^i_{dR}(X)$

#### 与K-理论的联系

**Bloch-Lichtenbaum谱序列**：
$$E_2^{p,q} = CH^{-q}(X, -p-q) \Rightarrow K_{-p-q}(X)$$

#### Beilinson猜想

$$\text{ord}_{s=p} L(H^{2p-i}(X), s) = \dim_\mathbb{Q} H^i_M(X, \mathbb{Q}(p))$$

---

### (c) 循环映射与Abel-Jacobi

#### 循环映射

**经典循环映射**：
$$\text{cl}: CH^p(X) \to H^{2p}(X, \mathbb{Z}(p))$$

**高阶循环映射**：
$$\text{cl}: CH^p(X, n) \to H^{2p-n}(X, \mathbb{Z}(p))$$

#### Abel-Jacobi映射

对 $Z \in CH^p(X)_{\text{hom}}$（同调平凡的）：
$$\Phi: CH^p(X)_{\text{hom}} \to J^p(X) = \frac{H^{2p-1}(X, \mathbb{C})}{F^p + H^{2p-1}(X, \mathbb{Z})}$$

**高阶Abel-Jacobi**：对高阶Chow群，有类似的映射到 intermediate Jacobian。

#### 应用

- **Griffiths群**：$\text{Griff}^p(X) = CH^p(X)_{\text{hom}} / CH^p(X)_{\text{alg}}$，可能非零
- **Bloch猜想**：$S$ 是一般型曲面 $\Rightarrow$ $CH^2(S)_{\text{hom}} = 0$