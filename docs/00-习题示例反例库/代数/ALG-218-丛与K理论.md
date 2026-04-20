---
msc_primary: 00A99
习题编号: ALG-218
学科: 代数
知识点: 表示论-K理论
难度: ⭐⭐⭐⭐
预计时间: 50分钟
---

# 向量丛与 K-理论

## 题目

**(a)** 证明 Serre-Swan 定理。

**(b)** 定义拓扑 K-群 $K^0(X)$ 并证明 Bott 周期性。

**(c)** 讨论代数 K-群与拓扑 K-群的关系。

## 解答

### (a) Serre-Swan 定理

**定理**：设 $X$ 是紧 Hausdorff 空间。则：

$$\{\text{向量丛}\} \xrightarrow{\sim} \{\text{有限生成投射 } C(X)\text{-模}\}$$

*证明*：

**函子 $\Gamma$**：$E \mapsto \Gamma(E) = \{\text{连续截面}\}$。

- $\Gamma(E)$ 是 $C(X)$-模（逐点乘法）
- $E$ 局部平凡 $
$ \Rightarrow$ $\Gamma(E)$ 局部自由 $
$ \Rightarrow$ 投射

**逆构造**：对有限生成投射 $C(X)$-模 $P$，存在 idempotent $e \in M_n(C(X))$，$P = e C(X)^n$。

定义 $E = \{(x, v) \in X \times \mathbb{C}^n : v \in e(x)\mathbb{C}^n\}$。

**等价性**：$\Gamma(E) \cong P$，$E_P \cong E$。

---

### (b) 拓扑 K-群与 Bott 周期性

**$K^0(X)$**：向量丛的 Grothendieck 群：

$$K^0(X) = \{(E, F)\}/\sim$$

$(E, F) \sim (E', F')$ 若 $E \oplus F' \cong E' \oplus F$。

**约化 K-群**：$\tilde{K}^0(X) = \ker(K^0(X) \to K^0(pt))$。

**$K^{-n}(X)$**：

$$K^{-n}(X) = \tilde{K}^0(S^n X_+)$$

**Bott 周期性**：

$$\tilde{K}^{-n}(X) \cong \tilde{K}^{-n-2}(X)$$

*证明*（Atiyah-Bott-Shapiro）：

利用 Clifford 代数和 Thom 同构，$K^0(\mathbb{C}P^1) \cong \mathbb{Z}[H]/(H-1)^2$。

Bott 元 $\beta = [H] - [1]$ 生成 $\tilde{K}^0(S^2) \cong \mathbb{Z}$。

外部积 $\otimes \beta: K^{-n}(X) \to K^{-n-2}(X)$ 是同构。

---

### (c) 代数 K-群与拓扑 K-群

**代数 K-群**：对环 $A$，$K_0(A)$ 是有限生成投射 $A$-模的 Grothendieck 群。

**比较**：$A = C(X)$ 时，Serre-Swan 给出 $K_0(C(X)) \cong K^0(X)$。

**高阶 K-群**：

- **拓扑**：$K_i^{\mathrm{top}}(X) = \pi_i(BU \times \mathbb{Z})$（Bott 周期性，$i$ 模 2）
- **代数**：Quillen 的 $+$-构造，$K_i^{\mathrm{alg}}(A) = \pi_i(BGL(A)^+)$

**比较映射**：$K_i^{\mathrm{alg}}(C(X)) \to K_i^{\mathrm{top}}(X)$。

**Swan 定理**：此映射在 $i = 0$ 是同构，$i > 0$ 一般不同。

**Karoubi 的相对 K-理论**：$K^{\mathrm{rel}}$ 度量代数与拓扑 K-群的差异，与 cyclic homology 相关。

---

## 常见错误

- **投射模 vs 自由模**：投射模局部自由但不必整体自由（如 Möbius 带的截面模）。
- **Bott 周期的维数**：复 K-理论周期为 2，实 K-理论（KO）周期为 8。
- **代数 K-群的非交换性**：$K_1(A) = GL(A)/E(A)$，非交换环也有定义。

## 参考文献

- Atiyah, *K-Theory*.
- Swan, *Vector Bundles and Projective Modules*.
