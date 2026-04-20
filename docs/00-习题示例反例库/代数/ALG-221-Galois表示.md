---
msc_primary: 00A99
习题编号: ALG-221
学科: 代数
知识点: 代数数论-Galois表示
难度: ⭐⭐⭐⭐⭐
预计时间: 55分钟
---

# Galois 表示

## 题目

**(a)** 定义 $\ell$-adic Galois 表示并证明其基本性质。

**(b)** 证明 Tate 模上的 Galois 作用及特征标性质。

**(c)** 讨论 Fontaine-Laffaille 理论和 $p$-进 Hodge 理论。

## 解答

### (a) $\ell$-adic Galois 表示

**定义**：设 $K$ 是域，$G_K = \operatorname{Gal}(\overline{K}/K)$。$\ell$-adic Galois 表示是连续同态：

$$\rho: G_K \to \operatorname{GL}(V)$$

$V$ 是有限维 $\mathbb{Q}_\ell$-向量空间。

**连续性**：$G_K$ 的 Krull 拓扑（pro-finite），$\operatorname{GL}(V)$ 的 $\ell$-进拓扑。

**例**：

- **Tate 模**：$E/K$ 椭圆曲线，$T_\ell(E) = \varprojlim E[\ell^n] \cong \mathbb{Z}_\ell^2$
- **Étale 上同调**：$V = H^i_{\text{ét}}(X_{\overline{K}}, \mathbb{Q}_\ell)$

**性质**：

1. **惯性群**：$I_K \subset G_K$（惯性子群），$\rho|_{I_K}$ 给出单调性信息
2. **Frobenius**：对非分歧素 $v$，$\operatorname{Frob}_v \in G_K/I_K$
3. **特征多项式**：$\det(1 - \rho(\operatorname{Frob}_v)T | V^{I_v})$

---

### (b) Tate 模上的 Galois 作用

**椭圆曲线**：$E/K$，$T_\ell(E) \cong \mathbb{Z}_\ell^2$。

$$\rho_{E,\ell}: G_K \to \operatorname{GL}_2(\mathbb{Z}_\ell)$$

**性质**：

1. **行列式**：$\det \rho_{E,\ell} = \chi_\ell$（分圆特征标）
2. **Weil 配对**：$e_\ell: T_\ell(E) \times T_\ell(E) \to \mathbb{Z}_\ell(1)$，Galois 等变

**Frobenius 的迹**：$p \nmid \ell N_E$，

$$\operatorname{tr}(\rho_{E,\ell}(\operatorname{Frob}_p)) = a_p = p + 1 - |E(\mathbb{F}_p)|$$

**Serre 开像定理**：$E$ 无 CM 时，$\rho_{E,\ell}(G_\mathbb{Q})$ 在 $\operatorname{GL}_2(\mathbb{Z}_\ell)$ 中开。

---

### (c) Fontaine-Laffaille 理论

**$p$-进 Hodge 理论**：比较 $p$-adic Galois 表示与 de Rham 上同调。

**Fontaine 的环**：

| 环 | 性质 | 表示类型 |
|---|------|---------|
| $B_{HT}$ | Hodge-Tate | $V \otimes \mathbb{C}_p \cong \bigoplus \mathbb{C}_p(i)$ |
| $B_{dR}$ | de Rham | 有滤过 |
| $B_{st}$ | 半稳定 | 有滤过 + 单调算子 $N$ |
| $B_{crys}$ | 晶体 | 有滤过，$N = 0$ |

**比较函子**：$D_{?}(V) = (V \otimes B_{?})^{G_K}$。

**Fontaine-Laffaille 理论**：对 $K$ 绝对非分歧，$V$ 是 $G_K$ 的晶体表示，$D_{crys}(V)$ 是 filtered $\varphi$-module。

**分类定理**：$\{\text{晶体表示}\} \xrightarrow{\sim} \{\text{admissible filtered } \varphi\text{-modules}\}$。

**应用**：

- **Faltings 定理**：Abel 簇的 Tate 猜想
- **p-进 Langlands**：$GL_2(\mathbb{Q}_p)$ 的 $p$-进表示分类

---

## 常见错误

- **$\ell$-进表示的连续性**：$G_K$ 的拓扑是 Krull 拓扑，要求 $\rho^{-1}(U)$ 开对 $\operatorname{GL}(V)$ 的开子群 $U$。
- **惯性群的作用**：$\rho|_{I_K}$ 可能非平凡（wild inertia）。
- **$B_{dR}$ 的幂零元**：$B_{dR}$ 是 DVR，剩余域 $\mathbb{C}_p$，不是域的完备化。

## 参考文献

- Serre, *Abelian $\ell$-adic Representations and Elliptic Curves*.
- Fontaine, *Représentations $p$-adiques semi-stables*.
- Brinon & Conrad, *CMI Summer School notes on $p$-adic Hodge theory*.
