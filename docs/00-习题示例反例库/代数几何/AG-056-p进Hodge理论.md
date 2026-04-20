---
msc_primary: 00A99
习题编号: AG-056
学科: 代数几何
知识点: 代数几何-p进Hodge
难度: ⭐⭐⭐⭐⭐
预计时间: 60分钟
---

# p-进 Hodge 理论

## 题目

**(a)** 证明 $p$-进比较定理：étale 上同调与 de Rham 上同调。

**(b)** 讨论 Fontaine 的环 $B_{dR}$、$B_{crys}$ 的构造。

**(c)** 证明半稳定表示的判别及其与 de Rham 表示的关系。

## 解答

### (a) p-进比较定理

**定理（Faltings, Tsuji, Niziol）**：设 $X$ 是特征零完备离散赋值域 $K$ 上的真光滑簇。则：

$$H^i_{\text{ét}}(X_{\overline{K}}, \mathbb{Q}_p) \otimes_{\mathbb{Q}_p} B_{dR} \cong H^i_{\text{dR}}(X/K) \otimes_K B_{dR}$$

且此同构保持滤过（Hodge 滤过与étale 的某种滤过对应）。

*证明概要*：

1. **近 proper 情形**：先证 $X$ 有 good reduction 的情形（用 crystalline 上同调）。

2. **Simpson 的函子ial 同构**：构造从 étale 到 de Rham 的 canonical 同构。

3. **Poincaré 引理**：$p$-进版本的 de Rham 复形与常数层的比较。

4. **Galois 等变性**：同构与 $G_K$ 作用相容。

**推论**：$\dim_{\mathbb{Q}_p} H^i_{\text{ét}} = \dim_K H^i_{\text{dR}}$。

---

### (b) Fontaine 的环

**$\mathbb{C}_K$**：$K$ 的代数闭包的 $p$-进完备化。

**$A_{\mathrm{inf}}$**：Witt 向量的无穷范数完备化，$A_{\mathrm{inf}} = W(\mathcal{O}_{\mathbb{C}_K}^\flat)$。

**$B_{dR}^+$**：$A_{\mathrm{inf}}[1/p]$ 关于 $\ker(\theta)$ 的完备化，其中 $\theta: A_{\mathrm{inf}} \to \mathcal{O}_{\mathbb{C}_K}$。

**$B_{dR}$**：$B_{dR}^+$ 的分式域。是 $G_K$-不变的完备 DVR，剩余域 $\mathbb{C}_K$。

**滤过**：$\operatorname{Fil}^i B_{dR} = (\xi)^i B_{dR}^+$，其中 $\xi$ 是 uniformizer。

**$B_{crys}$**：$B_{dR}$ 的子环，包含 crystalline 周期。有 Frobenius $\varphi$ 作用。

**$B_{st}$**：$B_{crys}[\log[\varpi]]$，有额外的 monodromy 算子 $N$。

**性质**：

| 环 | 分式域 | Frobenius | 算子 $N$ | 滤过 |
|---|-------|----------|---------|------|
| $B_{crys}$ | 有 | $\varphi$ | 无 | 有 |
| $B_{st}$ | 有 | $\varphi$ | $N$ | 有 |
| $B_{dR}$ | 是 | 无 | 无 | 有 |

---

### (c) 半稳定表示

**定义**：$p$-adic 表示 $V$ 是：

- **de Rham**：$\dim_K D_{dR}(V) = \dim_{\mathbb{Q}_p} V$，其中 $D_{dR}(V) = (V \otimes B_{dR})^{G_K}$
- **半稳定**：$\dim_K D_{st}(V) = \dim_{\mathbb{Q}_p} V$
- **晶体**：半稳定且 $N = 0$

**关系**：

$$\text{晶体} \; \Rightarrow \; \text{半稳定} \; \Rightarrow \; \text{de Rham}$$

**Cerffalaine 猜想/定理（Berger, 2002）**：de Rham $
$ \Leftrightarrow$ potentially 半稳定。

即任何 de Rham 表示在 $K$ 的有限扩张上变为半稳定。

**判别**：$V$ 是 de Rham 当且仅当 $V$ 是 potentially 半稳定。

---

## 常见错误

- **$B_{dR}$ 与 $\mathbb{C}_p$ 的区别**：$B_{dR}$ 是域，但有非平凡 Galois 作用；$\mathbb{C}_p$ 的 Galois 作用不连续。
- **半稳定 vs 潜在半稳定**：潜在半稳定允许域扩张，de Rham 不自动半稳定。
- **比较定理的条件**：需 $X$ proper smooth，非 proper 需紧支或 log 结构。

## 参考文献

- Fontaine, *Représentations $p$-adiques semi-stables*.
- Tsuji, *p-adic étale cohomology and crystalline cohomology in the semi-stable reduction case*.
