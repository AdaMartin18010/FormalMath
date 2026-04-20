---
msc_primary: 00A99
习题编号: ALG-200
学科: 代数
知识点: 代数数论-p进数
难度: ⭐⭐⭐⭐
预计时间: 40分钟
---

# p-进数

## 题目

**(a)** 构造 p-进数域 $\mathbb{Q}_p$ 并证明其拓扑性质。

**(b)** 证明 Hensel 引理及其应用。

**(c)** 讨论局部域 Galois 理论（局部类域论）。

## 解答

### (a) $\mathbb{Q}_p$ 的构造与拓扑性质

**定义（p-进赋值）**：对素数 $p$，$\mathbb{Q}$ 上的 **p-进赋值**定义为：
$$v_p: \mathbb{Q}^\times \to \mathbb{Z}, \quad v_p(p^n \frac{a}{b}) = n$$
其中 $a, b$ 与 $p$ 互素。$p$-进绝对值：
$$|x|_p = p^{-v_p(x)}, \quad |0|_p = 0$$

满足强三角不等式（ultrametric inequality）：$|x + y|_p \leq \max(|x|_p, |y|_p)$，等号当 $|x|_p \neq |y|_p$ 时成立。

**构造**：$\mathbb{Q}_p$ 是 $\mathbb{Q}$ 关于 $|\cdot|_p$ 的完备化。

**定理（$\mathbb{Q}_p$ 的显式描述）**：每个 $x \in \mathbb{Q}_p$ 可唯一表示为：
$$x = \sum_{n \geq N} a_n p^n$$
其中 $N \in \mathbb{Z}$，$a_n \in \{0, 1, \ldots, p-1\}$，$a_N \neq 0$（若 $x \neq 0$）。

*证明*：完备化的标准构造。$\mathbb{Q}$ 中 Cauchy 列 $\{x_n\}$ 关于 $|\cdot|_p$ 收敛当且仅当 $|x_{n+1} - x_n|_p \to 0$。利用整数的 $p$-进展开，极限给出上述形式。∎

**$\mathbb{Q}_p$ 的拓扑性质**：

**定理**：$(\mathbb{Q}_p, +)$ 是局部紧 Abel 群。

*证明*：
1. ** Hausdorff**：由度量空间的性质。
2. **局部紧**：$\mathbb{Z}_p = \{x \in \mathbb{Q}_p : |x|_p \leq 1\} = \{x = \sum_{n \geq 0} a_n p^n\}$ 是开子环。$\mathbb{Z}_p$ 同胚于 $\prod_{n=0}^\infty \{0,1,\ldots,p-1\}$（乘积拓扑），由 Tychonoff 定理是紧的。
3. $\mathbb{Z}_p$ 是 $0$ 的紧邻域，故 $\mathbb{Q}_p$ 局部紧。∎

**命题**：$\mathbb{Z}_p$ 是 $\mathbb{Q}_p$ 中唯一的极大紧开子环。

*证明*：设 $R$ 是紧开子环。因 $R$ 开，含某个球 $B(0, p^{-N})$。因 $R$ 紧，乘法闭，且 $\mathbb{Q}_p^\times$ 的幂等作用于范数。分析可知必有 $R = \mathbb{Z}_p$。∎

**性质总结**：
- $\mathbb{Q}_p$ 完全不连通（ultrametric 空间中任意两开球不交或一个含于另一个）。
- $\mathbb{Z}_p$ 是主理想整环，非零理想形如 $p^n\mathbb{Z}_p$。
- 剩余域 $\mathbb{Z}_p/p\mathbb{Z}_p \cong \mathbb{F}_p$。

### (b) Hensel 引理

**定理（Hensel 引理，简单形式）**：设 $f \in \mathbb{Z}_p[x]$，$a \in \mathbb{Z}_p$ 满足：
$$f(a) \equiv 0 \pmod{p}, \quad f'(a) \not\equiv 0 \pmod{p}$$

则存在唯一的 $\alpha \in \mathbb{Z}_p$ 使得 $f(\alpha) = 0$ 且 $\alpha \equiv a \pmod{p}$。

**证明**：Newton 迭代法。定义：
$$a_{n+1} = a_n - \frac{f(a_n)}{f'(a_n)}$$

**步骤 1**：归纳证明 $|f(a_n)|_p \leq p^{-2^n}$ 且 $|a_{n+1} - a_n|_p \leq p^{-2^n}$。

基础 $n = 0$：$|f(a_0)|_p \leq p^{-1}$（由假设），$|f'(a_0)|_p = 1$（由假设）。

**步骤 2**：Taylor 展开：
$$f(a_{n+1}) = f(a_n) + f'(a_n)(a_{n+1} - a_n) + \frac{f''(\xi)}{2}(a_{n+1} - a_n)^2$$

由迭代定义，$f(a_n) + f'(a_n)(a_{n+1} - a_n) = 0$，故：
$$|f(a_{n+1})|_p \leq |a_{n+1} - a_n|_p^2 \leq p^{-2^{n+1}}$$

且 $|f'(a_{n+1})|_p = |f'(a_n)|_p = 1$（因 $|a_{n+1} - a_n|_p < 1$，不影响 mod $p$）。

**步骤 3**：$\{a_n\}$ 是 Cauchy 列，收敛到 $\alpha \in \mathbb{Z}_p$。由连续性 $f(\alpha) = 0$。

**推广形式**：设 $f \in \mathbb{Z}_p[x]$，存在 $a \in \mathbb{Z}_p$ 使 $|f(a)|_p < |f'(a)|_p^2$。则存在根 $\alpha \equiv a \pmod{p^{n}}$，其中 $n = v_p(f(a)/f'(a)^2)$。

**应用**：

1. **$\sqrt{2}$ 在 $\mathbb{Q}_7$ 中的存在性**：$f(x) = x^2 - 2$。$a = 3$：$f(3) = 7 \equiv 0 \pmod{7}$，$f'(3) = 6 \not\equiv 0 \pmod{7}$。故 $\sqrt{2} \in \mathbb{Z}_7$。

2. **$\mathbb{Q}_p$ 中 $n$-次单位根**：设 $(n, p) = 1$。$f(x) = x^n - 1$。在 $\mathbb{F}_p$ 中有 $n$ 个不同根（因 $f'(x) = nx^{n-1}$ 在这些根上非零），每个提升为 $\mathbb{Z}_p$ 中唯一根。故 $\mu_n \subset \mathbb{Z}_p^\times$ 当 $(n,p)=1$。

### (c) 局部类域论

**局部 Artin 映射**：设 $K$ 是局部域（如 $\mathbb{Q}_p$ 的有限扩张）。局部类域论建立交换扩张与 $K^\times$ 的开子群之间的对应。

**定理（局部互反律）**：存在典范的拓扑同构（局部 Artin 映射）：
$$\text{rec}_K: \widehat{K^\times} = K^\times / \overline{(K^\times)^0} \xrightarrow{\cong} \text{Gal}(K^{\text{ab}}/K)$$

其中 $K^{\text{ab}}$ 是 $K$ 的极大 Abel 扩张，$(K^\times)^0$ 是 $K^\times$ 的连通分支（对 $p$-进域，$K^\times \cong \pi^\mathbb{Z} \times \mathcal{O}_K^\times$，连通分支平凡；对 $\mathbb{R}, \mathbb{C}$ 需适当处理）。

对 $\mathbb{Q}_p$，更精确地：
$$\text{rec}_{\mathbb{Q}_p}: \mathbb{Q}_p^\times \xrightarrow{\cong} \text{Gal}(\mathbb{Q}_p^{\text{ab}}/\mathbb{Q}_p)$$

**关键性质**：

1. **存在性定理**：$K$ 的有限 Abel 扩张 $L/K$ 与 $K^\times$ 中有限指数开子群 $N_{L/K}(L^\times)$ 一一对应。

2. **范数群**：$N_{L/K}(L^\times)$ 是 $K^\times$ 的开子群，且：
   $$\text{Gal}(L/K) \cong K^\times / N_{L/K}(L^\times)$$

3. **分歧理论**：若 $L/K$ 对应 $H \subset K^\times$，则：
   - $L/K$ 非分歧当且仅当 $\mathcal{O}_K^\times \subset H$
   - 分歧指数 $e(L/K) = [K^\times : H \cdot \mathcal{O}_K^\times]$

**对 $\mathbb{Q}_p$ 的显式描述**：

$\mathbb{Q}_p^{\text{ab}} = \mathbb{Q}_p^{\text{unr}}(\zeta_{p^\infty})$，其中：
- $\mathbb{Q}_p^{\text{unr}} = \bigcup_{(n,p)=1} \mathbb{Q}_p(\zeta_n)$ 是极大非分歧扩张
- $\mathbb{Q}_p(\zeta_{p^\infty}) = \bigcup_{n} \mathbb{Q}_p(\zeta_{p^n})$ 是 cyclotomic $\mathbb{Z}_p$-扩张

局部 Artin 映射在 $\mathbb{Z}_p^\times$ 上由 cyclotomic 作用给出：$u \in \mathbb{Z}_p^\times$ 映到 $\sigma_u: \zeta_{p^n} \mapsto \zeta_{p^n}^{u^{-1}}$（$p$-adic 指数）。在 $p$ 上：$\text{rec}(p)$ 作用为 Frobenius $\text{Frob}: \zeta_n \mapsto \zeta_n^p$（$(n,p)=1$）且在 $\zeta_{p^\infty}$ 上平凡。

**常见错误**：
- 将 Hensel 引理应用于 $f'(a) \equiv 0 \pmod{p}$ 的情形：此时结论不成立，可能有多个根或无根。
- 混淆局部和整体类域论：整体 Artin 映射定义在 idele 类群上，局部的是在乘法群上。

**参考文献**：
- J.-P. Serre, *Local Fields*, Springer, 1979
- K. Iwasawa, *Local Class Field Theory*, Oxford, 1986
- S. Lang, *Algebraic Number Theory*, Springer, 1994
- F. Q. Gouvêa, *p-adic Numbers*, Springer, 1997
