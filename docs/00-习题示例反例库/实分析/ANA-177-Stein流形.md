---
msc_primary: 32
习题编号: ANA-177
学科: 多复变函数论
知识点: Stein流形
难度: ⭐⭐⭐⭐⭐
预计时间: 90分钟
processed_at: '2026-04-20'
---

# Stein 流形

## 题目

**(a)** 给出 Stein 流形的严格定义，并证明：若 $X$ 是 Stein 流形，则 $X$ 上存在严格多重次调和穷竭函数。

**(b)** 叙述并证明 Cartan 定理 A：Stein 流形上的凝聚解析层由整体截面生成。

**(c)** 叙述 Remmert-Bishop-Narasimhan 嵌入定理，并证明 Stein 流形可恰当嵌入到某个 $\mathbb{C}^N$ 中。

---

## 解答

### (a) Stein 流形的定义与基本性质

**定义（Stein 流形）**。复流形 $X$ 称为 **Stein 流形**，若满足以下三个条件：

1. **全纯凸性**（Holomorphic Convexity）：对任意紧集 $K \Subset X$，其全纯凸包
$$\widehat{K}_X = \{z \in X : |f(z)| \leq \sup_K |f|, \forall f \in \mathcal{O}(X)\}$$
仍是 $X$ 的紧子集。

2. **全纯分离性**（Holomorphic Separation）：对任意 $x \neq y \in X$，存在 $f \in \mathcal{O}(X)$ 使得 $f(x) \neq f(y)$。

3. **局部坐标由整体全纯函数给出**：每点 $x \in X$ 有邻域 $U$ 和 $f_1, \dots, f_n \in \mathcal{O}(X)$，使得 $(f_1|_U, \dots, f_n|_U)$ 给出 $U$ 上的局部全纯坐标。

**定理**：Stein 流形 $X$ 上存在 $C^\infty$ 的严格多重次调和穷竭函数 $\rho: X \to \mathbb{R}$。

**证明**：

由于 $X$ 全纯凸，取一列紧全纯凸集 $K_j = \widehat{K_j}$ 使得 $K_j \subset K_{j+1}^\circ$ 且 $\bigcup_j K_j = X$。

对每个 $j$，由全纯分离性和局部坐标条件，可找到有限个全纯函数 $f_{j,1}, \dots, f_{j,m_j} \in \mathcal{O}(X)$ 使得在 $K_{j+1} \setminus K_j^\circ$ 上有
$$\sum_{k=1}^{m_j} |f_{j,k}|^2 > j + 1.$$

选取光滑截断函数 $\chi_j$ 使得 $\chi_j \equiv 1$ 在 $K_{j+1} \setminus K_j^\circ$ 附近，$\mathrm{supp}\,\chi_j \subset K_{j+2} \setminus K_{j-1}$。定义
$$\rho(x) = \sum_{j=1}^\infty \chi_j(x) \sum_{k=1}^{m_j} |f_{j,k}(x)|^2.$$

由于局部只有有限项非零，$\rho$ 是 $C^\infty$ 的。$|f_{j,k}|^2$ 是多重次调和的（plurisubharmonic），其 Levi 形式
$$\mathcal{L}(|f|^2; v) = |\partial f(v)|^2 \geq 0,$$
且严格正当 $df(v) \neq 0$。通过对 $m_j$ 和系数选取的适当调整（加上小的 $|z|^2$ 扰动），可使 $\rho$ 是**严格**多重次调和的。

对任意 $c \in \mathbb{R}$，水平集 $\{x : \rho(x) \leq c\}$ 包含于某个 $K_j$ 中，故为紧集。因此 $\rho$ 是穷竭函数。 ∎

---

### (b) Cartan 定理 A

**定理（Cartan A）**。设 $X$ 为 Stein 流形，$\mathcal{F}$ 为 $X$ 上的凝聚解析层。则整体截面层 $\mathcal{F}(X)$ 生成每个茎 $\mathcal{F}_x$ 作为 $\mathcal{O}_{X,x}$-模，即映射
$$\mathcal{F}(X) \otimes_\mathbb{C} \mathcal{O}_{X,x} \longrightarrow \mathcal{F}_x$$
是满射。等价地说，$\mathcal{F}$ 由整体截面生成。

**证明**：利用 Cartan 定理 B：Stein 流形上凝聚解析层的高阶上同调消失，即 $H^q(X, \mathcal{F}) = 0$ 对所有 $q \geq 1$。

取 $x \in X$。由于 $\mathcal{F}$ 凝聚，存在 $x$ 的邻域 $U$ 和正合列
$$\mathcal{O}_U^{\oplus p} \longrightarrow \mathcal{O}_U^{\oplus q} \longrightarrow \mathcal{F}|_U \longrightarrow 0.$$

设 $\mathcal{I}_x \subset \mathcal{O}_X$ 为点 $x$ 的理想层。对任意正整数 $k$，考虑短正合列
$$0 \longrightarrow \mathcal{I}_x^k \cdot \mathcal{F} \longrightarrow \mathcal{F} \longrightarrow \mathcal{F} / \mathcal{I}_x^k \mathcal{F} \longrightarrow 0.$$

由 Cartan 定理 B，$H^1(X, \mathcal{I}_x^k \cdot \mathcal{F}) = 0$，故整体截面映射
$$\mathcal{F}(X) \longrightarrow (\mathcal{F}/\mathcal{I}_x^k\mathcal{F})(X) = \mathcal{F}_x / \mathfrak{m}_x^k \mathcal{F}_x$$
是满射，其中 $\mathfrak{m}_x$ 为极大理想。

由 Artin-Rees 引理和 Krull 交集定理，$\mathcal{F}_x$ 是 $\mathfrak{m}_x$-adic 完备的，故
$$\mathcal{F}_x = \varprojlim_k \mathcal{F}_x / \mathfrak{m}_x^k \mathcal{F}_x.$$

由于 $\mathcal{F}(X) \to \mathcal{F}_x / \mathfrak{m}_x^k \mathcal{F}_x$ 对所有 $k$ 满射，由完备模上的一致收敛性，$\mathcal{F}(X) \to \mathcal{F}_x$ 的像稠密且 $\mathcal{F}_x$ 是有限生成 $\mathcal{O}_{X,x}$-模，故该映射为满射。 ∎

---

### (c) 嵌入定理

**定理（Remmert-Bishop-Narasimhan）**。设 $X$ 为 $n$ 维 Stein 流形，则存在真全纯嵌入 $F: X \hookrightarrow \mathbb{C}^{2n+1}$。

**证明概要**：

**步骤 1**：构造到 $\mathbb{C}^N$ 的恰当全纯映射。

由于 $X$ Stein，存在穷竭的一列紧全纯凸集 $\{K_j\}$。由全纯分离性和局部坐标条件，可找到可数多个全纯函数 $f_1, f_2, \dots \in \mathcal{O}(X)$ 使得
- 每点 $x \in X$ 有邻域 $U$ 和 $n$ 个函数构成局部坐标；
- 对任意 $j$，在 $X \setminus K_j$ 上 $|f_{m_j}| > j$ 对某个 $m_j$。

由此 $F = (f_1, f_2, \dots): X \to \mathbb{C}^\infty$（适当截断到有限维）是恰当且为局部嵌入。

**步骤 2**：降维到 $2n$。利用 Sard 定理，对 $N > 2n$，几乎每一组平行投影 $\pi: \mathbb{C}^N \to \mathbb{C}^{N-1}$ 限制在 $F(X)$ 上仍是单射和 immersion。逐步降维得到到 $\mathbb{C}^{2n}$ 的嵌入（可能不是恰当的）。

**步骤 3**：修正为恰当嵌入。通过添加一个额外的全纯函数 $g$（控制无穷远行为），可得到到 $\mathbb{C}^{2n+1}$ 的恰当嵌入。具体地，取 $g$ 使得 $|g(z)| \to \infty$ 当 $z \to \infty$ 沿 $X$ 的任何非预紧序列，则 $(F, g): X \to \mathbb{C}^{2n} \times \mathbb{C}$ 是恰当的。

因此存在到 $\mathbb{C}^{2n+1}$ 的恰当全纯嵌入。 ∎

---

## 关键概念总结

| 概念 | 含义 | 在 Stein 流形上的性质 |
|------|------|---------------------|
| 全纯凸 | 全纯凸包紧 | 保证存在穷竭函数 |
| 凝聚层 | 局部有限表现 | Cartan A/B 适用 |
| 严格多重次调和 | Levi 形式正定 | 保证强拟凸性 |
| 恰当映射 | 逆像紧则紧 | 嵌入的几何控制 |

---

## 相关文档

- [Kähler 流形](../几何与拓扑/Kähler流形-基础.md)
- [层上同调](../代数几何/层上同调-基础.md)
- [多复变函数论](../分析学/多复变函数-基础.md)
