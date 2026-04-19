---
msc_primary: 00

  - 00A99
title: 拓扑动力系统
processed_at: '2026-04-05'
---
msc_primary: "00A99"
msc_secondary: ['00-00']
---

# 拓扑动力系统

拓扑动力系统研究连续映射或流在拓扑空间上的迭代行为，关注轨道的长期统计性质和拓扑结构。

## 1. 基本概念

### 1.1 离散与连续系统

**定义 1.1（拓扑动力系统）**. 拓扑动力系统是二元组 $(X, f)$，其中 $X$ 为紧度量空间，$f: X \to X$ 为连续映射。

**定义 1.2（流）**. 流是连续映射 $\phi: X \times \mathbb{R} \to X$，满足 $\phi(x, 0) = x$，$\phi(\phi(x, t), s) = \phi(x, t+s)$。

### 1.2 轨道与极限集

**定义 1.3（轨道）**. $x$ 的正轨道为 $\mathcal{O}^+(x) = \{f^n(x) : n \geq 0\}$。

**定义 1.4（$\omega$-极限集）**. $\omega(x) = \bigcap_{n \geq 0} \overline{\{f^k(x) : k \geq n\}}$。

## 2. 传递性与混合性

**定义 2.1（拓扑传递）**. $f$ 拓扑传递，若对任意非空开集 $U, V$，存在 $n$ 使 $f^n(U) \cap V \neq \emptyset$。

**定义 2.2（拓扑混合）**. $f$ 拓扑混合，若对任意非空开集 $U, V$，存在 $N$ 使 $f^n(U) \cap V \neq \emptyset$ 对所有 $n \geq N$。

**定理 2.3**. 拓扑混合 $
Rightarrow$ 拓扑传递。

## 3. 熵

**定义 3.1（拓扑熵）**.

$$h_{\text{top}}(f) = \lim_{\epsilon \to 0} \limsup_{n \to \infty} \frac{1}{n} \log N(n, \epsilon),$$

其中 $N(n, \epsilon)$ 为 $n$-分离集的最大基数。

## 4. 例子

### 4.1 例子：圆周旋转

$f_\alpha: S^1 \to S^1$，$f_\alpha(x) = x + \alpha \pmod{1}$。

若 $\alpha$ 无理，则每个轨道稠密，系统极小。熵为零。

### 4.2 例子：符号动力系统

全移位 $(\Sigma_k, \sigma)$，$\Sigma_k = \{1, \dots, k\}^\mathbb{Z}$，$(\sigma x)_n = x_{n+1}$。

拓扑熵 $h_{\text{top}}(\sigma) = \log k$。

## 5. 交叉引用

- [定性理论](docs/11-高级数学/动力系统-扩展/01-常微分方程定性理论/00-README.md) — ODE 定性理论
- [光滑系统](docs/11-高级数学/动力系统-扩展/03-光滑动力系统/00-README.md) — 光滑动力系统
- [哈密顿系统](docs/11-高级数学/动力系统-扩展/04-哈密顿系统/00-README.md) — 哈密顿系统
- [复动力系统](docs/11-高级数学/动力系统-扩展/05-复动力系统/00-README.md) — 复动力系统

---

**适用**：docs/11-高级数学/
