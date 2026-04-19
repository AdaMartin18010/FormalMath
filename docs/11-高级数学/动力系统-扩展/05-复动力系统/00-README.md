---
msc_primary: 00

  - 00A99
title: 复动力系统
processed_at: '2026-04-05'
---
msc_primary: "00A99"
msc_secondary: ['00-00']
---

# 复动力系统

复动力系统研究复平面上有理函数或整函数的迭代，连接复分析、几何与动力系统，以 Julia 集和 Mandelbrot 集的精美图像闻名于世。

## 1. Fatou 与 Julia 集

**定义 1.1（正规族）**. 全纯函数族 $\mathcal{F}$ 在区域 $U$ 上正规，若任意序列有子列在紧集上一致收敛或发散到 $\infty$。

**定义 1.2（Fatou 集）**. $F(f) = \{z \in \widehat{\mathbb{C}} : \{f^n\} \text{ 在 } z \text{ 的邻域正规}\}$。

**定义 1.3（Julia 集）**. $J(f) = \widehat{\mathbb{C}} \setminus F(f)$。

## 2. 基本性质

**定理 2.1**. Julia 集 $J(f)$ 非空、完美、完全不变（$f(J) = J = f^{-1}(J)$）。

**定理 2.2**. $J(f)$ 是周期点的闭包。

## 3. Mandelbrot 集

**定义 3.1（Mandelbrot 集）**. 

$$M = \{c \in \mathbb{C} : f_c^n(0) \not\to \infty\},$$

其中 $f_c(z) = z^2 + c$。

**定理 3.2（Douady-Hubbard）**. $M$ 连通，且存在共形映射 $\phi: \widehat{\mathbb{C}} \setminus M \to \widehat{\mathbb{C}} \setminus \overline{\mathbb{D}}$。

## 4. 例子

### 4.1 例子：$f(z) = z^2$

Julia 集为单位圆 $S^1$。$|z| < 1$ 时 $f^n(z) \to 0$；$|z| > 1$ 时 $f^n(z) \to \infty$。

### 4.2 例子：$f(z) = z^2 - 2$

Julia 集为区间 $[-2, 2]$。$f$ 在 $J(f)$ 上共轭于帐篷映射。

## 5. 交叉引用

- [复分析](docs/03-分析学/02-复分析/01-复分析基础.md) — 全纯函数与 Riemann 曲面
- [拓扑系统](docs/11-高级数学/动力系统-扩展/02-拓扑动力系统/00-README.md) — 拓扑动力系统
- [光滑系统](docs/11-高级数学/动力系统-扩展/03-光滑动力系统/00-README.md) — 光滑动力系统
- [哈密顿系统](docs/11-高级数学/动力系统-扩展/04-哈密顿系统/00-README.md) — 哈密顿系统

---

**适用**：docs/11-高级数学/
