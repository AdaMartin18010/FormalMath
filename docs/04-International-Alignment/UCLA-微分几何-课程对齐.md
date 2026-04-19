---
msc_primary: 97A99
msc_secondary:
  - 00A99
---

# UCLA 微分几何核心内容

UCLA Math 164（微分几何）涵盖曲线与曲面的局部理论、曲率、测地线与 Gauss-Bonnet 定理。本节提供该课程的严格数学内容。

## 1. 曲线的局部理论

**定义 1.1（正则曲线）**. 参数曲线 $\gamma: I \to \mathbb{R}^3$ 称为正则的，若 $\gamma'(t) \neq 0$ 对所有 $t \in I$。

**定理 1.2（Frenet-Serret）**. 对弧长参数化的正则曲线，存在标架 $\{T, N, B\}$ 满足：

$$T' = \kappa N, \quad N' = -\kappa T + \tau B, \quad B' = -\tau N,$$

其中 $\kappa$ 为曲率，$\tau$ 为挠率。

## 2. 曲面的局部理论

### 2.1 第一基本形式

**定义 2.1（第一基本形式）**. 曲面 $S \subset \mathbb{R}^3$ 上的诱导度量：

$$I = E du^2 + 2F dudv + G dv^2,$$

其中 $E = \langle r_u, r_u \rangle$，$F = \langle r_u, r_v \rangle$，$G = \langle r_v, r_v \rangle$。

### 2.2 第二基本形式与曲率

**定义 2.2（Gauss 曲率）**. $K = \frac{LN - M^2}{EG - F^2}$，其中 $L, M, N$ 为第二基本形式系数。

**定理 2.3（Gauss 绝妙定理）**. $K$ 是内蕴量，仅依赖于第一基本形式。

## 3. Gauss-Bonnet 定理

**定理 3.1（Gauss-Bonnet）**. 设 $S$ 为紧定向曲面（无边），则：

$$\int_S K dA = 2\pi \chi(S) = 2\pi (2 - 2g).$$

*证明概要*. 对三角剖分，利用每个三角形上的局部 Gauss-Bonnet 公式，边界项相消，顶点贡献总和为 $2\pi V$，边贡献为 $-2\pi E$，面贡献为 $\pi F$，整理得 $2\pi (V - E + F) = 2\pi \chi$。$\square$

## 4. 测地线

**定义 4.1（测地线）**. 曲面上测地曲率为零的曲线，即"尽可能直"的曲线。

**定理 4.2**. 在局部坐标下，测地线满足方程：

$$\frac{d^2 u^k}{dt^2} + \Gamma^k_{ij} \frac{du^i}{dt} \frac{du^j}{dt} = 0.$$

## 5. 例子

### 5.1 例子：球面

半径 $R$ 的球面：$K = 1/R^2$（常数），$\int K dA = 4\pi = 2\pi \cdot 2$，$\chi(S^2) = 2$。

### 5.2 例子：环面

环面 $T^2$：$K$ 变号，$\int K dA = 0 = 2\pi \cdot 0$，$\chi(T^2) = 0$。

## 6. 交叉引用

- [微分几何](docs/04-几何与拓扑/02-微分几何-扩展/01-微分几何基础.md) — 流形与联络
- [黎曼几何](docs/04-几何与拓扑/02-微分几何-扩展/02-黎曼几何/01-黎曼几何基础.md) — 测地线与曲率深化
- [张量分析](docs/03-分析学/张量分析-基础.md) — Christoffel 符号与曲率张量
- [指标定理](docs/04-几何与拓扑/指标定理应用.md) — Gauss-Bonnet 的高维推广

---

**适用**：docs/04-International-Alignment/
