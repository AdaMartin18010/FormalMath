---
msc_primary: 00A99
习题编号: GEO-074
学科: 几何
知识点: 几何-Finsler几何
难度: ⭐⭐⭐⭐
预计时间: 40分钟
---

# Finsler 几何

## 题目

**(a)** 定义 Finsler 度规并证明其基本性质。

**(b)** 讨论 Finsler 曲率和 Flag 曲率。

**(c)** 证明 Finsler 流形的体积形式。

---

## 解答

### (a) Finsler度规

#### 定义

**Finsler度规**：$F: TM \to [0, \infty)$ 满足：
1. **正齐次**：$F(x, \lambda v) = \lambda F(x, v)$（$\lambda > 0$）
2. **光滑**：$F$ 在 $TM \setminus \{0\}$ 上光滑
3. **正定型**：Hessian矩阵
$$g_{ij}(x,v) = \frac{1}{2} \frac{\partial^2 F^2}{\partial v^i \partial v^j}$$
正定。

#### 与Riemann几何的关系

**Riemann度量**：$F(x,v) = \sqrt{g_{ij}(x)v^i v^j}$（$g_{ij}$ 只依赖于 $x$）。

**Finsler度量**：$g_{ij}$ 依赖于 $(x, v)$（切方向）。

#### 例子

**Randers度量**：$F = \alpha + \beta$，其中：
- $\alpha = \sqrt{a_{ij}(x)v^i v^j}$ 是Riemann度量
- $\beta = b_i(x)v^i$ 是1-形式，$\|\beta\|_\alpha < 1$

**物理意义**：Randers度量描述在Riemann背景中的"风"或"流"（Zermelo导航问题）。

---

### (b) Flag曲率

#### 曲率张量

**Chern联络**：Finsler流形上的典范联络（与Riemann的Levi-Civita联络类比）。

**曲率张量**：$R^i_{jkl}$（依赖于方向 $v$）。

#### Flag曲率

设 $P \subseteq T_xM$ 是2维平面（"flag"），$y \in P$ 是"flag pole"。

**Flag曲率**：
$$K(P, y) = \frac{g_y(R_y(u), u)}{g_y(y,y)g_y(u,u) - g_y(y,u)^2}$$

其中 $u \in P$，$g_y = g_{ij}(x,y)dx^i dx^j$。

**性质**：
- 对Riemann度量，$K(P, y)$ 不依赖于 $y$，退化为**截面曲率**
- Finsler几何中，曲率依赖于flag pole的方向

#### 常曲率

**定理**（Finsler空间的Schur引理）：若 $\dim \geq 3$ 且 $K(P, y) = K(x)$ 只依赖于 $x$，则 $K$ 是常数。

**常曲率Finsler空间**：
- $K = 0$：Minkowski空间（平坦）
- $K = 1$：Finsler球面
- $K = -1$：Finsler双曲空间

---

### (c) 体积形式

#### 两种体积

**Busemann-Hausdorff体积**：
$$\text{Vol}_{BH}(U) = c_n \int_U \frac{1}{\text{Vol}_{Euc}(B_x)} dx$$

其中 $B_x = \{v \in T_xM : F(x,v) < 1\}$ 是切空间中的"单位球"。

**Holmes-Thompson体积**：
$$\text{Vol}_{HT}(U) = \frac{1}{c_n} \int_U \text{Vol}_{Euc}(B_x) dx$$

#### 与Riemann体积的关系

对Riemann度量：
$$\text{Vol}_{BH} = \text{Vol}_{HT} = \text{Vol}_{Riemann}$$

对一般Finsler度量：
$$\text{Vol}_{HT} \leq \text{Vol}_{BH}$$

等号成立当且仅当Finsler度量是Riemann的。

#### 应用

- **积分几何**：Crofton公式在Finsler情形
- **变分法**：Finsler测地线的Morse理论
- **相对论**：Finsler时空模型（Bogoslovsky, Miron等）