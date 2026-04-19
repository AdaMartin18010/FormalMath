---
title: "MIT 18.06 线性代数课堂验证测试题库"
msc_primary: 00A99
date: "2026-04-18"
version: "1.0"
course: "MIT 18.06 Linear Algebra"
textbook: "Gilbert Strang, Introduction to Linear Algebra, 4th Edition"
validation_id: "VAL-2026-Q2"
---

# MIT 18.06 线性代数课堂验证测试题库

> 本题库对应 FormalMath 银层文档 MIT 18.06 模块（15章核心内容）。
> 所有题目使用标准 LaTeX 数学符号。

---

## 课前基线测试（Pre-test）

> **测试说明**：本测试用于评估学生进入课程前的先备知识水平，不计入最终成绩。
> **限时**：20 分钟　**总分**：100 分（每题 20 分）

---

### Q1：向量与线性组合基础

**难度**：★☆☆（易）　**对应章节**：Ch 1 — 向量与线性组合

**题目陈述**：

在 $\mathbb{R}^3$ 中，给定向量
$$\mathbf{v}_1 = \begin{pmatrix} 1 \\ 0 \\ 1 \end{pmatrix}, \quad \mathbf{v}_2 = \begin{pmatrix} 0 \\ 1 \\ 1 \end{pmatrix}, \quad \mathbf{b} = \begin{pmatrix} 2 \\ 3 \\ 5 \end{pmatrix}.$$

(a) 判断 $\mathbf{b}$ 是否可以表示为 $\mathbf{v}_1$ 和 $\mathbf{v}_2$ 的线性组合。如果可以，写出具体的组合系数。

(b) 向量 $\mathbf{v}_1$ 和 $\mathbf{v}_2$ 是否线性无关？请说明理由。

**参考答案**：

(a) 设 $\mathbf{b} = c_1 \mathbf{v}_1 + c_2 \mathbf{v}_2$，即
$$\begin{pmatrix} 2 \\ 3 \\ 5 \end{pmatrix} = c_1 \begin{pmatrix} 1 \\ 0 \\ 1 \end{pmatrix} + c_2 \begin{pmatrix} 0 \\ 1 \\ 1 \end{pmatrix} = \begin{pmatrix} c_1 \\ c_2 \\ c_1 + c_2 \end{pmatrix}.$$

由第一分量得 $c_1 = 2$，由第二分量得 $c_2 = 3$。验证第三分量：$c_1 + c_2 = 2 + 3 = 5$，与 $\mathbf{b}$ 的第三分量一致。

**结论**：$\mathbf{b}$ 可以表示为线性组合，且 $\mathbf{b} = 2\mathbf{v}_1 + 3\mathbf{v}_2$。

(b) 两向量线性无关的判定：若 $c_1 \mathbf{v}_1 + c_2 \mathbf{v}_2 = \mathbf{0}$，则
$$\begin{cases} c_1 = 0 \\ c_2 = 0 \\ c_1 + c_2 = 0 \end{cases}$$
由前两式直接得 $c_1 = c_2 = 0$。因此 $\mathbf{v}_1$ 和 $\mathbf{v}_2$ **线性无关**。

**评分标准**：

| 评分项 | 分值 | 说明 |
|--------|------|------|
| 正确设立线性组合方程 | 5 | 列出 $c_1 \mathbf{v}_1 + c_2 \mathbf{v}_2 = \mathbf{b}$ |
| 正确求解系数 | 7 | 得到 $c_1 = 2, c_2 = 3$ 并验证第三分量 |
| 给出正确结论 | 3 | 明确回答"可以"并写出组合式 |
| 正确判定线性无关 | 3 | 通过定义或观察得出线性无关 |
| 理由完整清晰 | 2 | 推理过程无逻辑跳跃 |
| **合计** | **20** | |

---

### Q2：矩阵乘法

**难度**：★☆☆（易）　**对应章节**：Ch 2 — 求解线性方程组

**题目陈述**：

设矩阵
$$A = \begin{pmatrix} 1 & 2 \\ 3 & 4 \\ 0 & 1 \end{pmatrix}, \quad B = \begin{pmatrix} 1 & 0 & 1 \\ 2 & 1 & 0 \end{pmatrix}.$$

(a) 计算乘积 $AB$（若存在），并指明其行列维度。

(b) 计算乘积 $BA$（若存在），并指明其行列维度。

(c) 验证 $AB$ 的第 $(2,3)$ 元等于 $A$ 的第 2 行与 $B$ 的第 3 列的点积。

**参考答案**：

(a) $A$ 为 $3 \times 2$ 矩阵，$B$ 为 $2 \times 3$ 矩阵，故 $AB$ 存在且为 $3 \times 3$ 矩阵。

$$AB = \begin{pmatrix} 1 \cdot 1 + 2 \cdot 2 & 1 \cdot 0 + 2 \cdot 1 & 1 \cdot 1 + 2 \cdot 0 \\ 3 \cdot 1 + 4 \cdot 2 & 3 \cdot 0 + 4 \cdot 1 & 3 \cdot 1 + 4 \cdot 0 \\ 0 \cdot 1 + 1 \cdot 2 & 0 \cdot 0 + 1 \cdot 1 & 0 \cdot 1 + 1 \cdot 0 \end{pmatrix} = \begin{pmatrix} 5 & 2 & 1 \\ 11 & 4 & 3 \\ 2 & 1 & 0 \end{pmatrix}.$$

(b) $B$ 为 $2 \times 3$，$A$ 为 $3 \times 2$，故 $BA$ 存在且为 $2 \times 2$ 矩阵。

$$BA = \begin{pmatrix} 1 \cdot 1 + 0 \cdot 3 + 1 \cdot 0 & 1 \cdot 2 + 0 \cdot 4 + 1 \cdot 1 \\ 2 \cdot 1 + 1 \cdot 3 + 0 \cdot 0 & 2 \cdot 2 + 1 \cdot 4 + 0 \cdot 1 \end{pmatrix} = \begin{pmatrix} 1 & 3 \\ 5 & 8 \end{pmatrix}.$$

(c) $AB$ 的第 $(2,3)$ 元为 $3$。$A$ 的第 2 行为 $(3, 4)$，$B$ 的第 3 列为 $\begin{pmatrix} 1 \\ 0 \end{pmatrix}$。点积为 $3 \cdot 1 + 4 \cdot 0 = 3$。两者相等，验证成立。

**评分标准**：

| 评分项 | 分值 | 说明 |
|--------|------|------|
| 正确判断 $AB$ 可计算并指明维度 | 3 | 指出 $3 \times 3$ |
| 正确计算 $AB$ | 6 | 每个元素 2 分，共 9 个元素（按行给分） |
| 正确判断 $BA$ 可计算并指明维度 | 3 | 指出 $2 \times 2$ |
| 正确计算 $BA$ | 4 | 每个元素 2 分 |
| 正确提取第 $(2,3)$ 元 | 2 | |
| 正确计算点积并验证相等 | 2 | |
| **合计** | **20** | |

---

### Q3：线性方程组几何

**难度**：★★☆（中）　**对应章节**：Ch 1–2 — 列图像与行图像

**题目陈述**：

考虑二元线性方程组
$$\begin{cases} x + 2y = 3 \\ 2x + 4y = 6 \end{cases}$$

(a) 从**行图像**（row picture）的角度解释：该方程组在 $\mathbb{R}^2$ 中表示什么几何对象？它们的位置关系如何？

(b) 从**列图像**（column picture）的角度解释：该方程组在 $\mathbb{R}^2$ 中表示什么几何问题？

(c) 该方程组的解集是什么？用集合符号写出所有解。

**参考答案**：

(a) **行图像**：每个方程代表 $\mathbb{R}^2$ 中的一条直线。第一条直线 $x + 2y = 3$ 的斜率为 $-\frac{1}{2}$，截距为 $\frac{3}{2}$；第二条直线 $2x + 4y = 6$ 可化简为 $x + 2y = 3$，与第一条完全相同。因此两条直线**重合**，有无穷多交点。

(b) **列图像**：将方程组写成向量形式
$$x \begin{pmatrix} 1 \\ 2 \end{pmatrix} + y \begin{pmatrix} 2 \\ 4 \end{pmatrix} = \begin{pmatrix} 3 \\ 6 \end{pmatrix}.$$
问题转化为：寻找系数 $x, y$ 使得左侧列向量的线性组合等于右侧向量。注意到 $\begin{pmatrix} 2 \\ 4 \end{pmatrix} = 2 \begin{pmatrix} 1 \\ 2 \end{pmatrix}$，且 $\begin{pmatrix} 3 \\ 6 \end{pmatrix} = 3 \begin{pmatrix} 1 \\ 2 \end{pmatrix}$，因此有无穷多组 $(x, y)$ 满足条件。

(c) 令 $y = t$（$t \in \mathbb{R}$），则 $x = 3 - 2t$。解集为
$$\left\{ (x, y) \in \mathbb{R}^2 \mid x = 3 - 2t,\ y = t,\ t \in \mathbb{R} \right\},$$
或等价地写成
$$\left\{ \begin{pmatrix} 3 \\ 0 \end{pmatrix} + t \begin{pmatrix} -2 \\ 1 \end{pmatrix} \mid t \in \mathbb{R} \right\}.$$

**评分标准**：

| 评分项 | 分值 | 说明 |
|--------|------|------|
| 正确识别两条直线 | 4 | 每个方程对应一条直线 |
| 正确判断位置关系（重合） | 4 | 需说明第二条可化简为第一条 |
| 正确写出列图像的向量方程 | 4 | 写出 $x \mathbf{a}_1 + y \mathbf{a}_2 = \mathbf{b}$ 形式 |
| 正确解释列图像的几何意义 | 4 | 说明是寻找线性组合系数 |
| 正确写出参数化解集 | 4 | 用集合符号或参数形式 |
| **合计** | **20** | |

---

### Q4：子空间判定

**难度**：★★☆（中）　**对应章节**：Ch 3 — 向量空间与子空间

**题目陈述**：

设 $V = \mathbb{R}^3$。判断下列子集 $W$ 是否为 $V$ 的子空间。如果是，请证明；如果不是，请指出违背了子空间的哪一条公理，并给出反例。

(a) $W_1 = \left\{ (x, y, z) \in \mathbb{R}^3 \mid x + y + z = 0 \right\}$

(b) $W_2 = \left\{ (x, y, z) \in \mathbb{R}^3 \mid x, y, z \geq 0 \right\}$

(c) $W_3 = \left\{ (x, y, z) \in \mathbb{R}^3 \mid x = y \right\}$

**参考答案**：

子空间判定三条件：① 包含零向量；② 对加法封闭；③ 对数乘封闭。

(a) **$W_1$ 是子空间**。

- 零向量：$(0, 0, 0)$ 满足 $0 + 0 + 0 = 0$，故 $\mathbf{0} \in W_1$。
- 加法封闭：设 $\mathbf{u} = (x_1, y_1, z_1), \mathbf{v} = (x_2, y_2, z_2) \in W_1$，则 $x_1 + y_1 + z_1 = 0$，$x_2 + y_2 + z_2 = 0$。于是
  $$(x_1 + x_2) + (y_1 + y_2) + (z_1 + z_2) = (x_1 + y_1 + z_1) + (x_2 + y_2 + z_2) = 0 + 0 = 0,$$
  故 $\mathbf{u} + \mathbf{v} \in W_1$。
- 数乘封闭：设 $\mathbf{u} = (x, y, z) \in W_1$，$c \in \mathbb{R}$，则 $cx + cy + cz = c(x + y + z) = c \cdot 0 = 0$，故 $c\mathbf{u} \in W_1$。

(b) **$W_2$ 不是子空间**。违背**数乘封闭性**。

反例：取 $\mathbf{v} = (1, 1, 1) \in W_2$，令 $c = -1$，则 $c\mathbf{v} = (-1, -1, -1)$，其分量均为负，不满足 $x, y, z \geq 0$，故 $c\mathbf{v} \notin W_2$。

(c) **$W_3$ 是子空间**。

- 零向量：$(0, 0, 0)$ 满足 $0 = 0$，故 $\mathbf{0} \in W_3$。
- 加法封闭：设 $(x_1, y_1, z_1), (x_2, y_2, z_2) \in W_3$，则 $x_1 = y_1$，$x_2 = y_2$。于是 $x_1 + x_2 = y_1 + y_2$，故和向量仍满足条件。
- 数乘封闭：设 $(x, y, z) \in W_3$，$c \in \mathbb{R}$，则 $cx = cy$，故 $c(x, y, z) \in W_3$。

**评分标准**：

| 评分项 | 分值 | 说明 |
|--------|------|------|
| (a) 正确判定为子空间 | 2 | |
| (a) 验证零向量 | 2 | |
| (a) 验证加法封闭 | 3 | 需有代数推导 |
| (a) 验证数乘封闭 | 3 | 需有代数推导 |
| (b) 正确判定不是子空间 | 2 | |
| (b) 指出违背的公理 | 3 | 数乘封闭 |
| (b) 给出有效反例 | 3 | 具体向量 + 具体标量 |
| (c) 正确判定为子空间 | 2 | |
| (c) 完整验证三条 | 需有推导 | 共 3 分（每项 1 分） |
| **合计** | **20** | |

---

### Q5：行列式计算

**难度**：★★☆（中）　**对应章节**：Ch 5 — 行列式

**题目陈述**：

计算下列矩阵的行列式，并说明每一步所用的行列式性质。

$$A = \begin{pmatrix} 2 & 1 & 3 \\ 4 & 3 & 8 \\ 6 & 5 & 16 \end{pmatrix}$$

**参考答案**：

**方法一：行变换化上三角**

$$\det A = \begin{vmatrix} 2 & 1 & 3 \\ 4 & 3 & 8 \\ 6 & 5 & 16 \end{vmatrix}$$

$R_2 - 2R_1 \to R_2$（行倍加不改变行列式）：
$$= \begin{vmatrix} 2 & 1 & 3 \\ 0 & 1 & 2 \\ 6 & 5 & 16 \end{vmatrix}$$

$R_3 - 3R_1 \to R_3$：
$$= \begin{vmatrix} 2 & 1 & 3 \\ 0 & 1 & 2 \\ 0 & 2 & 7 \end{vmatrix}$$

$R_3 - 2R_2 \to R_3$：
$$= \begin{vmatrix} 2 & 1 & 3 \\ 0 & 1 & 2 \\ 0 & 0 & 3 \end{vmatrix}$$

上三角矩阵的行列式等于对角元乘积：
$$\det A = 2 \cdot 1 \cdot 3 = 6.$$

**方法二：余子式展开（按第一行）**

$$\det A = 2 \begin{vmatrix} 3 & 8 \\ 5 & 16 \end{vmatrix} - 1 \begin{vmatrix} 4 & 8 \\ 6 & 16 \end{vmatrix} + 3 \begin{vmatrix} 4 & 3 \\ 6 & 5 \end{vmatrix}$$

$$= 2(3 \cdot 16 - 8 \cdot 5) - 1(4 \cdot 16 - 8 \cdot 6) + 3(4 \cdot 5 - 3 \cdot 6)$$

$$= 2(48 - 40) - 1(64 - 48) + 3(20 - 18)$$

$$= 2 \cdot 8 - 16 + 3 \cdot 2 = 16 - 16 + 6 = 6.$$

**评分标准**：

| 评分项 | 分值 | 说明 |
|--------|------|------|
| 正确选择并说明计算方法 | 3 | 行变换法或余子式法 |
| 正确执行第一步变换/展开 | 4 | 计算过程无误 |
| 正确执行后续变换/展开 | 6 | 每步 2–3 分 |
| 正确引用行列式性质 | 4 | 如"行倍加不改变行列式"、"上三角行列式=对角元乘积"等 |
| 得出正确最终结果 | 3 | $\det A = 6$ |
| **合计** | **20** | |

---

## 期末综合测试（Final Comprehensive Test）

> **测试说明**：本测试覆盖 MIT 18.06 全部 15 章核心内容，评估学期整体学习成效。
> **限时**：120 分钟　**总分**：100 分

---

### 模块一：定义复述（2题，共20分）

---

#### Q1：定义 — 向量空间的公理化定义

**难度**：★★☆（中）　**对应章节**：Ch 3 — 向量空间与子空间　**分值**：10 分

**题目陈述**：

请给出**向量空间**（vector space）的完整公理化定义。具体地，设 $V$ 是一个集合，$\mathbb{F}$ 是一个数域（通常为 $\mathbb{R}$ 或 $\mathbb{C}$）。列出 $V$ 成为 $\mathbb{F}$ 上的向量空间所需满足的全部公理（包括加法公理和数乘公理）。

**参考答案**：

集合 $V$ 配以加法运算 $+: V \times V \to V$ 和数乘运算 $\cdot: \mathbb{F} \times V \to V$，称为 $\mathbb{F}$ 上的**向量空间**，如果满足以下公理：

**加法公理**（$V$ 关于加法构成 Abel 群）：

1. **封闭性**：$\forall \mathbf{u}, \mathbf{v} \in V$，$\mathbf{u} + \mathbf{v} \in V$。
2. **交换律**：$\forall \mathbf{u}, \mathbf{v} \in V$，$\mathbf{u} + \mathbf{v} = \mathbf{v} + \mathbf{u}$。
3. **结合律**：$\forall \mathbf{u}, \mathbf{v}, \mathbf{w} \in V$，$(\mathbf{u} + \mathbf{v}) + \mathbf{w} = \mathbf{u} + (\mathbf{v} + \mathbf{w})$。
4. **零向量**：$\exists \mathbf{0} \in V$，$\forall \mathbf{v} \in V$，$\mathbf{v} + \mathbf{0} = \mathbf{v}$。
5. **负向量**：$\forall \mathbf{v} \in V$，$\exists (-\mathbf{v}) \in V$，$\mathbf{v} + (-\mathbf{v}) = \mathbf{0}$。

**数乘公理**：

1. **封闭性**：$\forall c \in \mathbb{F}, \mathbf{v} \in V$，$c \mathbf{v} \in V$。
2. **数乘结合律**：$\forall c, d \in \mathbb{F}, \mathbf{v} \in V$，$c(d\mathbf{v}) = (cd)\mathbf{v}$。
3. **数乘单位元**：$\forall \mathbf{v} \in V$，$1 \cdot \mathbf{v} = \mathbf{v}$（其中 $1$ 是 $\mathbb{F}$ 的乘法单位元）。
4. **分配律（对向量加法）**：$\forall c \in \mathbb{F}, \mathbf{u}, \mathbf{v} \in V$，$c(\mathbf{u} + \mathbf{v}) = c\mathbf{u} + c\mathbf{v}$。
5. **分配律（对标量加法）**：$\forall c, d \in \mathbb{F}, \mathbf{v} \in V$，$(c + d)\mathbf{v} = c\mathbf{v} + d\mathbf{v}$。

**评分标准**：

| 评分项 | 分值 | 说明 |
|--------|------|------|
| 正确说明集合 + 两种运算的结构 | 2 | |
| 完整列出 5 条加法公理 | 4 | 每条 0.8 分（允许合并不当扣 1 分） |
| 完整列出 5 条数乘公理 | 4 | 每条 0.8 分 |
| **合计** | **10** | |

---

#### Q2：定义 — 特征值与特征向量

**难度**：★★☆（中）　**对应章节**：Ch 6 — 特征值与特征向量　**分值**：10 分

**题目陈述**：

设 $A$ 为 $n \times n$ 方阵。

(a) 给出 $A$ 的**特征值**和**特征向量**的严格定义。

(b) 给出 $A$ 的**特征多项式**的定义。

(c) 解释为什么特征值 $\lambda$ 是特征多项式的根。

**参考答案**：

(a) 若存在标量 $\lambda \in \mathbb{F}$ 和非零向量 $\mathbf{v} \in \mathbb{F}^n \setminus \{\mathbf{0}\}$，使得
$$A\mathbf{v} = \lambda \mathbf{v},$$
则称 $\lambda$ 为 $A$ 的**特征值**（eigenvalue），$\mathbf{v}$ 为对应于 $\lambda$ 的**特征向量**（eigenvector）。

注意：定义中必须强调 $\mathbf{v} \neq \mathbf{0}$。

(b) $A$ 的**特征多项式**定义为
$$p_A(\lambda) = \det(A - \lambda I),$$
其中 $I$ 为 $n \times n$ 单位矩阵。这是一个关于 $\lambda$ 的 $n$ 次多项式。

(c) 由 $A\mathbf{v} = \lambda \mathbf{v}$ 可得 $(A - \lambda I)\mathbf{v} = \mathbf{0}$。若 $\mathbf{v} \neq \mathbf{0}$，则齐次线性方程组 $(A - \lambda I)\mathbf{x} = \mathbf{0}$ 有非零解，这等价于系数矩阵 $A - \lambda I$ 为奇异矩阵，即
$$\det(A - \lambda I) = 0.$$
因此 $\lambda$ 满足特征方程，即 $\lambda$ 是特征多项式 $p_A(\lambda)$ 的根。

**评分标准**：

| 评分项 | 分值 | 说明 |
|--------|------|------|
| (a) 正确给出特征值定义 | 2 | 含 $A\mathbf{v} = \lambda \mathbf{v}$ |
| (a) 正确给出特征向量定义并强调非零 | 2 | 必须强调 $\mathbf{v} \neq \mathbf{0}$ |
| (b) 正确写出特征多项式公式 | 2 | |
| (c) 正确推导 $(A - \lambda I)\mathbf{v} = \mathbf{0}$ | 2 | |
| (c) 正确联系到奇异矩阵与行列式为零 | 2 | 完整逻辑链 |
| **合计** | **10** | |

---

### 模块二：定理证明（3题，共30分）

---

#### Q3：证明 — 秩-零化度定理（Rank-Nullity Theorem）

**难度**：★★★（难）　**对应章节**：Ch 3 — 秩-零化度定理　**分值**：10 分

**题目陈述**：

设 $T: V \to W$ 是有限维向量空间之间的线性映射，$\dim V = n$。证明**秩-零化度定理**：
$$\dim \operatorname{Im} T + \dim \ker T = \dim V.$$

即：$\operatorname{rank}(T) + \operatorname{nullity}(T) = n$。

**参考答案**：

**证明**：

设 $\dim \ker T = k$，取 $\ker T$ 的一组基 $\{\mathbf{v}_1, \mathbf{v}_2, \ldots, \mathbf{v}_k\}$。

根据基扩充定理，可将这组基扩充为 $V$ 的一组基：
$$\{\mathbf{v}_1, \ldots, \mathbf{v}_k, \mathbf{w}_1, \ldots, \mathbf{w}_{n-k}\}.$$

**断言**：$\{T(\mathbf{w}_1), T(\mathbf{w}_2), \ldots, T(\mathbf{w}_{n-k})\}$ 是 $\operatorname{Im} T$ 的一组基。

**第一步：证明张成性。**

任取 $\mathbf{y} \in \operatorname{Im} T$，则存在 $\mathbf{x} \in V$ 使得 $\mathbf{y} = T(\mathbf{x})$。由于 $\{\mathbf{v}_1, \ldots, \mathbf{v}_k, \mathbf{w}_1, \ldots, \mathbf{w}_{n-k}\}$ 是 $V$ 的基，可设
$$\mathbf{x} = a_1 \mathbf{v}_1 + \cdots + a_k \mathbf{v}_k + b_1 \mathbf{w}_1 + \cdots + b_{n-k} \mathbf{w}_{n-k}.$$

于是
$$\mathbf{y} = T(\mathbf{x}) = a_1 T(\mathbf{v}_1) + \cdots + a_k T(\mathbf{v}_k) + b_1 T(\mathbf{w}_1) + \cdots + b_{n-k} T(\mathbf{w}_{n-k}).$$

由于 $\mathbf{v}_i \in \ker T$，有 $T(\mathbf{v}_i) = \mathbf{0}$（$i = 1, \ldots, k$）。因此
$$\mathbf{y} = b_1 T(\mathbf{w}_1) + \cdots + b_{n-k} T(\mathbf{w}_{n-k}).$$

这说明 $\operatorname{Im} T$ 中任一向量都可由 $\{T(\mathbf{w}_1), \ldots, T(\mathbf{w}_{n-k})\}$ 线性表示，即该集合张成 $\operatorname{Im} T$。

**第二步：证明线性无关性。**

设
$$c_1 T(\mathbf{w}_1) + \cdots + c_{n-k} T(\mathbf{w}_{n-k}) = \mathbf{0}.$$

由线性性，$T(c_1 \mathbf{w}_1 + \cdots + c_{n-k} \mathbf{w}_{n-k}) = \mathbf{0}$，故
$$c_1 \mathbf{w}_1 + \cdots + c_{n-k} \mathbf{w}_{n-k} \in \ker T.$$

由于 $\{\mathbf{v}_1, \ldots, \mathbf{v}_k\}$ 是 $\ker T$ 的基，存在 $d_1, \ldots, d_k$ 使得
$$c_1 \mathbf{w}_1 + \cdots + c_{n-k} \mathbf{w}_{n-k} = d_1 \mathbf{v}_1 + \cdots + d_k \mathbf{v}_k.$$

移项得
$$d_1 \mathbf{v}_1 + \cdots + d_k \mathbf{v}_k - c_1 \mathbf{w}_1 - \cdots - c_{n-k} \mathbf{w}_{n-k} = \mathbf{0}.$$

由于 $\{\mathbf{v}_1, \ldots, \mathbf{v}_k, \mathbf{w}_1, \ldots, \mathbf{w}_{n-k}\}$ 是 $V$ 的基，线性无关，故所有系数为零：
$$d_1 = \cdots = d_k = c_1 = \cdots = c_{n-k} = 0.$$

因此 $\{T(\mathbf{w}_1), \ldots, T(\mathbf{w}_{n-k})\}$ 线性无关。

**结论**：$\{T(\mathbf{w}_1), \ldots, T(\mathbf{w}_{n-k})\}$ 是 $\operatorname{Im} T$ 的基，故 $\dim \operatorname{Im} T = n - k$。

于是
$$\dim \operatorname{Im} T + \dim \ker T = (n - k) + k = n = \dim V.$$

证毕。$\square$

**评分标准**：

| 评分项 | 分值 | 说明 |
|--------|------|------|
| 正确取 $\ker T$ 的基并扩充为 $V$ 的基 | 2 | 关键第一步 |
| 正确提出关于 $\operatorname{Im} T$ 基的断言 | 1 | |
| 证明张成性 | 3 | 利用 $T(\mathbf{v}_i) = \mathbf{0}$ 化简 |
| 证明线性无关性 | 3 | 将向量拉回 $V$ 中使用基的线性无关 |
| 正确得出维数等式 | 1 | |
| **合计** | **10** | |

---

#### Q4：证明 — 投影矩阵的幂等性与对称性

**难度**：★★★（难）　**对应章节**：Ch 4 — 正交性　**分值**：10 分

**题目陈述**：

设 $A$ 为 $m \times n$ 矩阵，$\operatorname{rank}(A) = n$（即 $A$ 列满秩）。定义投影矩阵
$$P = A(A^T A)^{-1} A^T.$$

(a) 证明 $P$ 是**幂等矩阵**（idempotent），即 $P^2 = P$。

(b) 证明 $P$ 是**对称矩阵**（symmetric），即 $P^T = P$。

(c) 从几何角度解释：$P$ 将 $\mathbb{R}^m$ 中的任意向量投影到哪个子空间上？

**参考答案**：

(a) 计算 $P^2$：

$$P^2 = \left[ A(A^T A)^{-1} A^T \right] \left[ A(A^T A)^{-1} A^T \right]$$

$$= A(A^T A)^{-1} (A^T A) (A^T A)^{-1} A^T$$

注意到 $(A^T A)^{-1} (A^T A) = I_n$（$n \times n$ 单位矩阵），因此

$$P^2 = A \cdot I_n \cdot (A^T A)^{-1} A^T = A(A^T A)^{-1} A^T = P.$$

(b) 计算 $P^T$：

$$P^T = \left[ A(A^T A)^{-1} A^T \right]^T$$

利用转置性质 $(BC)^T = C^T B^T$ 和 $((A^T A)^{-1})^T = ((A^T A)^T)^{-1} = (A^T A)^{-1}$（因为 $A^T A$ 对称）：

$$P^T = (A^T)^T \left[ (A^T A)^{-1} \right]^T A^T = A(A^T A)^{-1} A^T = P.$$

(c) $P$ 将 $\mathbb{R}^m$ 中的任意向量投影到 $A$ 的**列空间**（column space）$C(A)$ 上。

解释：对任意 $\mathbf{b} \in \mathbb{R}^m$，$P\mathbf{b} = A\underbrace{(A^T A)^{-1} A^T \mathbf{b}}_{\hat{\mathbf{x}}}$，显然 $P\mathbf{b}$ 是 $A$ 的列的线性组合，故 $P\mathbf{b} \in C(A)$。同时，$\mathbf{b} - P\mathbf{b}$ 与 $C(A)$ 正交，因此 $P\mathbf{b}$ 是 $\mathbf{b}$ 在 $C(A)$ 上的正交投影。

**评分标准**：

| 评分项 | 分值 | 说明 |
|--------|------|------|
| (a) 正确展开 $P^2$ | 2 | |
| (a) 利用结合律化简 | 2 | 关键步骤：$(A^T A)^{-1}(A^T A) = I$ |
| (b) 正确应用转置性质 | 2 | $(BC)^T = C^T B^T$ |
| (b) 利用 $(A^T A)^{-1}$ 的对称性 | 2 | |
| (c) 正确指出列空间 | 1 | |
| (c) 几何解释完整 | 1 | 说明残差正交 |
| **合计** | **10** | |

---

#### Q5：证明 — 实对称矩阵特征值为实数

**难度**：★★★☆（较难）　**对应章节**：Ch 6 — 对称矩阵与正定矩阵　**分值**：10 分

**题目陈述**：

设 $A$ 为 $n \times n$ **实对称矩阵**（即 $A^T = A$，且 $A$ 的元素均为实数）。证明：$A$ 的所有特征值都是**实数**。

**提示**：考虑复内积 $\langle \mathbf{x}, \mathbf{y} \rangle = \mathbf{x}^H \mathbf{y}$（$H$ 表示共轭转置），利用 $A$ 的对称性。

**参考答案**：

**证明**：

设 $\lambda$ 是 $A$ 的一个特征值，$\mathbf{v} \neq \mathbf{0}$ 是对应的特征向量（在 $\mathbb{C}^n$ 中）。则有
$$A\mathbf{v} = \lambda \mathbf{v} \quad (*)$$

**第一步**：对 $(*)$ 两边取共轭转置。由于 $A$ 是实矩阵，$\bar{A} = A$；又 $A$ 对称，$A^T = A$。因此
$$\mathbf{v}^H A^H = \mathbf{v}^H A^T = \mathbf{v}^H A = \bar{\lambda} \mathbf{v}^H.$$

**第二步**：将上式右乘 $\mathbf{v}$：
$$\mathbf{v}^H A \mathbf{v} = \bar{\lambda} \mathbf{v}^H \mathbf{v} = \bar{\lambda} \|\mathbf{v}\|^2. \quad (1)$$

另一方面，将 $(*)$ 左乘 $\mathbf{v}^H$：
$$\mathbf{v}^H A \mathbf{v} = \lambda \mathbf{v}^H \mathbf{v} = \lambda \|\mathbf{v}\|^2. \quad (2)$$

**第三步**：比较 (1) 和 (2)：
$$\lambda \|\mathbf{v}\|^2 = \bar{\lambda} \|\mathbf{v}\|^2.$$

由于 $\mathbf{v} \neq \mathbf{0}$，$\|\mathbf{v}\|^2 > 0$。两边除以 $\|\mathbf{v}\|^2$ 得
$$\lambda = \bar{\lambda}.$$

这意味着 $\lambda$ 是实数。$\square$

**评分标准**：

| 评分项 | 分值 | 说明 |
|--------|------|------|
| 正确设定特征值-特征向量关系 | 1 | |
| 正确取共轭转置并利用 $A$ 的实对称性 | 3 | $A^H = A$ 是关键 |
| 正确得到 $\mathbf{v}^H A \mathbf{v} = \bar{\lambda}\|\mathbf{v}\|^2$ | 2 | |
| 正确得到 $\mathbf{v}^H A \mathbf{v} = \lambda\|\mathbf{v}\|^2$ | 2 | |
| 正确比较并推出 $\lambda = \bar{\lambda}$ | 2 | |
| **合计** | **10** | |

---

### 模块三：计算应用（3题，共30分）

---

#### Q6：计算 — LU 分解与求解线性方程组

**难度**：★★☆（中）　**对应章节**：Ch 2 — LU 分解　**分值**：10 分

**题目陈述**：

给定矩阵
$$A = \begin{pmatrix} 2 & 1 & 1 \\ 4 & 3 & 3 \\ 8 & 7 & 9 \end{pmatrix}.$$

(a) 不使用行交换，将 $A$ 分解为 $A = LU$，其中 $L$ 为单位下三角矩阵，$U$ 为上三角矩阵。写出 $L$ 和 $U$ 的具体形式。

(b) 利用 LU 分解求解 $A\mathbf{x} = \mathbf{b}$，其中 $\mathbf{b} = \begin{pmatrix} 4 \\ 10 \\ 26 \end{pmatrix}$。

**参考答案**：

(a) 通过高斯消元：

$R_2 - 2R_1 \to R_2$（乘数 $l_{21} = 2$）：
$$\begin{pmatrix} 2 & 1 & 1 \\ 0 & 1 & 1 \\ 8 & 7 & 9 \end{pmatrix}$$

$R_3 - 4R_1 \to R_3$（乘数 $l_{31} = 4$）：
$$\begin{pmatrix} 2 & 1 & 1 \\ 0 & 1 & 1 \\ 0 & 3 & 5 \end{pmatrix}$$

$R_3 - 3R_2 \to R_3$（乘数 $l_{32} = 3$）：
$$U = \begin{pmatrix} 2 & 1 & 1 \\ 0 & 1 & 1 \\ 0 & 0 & 2 \end{pmatrix}$$

$$L = \begin{pmatrix} 1 & 0 & 0 \\ 2 & 1 & 0 \\ 4 & 3 & 1 \end{pmatrix}$$

验证：$LU = \begin{pmatrix} 1 & 0 & 0 \\ 2 & 1 & 0 \\ 4 & 3 & 1 \end{pmatrix} \begin{pmatrix} 2 & 1 & 1 \\ 0 & 1 & 1 \\ 0 & 0 & 2 \end{pmatrix} = \begin{pmatrix} 2 & 1 & 1 \\ 4 & 3 & 3 \\ 8 & 7 & 9 \end{pmatrix} = A$。✓

(b) 解 $A\mathbf{x} = \mathbf{b}$ 等价于解 $LU\mathbf{x} = \mathbf{b}$。

**Step 1**：解 $L\mathbf{c} = \mathbf{b}$（前代法）：

$$\begin{pmatrix} 1 & 0 & 0 \\ 2 & 1 & 0 \\ 4 & 3 & 1 \end{pmatrix} \begin{pmatrix} c_1 \\ c_2 \\ c_3 \end{pmatrix} = \begin{pmatrix} 4 \\ 10 \\ 26 \end{pmatrix}$$

- $c_1 = 4$
- $2c_1 + c_2 = 10 \Rightarrow c_2 = 10 - 8 = 2$
- $4c_1 + 3c_2 + c_3 = 26 \Rightarrow c_3 = 26 - 16 - 6 = 4$

故 $\mathbf{c} = \begin{pmatrix} 4 \\ 2 \\ 4 \end{pmatrix}$。

**Step 2**：解 $U\mathbf{x} = \mathbf{c}$（回代法）：

$$\begin{pmatrix} 2 & 1 & 1 \\ 0 & 1 & 1 \\ 0 & 0 & 2 \end{pmatrix} \begin{pmatrix} x_1 \\ x_2 \\ x_3 \end{pmatrix} = \begin{pmatrix} 4 \\ 2 \\ 4 \end{pmatrix}$$

- $2x_3 = 4 \Rightarrow x_3 = 2$
- $x_2 + x_3 = 2 \Rightarrow x_2 = 0$
- $2x_1 + x_2 + x_3 = 4 \Rightarrow 2x_1 = 2 \Rightarrow x_1 = 1$

**答案**：$\mathbf{x} = \begin{pmatrix} 1 \\ 0 \\ 2 \end{pmatrix}$。

**评分标准**：

| 评分项 | 分值 | 说明 |
|--------|------|------|
| 正确执行消元并记录乘数 | 3 | 每个乘数 1 分 |
| 正确写出 $L$ 和 $U$ | 2 | |
| 正确解 $L\mathbf{c} = \mathbf{b}$（前代） | 2 | |
| 正确解 $U\mathbf{x} = \mathbf{c}$（回代） | 2 | |
| 最终答案正确 | 1 | |
| **合计** | **10** | |

---

#### Q7：计算 — 特征值分解与对角化

**难度**：★★★（难）　**对应章节**：Ch 6 — 特征值与特征向量　**分值**：10 分

**题目陈述**：

给定矩阵
$$A = \begin{pmatrix} 4 & 2 \\ 1 & 3 \end{pmatrix}.$$

(a) 求 $A$ 的所有特征值和对应的特征向量。

(b) 判断 $A$ 是否可对角化。如果可以，求出可逆矩阵 $P$ 和对角矩阵 $D$，使得 $A = PDP^{-1}$。

(c) 利用对角化计算 $A^{10} \begin{pmatrix} 1 \\ 1 \end{pmatrix}$。

**参考答案**：

(a) **特征值**：解特征方程 $\det(A - \lambda I) = 0$。

$$\det\begin{pmatrix} 4 - \lambda & 2 \\ 1 & 3 - \lambda \end{pmatrix} = (4 - \lambda)(3 - \lambda) - 2 = \lambda^2 - 7\lambda + 10 = (\lambda - 5)(\lambda - 2) = 0.$$

特征值为 $\lambda_1 = 5$，$\lambda_2 = 2$。

**特征向量**：

- 对 $\lambda_1 = 5$：
  $$(A - 5I)\mathbf{v} = \begin{pmatrix} -1 & 2 \\ 1 & -2 \end{pmatrix}\mathbf{v} = \mathbf{0}.$$
  由第一行：$-v_1 + 2v_2 = 0$，取 $\mathbf{v}_1 = \begin{pmatrix} 2 \\ 1 \end{pmatrix}$。

- 对 $\lambda_2 = 2$：
  $$(A - 2I)\mathbf{v} = \begin{pmatrix} 2 & 2 \\ 1 & 1 \end{pmatrix}\mathbf{v} = \mathbf{0}.$$
  由第一行：$2v_1 + 2v_2 = 0$，取 $\mathbf{v}_2 = \begin{pmatrix} 1 \\ -1 \end{pmatrix}$。

(b) $A$ 有两个**互异**特征值，因此必可对角化。

$$P = \begin{pmatrix} 2 & 1 \\ 1 & -1 \end{pmatrix}, \quad D = \begin{pmatrix} 5 & 0 \\ 0 & 2 \end{pmatrix}.$$

求 $P^{-1}$：$\det P = -2 - 1 = -3$。

$$P^{-1} = -\frac{1}{3} \begin{pmatrix} -1 & -1 \\ -1 & 2 \end{pmatrix} = \begin{pmatrix} \frac{1}{3} & \frac{1}{3} \\ \frac{1}{3} & -\frac{2}{3} \end{pmatrix}.$$

(c) 首先将 $\begin{pmatrix} 1 \\ 1 \end{pmatrix}$ 用特征向量表示：

$$\begin{pmatrix} 1 \\ 1 \end{pmatrix} = c_1 \begin{pmatrix} 2 \\ 1 \end{pmatrix} + c_2 \begin{pmatrix} 1 \\ -1 \end{pmatrix}$$

解方程组：
$$\begin{cases} 2c_1 + c_2 = 1 \\ c_1 - c_2 = 1 \end{cases} \Rightarrow c_1 = \frac{2}{3},\ c_2 = -\frac{1}{3}.$$

于是
$$A^{10} \begin{pmatrix} 1 \\ 1 \end{pmatrix} = \frac{2}{3} \cdot 5^{10} \begin{pmatrix} 2 \\ 1 \end{pmatrix} - \frac{1}{3} \cdot 2^{10} \begin{pmatrix} 1 \\ -1 \end{pmatrix}$$

$$= \frac{2}{3} \cdot 9765625 \begin{pmatrix} 2 \\ 1 \end{pmatrix} - \frac{1}{3} \cdot 1024 \begin{pmatrix} 1 \\ -1 \end{pmatrix}$$

$$= \begin{pmatrix} \frac{4 \cdot 9765625 - 1024}{3} \\ \frac{2 \cdot 9765625 + 1024}{3} \end{pmatrix} = \begin{pmatrix} \frac{39062476}{3} \\ \frac{19531274}{3} \end{pmatrix}.$$

或保留为 $= \begin{pmatrix} \frac{2}{3} \cdot 5^{10} \cdot 2 - \frac{1}{3} \cdot 2^{10} \\ \frac{2}{3} \cdot 5^{10} + \frac{1}{3} \cdot 2^{10} \end{pmatrix}$。

**评分标准**：

| 评分项 | 分值 | 说明 |
|--------|------|------|
| 正确求出特征值 | 2 | 解二次方程 |
| 正确求出两个特征向量 | 2 | 各 1 分 |
| 正确判定可对角化 | 1 | 互异特征值即可判定 |
| 正确构造 $P$ 和 $D$ | 2 | |
| 正确求 $P^{-1}$ | 1 | |
| 正确分解初始向量 | 1 | 解出 $c_1, c_2$ |
| 正确利用对角化计算幂 | 1 | 公式 $A^n = PD^nP^{-1}$ 或特征分解法 |
| **合计** | **10** | |

---

#### Q8：计算 — 最小二乘拟合

**难度**：★★★（难）　**对应章节**：Ch 4 — 正交投影与最小二乘　**分值**：10 分

**题目陈述**：

给定三个数据点 $(1, 2)$，$(2, 3)$，$(3, 5)$。希望用一条直线 $y = C + Dt$ 进行最小二乘拟合。

(a) 建立超定方程组 $A\mathbf{x} = \mathbf{b}$，写出矩阵 $A$ 和向量 $\mathbf{b}$。

(b) 导出并求解正规方程（normal equation）$A^T A \hat{\mathbf{x}} = A^T \mathbf{b}$，求出最佳拟合参数 $\hat{C}$ 和 $\hat{D}$。

(c) 计算拟合误差 $\|\mathbf{b} - A\hat{\mathbf{x}}\|^2$。

**参考答案**：

(a) 将三个点代入 $y = C + Dt$：

$$\begin{cases} C + D \cdot 1 = 2 \\ C + D \cdot 2 = 3 \\ C + D \cdot 3 = 5 \end{cases}$$

矩阵形式：

$$A = \begin{pmatrix} 1 & 1 \\ 1 & 2 \\ 1 & 3 \end{pmatrix}, \quad \mathbf{b} = \begin{pmatrix} 2 \\ 3 \\ 5 \end{pmatrix}, \quad \mathbf{x} = \begin{pmatrix} C \\ D \end{pmatrix}.$$

(b) **正规方程**：

$$A^T A = \begin{pmatrix} 1 & 1 & 1 \\ 1 & 2 & 3 \end{pmatrix} \begin{pmatrix} 1 & 1 \\ 1 & 2 \\ 1 & 3 \end{pmatrix} = \begin{pmatrix} 3 & 6 \\ 6 & 14 \end{pmatrix}.$$

$$A^T \mathbf{b} = \begin{pmatrix} 1 & 1 & 1 \\ 1 & 2 & 3 \end{pmatrix} \begin{pmatrix} 2 \\ 3 \\ 5 \end{pmatrix} = \begin{pmatrix} 10 \\ 23 \end{pmatrix}.$$

解方程组：
$$\begin{pmatrix} 3 & 6 \\ 6 & 14 \end{pmatrix} \begin{pmatrix} C \\ D \end{pmatrix} = \begin{pmatrix} 10 \\ 23 \end{pmatrix}.$$

第一式：$3C + 6D = 10 \Rightarrow C + 2D = \frac{10}{3}$。

第二式：$6C + 14D = 23$。由第一式 $C = \frac{10}{3} - 2D$，代入第二式：

$$6\left(\frac{10}{3} - 2D\right) + 14D = 20 - 12D + 14D = 20 + 2D = 23 \Rightarrow D = \frac{3}{2}.$$

于是 $C = \frac{10}{3} - 2 \cdot \frac{3}{2} = \frac{10}{3} - 3 = \frac{1}{3}$。

**最佳拟合直线**：$y = \frac{1}{3} + \frac{3}{2}t$。

(c) **拟合值**：

- $t = 1$：$y = \frac{1}{3} + \frac{3}{2} = \frac{11}{6}$，误差 $= 2 - \frac{11}{6} = \frac{1}{6}$
- $t = 2$：$y = \frac{1}{3} + 3 = \frac{10}{3}$，误差 $= 3 - \frac{10}{3} = -\frac{1}{3}$
- $t = 3$：$y = \frac{1}{3} + \frac{9}{2} = \frac{29}{6}$，误差 $= 5 - \frac{29}{6} = \frac{1}{6}$

误差向量：$\mathbf{e} = \begin{pmatrix} \frac{1}{6} \\ -\frac{1}{3} \\ \frac{1}{6} \end{pmatrix}$。

$$\|\mathbf{e}\|^2 = \left(\frac{1}{6}\right)^2 + \left(-\frac{1}{3}\right)^2 + \left(\frac{1}{6}\right)^2 = \frac{1}{36} + \frac{4}{36} + \frac{1}{36} = \frac{6}{36} = \frac{1}{6}.$$

**评分标准**：

| 评分项 | 分值 | 说明 |
|--------|------|------|
| 正确建立 $A$ 和 $\mathbf{b}$ | 2 | |
| 正确计算 $A^T A$ | 2 | |
| 正确计算 $A^T \mathbf{b}$ | 2 | |
| 正确求解正规方程 | 2 | 得到 $C = \frac{1}{3}, D = \frac{3}{2}$ |
| 正确计算拟合误差 | 2 | |
| **合计** | **10** | |

---

### 模块四：综合拓展（2题，共20分）

---

#### Q9：综合 — 四大基本子空间与 SVD 初探

**难度**：★★★☆（较难）　**对应章节**：Ch 3, Ch 7 — 四大子空间与 SVD　**分值**：10 分

**题目陈述**：

设
$$A = \begin{pmatrix} 1 & 1 \\ 2 & 2 \\ 1 & -1 \end{pmatrix}.$$

(a) 求 $A$ 的四个基本子空间（列空间 $C(A)$、零空间 $N(A)$、行空间 $C(A^T)$、左零空间 $N(A^T)$）的维数，并验证维数关系公式。

(b) 求 $A$ 的奇异值分解 $A = U\Sigma V^T$ 中的矩阵 $V$ 和奇异值（只需写出 $\Sigma$ 和 $V$，不需要完整求出 $U$）。

**参考答案**：

(a) $A$ 为 $3 \times 2$ 矩阵，$\operatorname{rank}(A) = 2$（两列线性无关，因为第二列不是第一列的倍数）。

- **列空间** $C(A)$：$\dim C(A) = \operatorname{rank}(A) = 2$。
- **零空间** $N(A)$：由秩-零化度定理，$\dim N(A) = 2 - \operatorname{rank}(A) = 0$。即 $N(A) = \{\mathbf{0}\}$。
- **行空间** $C(A^T)$：$\dim C(A^T) = \operatorname{rank}(A) = 2$。
- **左零空间** $N(A^T)$：$\dim N(A^T) = 3 - \operatorname{rank}(A) = 1$。

**维数关系验证**：

- $C(A) \oplus N(A^T)$ 分解 $\mathbb{R}^3$：$2 + 1 = 3$ ✓
- $C(A^T) \oplus N(A)$ 分解 $\mathbb{R}^2$：$2 + 0 = 2$ ✓

(b) 计算 $A^T A$：

$$A^T A = \begin{pmatrix} 1 & 2 & 1 \\ 1 & 2 & -1 \end{pmatrix} \begin{pmatrix} 1 & 1 \\ 2 & 2 \\ 1 & -1 \end{pmatrix} = \begin{pmatrix} 6 & 4 \\ 4 & 6 \end{pmatrix}.$$

特征值：$\det(A^T A - \lambda I) = (6 - \lambda)^2 - 16 = \lambda^2 - 12\lambda + 20 = (\lambda - 10)(\lambda - 2) = 0$。

特征值为 $\lambda_1 = 10$，$\lambda_2 = 2$。

**奇异值**：$\sigma_1 = \sqrt{10}$，$\sigma_2 = \sqrt{2}$。

$$\Sigma = \begin{pmatrix} \sqrt{10} & 0 \\ 0 & \sqrt{2} \\ 0 & 0 \end{pmatrix}.$$

**求 $V$**（$A^T A$ 的特征向量，单位化）：

- 对 $\lambda_1 = 10$：$(A^T A - 10I)\mathbf{v} = \begin{pmatrix} -4 & 4 \\ 4 & -4 \end{pmatrix}\mathbf{v} = \mathbf{0}$，得 $\mathbf{v}_1 = \frac{1}{\sqrt{2}}\begin{pmatrix} 1 \\ 1 \end{pmatrix}$。
- 对 $\lambda_2 = 2$：$(A^T A - 2I)\mathbf{v} = \begin{pmatrix} 4 & 4 \\ 4 & 4 \end{pmatrix}\mathbf{v} = \mathbf{0}$，得 $\mathbf{v}_2 = \frac{1}{\sqrt{2}}\begin{pmatrix} 1 \\ -1 \end{pmatrix}$。

$$V = \frac{1}{\sqrt{2}} \begin{pmatrix} 1 & 1 \\ 1 & -1 \end{pmatrix}.$$

**评分标准**：

| 评分项 | 分值 | 说明 |
|--------|------|------|
| 正确判断秩为 2 | 1 | |
| 正确求出四个子空间维数 | 2 | 各 0.5 分 |
| 正确验证维数关系 | 1 | |
| 正确计算 $A^T A$ | 1 | |
| 正确求出特征值/奇异值 | 2 | |
| 正确构造 $\Sigma$ | 1 | |
| 正确求出 $V$ 的列向量 | 2 | 各 1 分（含单位化） |
| **合计** | **10** | |

---

#### Q10：综合拓展 — 矩阵指数与微分方程组

**难度**：★★★★（难）　**对应章节**：Ch 6 — 矩阵指数 $e^{At}$　**分值**：10 分

**题目陈述**：

考虑线性常微分方程组
$$\frac{d\mathbf{u}}{dt} = A\mathbf{u}, \quad A = \begin{pmatrix} 0 & 1 \\ -2 & 3 \end{pmatrix}, \quad \mathbf{u}(0) = \begin{pmatrix} 1 \\ 0 \end{pmatrix}.$$

(a) 求 $A$ 的特征值和特征向量，并判断 $A$ 是否可对角化。

(b) 利用对角化求矩阵指数 $e^{At}$ 的显式表达式。

(c) 求方程组的解 $\mathbf{u}(t)$。

**参考答案**：

(a) 特征方程：

$$\det(A - \lambda I) = \det\begin{pmatrix} -\lambda & 1 \\ -2 & 3 - \lambda \end{pmatrix} = -\lambda(3 - \lambda) + 2 = \lambda^2 - 3\lambda + 2 = (\lambda - 1)(\lambda - 2) = 0.$$

特征值：$\lambda_1 = 1$，$\lambda_2 = 2$（互异，故可对角化）。

- 对 $\lambda_1 = 1$：$(A - I)\mathbf{v} = \begin{pmatrix} -1 & 1 \\ -2 & 2 \end{pmatrix}\mathbf{v} = \mathbf{0}$，$\mathbf{v}_1 = \begin{pmatrix} 1 \\ 1 \end{pmatrix}$。
- 对 $\lambda_2 = 2$：$(A - 2I)\mathbf{v} = \begin{pmatrix} -2 & 1 \\ -2 & 1 \end{pmatrix}\mathbf{v} = \mathbf{0}$，$\mathbf{v}_2 = \begin{pmatrix} 1 \\ 2 \end{pmatrix}$。

(b) $A = PDP^{-1}$，其中

$$P = \begin{pmatrix} 1 & 1 \\ 1 & 2 \end{pmatrix}, \quad D = \begin{pmatrix} 1 & 0 \\ 0 & 2 \end{pmatrix}, \quad P^{-1} = \begin{pmatrix} 2 & -1 \\ -1 & 1 \end{pmatrix}.$$

矩阵指数：

$$e^{At} = P e^{Dt} P^{-1} = \begin{pmatrix} 1 & 1 \\ 1 & 2 \end{pmatrix} \begin{pmatrix} e^t & 0 \\ 0 & e^{2t} \end{pmatrix} \begin{pmatrix} 2 & -1 \\ -1 & 1 \end{pmatrix}$$

$$= \begin{pmatrix} e^t & e^{2t} \\ e^t & 2e^{2t} \end{pmatrix} \begin{pmatrix} 2 & -1 \\ -1 & 1 \end{pmatrix}$$

$$= \begin{pmatrix} 2e^t - e^{2t} & -e^t + e^{2t} \\ 2e^t - 2e^{2t} & -e^t + 2e^{2t} \end{pmatrix}.$$

(c) 解为 $\mathbf{u}(t) = e^{At}\mathbf{u}(0)$：

$$\mathbf{u}(t) = \begin{pmatrix} 2e^t - e^{2t} & -e^t + e^{2t} \\ 2e^t - 2e^{2t} & -e^t + 2e^{2t} \end{pmatrix} \begin{pmatrix} 1 \\ 0 \end{pmatrix} = \begin{pmatrix} 2e^t - e^{2t} \\ 2e^t - 2e^{2t} \end{pmatrix}.$$

**评分标准**：

| 评分项 | 分值 | 说明 |
|--------|------|------|
| 正确求出两个特征值 | 1 | |
| 正确求出两个特征向量 | 2 | 各 1 分 |
| 正确构造 $P, D, P^{-1}$ | 2 | |
| 正确写出 $e^{Dt}$ | 1 | 对角元取指数 |
| 正确计算 $e^{At} = Pe^{Dt}P^{-1}$ | 2 | 矩阵乘法 |
| 正确求出 $\mathbf{u}(t)$ | 2 | |
| **合计** | **10** | |

---

## 附录：题目与课程章节对应总表

| 题号 | 测试阶段 | 模块 | 对应章节 | 核心概念 | 难度 |
|------|----------|------|----------|----------|------|
| Q1 | 课前基线 | — | Ch 1 | 线性组合、线性无关 | ★☆☆ |
| Q2 | 课前基线 | — | Ch 2 | 矩阵乘法 | ★☆☆ |
| Q3 | 课前基线 | — | Ch 1–2 | 行图像、列图像 | ★★☆ |
| Q4 | 课前基线 | — | Ch 3 | 子空间判定 | ★★☆ |
| Q5 | 课前基线 | — | Ch 5 | 行列式计算 | ★★☆ |
| Q6 | 期末综合 | 计算应用 | Ch 2 | LU 分解 | ★★☆ |
| Q7 | 期末综合 | 计算应用 | Ch 6 | 特征值分解、对角化 | ★★★ |
| Q8 | 期末综合 | 计算应用 | Ch 4 | 最小二乘拟合 | ★★★ |
| Q9 | 期末综合 | 综合拓展 | Ch 3, Ch 7 | 四大子空间、SVD | ★★★☆ |
| Q10 | 期末综合 | 综合拓展 | Ch 6 | 矩阵指数、微分方程 | ★★★★ |
| Q1(期末) | 期末综合 | 定义复述 | Ch 3 | 向量空间公理 | ★★☆ |
| Q2(期末) | 期末综合 | 定义复述 | Ch 6 | 特征值、特征多项式 | ★★☆ |
| Q3(期末) | 期末综合 | 定理证明 | Ch 3 | 秩-零化度定理 | ★★★ |
| Q4(期末) | 期末综合 | 定理证明 | Ch 4 | 投影矩阵性质 | ★★★ |
| Q5(期末) | 期末综合 | 定理证明 | Ch 6 | 实对称矩阵特征值为实 | ★★★☆ |

---

**文档版本**：v1.0（2026-04-18）

**关联文件**：

- `project/MIT-18.06-课堂验证模块设计.md`
- `project/MIT-18.06-讲义逐章拆解索引.md`
