---
title: "Ch.11 最小二乘与Gram-Schmidt（Least Squares & Gram-Schmidt）"
level: "silver"
course: MIT 18.06 线性代数
chapter: "11"
msc_primary: "15-01"
target_courses:
  - "MIT 18.06 Ch.11"
references:
  textbooks:
    - title: "Introduction to Linear Algebra"
      author: "Gilbert Strang"
      edition: "5th"
      chapters: "Chapter 4"
      pages: "219-245"
  lectures:
    - institution: "MIT"
      course_code: "18.06"
      lecture: "L14-L16"
      url: "https://ocw.mit.edu/courses/mathematics/18-06-linear-algebra-spring-2010/"
keywords:
  - "least squares"
  - "normal equation"
  - "QR decomposition"
  - "orthogonal matrix"
  - "projection matrix"
  - "Gram-Schmidt"
status: "draft"
review_rounds: 0
created_at: "2026-04-18"
---

# Ch.11 最小二乘与Gram-Schmidt（Least Squares & Gram-Schmidt）

> **课程**: MIT 18.06 Linear Algebra | **章节**: Chapter 11
> **学习目标**: 掌握最小二乘问题的理论与计算，理解正规方程与QR分解的联系，熟练运用Gram-Schmidt正交化构造标准正交基，建立从几何投影到数值算法的完整认知链条。

---

## 一、核心定义

### 定义 11.1（最小二乘问题）

**严格陈述**: 设 $A \in \mathbb{R}^{m \times n}$，$\mathbf{b} \in \mathbb{R}^m$。若线性方程组 $A\mathbf{x} = \mathbf{b}$ 不相容（即 $\mathbf{b} \notin C(A)$），则称寻找 $\hat{\mathbf{x}} \in \mathbb{R}^n$ 使得

$$\|A\hat{\mathbf{x}} - \mathbf{b}\| = \min_{\mathbf{x} \in \mathbb{R}^n} \|A\mathbf{x} - \mathbf{b}\|$$

的问题为**最小二乘问题**（least squares problem），其中 $\|\cdot\|$ 表示欧几里得范数。向量 $\hat{\mathbf{x}}$ 称为**最小二乘解**（least squares solution），$\hat{\mathbf{b}} = A\hat{\mathbf{x}}$ 称为 $\mathbf{b}$ 在 $C(A)$ 上的**最佳逼近**（best approximation）。

**条件说明**: 此处不要求 $A$ 列满秩；当 $A$ 列不满秩时，最小二乘解不唯一，但最佳逼近 $\hat{\mathbf{b}}$ 总是唯一存在（由投影定理保证）。

**直观解释**: 最小二乘问题的几何本质是：在 $A$ 的列空间 $C(A)$ 中寻找离 $\mathbf{b}$ 最近的点 $\hat{\mathbf{b}}$。这个最近点正是 $\mathbf{b}$ 在 $C(A)$ 上的正交投影。误差向量 $\mathbf{e} = \mathbf{b} - \hat{\mathbf{b}}$ 垂直于 $C(A)$。

---

### 定义 11.2（正规方程）

**严格陈述**: 设 $A \in \mathbb{R}^{m \times n}$，$\mathbf{b} \in \mathbb{R}^m$。方程组

$$A^T A \mathbf{x} = A^T \mathbf{b}$$

称为最小二乘问题的**正规方程**（normal equations）。

**直观解释**: 正规方程的推导来源于误差向量与列空间正交的条件：$\mathbf{e} = \mathbf{b} - A\hat{\mathbf{x}}$ 必须垂直于 $C(A)$ 中所有向量，即 $A^T(\mathbf{b} - A\hat{\mathbf{x}}) = \mathbf{0}$。整理即得 $A^T A \hat{\mathbf{x}} = A^T \mathbf{b}$。

---

### 定义 11.3（QR 分解）

**严格陈述**: 设 $A \in \mathbb{R}^{m \times n}$（$m \geq n$）且列满秩（$\operatorname{rank}(A) = n$）。若存在列正交矩阵 $Q \in \mathbb{R}^{m \times n}$（即 $Q^T Q = I_n$）和上三角矩阵 $R \in \mathbb{R}^{n \times n}$（对角元为正），使得

$$A = QR,$$

则称此分解为 $A$ 的**QR 分解**（QR decomposition）。当要求 $R$ 的对角元均为正数时，此分解唯一。

**注**: 若 $A$ 为方阵（$m = n$），则 $Q$ 为正交矩阵（$Q^T Q = QQ^T = I_n$）。

**直观解释**: QR 分解将矩阵 $A$ 的列向量"重新包装"为一组标准正交列向量（$Q$ 的列），而 $R$ 记录了原列向量在新基下的坐标。$R$ 的上三角性反映了 Gram-Schmidt 正交化的逐层构造——每个新向量只依赖于之前已正交化的向量。

---

### 定义 11.4（正交矩阵）

**严格陈述**: 方阵 $Q \in \mathbb{R}^{n \times n}$ 称为**正交矩阵**（orthogonal matrix），如果

$$Q^T Q = QQ^T = I_n,$$

即 $Q^{-1} = Q^T$。

**等价刻画**: $Q$ 为正交矩阵当且仅当其列向量构成 $\mathbb{R}^n$ 的一组标准正交基（orthonormal basis）。

**直观解释**: 正交矩阵代表"刚体运动"——保持长度和角度不变的线性变换。旋转和反射都是正交变换。$Q^T Q = I$ 意味着 $Q$ 的各列两两正交且长度均为 1。

---

### 定义 11.5（投影矩阵）

**严格陈述**: 设 $V \subseteq \mathbb{R}^m$ 为子空间。线性变换 $P: \mathbb{R}^m \to \mathbb{R}^m$ 称为到 $V$ 上的**正交投影矩阵**（orthogonal projection matrix），如果：

1. $P^2 = P$（幂等性，idempotent）；
2. $P^T = P$（对称性，symmetric）；
3. $C(P) = V$（值域恰为 $V$）。

**直观解释**: 投影矩阵将任意向量"压扁"到子空间 $V$ 上，且是沿着 $V$ 的正交补方向进行的。幂等性表示"投影一次后再投影不变"；对称性保证投影方向与目标子空间正交。

---

### 定义 11.6（Gram-Schmidt 正交化）

**严格陈述**: 设 $\{\mathbf{a}_1, \mathbf{a}_2, \ldots, \mathbf{a}_n\}$ 是 $\mathbb{R}^m$ 中线性无关的向量组。Gram-Schmidt 正交化过程递归地构造正交向量组 $\{\mathbf{q}_1, \ldots, \mathbf{q}_n\}$ 如下：

$$\mathbf{v}_1 = \mathbf{a}_1, \quad \mathbf{q}_1 = \frac{\mathbf{v}_1}{\|\mathbf{v}_1\|};$$

$$\mathbf{v}_k = \mathbf{a}_k - \sum_{j=1}^{k-1} (\mathbf{q}_j^T \mathbf{a}_k) \mathbf{q}_j, \quad \mathbf{q}_k = \frac{\mathbf{v}_k}{\|\mathbf{v}_k\|}, \quad k = 2, \ldots, n.$$

若记 $r_{jk} = \mathbf{q}_j^T \mathbf{a}_k$（$j < k$），$r_{kk} = \|\mathbf{v}_k\|$，则 $\mathbf{a}_k = \sum_{j=1}^k r_{jk} \mathbf{q}_j$，从而得到 QR 分解 $A = QR$。

**直观解释**: Gram-Schmidt 的核心思想是"逐层剥离"——在处理 $\mathbf{a}_k$ 时，先减去它在前面所有已正交化方向上的投影分量，剩下的就是与前面所有向量都正交的新方向，再单位化即可。

---

## 二、核心定理与完整证明

### 定理 11.1（最小二乘解与正规方程）

**定理陈述**: 设 $A \in \mathbb{R}^{m \times n}$，$\mathbf{b} \in \mathbb{R}^m$。

1. 向量 $\hat{\mathbf{x}} \in \mathbb{R}^n$ 是最小二乘解（即最小化 $\|A\mathbf{x} - \mathbf{b}\|$）当且仅当 $\hat{\mathbf{x}}$ 满足正规方程 $A^T A \hat{\mathbf{x}} = A^T \mathbf{b}$。

2. 正规方程总有解。若 $A$ 列满秩，则最小二乘解唯一，且可表示为

$$\hat{\mathbf{x}} = (A^T A)^{-1} A^T \mathbf{b}.$$

**证明**:

**(1) 最小二乘解 $\Rightarrow$ 满足正规方程**

设 $\hat{\mathbf{x}}$ 最小化 $f(\mathbf{x}) = \|A\mathbf{x} - \mathbf{b}\|^2 = (A\mathbf{x} - \mathbf{b})^T(A\mathbf{x} - \mathbf{b})$。

这是关于 $\mathbf{x}$ 的二次函数。由多元微积分，极值点处梯度为零：

$$\nabla f(\mathbf{x}) = 2A^T(A\mathbf{x} - \mathbf{b}) = \mathbf{0}.$$

（梯度计算验证：$f(\mathbf{x}) = \mathbf{x}^T A^T A \mathbf{x} - 2\mathbf{b}^T A \mathbf{x} + \mathbf{b}^T \mathbf{b}$，故 $\nabla f = 2A^T A \mathbf{x} - 2A^T \mathbf{b}$。）

因此 $A^T A \hat{\mathbf{x}} = A^T \mathbf{b}$。

**替代几何证明（不依赖微积分）**:

$\|A\mathbf{x} - \mathbf{b}\|$ 最小等价于 $A\hat{\mathbf{x}}$ 是 $\mathbf{b}$ 在 $C(A)$ 上的正交投影。误差向量 $\mathbf{e} = \mathbf{b} - A\hat{\mathbf{x}}$ 必须与 $C(A)$ 中所有向量正交，即与 $A$ 的每一列正交：

$$A^T \mathbf{e} = A^T(\mathbf{b} - A\hat{\mathbf{x}}) = \mathbf{0} \Rightarrow A^T A \hat{\mathbf{x}} = A^T \mathbf{b}.$$

**(2) 正规方程 $\Rightarrow$ 最小二乘解**

设 $\hat{\mathbf{x}}$ 满足 $A^T A \hat{\mathbf{x}} = A^T \mathbf{b}$。对任意 $\mathbf{x} \in \mathbb{R}^n$，记 $\mathbf{y} = \mathbf{x} - \hat{\mathbf{x}}$，则

$$\|A\mathbf{x} - \mathbf{b}\|^2 = \|A(\hat{\mathbf{x}} + \mathbf{y}) - \mathbf{b}\|^2 = \|(A\hat{\mathbf{x}} - \mathbf{b}) + A\mathbf{y}\|^2.$$

展开：

$$= \|A\hat{\mathbf{x}} - \mathbf{b}\|^2 + 2(A\hat{\mathbf{x}} - \mathbf{b})^T A\mathbf{y} + \|A\mathbf{y}\|^2.$$

中间项：$(A\hat{\mathbf{x}} - \mathbf{b})^T A\mathbf{y} = \mathbf{y}^T A^T(A\hat{\mathbf{x}} - \mathbf{b}) = \mathbf{y}^T(A^T A \hat{\mathbf{x}} - A^T \mathbf{b}) = \mathbf{y}^T \mathbf{0} = 0$。

因此

$$\|A\mathbf{x} - \mathbf{b}\|^2 = \|A\hat{\mathbf{x}} - \mathbf{b}\|^2 + \|A\mathbf{y}\|^2 \geq \|A\hat{\mathbf{x}} - \mathbf{b}\|^2.$$

等号成立当且仅当 $\|A\mathbf{y}\| = 0$，即 $A\mathbf{y} = \mathbf{0}$，亦即 $A\mathbf{x} = A\hat{\mathbf{x}}$。

**(3) 解的存在性与唯一性**

正规方程 $A^T A \mathbf{x} = A^T \mathbf{b}$ 总有解，因为 $A^T \mathbf{b} \in C(A^T) = C(A^T A)$（因为 $C(A^T A) = C(A^T)$，见习题 11.8）。

若 $A$ 列满秩，则 $A^T A$ 可逆（定理 11.2），故解唯一：$\hat{\mathbf{x}} = (A^T A)^{-1} A^T \mathbf{b}$。$\square$

> **证明要点提示**: 正规方程的本质是"误差与列空间正交"。第二部分的展开技巧（将任意解与特解之差分离）是处理最小化问题的标准手法，其关键在于交叉项为零。

---

### 定理 11.2（$A^T A$ 的正定性与可逆性）

**定理陈述**: 设 $A \in \mathbb{R}^{m \times n}$。则：

1. $A^T A$ 是半正定矩阵；
2. $A^T A$ 正定当且仅当 $A$ 列满秩（$\operatorname{rank}(A) = n$）；
3. 若 $A$ 列满秩，则 $A^T A$ 可逆。

**证明**:

**(1) 半正定性**

对任意 $\mathbf{x} \in \mathbb{R}^n$：

$$\mathbf{x}^T (A^T A) \mathbf{x} = (A\mathbf{x})^T (A\mathbf{x}) = \|A\mathbf{x}\|^2 \geq 0.$$

故 $A^T A$ 半正定。

**(2) 正定的等价条件**

$A^T A$ 正定 $\Leftrightarrow$ 对所有 $\mathbf{x} \neq \mathbf{0}$，$\mathbf{x}^T(A^T A)\mathbf{x} > 0$

$\Leftrightarrow$ 对所有 $\mathbf{x} \neq \mathbf{0}$，$\|A\mathbf{x}\|^2 > 0$

$\Leftrightarrow$ 对所有 $\mathbf{x} \neq \mathbf{0}$，$A\mathbf{x} \neq \mathbf{0}$

$\Leftrightarrow$ $N(A) = \{\mathbf{0}\}$

$\Leftrightarrow$ $A$ 的列线性无关

$\Leftrightarrow$ $\operatorname{rank}(A) = n$（列满秩）。

**(3) 可逆性**

若 $A$ 列满秩，则 $A^T A$ 正定。正定矩阵的所有特征值均为正，故行列式 $\det(A^T A) > 0$，从而 $A^T A$ 可逆。$\square$

---

### 定理 11.3（投影矩阵的显式公式）

**定理陈述**: 设 $A \in \mathbb{R}^{m \times n}$ 列满秩。则到 $C(A)$ 上的正交投影矩阵为

$$P = A(A^T A)^{-1} A^T \in \mathbb{R}^{m \times m}.$$

对任意 $\mathbf{b} \in \mathbb{R}^m$，$\mathbf{b}$ 在 $C(A)$ 上的投影为 $\hat{\mathbf{b}} = P\mathbf{b}$，且 $\mathbf{b} = \hat{\mathbf{b}} + \mathbf{e}$，其中 $\mathbf{e} = (I-P)\mathbf{b} \perp C(A)$。

**证明**:

**验证 $P$ 是投影矩阵**:

- **幂等性**: $P^2 = A(A^T A)^{-1} A^T \cdot A(A^T A)^{-1} A^T = A(A^T A)^{-1}(A^T A)(A^T A)^{-1}A^T = A(A^T A)^{-1}A^T = P$。

- **对称性**: $P^T = (A(A^T A)^{-1}A^T)^T = A((A^T A)^{-1})^T A^T = A(A^T A)^{-1}A^T = P$（因 $A^T A$ 对称，其逆亦对称）。

- **值域为 $C(A)$**: 显然 $C(P) \subseteq C(A)$。反之，对任意 $A\mathbf{x} \in C(A)$，有 $PA\mathbf{x} = A(A^T A)^{-1}A^T A \mathbf{x} = A\mathbf{x}$，故 $A\mathbf{x} \in C(P)$。因此 $C(P) = C(A)$。

**正交分解**: 对任意 $\mathbf{b}$，$\hat{\mathbf{b}} = P\mathbf{b} \in C(A)$，$\mathbf{e} = \mathbf{b} - P\mathbf{b} = (I-P)\mathbf{b}$。

验证 $\mathbf{e} \perp C(A)$：$A^T \mathbf{e} = A^T(I-P)\mathbf{b} = A^T\mathbf{b} - A^T A(A^T A)^{-1}A^T \mathbf{b} = A^T\mathbf{b} - A^T\mathbf{b} = \mathbf{0}$。

故 $\mathbf{e}$ 与 $A$ 的每一列正交，从而与 $C(A)$ 中所有向量正交。$\square$

---

### 定理 11.4（QR 分解的存在唯一性）

**定理陈述**: 设 $A \in \mathbb{R}^{m \times n}$（$m \geq n$）且列满秩。则存在唯一的 QR 分解 $A = QR$，其中 $Q \in \mathbb{R}^{m \times n}$ 满足 $Q^T Q = I_n$，$R \in \mathbb{R}^{n \times n}$ 为上三角矩阵且对角元 $r_{ii} > 0$。

**证明**:

**存在性**（构造性证明，即 Gram-Schmidt 过程）:

设 $A = [\mathbf{a}_1 \; \mathbf{a}_2 \; \cdots \; \mathbf{a}_n]$，$\{\mathbf{a}_i\}$ 线性无关。

**步骤 1**: $\mathbf{v}_1 = \mathbf{a}_1$，$r_{11} = \|\mathbf{v}_1\| > 0$，$\mathbf{q}_1 = \mathbf{v}_1 / r_{11}$。则 $\mathbf{a}_1 = r_{11}\mathbf{q}_1$。

**步骤 k**（归纳）: 假设已构造出标准正交组 $\{\mathbf{q}_1, \ldots, \mathbf{q}_{k-1}\}$ 及上三角关系使得 $[\mathbf{a}_1 \; \cdots \; \mathbf{a}_{k-1}] = [\mathbf{q}_1 \; \cdots \; \mathbf{q}_{k-1}] R_{k-1}$。

定义

$$\mathbf{v}_k = \mathbf{a}_k - \sum_{j=1}^{k-1} (\mathbf{q}_j^T \mathbf{a}_k) \mathbf{q}_j.$$

**断言**: $\mathbf{v}_k \neq \mathbf{0}$。若不然，$\mathbf{a}_k \in \operatorname{span}\{\mathbf{q}_1, \ldots, \mathbf{q}_{k-1}\} = \operatorname{span}\{\mathbf{a}_1, \ldots, \mathbf{a}_{k-1}\}$，与列满秩矛盾。

令 $r_{kk} = \|\mathbf{v}_k\| > 0$，$r_{jk} = \mathbf{q}_j^T \mathbf{a}_k$（$j < k$），$\mathbf{q}_k = \mathbf{v}_k / r_{kk}$。

则 $\mathbf{a}_k = \sum_{j=1}^{k-1} r_{jk} \mathbf{q}_j + \mathbf{v}_k = \sum_{j=1}^k r_{jk} \mathbf{q}_j$。

归纳完成，得到 $A = QR$，其中 $Q = [\mathbf{q}_1 \; \cdots \; \mathbf{q}_n]$，$R = (r_{jk})$（当 $j > k$ 时 $r_{jk} = 0$），且 $r_{kk} > 0$。

**唯一性**: 设 $A = Q_1 R_1 = Q_2 R_2$ 均为满足条件的 QR 分解。则

$$Q_1 R_1 = Q_2 R_2 \Rightarrow Q_2^T Q_1 = R_2 R_1^{-1}.$$

左端：$(Q_2^T Q_1)^T(Q_2^T Q_1) = Q_1^T Q_2 Q_2^T Q_1 = Q_1^T Q_1 = I_n$？等等，$Q_2$ 不是方阵，$Q_2 Q_2^T \neq I$ 一般成立。需修正。

正确论证：$Q_2^T Q_1 = R_2 R_1^{-1}$。右端 $R_2 R_1^{-1}$ 是上三角矩阵（上三角之逆仍上三角，上三角之积仍上三角）。左端 $(Q_2^T Q_1)^T = Q_1^T Q_2$。但 $Q_2^T Q_1$ 本身一般不是上三角或下三角。

换个思路：由 $A^T A = R_1^T Q_1^T Q_1 R_1 = R_1^T R_1 = R_2^T R_2$。$A^T A$ 是正定矩阵，其Cholesky分解唯一（要求对角元为正）。故 $R_1 = R_2$。进而 $Q_1 = AR_1^{-1} = AR_2^{-1} = Q_2$。$\square$

---

### 定理 11.5（QR 分解求解最小二乘）

**定理陈述**: 设 $A \in \mathbb{R}^{m \times n}$ 列满秩，$A = QR$ 为其 QR 分解，$\mathbf{b} \in \mathbb{R}^m$。则最小二乘解可通过解上三角方程组

$$R\hat{\mathbf{x}} = Q^T \mathbf{b}$$

得到。此方法数值稳定性优于直接求解正规方程。

**证明**:

由正规方程：$A^T A \hat{\mathbf{x}} = A^T \mathbf{b}$。代入 $A = QR$：

$$(QR)^T (QR) \hat{\mathbf{x}} = (QR)^T \mathbf{b} \Rightarrow R^T Q^T Q R \hat{\mathbf{x}} = R^T Q^T \mathbf{b}.$$

因 $Q^T Q = I_n$：

$$R^T R \hat{\mathbf{x}} = R^T Q^T \mathbf{b}.$$

因 $R$ 可逆（对角元均为正），$R^T$ 亦可逆。左乘 $(R^T)^{-1}$：

$$R \hat{\mathbf{x}} = Q^T \mathbf{b}.$$

这正是待证结论。$\square$

> **证明要点提示**: QR 方法避免直接计算 $A^T A$，而 $A^T A$ 的条件数是 $A$ 条件数的平方。数值上，QR 分解法更加稳定。

---

## 三、典型例题

### 例题 11.1（直线拟合）

**题目**: 给定数据点 $(1, 2)$, $(2, 3)$, $(3, 5)$，求最佳拟合直线 $y = C + Dx$ 的最小二乘参数 $C, D$。

**解答**:

将三个点代入 $y = C + Dx$：

$$\begin{cases} C + D = 2 \\ C + 2D = 3 \\ C + 3D = 5 \end{cases}$$

写成矩阵形式 $A\mathbf{x} = \mathbf{b}$：

$$A = \begin{pmatrix} 1 & 1 \\ 1 & 2 \\ 1 & 3 \end{pmatrix}, \quad \mathbf{x} = \begin{pmatrix} C \\ D \end{pmatrix}, \quad \mathbf{b} = \begin{pmatrix} 2 \\ 3 \\ 5 \end{pmatrix}.$$

**方法 1：正规方程**

$$A^T A = \begin{pmatrix} 1 & 1 & 1 \\ 1 & 2 & 3 \end{pmatrix} \begin{pmatrix} 1 & 1 \\ 1 & 2 \\ 1 & 3 \end{pmatrix} = \begin{pmatrix} 3 & 6 \\ 6 & 14 \end{pmatrix}.$$

$$A^T \mathbf{b} = \begin{pmatrix} 1 & 1 & 1 \\ 1 & 2 & 3 \end{pmatrix} \begin{pmatrix} 2 \\ 3 \\ 5 \end{pmatrix} = \begin{pmatrix} 10 \\ 23 \end{pmatrix}.$$

解

$$\begin{pmatrix} 3 & 6 \\ 6 & 14 \end{pmatrix} \begin{pmatrix} C \\ D \end{pmatrix} = \begin{pmatrix} 10 \\ 23 \end{pmatrix}.$$

由第一式：$3C + 6D = 10 \Rightarrow C = \frac{10 - 6D}{3}$。

代入第二式：$6 \cdot \frac{10 - 6D}{3} + 14D = 23 \Rightarrow 20 - 12D + 14D = 23 \Rightarrow 2D = 3 \Rightarrow D = \frac{3}{2}$。

$C = \frac{10 - 9}{3} = \frac{1}{3}$。

**最佳拟合直线**: $y = \frac{1}{3} + \frac{3}{2}x$。

**验证误差**: $\hat{\mathbf{b}} = A\hat{\mathbf{x}} = (\frac{11}{6}, \frac{10}{3}, \frac{29}{6})^T \approx (1.83, 3.33, 4.83)^T$。

实际值 $\mathbf{b} = (2, 3, 5)^T$。误差 $\mathbf{e} = \mathbf{b} - \hat{\mathbf{b}} = (\frac{1}{6}, -\frac{1}{3}, \frac{1}{6})^T$。

验证 $A^T \mathbf{e} = \mathbf{0}$：$\frac{1}{6} - \frac{1}{3} + \frac{1}{6} = 0$，$\frac{1}{6} - \frac{2}{3} + \frac{3}{6} = 0$。正确。

**关键步骤解析**: 直线拟合的关键是正确构造设计矩阵 $A$——第一列全为 1（对应截距 $C$），第二列为 $x$ 坐标（对应斜率 $D$）。

---

### 例题 11.2（Gram-Schmidt 正交化）

**题目**: 对矩阵 $A = \begin{pmatrix} 1 & 1 & 0 \\ 1 & 0 & 1 \\ 0 & 1 & 1 \end{pmatrix}$ 的列向量执行 Gram-Schmidt 正交化，求 QR 分解。

**解答**:

设 $A = [\mathbf{a}_1 \; \mathbf{a}_2 \; \mathbf{a}_3]$，其中 $\mathbf{a}_1 = (1,1,0)^T$，$\mathbf{a}_2 = (1,0,1)^T$，$\mathbf{a}_3 = (0,1,1)^T$。

**步骤 1**: $\mathbf{v}_1 = \mathbf{a}_1 = (1,1,0)^T$。

$r_{11} = \|\mathbf{v}_1\| = \sqrt{1^2 + 1^2 + 0^2} = \sqrt{2}$。

$\mathbf{q}_1 = \frac{1}{\sqrt{2}}(1,1,0)^T = (\frac{1}{\sqrt{2}}, \frac{1}{\sqrt{2}}, 0)^T$。

**步骤 2**: $r_{12} = \mathbf{q}_1^T \mathbf{a}_2 = \frac{1}{\sqrt{2}} \cdot 1 + \frac{1}{\sqrt{2}} \cdot 0 + 0 \cdot 1 = \frac{1}{\sqrt{2}}$。

$\mathbf{v}_2 = \mathbf{a}_2 - r_{12}\mathbf{q}_1 = (1,0,1)^T - \frac{1}{\sqrt{2}}(\frac{1}{\sqrt{2}}, \frac{1}{\sqrt{2}}, 0)^T = (1,0,1)^T - (\frac{1}{2}, \frac{1}{2}, 0)^T = (\frac{1}{2}, -\frac{1}{2}, 1)^T$。

$r_{22} = \|\mathbf{v}_2\| = \sqrt{\frac{1}{4} + \frac{1}{4} + 1} = \sqrt{\frac{3}{2}} = \frac{\sqrt{6}}{2}$。

$\mathbf{q}_2 = \frac{1}{\sqrt{3/2}}(\frac{1}{2}, -\frac{1}{2}, 1)^T = \sqrt{\frac{2}{3}}(\frac{1}{2}, -\frac{1}{2}, 1)^T = (\frac{1}{\sqrt{6}}, -\frac{1}{\sqrt{6}}, \frac{2}{\sqrt{6}})^T$。

**步骤 3**: $r_{13} = \mathbf{q}_1^T \mathbf{a}_3 = \frac{1}{\sqrt{2}} \cdot 0 + \frac{1}{\sqrt{2}} \cdot 1 + 0 \cdot 1 = \frac{1}{\sqrt{2}}$。

$r_{23} = \mathbf{q}_2^T \mathbf{a}_3 = \frac{1}{\sqrt{6}} \cdot 0 + (-\frac{1}{\sqrt{6}}) \cdot 1 + \frac{2}{\sqrt{6}} \cdot 1 = \frac{1}{\sqrt{6}}$。

$\mathbf{v}_3 = \mathbf{a}_3 - r_{13}\mathbf{q}_1 - r_{23}\mathbf{q}_2$

$= (0,1,1)^T - \frac{1}{\sqrt{2}}(\frac{1}{\sqrt{2}}, \frac{1}{\sqrt{2}}, 0)^T - \frac{1}{\sqrt{6}}(\frac{1}{\sqrt{6}}, -\frac{1}{\sqrt{6}}, \frac{2}{\sqrt{6}})^T$

$= (0,1,1)^T - (\frac{1}{2}, \frac{1}{2}, 0)^T - (\frac{1}{6}, -\frac{1}{6}, \frac{2}{6})^T$

$= (-\frac{2}{3}, \frac{2}{3}, \frac{2}{3})^T$。

$r_{33} = \|\mathbf{v}_3\| = \sqrt{\frac{4}{9} + \frac{4}{9} + \frac{4}{9}} = \sqrt{\frac{12}{9}} = \frac{2}{\sqrt{3}}$。

$\mathbf{q}_3 = \frac{\sqrt{3}}{2}(-\frac{2}{3}, \frac{2}{3}, \frac{2}{3})^T = (-\frac{1}{\sqrt{3}}, \frac{1}{\sqrt{3}}, \frac{1}{\sqrt{3}})^T$。

**结果**:

$$Q = \begin{pmatrix} \frac{1}{\sqrt{2}} & \frac{1}{\sqrt{6}} & -\frac{1}{\sqrt{3}} \\ \frac{1}{\sqrt{2}} & -\frac{1}{\sqrt{6}} & \frac{1}{\sqrt{3}} \\ 0 & \frac{2}{\sqrt{6}} & \frac{1}{\sqrt{3}} \end{pmatrix}, \quad R = \begin{pmatrix} \sqrt{2} & \frac{1}{\sqrt{2}} & \frac{1}{\sqrt{2}} \\ 0 & \frac{\sqrt{6}}{2} & \frac{1}{\sqrt{6}} \\ 0 & 0 & \frac{2}{\sqrt{3}} \end{pmatrix}.$$

验证 $Q^T Q = I$ 及 $A = QR$（留作练习）。

**关键步骤解析**: Gram-Schmidt 的每一步都要确保减去所有先前方向的投影。计算 $r_{ij} = \mathbf{q}_i^T \mathbf{a}_j$ 时，注意是用原始向量 $\mathbf{a}_j$ 而非中间向量，这保证了 $R$ 的上三角结构。

---

## 四、常见误区与纠正

### 误区 11.1: "$A^T A$ 总是可逆的"

**错误观点**: 许多学生在使用最小二乘法时，不加检验就直接写 $(A^T A)^{-1}$，认为 $A^T A$ 总是可逆的。

**反例**: 取 $A = \begin{pmatrix} 1 & 2 \\ 2 & 4 \end{pmatrix}$，则 $A$ 的两列线性相关（第二列是第一列的 2 倍）。计算

$$A^T A = \begin{pmatrix} 1 & 2 \\ 2 & 4 \end{pmatrix} \begin{pmatrix} 1 & 2 \\ 2 & 4 \end{pmatrix} = \begin{pmatrix} 5 & 10 \\ 10 & 20 \end{pmatrix}.$$

$\det(A^T A) = 5 \times 20 - 10 \times 10 = 0$，故 $A^T A$ 不可逆。

**正确理解**: $A^T A$ 可逆当且仅当 $A$ 列满秩（$\operatorname{rank}(A) = n$）。当 $A$ 列不满秩时，最小二乘解不唯一，但最佳逼近 $\hat{\mathbf{b}}$ 仍然唯一。此时可用广义逆或选取最小范数解。

> **为什么错**: $A^T A$ 是 $n \times n$ 矩阵，其秩为 $\operatorname{rank}(A^T A) = \operatorname{rank}(A) \leq \min(m, n)$。当 $n > m$ 或 $A$ 列相关时，$\operatorname{rank}(A) < n$，$A^T A$ 必不可逆。混淆了"$A^T A$ 半正定"（总是成立）与"$A^T A$ 正定"（需要列满秩条件）。

---

## 五、思想方法提炼

**本章核心思想**:

1. **正交投影是最优逼近**: 最小二乘法的几何本质是将 $\mathbf{b}$ 投影到 $C(A)$ 上。正交性条件（误差垂直于列空间）是推导一切的核心。

2. **Gram-Schmidt = 构造正交基**: 正交基简化计算（$Q^T Q = I$ 消去交叉项），Gram-Schmidt 提供了从任意基构造标准正交基的系统性方法。

3. **数值稳定性意识**: 正规方程 $A^T A$ 的条件数平方增长，QR 分解是更稳定的数值方法。理论推导与数值实现需要兼顾。

**与前后章节的联系**:

- **前承**: Ch.10 的正交性与投影为本章提供了几何语言；Ch.7-8 的求解线性方程组是正规方程的基础。
- **后续**: Ch.12 的行列式为正定性的判定提供工具；Ch.13-14 的特征值理论将深化对 $A^T A$ 的理解（其特征值为 $A$ 的奇异值的平方）；Ch.15 的 SVD 是 QR 分解向一般矩阵的自然推广。

---

## 六、习题

### 习题 11.1

**题目**: 求数据点 $(0, 1)$, $(1, 3)$, $(2, 4)$, $(3, 4)$ 的最小二乘拟合直线 $y = C + Dx$。

**解答**:

$$A = \begin{pmatrix} 1 & 0 \\ 1 & 1 \\ 1 & 2 \\ 1 & 3 \end{pmatrix}, \quad \mathbf{b} = \begin{pmatrix} 1 \\ 3 \\ 4 \\ 4 \end{pmatrix}.$$

$$A^T A = \begin{pmatrix} 4 & 6 \\ 6 & 14 \end{pmatrix}, \quad A^T \mathbf{b} = \begin{pmatrix} 12 \\ 23 \end{pmatrix}.$$

解 $\begin{pmatrix} 4 & 6 \\ 6 & 14 \end{pmatrix} \begin{pmatrix} C \\ D \end{pmatrix} = \begin{pmatrix} 12 \\ 23 \end{pmatrix}$：

由 Cramer 法则：$\det(A^T A) = 56 - 36 = 20$。

$C = \frac{12 \times 14 - 6 \times 23}{20} = \frac{168 - 138}{20} = \frac{30}{20} = \frac{3}{2}$。

$D = \frac{4 \times 23 - 6 \times 12}{20} = \frac{92 - 72}{20} = \frac{20}{20} = 1$。

**答案**: $y = \frac{3}{2} + x$。$\square$

---

### 习题 11.2

**题目**: 求通过最小二乘法拟合抛物线 $y = C + Dx + Ex^2$ 到数据点 $(-1, 2)$, $(0, 0)$, $(1, 1)$, $(2, 3)$。

**解答**:

$$A = \begin{pmatrix} 1 & -1 & 1 \\ 1 & 0 & 0 \\ 1 & 1 & 1 \\ 1 & 2 & 4 \end{pmatrix}, \quad \mathbf{b} = \begin{pmatrix} 2 \\ 0 \\ 1 \\ 3 \end{pmatrix}.$$

$$A^T A = \begin{pmatrix} 4 & 2 & 6 \\ 2 & 6 & 8 \\ 6 & 8 & 18 \end{pmatrix}, \quad A^T \mathbf{b} = \begin{pmatrix} 6 \\ 5 \\ 15 \end{pmatrix}.$$

解方程组：

$4C + 2D + 6E = 6 \Rightarrow 2C + D + 3E = 3$ ... (1)

$2C + 6D + 8E = 5$ ... (2)

$6C + 8D + 18E = 15 \Rightarrow 3C + 4D + 9E = 7.5$ ... (3)

(2) - (1): $5D + 5E = 2 \Rightarrow D + E = 0.4$ ... (4)

(3) - 1.5(1): $3C + 4D + 9E - (3C + 1.5D + 4.5E) = 7.5 - 4.5 = 3$

$2.5D + 4.5E = 3$ ... (5)

由 (4): $D = 0.4 - E$。代入 (5): $2.5(0.4 - E) + 4.5E = 3 \Rightarrow 1 - 2.5E + 4.5E = 3 \Rightarrow 2E = 2 \Rightarrow E = 1$。

$D = 0.4 - 1 = -0.6 = -\frac{3}{5}$。

由 (1): $2C - 0.6 + 3 = 3 \Rightarrow 2C = 0.6 \Rightarrow C = 0.3 = \frac{3}{10}$。

**答案**: $y = \frac{3}{10} - \frac{3}{5}x + x^2$。$\square$

---

### 习题 11.3

**题目**: 设 $A = \begin{pmatrix} 1 & 1 \\ 1 & 2 \\ 1 & 3 \end{pmatrix}$，$\mathbf{b} = \begin{pmatrix} 1 \\ 2 \\ 2 \end{pmatrix}$。用 QR 分解求最小二乘解。

**解答**:

对 $A$ 的列做 Gram-Schmidt：

$\mathbf{a}_1 = (1,1,1)^T$，$r_{11} = \sqrt{3}$，$\mathbf{q}_1 = \frac{1}{\sqrt{3}}(1,1,1)^T$。

$r_{12} = \mathbf{q}_1^T \mathbf{a}_2 = \frac{1}{\sqrt{3}}(1 + 2 + 3) = \frac{6}{\sqrt{3}} = 2\sqrt{3}$。

$\mathbf{v}_2 = (1,2,3)^T - 2\sqrt{3} \cdot \frac{1}{\sqrt{3}}(1,1,1)^T = (1,2,3)^T - (2,2,2)^T = (-1, 0, 1)^T$。

$r_{22} = \sqrt{2}$，$\mathbf{q}_2 = \frac{1}{\sqrt{2}}(-1, 0, 1)^T$。

$$Q = \begin{pmatrix} \frac{1}{\sqrt{3}} & -\frac{1}{\sqrt{2}} \\ \frac{1}{\sqrt{3}} & 0 \\ \frac{1}{\sqrt{3}} & \frac{1}{\sqrt{2}} \end{pmatrix}, \quad R = \begin{pmatrix} \sqrt{3} & 2\sqrt{3} \\ 0 & \sqrt{2} \end{pmatrix}.$$

解 $R\hat{\mathbf{x}} = Q^T \mathbf{b}$：

$$Q^T \mathbf{b} = \begin{pmatrix} \frac{1}{\sqrt{3}} & \frac{1}{\sqrt{3}} & \frac{1}{\sqrt{3}} \\ -\frac{1}{\sqrt{2}} & 0 & \frac{1}{\sqrt{2}} \end{pmatrix} \begin{pmatrix} 1 \\ 2 \\ 2 \end{pmatrix} = \begin{pmatrix} \frac{5}{\sqrt{3}} \\ \frac{1}{\sqrt{2}} \end{pmatrix}.$$

回代：$\sqrt{2} D = \frac{1}{\sqrt{2}} \Rightarrow D = \frac{1}{2}$。

$\sqrt{3} C + 2\sqrt{3} \cdot \frac{1}{2} = \frac{5}{\sqrt{3}} \Rightarrow \sqrt{3} C = \frac{5}{\sqrt{3}} - \sqrt{3} = \frac{5-3}{\sqrt{3}} = \frac{2}{\sqrt{3}} \Rightarrow C = \frac{2}{3}$。

**答案**: $\hat{\mathbf{x}} = (\frac{2}{3}, \frac{1}{2})^T$。$\square$

---

### 习题 11.4

**题目**: 证明：若 $P$ 是到子空间 $V$ 的正交投影矩阵，则 $I - P$ 是到 $V^\perp$ 的正交投影矩阵。

**解答**:

验证 $I-P$ 满足投影矩阵的三个条件：

1. **幂等性**: $(I-P)^2 = I - 2P + P^2 = I - 2P + P = I - P$（因 $P^2 = P$）。

2. **对称性**: $(I-P)^T = I - P^T = I - P$（因 $P^T = P$）。

3. **值域为 $V^\perp$**: 对任意 $\mathbf{v} \in V$，$P\mathbf{v} = \mathbf{v}$，故 $(I-P)\mathbf{v} = \mathbf{0}$，即 $V \subseteq N(I-P)$。反之，若 $(I-P)\mathbf{x} = \mathbf{0}$，则 $\mathbf{x} = P\mathbf{x} \in V$，故 $N(I-P) = V$，从而 $C(I-P) = N(I-P)^\perp = V^\perp$。

因此 $I-P$ 是到 $V^\perp$ 的正交投影矩阵。$\square$

---

### 习题 11.5

**题目**: 设 $Q \in \mathbb{R}^{n \times n}$ 为正交矩阵。证明：
(1) $\|Q\mathbf{x}\| = \|\mathbf{x}\|$ 对所有 $\mathbf{x} \in \mathbb{R}^n$ 成立；
(2) 若 $\lambda$ 是 $Q$ 的特征值，则 $|\lambda| = 1$。

**解答**:

**(1)** $\|Q\mathbf{x}\|^2 = (Q\mathbf{x})^T(Q\mathbf{x}) = \mathbf{x}^T Q^T Q \mathbf{x} = \mathbf{x}^T \mathbf{x} = \|\mathbf{x}\|^2$。

**(2)** 设 $Q\mathbf{v} = \lambda \mathbf{v}$，$\mathbf{v} \neq \mathbf{0}$。由 (1)：$\|Q\mathbf{v}\| = \|\mathbf{v}\|$，即 $\|\lambda \mathbf{v}\| = |\lambda| \|\mathbf{v}\| = \|\mathbf{v}\|$。因 $\|\mathbf{v}\| \neq 0$，故 $|\lambda| = 1$。$\square$

---

### 习题 11.6

**题目**: 设 $A \in \mathbb{R}^{m \times n}$ 列满秩。证明投影矩阵 $P = A(A^T A)^{-1}A^T$ 满足 $\operatorname{rank}(P) = n$，$\operatorname{trace}(P) = n$。

**解答**:

$\operatorname{rank}(P) = \dim C(P) = \dim C(A) = \operatorname{rank}(A) = n$。

对迹：$P$ 是幂等矩阵（$P^2 = P$），其特征值只能是 0 或 1。$\operatorname{rank}(P) = n$ 意味着特征值 1 的几何重数为 $n$。因 $P$ 对称，可对角化，故特征值 1 的代数重数也为 $n$。

因此 $\operatorname{trace}(P) = $（特征值 1 的个数）$= n$。

另法：$\operatorname{trace}(P) = \operatorname{trace}(A(A^T A)^{-1}A^T) = \operatorname{trace}(A^T A (A^T A)^{-1}) = \operatorname{trace}(I_n) = n$。$\square$

---

### 习题 11.7

**题目**: 用 Gram-Schmidt 求 $A = \begin{pmatrix} 3 & 0 \\ 4 & 5 \end{pmatrix}$ 的 QR 分解。

**解答**:

$\mathbf{a}_1 = (3,4)^T$，$r_{11} = 5$，$\mathbf{q}_1 = (\frac{3}{5}, \frac{4}{5})^T$。

$r_{12} = \mathbf{q}_1^T \mathbf{a}_2 = \frac{3}{5} \cdot 0 + \frac{4}{5} \cdot 5 = 4$。

$\mathbf{v}_2 = (0,5)^T - 4(\frac{3}{5}, \frac{4}{5})^T = (0,5)^T - (\frac{12}{5}, \frac{16}{5})^T = (-\frac{12}{5}, \frac{9}{5})^T$。

$r_{22} = \sqrt{\frac{144}{25} + \frac{81}{25}} = \sqrt{\frac{225}{25}} = 3$。

$\mathbf{q}_2 = \frac{1}{3}(-\frac{12}{5}, \frac{9}{5})^T = (-\frac{4}{5}, \frac{3}{5})^T$。

$$Q = \begin{pmatrix} \frac{3}{5} & -\frac{4}{5} \\ \frac{4}{5} & \frac{3}{5} \end{pmatrix}, \quad R = \begin{pmatrix} 5 & 4 \\ 0 & 3 \end{pmatrix}.$$ $\square$

---

### 习题 11.8

**题目**: 证明 $C(A^T A) = C(A^T)$，从而说明正规方程 $A^T A \mathbf{x} = A^T \mathbf{b}$ 总有解。

**解答**:

首先 $C(A^T A) \subseteq C(A^T)$ 显然，因为 $A^T A \mathbf{x} = A^T(A\mathbf{x})$。

下证 $C(A^T) \subseteq C(A^T A)$，等价于证 $N(A^T A) = N(A)$（由正交补关系：$C(A^T) = N(A)^\perp$，$C(A^T A) = N(A^T A)^\perp$）。

- 若 $\mathbf{x} \in N(A)$，则 $A\mathbf{x} = \mathbf{0}$，故 $A^T A \mathbf{x} = \mathbf{0}$，$\mathbf{x} \in N(A^T A)$。所以 $N(A) \subseteq N(A^T A)$。

- 若 $\mathbf{x} \in N(A^T A)$，则 $A^T A \mathbf{x} = \mathbf{0}$。左乘 $\mathbf{x}^T$：$\mathbf{x}^T A^T A \mathbf{x} = \|A\mathbf{x}\|^2 = 0$，故 $A\mathbf{x} = \mathbf{0}$，$\mathbf{x} \in N(A)$。所以 $N(A^T A) \subseteq N(A)$。

因此 $N(A) = N(A^T A)$，$\dim N(A) = \dim N(A^T A)$。

由秩-零化度定理，$\operatorname{rank}(A^T) = n - \dim N(A) = n - \dim N(A^T A) = \operatorname{rank}(A^T A)$。

又 $C(A^T A) \subseteq C(A^T)$ 且维数相同，故 $C(A^T A) = C(A^T)$。

因此 $A^T \mathbf{b} \in C(A^T) = C(A^T A)$，正规方程总有解。$\square$

---

### 习题 11.9

**题目**: 设 $A \in \mathbb{R}^{m \times n}$，$m > n$，$\operatorname{rank}(A) = n$。证明最小二乘解的唯一性：若 $\hat{\mathbf{x}}_1, \hat{\mathbf{x}}_2$ 都是最小二乘解，则 $\hat{\mathbf{x}}_1 = \hat{\mathbf{x}}_2$。

**解答**:

由定理 11.1，最小二乘解必满足正规方程 $A^T A \mathbf{x} = A^T \mathbf{b}$。

因 $A$ 列满秩，$A^T A$ 可逆（定理 11.2），故正规方程有唯一解 $(A^T A)^{-1} A^T \mathbf{b}$。

因此 $\hat{\mathbf{x}}_1 = \hat{\mathbf{x}}_2 = (A^T A)^{-1} A^T \mathbf{b}$。$\square$

---

### 习题 11.10

**题目**: 设 $A = QR$ 为 QR 分解，$Q$ 为 $m \times n$ 列正交矩阵，$R$ 为 $n \times n$ 上三角可逆矩阵。证明：$\|A\mathbf{x}\| = \|R\mathbf{x}\|$ 对所有 $\mathbf{x} \in \mathbb{R}^n$ 成立。

**解答**:

$$\|A\mathbf{x}\|^2 = (A\mathbf{x})^T(A\mathbf{x}) = \mathbf{x}^T A^T A \mathbf{x} = \mathbf{x}^T (QR)^T(QR) \mathbf{x} = \mathbf{x}^T R^T Q^T Q R \mathbf{x} = \mathbf{x}^T R^T R \mathbf{x} = (R\mathbf{x})^T(R\mathbf{x}) = \|R\mathbf{x}\|^2.$$

因此 $\|A\mathbf{x}\| = \|R\mathbf{x}\|$。$\square$

---

### 习题 11.11

**题目**: 设 $A = \begin{pmatrix} 1 & 0 \\ 1 & 1 \\ 1 & 2 \end{pmatrix}$，$\mathbf{b} = \begin{pmatrix} 3 \\ 3 \\ 5 \end{pmatrix}$。
(1) 求 $\mathbf{b}$ 在 $C(A)$ 上的投影 $\\hat{\mathbf{b}}$；
(2) 求误差向量 $\mathbf{e}$ 并验证其与 $C(A)$ 正交；
(3) 求投影矩阵 $P$。

**解答**:

**(1)** $A^T A = \begin{pmatrix} 3 & 3 \\ 3 & 5 \end{pmatrix}$，$\det = 15 - 9 = 6$。

$(A^T A)^{-1} = \frac{1}{6}\begin{pmatrix} 5 & -3 \\ -3 & 3 \end{pmatrix}$。

$A^T \mathbf{b} = \begin{pmatrix} 11 \\ 13 \end{pmatrix}$。

$\hat{\mathbf{x}} = (A^T A)^{-1} A^T \mathbf{b} = \frac{1}{6}\begin{pmatrix} 5 & -3 \\ -3 & 3 \end{pmatrix}\begin{pmatrix} 11 \\ 13 \end{pmatrix} = \frac{1}{6}\begin{pmatrix} 55-39 \\ -33+39 \end{pmatrix} = \begin{pmatrix} \frac{16}{6} \\ 1 \end{pmatrix} = \begin{pmatrix} \frac{8}{3} \\ 1 \end{pmatrix}$。

$\hat{\mathbf{b}} = A\hat{\mathbf{x}} = \begin{pmatrix} 1 & 0 \\ 1 & 1 \\ 1 & 2 \end{pmatrix}\begin{pmatrix} \frac{8}{3} \\ 1 \end{pmatrix} = \begin{pmatrix} \frac{8}{3} \\ \frac{11}{3} \\ \frac{14}{3} \end{pmatrix}$。

**(2)** $\mathbf{e} = \mathbf{b} - \hat{\mathbf{b}} = \begin{pmatrix} 3 - \frac{8}{3} \\ 3 - \frac{11}{3} \\ 5 - \frac{14}{3} \end{pmatrix} = \begin{pmatrix} \frac{1}{3} \\ -\frac{2}{3} \\ \frac{1}{3} \end{pmatrix}$。

验证：$A^T \mathbf{e} = \begin{pmatrix} 1 & 1 & 1 \\ 0 & 1 & 2 \end{pmatrix}\begin{pmatrix} \frac{1}{3} \\ -\frac{2}{3} \\ \frac{1}{3} \end{pmatrix} = \begin{pmatrix} \frac{1-2+1}{3} \\ \frac{0-2+2}{3} \end{pmatrix} = \begin{pmatrix} 0 \\ 0 \end{pmatrix}$。

**(3)** $P = A(A^T A)^{-1}A^T = \begin{pmatrix} 1 & 0 \\ 1 & 1 \\ 1 & 2 \end{pmatrix} \cdot \frac{1}{6}\begin{pmatrix} 5 & -3 \\ -3 & 3 \end{pmatrix} \cdot \begin{pmatrix} 1 & 1 & 1 \\ 0 & 1 & 2 \end{pmatrix}$

$= \frac{1}{6}\begin{pmatrix} 5 & -3 \\ 2 & 0 \\ -1 & 3 \end{pmatrix}\begin{pmatrix} 1 & 1 & 1 \\ 0 & 1 & 2 \end{pmatrix} = \frac{1}{6}\begin{pmatrix} 5 & 2 & -1 \\ 2 & 2 & 2 \\ -1 & 2 & 5 \end{pmatrix}$。$\square$

---

### 习题 11.12

**题目**: （平面拟合）求最佳拟合平面 $z = C + Dx + Ey$ 到数据点 $(1,0,1)$, $(0,1,2)$, $(1,1,3)$, $(2,0,2)$。

**解答**:

$$A = \begin{pmatrix} 1 & 1 & 0 \\ 1 & 0 & 1 \\ 1 & 1 & 1 \\ 1 & 2 & 0 \end{pmatrix}, \quad \mathbf{b} = \begin{pmatrix} 1 \\ 2 \\ 3 \\ 2 \end{pmatrix}.$$

$$A^T A = \begin{pmatrix} 4 & 4 & 2 \\ 4 & 6 & 1 \\ 2 & 1 & 2 \end{pmatrix}, \quad A^T \mathbf{b} = \begin{pmatrix} 8 \\ 8 \\ 5 \end{pmatrix}.$$

解方程组：

$4C + 4D + 2E = 8 \Rightarrow 2C + 2D + E = 4$ ... (1)

$4C + 6D + E = 8$ ... (2)

$2C + D + 2E = 5$ ... (3)

(2) - (1): $2D = 4 \Rightarrow D = 2$？等等，重新：(2) - (1) = $2C + 4D + E - (2C + 2D + E) = 8 - 4$？不对，应该用原始式。

(2) - (1)*2（不对，直接用原始）：(2)-(1): $(4C+6D+E) - (4C+4D+2E) = 8-8 = 0 \Rightarrow 2D - E = 0 \Rightarrow E = 2D$ ... (4)

(3)*2 - (1): $(4C+2D+4E) - (4C+4D+2E) = 10 - 8 = 2 \Rightarrow -2D + 2E = 2 \Rightarrow -D + E = 1$ ... (5)

由 (4)(5): $-D + 2D = 1 \Rightarrow D = 1$，$E = 2$。

代入 (1): $2C + 2 + 2 = 4 \Rightarrow C = 0$。

**答案**: $z = x + 2y$。$\square$

---

## Lean4 形式化对照

### Gram-Schmidt 正交化

Mathlib4 提供了 `gramSchmidt` 函数，它接收一个内积空间中的向量族，返回一组正交向量。这正是定义 11.6 的算法实现：对每个新向量，减去它在前面所有已正交化方向上的投影分量。

```lean4
import Mathlib

open InnerProductSpace

-- Gram-Schmidt 正交化过程
-- 输入：内积空间 E 中的向量族 f : ι → E
-- 输出：正交向量族 gramSchmidt ℝ f : ι → E
example (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι]
    (f : ι → E) (i : ι) :
    gramSchmidt ℝ f i = f i - ∑ j ∈ Finset.Iio i, orthogonalProjection (𝕜 := ℝ)
      (span ℝ (gramSchmidt ℝ f '' Finset.Iio i)) (f i) := by
  rw [gramSchmidt_def]
```

### QR 分解与正交矩阵

QR 分解将列满秩矩阵 $A$ 分解为列正交矩阵 $Q$ 与上三角矩阵 $R$ 的乘积。正交矩阵在 Mathlib4 中由 $Q^T Q = I$ 刻画，对应 `Matrix` 的矩阵乘法验证。

```lean4
open Matrix

-- 定义 11.4：正交矩阵（QᵀQ = I）
def IsOrthogonalMatrix {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  Qᵀ * Q = 1

-- QR 分解的存在性（列满秩情形）
theorem qr_decomposition {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : LinearMap.ker A.mulVecLinear = ⊥) :
    ∃ Q : Matrix (Fin m) (Fin n) ℝ,
    ∃ R : Matrix (Fin n) (Fin n) ℝ,
      Qᵀ * Q = 1 ∧ (∀ i j : Fin n, j < i → R i j = 0) ∧ A = Q * R := by
  sorry -- 通过 Gram-Schmidt 构造性证明

-- 正交矩阵保持长度不变
theorem orthogonal_preserves_norm {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : IsOrthogonalMatrix Q) (x : Fin n → ℝ) :
    ‖Q.mulVec x‖ = ‖x‖ := by
  sorry -- ‖Qx‖² = (Qx)ᵀ(Qx) = xᵀQᵀQx = xᵀx = ‖x‖²
```

### 最小二乘解的唯一性

当 $A$ 列满秩时，最小二乘解唯一，且可由正规方程显式给出：$\hat{\mathbf{x}} = (A^T A)^{-1} A^T \mathbf{b}$。QR 分解求解法则通过 $R\hat{\mathbf{x}} = Q^T \mathbf{b}$ 避免直接计算 $(A^T A)^{-1}$。

```lean4
-- 定理 11.1：列满秩时最小二乘解唯一
theorem least_squares_unique {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (hA : LinearMap.ker A.mulVecLinear = ⊥) :
    ∃! x_hat : Fin n → ℝ, A.transpose * A * x_hat = A.transpose * b := by
  have hATA : Invertible (A.transpose * A) := by
    sorry -- AᵀA 正定故可逆
  use (A.transpose * A)⁻¹ * A.transpose * b
  constructor
  · -- 验证它是解
    simp [mul_assoc]
  · -- 验证唯一性
    intro y hy
    have : A.transpose * A * y = A.transpose * A * ((A.transpose * A)⁻¹ * A.transpose * b) := by
      rw [hy]
      simp [mul_assoc]
    sorry -- 由 AᵀA 可逆，消去得 y = (AᵀA)⁻¹Aᵀb

-- 定理 11.5：QR 分解求解最小二乘
-- 解上三角方程组 R x̂ = Qᵀb
theorem qr_solve_least_squares {m n : ℕ} (A Q R : Matrix (Fin m) (Fin n) ℝ)
    (hA : A = Q * R) (hQ : Qᵀ * Q = 1)
    (hR : ∀ i j : Fin n, j < i → R i j = 0)
    (b : Fin m → ℝ) :
    ∃! x_hat : Fin n → ℝ, R * x_hat = Qᵀ * b := by
  sorry -- R 可逆（对角元为正），故解唯一
```

---

**文档状态**: 🟡 草稿 | **审校轮次**: 0/2
**最后更新**: 2026-04-18
