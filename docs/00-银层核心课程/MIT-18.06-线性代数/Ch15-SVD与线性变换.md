---
title: "Ch.15 SVD与线性变换（SVD & Linear Transformations）"
level: "silver"
course: "MIT 18.06"
chapter: "15"
msc_primary: "15-01"
target_courses:
  - "MIT 18.06 Ch.15"
references:
  textbooks:
    - title: "Introduction to Linear Algebra"
      author: "Gilbert Strang"
      edition: "5th"
      chapters: "Chapter 7"
      pages: "363-390"
  lectures:
    - institution: "MIT"
      course_code: "18.06"
      lecture: "L29-L31"
      url: "https://ocw.mit.edu/courses/mathematics/18-06-linear-algebra-spring-2010/"
keywords:
  - "SVD"
  - "singular value"
  - "pseudo-inverse"
  - "PCA"
  - "linear transformation"
  - "change of basis"
status: "draft"
review_rounds: 0
created_at: "2026-04-18"
---

# Ch.15 SVD与线性变换（SVD & Linear Transformations）

> **课程**: MIT 18.06 Linear Algebra | **章节**: Chapter 15
> **学习目标**: 掌握奇异值分解的存在性、构造与几何意义，理解伪逆的最小二乘最优性，建立线性变换在不同基下矩阵表示的完整理论，以SVD为统领回顾全课程核心思想。

---

## 一、核心定义

### 定义 15.1（奇异值与奇异向量）

**严格陈述**: 设 $A \in \mathbb{R}^{m \times n}$，$r = \operatorname{rank}(A)$。对称半正定矩阵 $A^T A \in \mathbb{R}^{n \times n}$ 的特征值为 $\sigma_1^2 \geq \sigma_2^2 \geq \cdots \geq \sigma_r^2 > 0 = \sigma_{r+1}^2 = \cdots = \sigma_n^2$。

称 $\sigma_1, \ldots, \sigma_r$ 为 $A$ 的**奇异值**（singular values）。$\sigma_i = \sqrt{\lambda_i(A^T A)} = \sqrt{\lambda_i(AA^T)}$。

$A^T A$ 对应于 $\sigma_i^2$ 的单位特征向量 $\mathbf{v}_i \in \mathbb{R}^n$ 称为**右奇异向量**（right singular vectors）；$AA^T$ 对应于 $\sigma_i^2$ 的单位特征向量 $\mathbf{u}_i \in \mathbb{R}^m$ 称为**左奇异向量**（left singular vectors）。

**条件说明**: 奇异值恒为非负实数，即使 $A$ 本身非对称、非方阵。这是与特征值的根本区别之一。

**直观解释**: 奇异值度量了 $A$ 在各"主轴方向"上的"伸缩强度"。最大奇异值 $\sigma_1$ 是 $A$ 的算子范数（$\max_{\|\mathbf{x}\|=1}\|A\mathbf{x}\|$），最小非零奇异值 $\sigma_r$ 度量了 $A$ 的"可逆程度"。

---

### 定义 15.2（奇异值分解 / SVD）

**严格陈述**: 设 $A \in \mathbb{R}^{m \times n}$，$r = \operatorname{rank}(A)$。$A$ 的**奇异值分解**（Singular Value Decomposition）为

$$A = U \Sigma V^T,$$

其中：

- $U \in \mathbb{R}^{m \times m}$ 为正交矩阵，列向量为左奇异向量 $\{\mathbf{u}_1, \ldots, \mathbf{u}_m\}$；
- $V \in \mathbb{R}^{n \times n}$ 为正交矩阵，列向量为右奇异向量 $\{\mathbf{v}_1, \ldots, \mathbf{v}_n\}$；
- $\Sigma \in \mathbb{R}^{m \times n}$ 为矩形对角矩阵，$\Sigma_{ii} = \sigma_i$（$i = 1, \ldots, r$），其余元素为 0。

**简化 SVD**（reduced SVD）: 取 $U_r = [\mathbf{u}_1 \; \cdots \; \mathbf{u}_r] \in \mathbb{R}^{m \times r}$，$V_r = [\mathbf{v}_1 \; \cdots \; \mathbf{v}_r] \in \mathbb{R}^{n \times r}$，$\Sigma_r = \operatorname{diag}(\sigma_1, \ldots, \sigma_r)$，则

$$A = U_r \Sigma_r V_r^T = \sum_{i=1}^r \sigma_i \mathbf{u}_i \mathbf{v}_i^T.$$

**直观解释**: SVD 将任意矩阵分解为"旋转-伸缩-旋转"。$V^T$ 在定义域中旋转到正交主轴，$\Sigma$ 沿各主轴伸缩，$U$ 在值域中再旋转。这是对任意线性变换最清晰的几何分解。

---

### 定义 15.3（伪逆 / Moore-Penrose 逆）

**严格陈述**: 设 $A \in \mathbb{R}^{m \times n}$ 有 SVD $A = U \Sigma V^T$。$A$ 的**伪逆**（pseudo-inverse，Moore-Penrose inverse）$A^+ \in \mathbb{R}^{n \times m}$ 定义为

$$A^+ = V \Sigma^+ U^T,$$

其中 $\Sigma^+ \in \mathbb{R}^{n \times m}$ 是将 $\Sigma$ 的非零对角元取倒数后转置：$(\Sigma^+)_{ii} = 1/\sigma_i$（$i = 1, \ldots, r$），其余为 0。

等价地，$A^+ = V_r \Sigma_r^{-1} U_r^T$。

**直观解释**: 伪逆是"尽可能逆"的矩阵。在非零奇异值方向，$A^+$ 执行逆伸缩；在零奇异值方向（$A$ 的零空间），$A^+$ 给出最小范数解。

---

### 定义 15.4（线性变换的矩阵表示）

**严格陈述**: 设 $T: V \to W$ 为向量空间之间的线性变换，$\mathcal{B} = \{\mathbf{v}_1, \ldots, \mathbf{v}_n\}$ 为 $V$ 的基，$\mathcal{C} = \{\mathbf{w}_1, \ldots, \mathbf{w}_m\}$ 为 $W$ 的基。$T$ 关于基 $\mathcal{B}, \mathcal{C}$ 的**矩阵表示** $[T]_{\mathcal{C} \leftarrow \mathcal{B}} \in \mathbb{R}^{m \times n}$ 的第 $j$ 列为 $[T(\mathbf{v}_j)]_{\mathcal{C}}$（$T(\mathbf{v}_j)$ 关于基 $\mathcal{C}$ 的坐标向量）。

即 $T(\mathbf{v}_j) = \sum_{i=1}^m a_{ij} \mathbf{w}_i$，$[T]_{\mathcal{C} \leftarrow \mathcal{B}} = (a_{ij})$。

**直观解释**: 矩阵表示是线性变换在特定坐标系下的"快照"。同一变换在不同基下有不同的矩阵表示（相似或更一般的等价关系），但它们代表相同的抽象变换。

---

### 定义 15.5（主成分分析 / PCA）

**严格陈述**: 给定数据矩阵 $X \in \mathbb{R}^{m \times n}$（$m$ 个样本，$n$ 个特征，通常已中心化），$X$ 的 SVD 为 $X = U \Sigma V^T$。$V$ 的列向量 $\mathbf{v}_1, \mathbf{v}_2, \ldots$ 称为**主成分方向**，$\sigma_1^2, \sigma_2^2, \ldots$ 为各方向的**方差贡献**。取前 $k$ 个主成分得到降维表示 $X_k = U_k \Sigma_k V_k^T$。

**直观解释**: PCA 寻找数据方差最大的方向（右奇异向量），并按重要性（奇异值平方）排序。低秩近似 $X_k$ 保留了数据的主要变异结构，是降维和去噪的核心工具。

---

## 二、核心定理与完整证明

### 定理 15.1（SVD 存在性）

**定理陈述**: 任意矩阵 $A \in \mathbb{R}^{m \times n}$ 都存在奇异值分解 $A = U \Sigma V^T$。

**证明**:

**步骤 1：构造右奇异向量**

$A^T A$ 为 $n \times n$ 对称半正定矩阵。由谱定理，存在正交矩阵 $V = [\mathbf{v}_1 \; \cdots \; \mathbf{v}_n]$ 使得

$$V^T (A^T A) V = \operatorname{diag}(\sigma_1^2, \ldots, \sigma_n^2),$$

其中 $\sigma_1 \geq \sigma_2 \geq \cdots \geq \sigma_r > 0 = \sigma_{r+1} = \cdots = \sigma_n$，$r = \operatorname{rank}(A^T A) = \operatorname{rank}(A)$。

即 $A^T A \mathbf{v}_i = \sigma_i^2 \mathbf{v}_i$，$\{\mathbf{v}_i\}$ 为标准正交基。

**步骤 2：构造左奇异向量**

对 $i = 1, \ldots, r$（$\sigma_i > 0$），定义

$$\mathbf{u}_i = \frac{1}{\sigma_i} A \mathbf{v}_i \in \mathbb{R}^m.$$

**验证 $\{\mathbf{u}_i\}$ 标准正交**:

$$\mathbf{u}_i^T \mathbf{u}_j = \frac{1}{\sigma_i \sigma_j} \mathbf{v}_i^T A^T A \mathbf{v}_j = \frac{\sigma_j^2}{\sigma_i \sigma_j} \mathbf{v}_i^T \mathbf{v}_j = \frac{\sigma_j}{\sigma_i} \delta_{ij} = \delta_{ij}.$$

因此 $\{\mathbf{u}_1, \ldots, \mathbf{u}_r\}$ 是 $\mathbb{R}^m$ 中标准正交组，可扩充为标准正交基 $\{\mathbf{u}_1, \ldots, \mathbf{u}_m\}$，构成正交矩阵 $U = [\mathbf{u}_1 \; \cdots \; \mathbf{u}_m]$。

**步骤 3：验证 $A = U \Sigma V^T$**

等价于验证 $AV = U \Sigma$，即 $A\mathbf{v}_j = U \Sigma \mathbf{e}_j$。

对 $j = 1, \ldots, r$：$U \Sigma \mathbf{e}_j = \sigma_j \mathbf{u}_j = \sigma_j \cdot \frac{1}{\sigma_j} A\mathbf{v}_j = A\mathbf{v}_j$。✓

对 $j = r+1, \ldots, n$：$\sigma_j = 0$，$U \Sigma \mathbf{e}_j = \mathbf{0}$。需证 $A\mathbf{v}_j = \mathbf{0}$。

因 $\sigma_j = 0$，$A^T A \mathbf{v}_j = \mathbf{0}$。故 $\|A\mathbf{v}_j\|^2 = \mathbf{v}_j^T A^T A \mathbf{v}_j = 0$，$A\mathbf{v}_j = \mathbf{0}$。✓

因此 $AV = U\Sigma$，$A = U\Sigma V^T$。$\square$

> **证明要点提示**: SVD 存在性的证明是谱定理的直接应用。关键观察是 $A^T A$ 的特征结构"一半决定"了 $A$ 的 SVD，另一半（左奇异向量）通过 $\mathbf{u}_i = A\mathbf{v}_i/\sigma_i$ 构造。

---

### 定理 15.2（伪逆的最小二乘最优性）

**定理陈述**: 设 $A \in \mathbb{R}^{m \times n}$，$\mathbf{b} \in \mathbb{R}^m$。则 $\mathbf{x}^+ = A^+ \mathbf{b}$ 满足：

1. **最小二乘**: $\|A\mathbf{x}^+ - \mathbf{b}\| \leq \|A\mathbf{x} - \mathbf{b}\|$ 对所有 $\mathbf{x} \in \mathbb{R}^n$；
2. **最小范数**: 在所有最小二乘解中，$\|\mathbf{x}^+\|$ 最小。

**证明**:

将 $\mathbf{b}$ 按左奇异向量分解：$\mathbf{b} = \sum_{i=1}^m (\mathbf{u}_i^T \mathbf{b}) \mathbf{u}_i$。

$$A\mathbf{x}^+ = A A^+ \mathbf{b} = U \Sigma V^T V \Sigma^+ U^T \mathbf{b} = U \Sigma \Sigma^+ U^T \mathbf{b}.$$

$\Sigma \Sigma^+$ 为 $m \times m$ 对角矩阵，前 $r$ 个对角元为 1，其余为 0。故 $U \Sigma \Sigma^+ U^T$ 是到 $C(A) = \operatorname{span}\{\mathbf{u}_1, \ldots, \mathbf{u}_r\}$ 的正交投影矩阵（由谱分解形式）。

因此 $A\mathbf{x}^+ = P_{C(A)} \mathbf{b}$，即 $\mathbf{b}$ 在 $C(A)$ 上的正交投影，这是最小二乘的最佳逼近（Ch.11）。

**最小范数**: 设 $\mathbf{x}$ 为任意最小二乘解。则 $A\mathbf{x} = A\mathbf{x}^+$，$A(\mathbf{x} - \mathbf{x}^+) = \mathbf{0}$，即 $\mathbf{x} - \mathbf{x}^+ \in N(A)$。

$$\|\mathbf{x}\|^2 = \|\mathbf{x}^+ + (\mathbf{x} - \mathbf{x}^+)\|^2 = \|\mathbf{x}^+\|^2 + \|\mathbf{x} - \mathbf{x}^+\|^2 + 2(\mathbf{x}^+)^T(\mathbf{x} - \mathbf{x}^+).$$

需证 $(\mathbf{x}^+)^T(\mathbf{x} - \mathbf{x}^+) = 0$。因 $\mathbf{x} - \mathbf{x}^+ \in N(A)$，而

$$\mathbf{x}^+ = A^+ \mathbf{b} = V \Sigma^+ U^T \mathbf{b} = \sum_{i=1}^r \frac{\mathbf{u}_i^T \mathbf{b}}{\sigma_i} \mathbf{v}_i \in \operatorname{span}\{\mathbf{v}_1, \ldots, \mathbf{v}_r\} = C(A^T) = N(A)^\perp.$$

故 $\mathbf{x}^+ \perp (\mathbf{x} - \mathbf{x}^+)$，交叉项为零，$\|\mathbf{x}\|^2 = \|\mathbf{x}^+\|^2 + \|\mathbf{x} - \mathbf{x}^+\|^2 \geq \|\mathbf{x}^+\|^2$。$\square$

---

### 定理 15.3（线性变换的基变换公式）

**定理陈述**: 设 $T: V \to W$，$\mathcal{B}, \mathcal{B}'$ 为 $V$ 的两组基，$\mathcal{C}, \mathcal{C}'$ 为 $W$ 的两组基。$P = [I]_{\mathcal{B}' \leftarrow \mathcal{B}}$ 为 $V$ 中从 $\mathcal{B}$ 到 $\mathcal{B}'$ 的过渡矩阵，$Q = [I]_{\mathcal{C}' \leftarrow \mathcal{C}}$ 为 $W$ 中从 $\mathcal{C}$ 到 $\mathcal{C}'$ 的过渡矩阵。则

$$[T]_{\mathcal{C}' \leftarrow \mathcal{B}'} = Q [T]_{\mathcal{C} \leftarrow \mathcal{B}} P^{-1}.$$

特别地，若 $T: V \to V$（自变换），$\mathcal{B}, \mathcal{B}'$ 为 $V$ 的两组基，$P = [I]_{\mathcal{B}' \leftarrow \mathcal{B}}$，则

$$[T]_{\mathcal{B}'} = P [T]_{\mathcal{B}} P^{-1}.$$

**证明**:

对任意 $\mathbf{v} \in V$，$[T(\mathbf{v})]_{\mathcal{C}'} = [T]_{\mathcal{C}' \leftarrow \mathcal{B}'} [\mathbf{v}]_{\mathcal{B}'}$。

同时 $[T(\mathbf{v})]_{\mathcal{C}'} = Q [T(\mathbf{v})]_{\mathcal{C}} = Q [T]_{\mathcal{C} \leftarrow \mathcal{B}} [\mathbf{v}]_{\mathcal{B}} = Q [T]_{\mathcal{C} \leftarrow \mathcal{B}} P^{-1} [\mathbf{v}]_{\mathcal{B}'}$。

因上式对所有 $\mathbf{v}$ 成立，$[T]_{\mathcal{C}' \leftarrow \mathcal{B}'} = Q [T]_{\mathcal{C} \leftarrow \mathcal{B}} P^{-1}$。

自变换情形：$W = V$，$\mathcal{C} = \mathcal{B}$，$\mathcal{C}' = \mathcal{B}'$，$Q = P$。$\square$

---

### 定理 15.4（低秩最优逼近 / Eckart-Young-Mirsky）

**定理陈述**: 设 $A \in \mathbb{R}^{m \times n}$，SVD 为 $A = \sum_{i=1}^r \sigma_i \mathbf{u}_i \mathbf{v}_i^T$。对 $1 \leq k < r$，定义秩 $k$ 截断

$$A_k = \sum_{i=1}^k \sigma_i \mathbf{u}_i \mathbf{v}_i^T.$$

则 $A_k$ 是所有秩不超过 $k$ 的矩阵中在谱范数（和 Frobenius 范数）意义下的最佳逼近：

$$\|A - A_k\|_2 = \sigma_{k+1}, \quad \|A - A_k\|_F = \sqrt{\sigma_{k+1}^2 + \cdots + \sigma_r^2}.$$

**证明**（概要）:

$A - A_k = \sum_{i=k+1}^r \sigma_i \mathbf{u}_i \mathbf{v}_i^T$ 的 SVD 显示其最大奇异值为 $\sigma_{k+1}$，故谱范数为 $\sigma_{k+1}$。

Frobenius 范数 = 所有奇异值平方和的平方根 = $\sqrt{\sigma_{k+1}^2 + \cdots + \sigma_r^2}$。

最优性证明需要更深入的扰动理论（Weyl 不等式），略。$\square$

---

## 三、典型例题

### 例题 15.1（具体矩阵的 SVD 分解）

**题目**: 求 $A = \begin{pmatrix} 3 & 0 \\ 0 & -2 \\ 0 & 0 \\ 0 & 0 \end{pmatrix}$ 的 SVD。

**解答**:

**步骤 1：求 $A^T A$ 的特征值与特征向量**

$$A^T A = \begin{pmatrix} 9 & 0 \\ 0 & 4 \end{pmatrix}.$$

特征值：$\lambda_1 = 9 = \sigma_1^2$（$\sigma_1 = 3$），$\lambda_2 = 4 = \sigma_2^2$（$\sigma_2 = 2$）。

特征向量：$\mathbf{v}_1 = (1, 0)^T$，$\mathbf{v}_2 = (0, 1)^T$。$V = \begin{pmatrix} 1 & 0 \\ 0 & 1 \end{pmatrix} = I_2$。

**步骤 2：求左奇异向量**

$\mathbf{u}_1 = \frac{1}{3} A \mathbf{v}_1 = \frac{1}{3}(3, 0, 0, 0)^T = (1, 0, 0, 0)^T$。

$\mathbf{u}_2 = \frac{1}{2} A \mathbf{v}_2 = \frac{1}{2}(0, -2, 0, 0)^T = (0, -1, 0, 0)^T$。

扩充为 $\mathbb{R}^4$ 的标准正交基：$\mathbf{u}_3 = (0, 0, 1, 0)^T$，$\mathbf{u}_4 = (0, 0, 0, 1)^T$。

$$U = \begin{pmatrix} 1 & 0 & 0 & 0 \\ 0 & -1 & 0 & 0 \\ 0 & 0 & 1 & 0 \\ 0 & 0 & 0 & 1 \end{pmatrix}.$$

**步骤 3：组装 SVD**

$$\Sigma = \begin{pmatrix} 3 & 0 \\ 0 & 2 \\ 0 & 0 \\ 0 & 0 \end{pmatrix}.$$

$$A = U \Sigma V^T = \begin{pmatrix} 1 & 0 & 0 & 0 \\ 0 & -1 & 0 & 0 \\ 0 & 0 & 1 & 0 \\ 0 & 0 & 0 & 1 \end{pmatrix} \begin{pmatrix} 3 & 0 \\ 0 & 2 \\ 0 & 0 \\ 0 & 0 \end{pmatrix} \begin{pmatrix} 1 & 0 \\ 0 & 1 \end{pmatrix}.$$ $\square$

**关键步骤解析**: 此例中 $A$ 已接近"对角"形式，只需注意 $\mathbf{u}_2$ 的符号来自 $A\mathbf{v}_2$ 的方向。对于一般矩阵，$A^T A$ 的特征向量计算是 SVD 的核心工作量。

---

### 例题 15.2（图像压缩的 SVD 应用）

**题目**: 设灰度图像表示为矩阵 $A \in \mathbb{R}^{m \times n}$（元素为像素亮度）。说明如何用低秩 SVD 逼近实现压缩，并分析误差。

**解答**:

**压缩原理**: 存储完整矩阵 $A$ 需要 $mn$ 个数。SVD 为 $A = \sum_{i=1}^r \sigma_i \mathbf{u}_i \mathbf{v}_i^T$。

取秩 $k$ 逼近 $A_k = \sum_{i=1}^k \sigma_i \mathbf{u}_i \mathbf{v}_i^T$。存储 $A_k$ 需要：

- $k$ 个奇异值 $\sigma_i$；
- $k$ 个左奇异向量 $\mathbf{u}_i \in \mathbb{R}^m$（各 $m$ 个分量）；
- $k$ 个右奇异向量 $\mathbf{v}_i \in \mathbb{R}^n$（各 $n$ 个分量）。

总计 $k(m + n + 1)$ 个数。压缩比 = $\frac{mn}{k(m+n+1)}$。当 $k \ll \min(m, n)$ 时压缩显著。

**误差**: 由 Eckart-Young-Mirsky 定理，Frobenius 误差

$$\|A - A_k\|_F = \sqrt{\sum_{i=k+1}^r \sigma_i^2}.$$

若奇异值快速衰减（自然图像通常如此），前几个分量即可捕获大部分能量。

**具体算例**: 设 $256 \times 256$ 图像，$r = 256$。取 $k = 20$：

存储原图：$65536$ 个数。
存储 $A_{20}$：$20 \times (256 + 256 + 1) = 10260$ 个数。
压缩比 ≈ $6.4:1$。

若 $\sigma_i$ 衰减如 $1/i$，则剩余能量 $\sum_{i=21}^{256} 1/i^2 \approx \int_{20}^{256} dx/x^2 \approx 1/20 = 5\%$。

**关键步骤解析**: SVD 图像压缩的有效性依赖于自然图像的"低秩结构"——相邻像素高度相关，全局模式可由少数特征图样叠加表示。

---

### 例题 15.3（线性变换在不同基下的矩阵）

**题目**: 设 $T: \mathbb{R}^2 \to \mathbb{R}^2$ 为逆时针旋转 $45^\circ$。求 $T$ 关于标准基 $\mathcal{E}$ 和关于基 $\mathcal{B} = \{(1,1)^T, (1,-1)^T\}$ 的矩阵表示。

**解答**:

**标准基下的矩阵**: 旋转矩阵

$$[T]_{\mathcal{E}} = \begin{pmatrix} \cos 45^\circ & -\sin 45^\circ \\ \sin 45^\circ & \cos 45^\circ \end{pmatrix} = \frac{1}{\sqrt{2}}\begin{pmatrix} 1 & -1 \\ 1 & 1 \end{pmatrix}.$$

**基 $\mathcal{B}$ 下的矩阵**: 过渡矩阵 $P = [I]_{\mathcal{E} \leftarrow \mathcal{B}} = \begin{pmatrix} 1 & 1 \\ 1 & -1 \end{pmatrix}$。

$$[T]_{\mathcal{B}} = P^{-1} [T]_{\mathcal{E}} P.$$

$\det(P) = -2$，$P^{-1} = \frac{1}{-2}\begin{pmatrix} -1 & -1 \\ -1 & 1 \end{pmatrix} = \frac{1}{2}\begin{pmatrix} 1 & 1 \\ 1 & -1 \end{pmatrix}$。

$$[T]_{\mathcal{B}} = \frac{1}{2}\begin{pmatrix} 1 & 1 \\ 1 & -1 \end{pmatrix} \cdot \frac{1}{\sqrt{2}}\begin{pmatrix} 1 & -1 \\ 1 & 1 \end{pmatrix} \cdot \begin{pmatrix} 1 & 1 \\ 1 & -1 \end{pmatrix}$$

$$= \frac{1}{2\sqrt{2}}\begin{pmatrix} 2 & 0 \\ 0 & -2 \end{pmatrix}\begin{pmatrix} 1 & 1 \\ 1 & -1 \end{pmatrix} = \frac{1}{2\sqrt{2}}\begin{pmatrix} 2 & 2 \\ -2 & 2 \end{pmatrix} = \frac{1}{\sqrt{2}}\begin{pmatrix} 1 & 1 \\ -1 & 1 \end{pmatrix}.$$

等等，这与预期不同。实际上 $\mathcal{B}$ 的两个向量不是标准正交的，旋转在斜坐标系下的表示较复杂。检验：$T(1,1) = (0, \sqrt{2})^T$，关于 $\mathcal{B}$ 的坐标？

$(0, \sqrt{2})^T = a(1,1)^T + b(1,-1)^T$，$a+b=0$，$a-b=\sqrt{2}$，$a = \sqrt{2}/2$，$b = -\sqrt{2}/2$。

$T(1,-1) = (\sqrt{2}, 0)^T = c(1,1)^T + d(1,-1)^T$，$c+d=\sqrt{2}$，$c-d=0$，$c=d=\sqrt{2}/2$。

故 $[T]_{\mathcal{B}} = \frac{\sqrt{2}}{2}\begin{pmatrix} 1 & 1 \\ -1 & 1 \end{pmatrix} = \frac{1}{\sqrt{2}}\begin{pmatrix} 1 & 1 \\ -1 & 1 \end{pmatrix}$。与上面一致。$\square$

---

## 四、常见误区与纠正

### 误区 15.1: "SVD 中奇异值可以为负"

**错误观点**: 有些学生将奇异值与特征值混淆，认为奇异值像特征值一样可以是负数（尤其当 $A$ 本身有负元素时）。

**反例与纠正**: 奇异值**定义**为 $\sigma_i = \sqrt{\lambda_i(A^T A)}$。$A^T A$ 半正定，其特征值 $\lambda_i(A^T A) \geq 0$，故 $\sigma_i = \sqrt{\lambda_i} \geq 0$ 恒成立。奇异值非负是定义的直接推论。

即使 $A$ 有负元素（如 $A = \begin{pmatrix} -3 & 0 \\ 0 & 2 \end{pmatrix}$），$A^T A = \begin{pmatrix} 9 & 0 \\ 0 & 4 \end{pmatrix}$，奇异值仍为 $\sigma_1 = 3$，$\sigma_2 = 2$（非负！）。负号被吸收到左或右奇异向量中（此例中 $\mathbf{u}_1 = (-1, 0)^T$ 或 $\mathbf{v}_1 = (-1, 0)^T$）。

**正确理解**: 奇异值恒非负。SVD 中的"符号信息"完全由正交矩阵 $U$ 和 $V$ 承担，$\Sigma$ 只负责记录"伸缩幅度"。这是 SVD 与特征值分解的根本差异之一。

> **为什么错**: 将"特征值可正可负"的经验错误迁移到奇异值。特征值来自 $A\mathbf{v} = \lambda\mathbf{v}$，无此限制；奇异值来自 $A^T A$ 的特征值开方，天然非负。

---

## 五、思想方法提炼

**本章核心思想**:

1. **SVD 是线性代数的"终极分解"**: 特征值分解仅适用于方阵，且要求可对角化；SVD 适用于任意矩阵（甚至长方矩阵），总是存在。它将任意线性变换清晰分解为"旋转-伸缩-旋转"，是数据科学、信号处理、数值分析的基石。

2. **秩 = 信息维度**: 低秩逼近揭示数据中的"有效自由度"。图像压缩、降噪、推荐系统本质上都是在寻找好的低秩近似。

3. **基变换 = 换角度看问题**: 同一变换在不同基下的矩阵不同，选择"好"的基（特征基、SVD 基）可使问题极大简化。这是贯穿 Ch.8（坐标）、Ch.14（正交对角化）、Ch.15（SVD）的统一主题。

**全课程回顾**:

| 章节 | 核心对象 | 核心思想 |
|------|----------|----------|
| Ch.1 | 线性方程组 | 行图像/列图像 |
| Ch.2-4 | 消元/LU | 系统化求解算法 |
| Ch.5-6 | 向量空间/子空间 | 结构性语言 |
| Ch.7-8 | 求解/基与维数 | 自由度与结构 |
| Ch.9-10 | 四大子空间/正交性 | 正交分解 |
| Ch.11 | 最小二乘/QR | 最优逼近 |
| Ch.12 | 行列式 | 有向体积 |
| Ch.13-14 | 特征值/对角化 | 变换的"X射线" |
| Ch.15 | SVD | 终极分解与低秩逼近 |

---

## 六、习题

### 习题 15.1

**题目**: 求 $A = \begin{pmatrix} 4 & 0 \\ 3 & 0 \end{pmatrix}$ 的 SVD。

**解答**:

$A^T A = \begin{pmatrix} 25 & 0 \\ 0 & 0 \end{pmatrix}$。$\lambda_1 = 25$，$\lambda_2 = 0$。$\sigma_1 = 5$，$\sigma_2 = 0$。

$\mathbf{v}_1 = (1, 0)^T$，$\mathbf{v}_2 = (0, 1)^T$。$V = I_2$。

$\mathbf{u}_1 = \frac{1}{5}A\mathbf{v}_1 = \frac{1}{5}(4, 3)^T = (\frac{4}{5}, \frac{3}{5})^T$。

$\mathbf{u}_2$ 与 $\mathbf{u}_1$ 正交：$(-\frac{3}{5}, \frac{4}{5})^T$。

$$U = \begin{pmatrix} \frac{4}{5} & -\frac{3}{5} \\ \frac{3}{5} & \frac{4}{5} \end{pmatrix}, \quad \Sigma = \begin{pmatrix} 5 & 0 \\ 0 & 0 \end{pmatrix}, \quad V = I_2.$$ $\square$

---

### 习题 15.2

**题目**: 设 $A = U\Sigma V^T$ 为 SVD。证明 $A^T A$ 与 $AA^T$ 有相同的非零特征值。

**解答**:

$A^T A = V \Sigma^T U^T U \Sigma V^T = V \Sigma^T \Sigma V^T = V \operatorname{diag}(\sigma_1^2, \ldots, \sigma_r^2, 0, \ldots) V^T$。

$AA^T = U \Sigma \Sigma^T U^T = U \operatorname{diag}(\sigma_1^2, \ldots, \sigma_r^2, 0, \ldots) U^T$。

两者对角化后非零特征值均为 $\sigma_1^2, \ldots, \sigma_r^2$。$\square$

---

### 习题 15.3

**题目**: 设 $A = \begin{pmatrix} 1 & 1 \\ 1 & 1 \\ 1 & 1 \end{pmatrix}$。求伪逆 $A^+$。

**解答**:

$A$ 秩为 1。$A^T A = \begin{pmatrix} 3 & 3 \\ 3 & 3 \end{pmatrix}$。特征值：$\lambda_1 = 6$（$\sigma_1 = \sqrt{6}$），$\lambda_2 = 0$。

$\mathbf{v}_1 = \frac{1}{\sqrt{2}}(1, 1)^T$。

$\mathbf{u}_1 = \frac{1}{\sqrt{6}} A \mathbf{v}_1 = \frac{1}{\sqrt{6}} \cdot \frac{1}{\sqrt{2}} (2, 2, 2)^T = \frac{1}{\sqrt{3}}(1, 1, 1)^T$。

简化 SVD：$A = \mathbf{u}_1 \sigma_1 \mathbf{v}_1^T$。

$A^+ = \mathbf{v}_1 \sigma_1^{-1} \mathbf{u}_1^T = \frac{1}{\sqrt{2}}\frac{1}{\sqrt{6}}\frac{1}{\sqrt{3}} \begin{pmatrix} 1 \\ 1 \end{pmatrix} \begin{pmatrix} 1 & 1 & 1 \end{pmatrix} = \frac{1}{6}\begin{pmatrix} 1 & 1 & 1 \\ 1 & 1 & 1 \end{pmatrix}$。

验证：$A A^+ = \begin{pmatrix} 1 & 1 \\ 1 & 1 \\ 1 & 1 \end{pmatrix} \cdot \frac{1}{6}\begin{pmatrix} 1 & 1 & 1 \\ 1 & 1 & 1 \end{pmatrix} = \frac{1}{3}\begin{pmatrix} 1 & 1 & 1 \\ 1 & 1 & 1 \\ 1 & 1 & 1 \end{pmatrix}$，这是到 $C(A) = \operatorname{span}\{(1,1,1)^T\}$ 的投影。$\square$

---

### 习题 15.4

**题目**: 设 $A \in \mathbb{R}^{m \times n}$，$m > n$，$\operatorname{rank}(A) = n$。证明 $A^+ = (A^T A)^{-1} A^T$。

**解答**:

$A$ 列满秩，$A^T A$ 可逆。验证 Moore-Penrose 四个条件：

1. $AA^+A = A(A^T A)^{-1}A^T A = A$。
2. $A^+AA^+ = (A^T A)^{-1}A^T A (A^T A)^{-1}A^T = (A^T A)^{-1}A^T = A^+$。
3. $(AA^+)^T = (A(A^T A)^{-1}A^T)^T = A(A^T A)^{-1}A^T = AA^+$（对称）。
4. $(A^+A)^T = ((A^T A)^{-1}A^T A)^T = I^T = I = A^+A$（对称）。

由伪逆唯一性，$A^+ = (A^T A)^{-1}A^T$。$\square$

---

### 习题 15.5

**题目**: 设 $A$ 为正交矩阵。求其 SVD。

**解答**:

$A^T A = I$。特征值全为 1，$\sigma_i = 1$。右奇异向量可取标准基 $\mathbf{v}_i = \mathbf{e}_i$，$V = I$。

$\mathbf{u}_i = A\mathbf{e}_i = A$ 的第 $i$ 列。故 $U = A$，$\Sigma = I$。

$A = A \cdot I \cdot I^T = A$。SVD 即为 $A = A I I$。$\square$

---

### 习题 15.6

**题目**: 设 $A \in \mathbb{R}^{m \times n}$，$\mathbf{b} \in \mathbb{R}^m$。用伪逆表示 $\mathbf{b}$ 在 $C(A)$ 上的投影。

**解答**:

$\hat{\mathbf{b}} = A\mathbf{x}^+ = A A^+ \mathbf{b}$。

由定理 15.2 的证明，$AA^+$ 是到 $C(A)$ 的正交投影矩阵。故 $P_{C(A)} = AA^+$。$\square$

---

### 习题 15.7

**题目**: 设 $T: \mathbb{R}^2 \to \mathbb{R}^2$ 为关于直线 $y = x$ 的反射。求 $T$ 关于标准基的矩阵，以及关于 $\mathcal{B} = \{(1,1)^T, (1,-1)^T\}$ 的矩阵。

**解答**:

标准基：$T(1,0) = (0,1)$，$T(0,1) = (1,0)$。

$$[T]_{\mathcal{E}} = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}.$$

对 $\mathcal{B}$：$T(1,1) = (1,1)$（在直线上不变），$T(1,-1) = (-1, 1) = -(1,-1)$（垂直于直线反向）。

故 $[T]_{\mathcal{B}} = \begin{pmatrix} 1 & 0 \\ 0 & -1 \end{pmatrix}$（对角矩阵！）。

验证基变换：$P = \begin{pmatrix} 1 & 1 \\ 1 & -1 \end{pmatrix}$，$P^{-1} = \frac{1}{2}\begin{pmatrix} 1 & 1 \\ 1 & -1 \end{pmatrix}$。

$P^{-1}[T]_{\mathcal{E}}P = \frac{1}{2}\begin{pmatrix} 1 & 1 \\ 1 & -1 \end{pmatrix}\begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}\begin{pmatrix} 1 & 1 \\ 1 & -1 \end{pmatrix} = \frac{1}{2}\begin{pmatrix} 1 & 1 \\ -1 & 1 \end{pmatrix}\begin{pmatrix} 1 & 1 \\ 1 & -1 \end{pmatrix} = \frac{1}{2}\begin{pmatrix} 2 & 0 \\ 0 & -2 \end{pmatrix} = \begin{pmatrix} 1 & 0 \\ 0 & -1 \end{pmatrix}$。✓ $\square$

---

### 习题 15.8

**题目**: 设 $A \in \mathbb{R}^{n \times n}$ 对称，特征值 $|\lambda_1| \geq |\lambda_2| \geq \cdots \geq |\lambda_n|$。证明 $A$ 的奇异值为 $|\lambda_1|, |\lambda_2|, \ldots, |\lambda_n|$。

**解答**:

$A$ 对称，谱分解 $A = QDQ^T$，$D = \operatorname{diag}(\lambda_1, \ldots, \lambda_n)$。

$A^T A = A^2 = QD^2 Q^T$。$A^T A$ 特征值为 $\lambda_i^2$。

$\sigma_i = \sqrt{\lambda_i^2} = |\lambda_i|$。$\square$

---

### 习题 15.9

**题目**: 设 $A = \begin{pmatrix} 2 & 2 \\ 1 & 1 \end{pmatrix}$。求秩 1 最佳逼近 $A_1$（在谱范数和 Frobenius 范数下）。

**解答**:

$A^T A = \begin{pmatrix} 5 & 5 \\ 5 & 5 \end{pmatrix}$。$\lambda_1 = 10$（$\sigma_1 = \sqrt{10}$），$\lambda_2 = 0$。

$\mathbf{v}_1 = \frac{1}{\sqrt{2}}(1, 1)^T$。

$\mathbf{u}_1 = \frac{1}{\sqrt{10}} A \mathbf{v}_1 = \frac{1}{\sqrt{10}} \cdot \frac{1}{\sqrt{2}} (4, 2)^T = \frac{1}{\sqrt{5}}(2, 1)^T$。

$$A_1 = \sigma_1 \mathbf{u}_1 \mathbf{v}_1^T = \sqrt{10} \cdot \frac{1}{\sqrt{5}}\frac{1}{\sqrt{2}} \begin{pmatrix} 2 \\ 1 \end{pmatrix}\begin{pmatrix} 1 & 1 \end{pmatrix} = \begin{pmatrix} 2 & 2 \\ 1 & 1 \end{pmatrix} = A.$$ $\square$

---

### 习题 15.10

**题目**: 设 $A \in \mathbb{R}^{m \times n}$，$m < n$，$\operatorname{rank}(A) = m$。证明 $A^+ = A^T(AA^T)^{-1}$。

**解答**:

类似习题 15.4，验证 Moore-Penrose 条件。或从 SVD：$A = U\Sigma V^T$，$\Sigma = [\Sigma_m \; 0]$。

$A^T(AA^T)^{-1} = V\Sigma^T U^T (U\Sigma\Sigma^T U^T)^{-1} = V\Sigma^T U^T U (\Sigma\Sigma^T)^{-1} U^T = V\Sigma^T (\Sigma\Sigma^T)^{-1} U^T$。

$\Sigma^T (\Sigma\Sigma^T)^{-1} = \begin{pmatrix} \Sigma_m^{-1} \\ 0 \end{pmatrix} = \Sigma^+$。故 $= V\Sigma^+ U^T = A^+$。$\square$

---

### 习题 15.11

**题目**: 设 $A \in \mathbb{R}^{n \times n}$ 可逆。证明 $A^+ = A^{-1}$。

**解答**:

$A$ 可逆，SVD 中 $r = n$，$\Sigma$ 为可逆对角矩阵。

$A^{-1} = (U\Sigma V^T)^{-1} = V \Sigma^{-1} U^T = V \Sigma^+ U^T = A^+$（因 $\Sigma$ 可逆，$\Sigma^+ = \Sigma^{-1}$）。$\square$

---

### 习题 15.12

**题目**: （PCA 解释）设数据矩阵 $X \in \mathbb{R}^{m \times n}$ 已中心化（每列均值为 0）。证明：$X^T X$ 是协方差矩阵的 $m$ 倍，其特征向量是主成分方向。

**解答**:

协方差矩阵 $C = \frac{1}{m} X^T X$（样本协方差）。$X^T X = mC$。

$X^T X$ 与 $C$ 有相同特征向量，特征值相差 $m$ 倍。

SVD：$X = U\Sigma V^T$，$X^T X = V\Sigma^T\Sigma V^T$。$V$ 的列是 $X^T X$ 的特征向量。

第一主成分 $\mathbf{v}_1$ 使投影方差最大：$\max_{\|\mathbf{v}\|=1} \|X\mathbf{v}\|^2 = \max_{\|\mathbf{v}\|=1} \mathbf{v}^T X^T X \mathbf{v} = \lambda_1(X^T X) = \sigma_1^2$（由 Rayleigh 商）。$\square$

---

**文档状态**: 🟡 草稿 | **审校轮次**: 0/2
**最后更新**: 2026-04-18
