---
msc_primary: 15-XX
msc_secondary:
  - 15A18
  - 15A23
processed_at: '2026-04-20'
title: 线性代数·特征值、对角化与SVD习题集
---

# 线性代数·特征值、对角化与SVD习题集

> 覆盖特征值计算、Jordan标准型、谱定理、奇异值分解（SVD）与主成分分析（PCA）等核心内容。共 20 题。

---

### 题1. 实矩阵复特征值的几何意义
**题目**：设 $A=\begin{pmatrix}0&-1\\1&0\end{pmatrix}$。求特征值与特征向量，并解释其几何意义。

**难度**：★★☆☆☆

**解答**：特征方程 $\det(A-\lambda I)=\lambda^2+1=0$，得 $\lambda=\pm i$。对应特征向量分别为 $(1,-i)^T$ 与 $(1,i)^T$。几何上，$A$ 表示平面旋转 $90°$，无实特征方向；复特征值 $e^{\pm i\pi/2}$ 反映旋转角。

---

### 题2. 特征多项式系数与迹、行列式
**题目**：设 $A\in M_n(\mathbb{C})$，特征多项式为 $p(\lambda)=\det(\lambda I-A)=\lambda^n+c_{n-1}\lambda^{n-1}+\cdots+c_0$。证明 $c_{n-1}=-\operatorname{tr}A$，$c_0=(-1)^n\det A$。

**难度**：★★★☆☆

**解答**：由 Vieta 公式，$p(\lambda)=\prod(\lambda-\lambda_i)$，展开得 $c_{n-1}=-\sum\lambda_i=-\operatorname{tr}A$，$c_0=(-1)^n\prod\lambda_i=(-1)^n\det A$。

---

### 题3. 上三角矩阵的特征值
**题目**：证明上三角矩阵的特征值即其对角元。

**难度**：★☆☆☆☆

**解答**：$\det(\lambda I-U)=\prod(\lambda-u_{ii})$，根为 $u_{ii}$。

---

### 题4. 幂等矩阵的特征值
**题目**：设 $P^2=P$（幂等）。证明 $P$ 的特征值只能是 $0$ 或 $1$，且 $P$ 可对角化。

**难度**：★★☆☆☆

**解答**：若 $Px=\lambda x$，则 $P^2x=\lambda^2x=\lambda x$，故 $\lambda(\lambda-1)=0$。最小多项式 $m(t)\mid t(t-1)$ 无重根，故可对角化。

---

### 题5. 友矩阵的特征多项式
**题目**：设 $C=\begin{pmatrix}0&0&\cdots&0&-c_0\\1&0&\cdots&0&-c_1\\0&1&\cdots&0&-c_2\\\vdots&&\ddots&&\vdots\\0&0&\cdots&1&-c_{n-1}\end{pmatrix}$。求其特征多项式。

**难度**：★★★☆☆

**解答**：按第一行展开 $\det(\lambda I-C)$，递推得 $p(\lambda)=\lambda^n+c_{n-1}\lambda^{n-1}+\cdots+c_0$。

---

### 题6. 对称矩阵特征值为实数
**题目**：设 $A$ 为实对称矩阵。证明其特征值均为实数。

**难度**：★★☆☆☆

**解答**：设 $Ax=\lambda x$，$x\neq 0$。取共轭转置得 $x^*A=\bar\lambda x^*$。右乘 $x$：$x^*Ax=\bar\lambda x^*x$；左乘 $x^*$：$x^*Ax=\lambda x^*x$。故 $(\lambda-\bar\lambda)\|x\|^2=0$，$\lambda\in\mathbb{R}$。

---

### 题7. 不同特征值对应特征向量正交
**题目**：设 $A$ 为实对称矩阵，$\lambda_1\neq\lambda_2$ 为不同特征值，对应特征向量 $v_1,v_2$。证明 $v_1\perp v_2$。

**难度**：★★☆☆☆

**解答**：$\lambda_1 v_1\cdot v_2=(Av_1)^Tv_2=v_1^TAv_2=\lambda_2 v_1\cdot v_2$。故 $(\lambda_1-\lambda_2)v_1\cdot v_2=0$，得 $v_1\cdot v_2=0$。

---

### 题8. 谱定理的几何解释
**题目**：设 $A$ 为 $n\times n$ 实对称矩阵。用谱定理说明 $A$ 表示沿正交方向的伸缩变换。

**难度**：★★☆☆☆

**解答**：谱定理：$A=Q\Lambda Q^T$，$Q$ 正交，$\Lambda=\operatorname{diag}(\lambda_1,\ldots,\lambda_n)$。在 $Q$ 的列向量（特征向量）构成的标准正交基下，$A$ 的作用为各坐标轴方向的伸缩，伸缩因子为特征值。

---

### 题9. 正定矩阵的判定
**题目**：判断 $A=\begin{pmatrix}2&1&1\\1&2&1\\1&1&2\end{pmatrix}$ 是否正定。

**难度**：★★☆☆☆

**解答**：顺序主子式：$D_1=2>0$，$D_2=3>0$，$D_3=4>0$。故正定。另法：特征值为 $4,1,1$（因 $A=I+J$，$J$ 为全1矩阵），均正。

---

### 题10. Rayleigh 商的极值
**题目**：设 $A$ 为实对称矩阵，特征值 $\lambda_1\le\cdots\le\lambda_n$。证明
$$\lambda_1=\min_{x\neq 0}\frac{x^TAx}{x^Tx},\qquad \lambda_n=\max_{x\neq 0}\frac{x^TAx}{x^Tx}.$$

**难度**：★★★☆☆

**解答**：由谱定理，$A=Q\Lambda Q^T$，令 $y=Q^Tx$。则 $R(x)=\frac{\sum\lambda_i y_i^2}{\sum y_i^2}$，为特征值的加权平均，权重 $w_i=y_i^2/\|y\|^2$。故 $\min R=\lambda_1$，$\max R=\lambda_n$。

---

### 题11. Jordan 标准型计算
**题目**：求 $A=\begin{pmatrix}3&1&0\\0&3&0\\0&0&2\end{pmatrix}$ 的 Jordan 标准型及变换矩阵 $P$。

**难度**：★★★☆☆

**解答**：特征值 $3$（代数重数2，几何重数1：$A-3I$ 的秩为2），$2$（代数重数1）。Jordan 型 $J=\begin{pmatrix}3&1&0\\0&3&0\\0&0&2\end{pmatrix}=A$ 本身已是 Jordan 型。$P=I$。

---

### 题12. 不可对角化矩阵的例子
**题目**：构造一个 $2\times 2$ 实矩阵，其特征值均为实数但不可对角化。

**难度**：★★☆☆☆

**解答**：$A=\begin{pmatrix}\lambda&1\\0&\lambda\end{pmatrix}$。特征值 $\lambda$（代数重数2），$A-\lambda I=\begin{pmatrix}0&1\\0&0\end{pmatrix}$ 秩为1，几何重数1<2，故不可对角化。

---

### 题13. SVD 的存在唯一性
**题目**：叙述 $m\times n$ 实矩阵 $A$ 的奇异值分解定理。奇异值是否唯一？左/右奇异向量呢？

**难度**：★★★☆☆

**解答**：$A=U\Sigma V^T$，$U\in O(m)$，$V\in O(n)$，$\Sigma=\operatorname{diag}(\sigma_1,\ldots,\sigma_r,0,\ldots)$，$\sigma_1\ge\cdots\ge\sigma_r>0$。
- 奇异值 $\sigma_i$ 唯一（$A^TA$ 特征值的正平方根）。
- 奇异向量：对应不同奇异值的子空间唯一；重奇异值对应的子空间中可任取标准正交基，不唯一。

---

### 题14. SVD 与矩阵范数
**题目**：证明 $\|A\|_2=\sigma_1$（谱范数 = 最大奇异值），$\|A\|_F=\sqrt{\sum\sigma_i^2}$（Frobenius 范数）。

**难度**：★★★☆☆

**解答**：$\|A\|_2=\max_{\|x\|=1}\|Ax\|=\max\sqrt{x^TA^TAx}=\sqrt{\lambda_{\max}(A^TA)}=\sigma_1$。
$\|A\|_F^2=\operatorname{tr}(A^TA)=\operatorname{tr}(V\Sigma^T\Sigma V^T)=\operatorname{tr}(\Sigma^T\Sigma)=\sum\sigma_i^2$。

---

### 题15. 低秩最优逼近（Eckart-Young-Mirsky）
**题目**：设 $A=U\Sigma V^T$ 为 SVD，$A_k=U\Sigma_k V^T$ 其中 $\Sigma_k$ 只保留前 $k$ 个奇异值。证明 $A_k$ 是在 Frobenius 范数和谱范数下对 $A$ 的最佳秩 $k$ 逼近。

**难度**：★★★★☆

**解答**：对任意秩 $k$ 矩阵 $B$，Weyl 不等式与交错原理表明 $\sum_{i>k}\sigma_i(A)^2\le\|A-B\|_F^2$。$A_k$ 达到下界。

---

### 题16. 伪逆与最小二乘
**题目**：设 $A$ 列满秩。证明最小二乘问题 $\min\|Ax-b\|_2$ 的解为 $x=A^+b$，其中 $A^+=V\Sigma^{-1}U^T$ 为 Moore-Penrose 伪逆。

**难度**：★★★☆☆

**解答**：正规方程 $A^TAx=A^Tb$。$A^TA=V\Sigma^T\Sigma V^T$ 可逆，$x=(A^TA)^{-1}A^Tb=V\Sigma^{-1}U^Tb=A^+b$。

---

### 题17. PCA 的 SVD 视角
**题目**：设数据矩阵 $X\in\mathbb{R}^{n\times p}$（已中心化）。证明主成分方向即 $X$ 的右奇异向量，方差解释率由奇异值平方决定。

**难度**：★★★☆☆

**解答**：协方差矩阵 $S=\frac{1}{n-1}X^TX$。SVD：$X=U\Sigma V^T$，则 $S=\frac{1}{n-1}V\Sigma^T\Sigma V^T$。$V$ 的列即为 $S$ 的特征向量（主成分方向），对应特征值 $\sigma_i^2/(n-1)$。

---

### 题18. 特征值的连续性
**题目**：证明矩阵特征值关于矩阵元素连续。

**难度**：★★★★☆

**解答**：特征多项式系数是矩阵元素的多项式（连续）。多项式根关于系数连续（由 Rouché 定理或复分析论证）。

---

### 题19. Gershgorin 圆盘定理应用
**题目**：用 Gershgorin 定理估计 $A=\begin{pmatrix}4&1&0\\1&3&1\\0&1&5\end{pmatrix}$ 的特征值范围。

**难度**：★★☆☆☆

**解答**：圆盘 $D(4,1)$、$D(3,2)$、$D(5,1)$。所有特征值位于并集内。因 $A$ 对称，特征值在 $[1,7]$ 中（更精确地，$\lambda\in[2,6]$ 由实际计算 $2,3,7$ 修正）。

---

### 题20. Cayley-Hamilton 定理证明（SVD/谱方法）
**题目**：对可对角化矩阵证明 Cayley-Hamilton 定理 $p(A)=0$，并说明稠密性论证可推广到所有矩阵。

**难度**：★★★★☆

**解答**：若 $A=P\Lambda P^{-1}$，则 $p(A)=Pp(\Lambda)P^{-1}=P\operatorname{diag}(p(\lambda_1),\ldots)P^{-1}=0$（因 $p(\lambda_i)=0$）。可对角化矩阵在 $M_n(\mathbb{C})$ 中稠密，$p(A)$ 关于 $A$ 连续，故对所有矩阵成立。

---

**Lean4 对应**：`LinearAlgebra.Eigenspace`、`LinearAlgebra.Spectrum`、`LinearAlgebra.Matrix.Svd`。
