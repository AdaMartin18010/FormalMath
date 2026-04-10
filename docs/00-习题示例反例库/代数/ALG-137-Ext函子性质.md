---
习题编号: ALG-137
学科: 代数
知识点: 同调代数-Ext函子
难度: ⭐⭐⭐⭐
预计时间: 40分钟
---

# Ext函子性质

## 题目

设 $R$ 是环，$A, B$ 是右 $R$-模。定义 $\text{Ext}_R^n(A, B) = (R^n \text{Hom}_R(-, B))(A)$。

**(a)** 证明 $\text{Ext}_R^0(A, B) \cong \text{Hom}_R(A, B)$，并计算 $\text{Ext}_R^1(A, B)$ 当 $A$ 投射时。

**(b)** 证明对短正合列 $0 \to B' \to B \to B'' \to 0$，有长正合列：
$$0 \to \text{Hom}(A, B') \to \text{Hom}(A, B) \to \text{Hom}(A, B'') \to \text{Ext}^1(A, B') \to \cdots$$

**(c)** 证明Baer和与Ext的关系：$\text{Ext}_R^1(A, B)$ 分类 $A$ 由 $B$ 扩张的等价类。

## 解答

### (a) Ext函子的初值

**证明：**

$\text{Ext}^n(A, B) = H^n(\text{Hom}_R(P_\bullet, B))$，其中 $P_\bullet \to A$ 是投射分解。

$n=0$：
$$\text{Ext}^0(A, B) = \ker(\text{Hom}(P_0, B) \to \text{Hom}(P_1, B))$$

$$= \{f: P_0 \to B : f \circ d_1 = 0\} = \text{Hom}(A, B)$$

（因 $P_1 \to P_0 \to A \to 0$ 正合，$A = \text{coker}(d_1)$）

**$A$ 投射时**：

取平凡分解 $0 \to A \to A \to 0$。

$\text{Hom}(P_\bullet, B)$：$0 \to \text{Hom}(A, B) \to 0$。

因此 $\text{Ext}^n(A, B) = 0$ 对 $n \geq 1$。$\square$

### (b) Hom-Ext长正合列

**证明：**

$\text{Hom}_R(A, -)$ 是左正合函子，其右导出函子为 $\text{Ext}^n(A, -)$。

对 $0 \to B' \to B \to B'' \to 0$，取内射分解（或 Hom 的长正合列标准构造）。

或：由导出函子的长正合列性质，应用于 $G = \text{Hom}_R(A, -)$。

具体：对 $A$ 的投射分解 $P_\bullet$，有复形短正合列：
$$0 \to \text{Hom}(P_\bullet, B') \to \text{Hom}(P_\bullet, B) \to \text{Hom}(P_\bullet, B'') \to 0$$

（因 $P_n$ 投射，$\text{Hom}(P_n, -)$ 正合）

蛇形引理得长正合列。$\square$

### (c) Baer和与扩张

**证明概要：**

**扩张**：短正合列 $0 \to B \to E \to A \to 0$。

**等价**：交换图连接。

**与Ext的对应**：

给定增广 $\varepsilon: P_0 \to A$，核 $K = \ker(\varepsilon)$。

$$0 \to K \to P_0 \to A \to 0$$

对扩张 $0 \to B \to E \to A \to 0$，由 $P_0$ 投射，存在提升：
$$\begin{array}{ccccccccc}
0 & \to & K & \to & P_0 & \to & A & \to & 0 \\
  &     & \downarrow &     & \downarrow &     & \| &     & \\
0 & \to & B & \to & E & \to & A & \to & 0
\end{array}$$

诱导 $\partial: K \to B$，确定 $\text{Ext}^1(A, B)$ 中元。

**Baer和**：推出构造对应Ext中的加法。

$\text{Ext}^1(A, B) \cong \{\text{扩张}\}/\sim$。$\square$
