---
msc_primary: 00A99
习题编号: AG-047
学科: 代数几何
知识点: 代数几何-Hilbert概形
难度: ⭐⭐⭐⭐⭐
预计时间: 50分钟
---

# Hilbert 概形深入

## 题目

**(a)** 证明 Hilbert 概形代表 Hilbert 函子。

**(b)** 讨论 Hilbert 概形的切空间与形变理论。

**(c)** 计算 $\operatorname{Hilb}^n(\mathbb{A}^2)$ 的几何与对称函数联系。

## 解答

### (a) 可表性定理

**Hilbert 函子**：设 $X$ 是局部 Noether 概形，$P(t) \in \mathbb{Q}[t]$ 是多项式（Hilbert 多项式）。

定义函子：

$$
\operatorname{Hilb}_P(X): (\mathrm{Sch}/S)^{\mathrm{op}} \to \mathrm{Set}
$$

对 $S$-概形 $T$，$\operatorname{Hilb}_P(X)(T) = \{Z \subset X \times_S T \text{ 闭子概形，平坦}/T, \text{ Hilbert 多项式 } P\}$。

**Grothendieck 定理（1962）**：若 $X \to S$ 是拟射影的，则 $\operatorname{Hilb}_P(X)$ 是可表函子，表出对象是 **射影 $S$-概形**。

*证明概要*：

1. **嵌入**：$X \subset \mathbb{P}^N_S$，子概形 $Z \subset X$ 对应饱和齐次理想 $I_Z \subset \mathcal{O}_X$
2. **Hilbert 多项式**：$P_Z(t) = \chi(Z, \mathcal{O}_Z(t)) = \dim H^0(Z, \mathcal{O}_Z(t))$（对大 $t$）
3. **Grassmann 簇**：固定 $m \gg 0$，$H^0(\mathbb{P}^N, \mathcal{O}(m))$ 的维数 $r_m$ 有限。$I_Z(m) \subset H^0(X, \mathcal{O}_X(m))$ 是子空间。
4. **平坦性**：$Z$ 平坦 $/T \Leftrightarrow$ $H^0(Z_t, \mathcal{O}_{Z_t}(m))$ 的维数局部恒定（对充分大 $m$）。
5. **闭条件**：给定子空间 $V \subset H^0(X, \mathcal{O}_X(m))$，要求 $V$ 生成饱和理想是闭条件，由 Hilbert 概形的闭子概形参数化。

**构造**：取 Grassmann 簇 $\operatorname{Gr}(r_m - P(m), r_m)$，闭子集由可乘性条件（$V$ 生成的理想在更高次有正确维数）给出。

---

### (b) 切空间与形变

**切空间**：设 $Z \subset X$ 是闭子概形，$[Z] \in \operatorname{Hilb}(X)$ 对应点。

$$
T_{[Z]} \operatorname{Hilb}(X) = \operatorname{Hom}_{\mathcal{O}_Z}(\mathcal{I}_Z/\mathcal{I}_Z^2, \mathcal{O}_Z) = H^0(Z, \mathcal{N}_{Z/X})
$$

其中 $\mathcal{N}_{Z/X} = \mathcal{H}om_{\mathcal{O}_Z}(\mathcal{I}_Z/\mathcal{I}_Z^2, \mathcal{O}_Z)$ 是 **法丛**。

*证明*：考虑形变 $Z_\epsilon \subset X \times \operatorname{Spec}(\mathbb{C}[\epsilon]/\epsilon^2)$，$Z_0 = Z$。

局部：$Z = \operatorname{Spec}(A/I)$，$Z_\epsilon = \operatorname{Spec}(A[\epsilon]/(I + \epsilon J))$，其中 $J$ 是 $A/I$-模同态 $I/I^2 \to A/I$。

全局化得 $H^0(Z, \mathcal{N}_{Z/X})$。

**阻碍空间**：$\operatorname{Ob}_Z = H^1(Z, \mathcal{N}_{Z/X})$。

若 $H^1(Z, \mathcal{N}_{Z/X}) = 0$，则 Hilbert 概形在 $[Z]$ 处光滑。

**例子**：

- 曲线 $C \subset \mathbb{P}^3$，$\mathcal{N}_{C/\mathbb{P}^3}$ 的 $H^1$ 可能非零（ obstructed 形变）
- 光滑超曲面 $Y \subset \mathbb{P}^n$，$\mathcal{N}_{Y/\mathbb{P}^n} = \mathcal{O}_Y(d)$，$H^1 = 0$，故 Hilbert 概形光滑

---

### (c) $\operatorname{Hilb}^n(\mathbb{A}^2)$

**定义**：$\operatorname{Hilb}^n(\mathbb{A}^2)$ 参数化 $\mathbb{A}^2$ 上长度为 $n$ 的零维子概形。

**维数**：$\dim \operatorname{Hilb}^n(\mathbb{A}^2) = 2n$。

**光滑性**：Fogarty 定理：$\operatorname{Hilb}^n(\mathbb{A}^2)$ 是光滑的（对任意 $n$）。

*证明*：对零维子概形 $Z \subset \mathbb{A}^2$，$\mathcal{N}_{Z/\mathbb{A}^2}$ 的 $H^1 = 0$（因 $\dim Z = 0$，$H^1$ 消失）。

**Hilbert-Chow 态射**：

$$
\pi: \operatorname{Hilb}^n(\mathbb{A}^2) \to \operatorname{Sym}^n(\mathbb{A}^2) = (\mathbb{A}^2)^n / S_n
$$

将子概形 $Z$ 映射到其支撑点（带重数）。$\pi$ 是解消奇点（crepant resolution）。

**例外集**：$\operatorname{Sym}^n(\mathbb{A}^2)$ 的对角奇点被 exceptional divisor 替代。

**几何描述**：$\operatorname{Hilb}^n(\mathbb{A}^2)$ 可描述为：

$$
\{(B_1, B_2, v) \in M_n(\mathbb{C})^2 \times \mathbb{C}^n : [B_1, B_2] = 0, \text{循环向量条件}\} / GL_n(\mathbb{C})
$$

其中循环向量条件：$\mathbb{C}[B_1, B_2]v = \mathbb{C}^n$。

**与对称函数的联系**：

$H^*(\operatorname{Hilb}^n(\mathbb{A}^2))$ 与 **Jack 多项式**、**对称函数** 的表示论密切相关。

Nakajima 的构造：$\bigoplus_n H^*(\operatorname{Hilb}^n(\mathbb{A}^2))$ 构成分次 Heisenberg 代数的 Fock 空间表示。

**公式**：生成函数

$$
\sum_{n \geq 0} q^n \chi(\operatorname{Hilb}^n(\mathbb{A}^2)) = \prod_{k \geq 1} \frac{1}{(1-q^k)}
$$

是 Euler 分拆函数的生成函数。

---

## 常见错误

- **混淆 Hilbert 多项式与 Hilbert 函数**：Hilbert 函数 $h_Z(t) = \dim H^0(Z, \mathcal{O}_Z(t))$ 对充分大 $t$ 是多项式（Hilbert 多项式），但对小 $t$ 可能不同。
- **Hilb^n(X) 的光滑性**：仅对 $\dim X \leq 2$ 或光滑曲线保证光滑；高维 $X$ 的 Hilbert 概形通常奇异。
- **平坦性的作用**：Hilbert 函子要求平坦族，否则无法得到良好参数空间。

## 参考文献

- Grothendieck, *Techniques de construction et théorèmes d'existence en géométrie algébrique IV*.
- Nakajima, *Lectures on Hilbert Schemes of Points on Surfaces*, AMS.
- Fogarty, *Algebraic families on an algebraic surface*.
