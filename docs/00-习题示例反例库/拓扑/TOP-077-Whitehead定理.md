---
msc_primary: 55P10
msc_secondary: 55Q05, 57N65
习题编号: TOP-077
学科: 拓扑
知识点: 同伦论-Whitehead定理
难度: ⭐⭐⭐⭐
预计时间: 40分钟
---

# Whitehead定理

## 题目

**(a)** 证明 Whitehead 定理：若 $f: X \to Y$ 是 CW 复形间的映射，诱导同伦群同构，则 $f$ 是同伦等价。

**(b)** 陈述并证明胞腔逼近定理。

**(c)** 讨论非 CW 空间的反例。

## 解答

### (a) Whitehead 定理

**定理的陈述**

**Whitehead 定理**：设 $X, Y$ 为道路连通的 CW 复形，$f: X \to Y$ 为连续映射。若 $f$ 在所有同伦群上诱导同构

$$
f_*: \pi_n(X, x_0) \xrightarrow{\cong} \pi_n(Y, f(x_0)), \quad \forall n \geq 1,
$$

则 $f$ 为**同伦等价**。即存在 $g: Y \to X$ 使得 $g \circ f \simeq \text{id}_X$ 且 $f \circ g \simeq \text{id}_Y$。

**注记**：
- 逆命题显然：同伦等价诱导同伦群同构。
- 若 $f$ 仅诱导弱同伦群同构（即 $f_*$ 为同构且 $\pi_0$ 为双射），则称 $f$ 为**弱同伦等价**。Whitehead 定理断言：CW 复形间的弱同伦等价必为（强）同伦等价。

**证明框架**

**步骤 1：映射柱与纤维化替换**

将 $f$ 替换为**映射柱**（mapping cylinder）$M_f = (X \times [0,1] \sqcup Y) / (x,1) \sim f(x)$ 的包含 $X \hookrightarrow M_f$。因 $M_f \simeq Y$，可设 $f$ 为**纤维化**（通过道路空间纤维化替换或 Moors 定理）。

对纤维化 $f: X \to Y$，纤维 $F = f^{-1}(y_0)$ 的同伦群与底空间有长正合列

$$
\cdots \to \pi_{n+1}(Y) \to \pi_n(F) \to \pi_n(X) \xrightarrow{f_*} \pi_n(Y) \to \pi_{n-1}(F) \to \cdots
$$

由假设 $f_*$ 为同构，故 $\pi_n(F) = 0$ 对所有 $n \geq 0$。即 $F$ 为**弱可缩**（weakly contractible）。

**步骤 2：弱可缩纤维的截面**

需证纤维化 $f: X \to Y$ 有截面（section）$s: Y \to X$（满足 $f \circ s = \text{id}_Y$），且任何两截面同伦。这通过 CW 复形上的**逐骨架归纳**（skeleton-wise induction）完成。

设 $Y$ 有 CW 分解 $Y^{(0)} \subset Y^{(1)} \subset \cdots$。归纳假设在 $n$-骨架 $Y^{(n)}$ 上已构造截面 $s_n$。

对 $(n+1)$-胞腔 $e^{n+1}_\alpha$，其粘贴映射为 $\varphi_\alpha: S^n \to Y^{(n)}$。因 $f$ 为纤维化，提升问题

$$
\begin{array}{ccc}
S^n & \xrightarrow{s_n \circ \varphi_\alpha} & X \\
\downarrow & & \downarrow f \\
D^{n+1} & \xrightarrow{\Phi_\alpha} & Y
\end{array}
$$

有解当且仅当 $s_n \circ \varphi_\alpha$ 在 $X$ 中可缩。由长正合列，$[S^n, F] = \pi_n(F) = 0$，故 $s_n \circ \varphi_\alpha$ 在纤维内可缩，因而可提升。由此定义 $s_{n+1}|_{e^{n+1}_\alpha}$。

**步骤 3：截面的同伦**

设 $s, s'$ 为两截面。考虑同伦提升问题：$H: Y \times [0,1] \to Y$ 为投影 $H(y,t) = y$，需提升为 $\tilde{H}: Y \times [0,1] \to X$ 使 $\tilde{H}(\cdot, 0) = s$，$\tilde{H}(\cdot, 1) = s'$。同样逐骨架归纳：对 $n$-骨架，同伦 $H|_{Y^{(n)} \times [0,1]}$ 的提升存在性由 $\pi_n(F) = 0$ 保证。

**步骤 4：从截面到同伦等价**

截面 $s: Y \to X$ 满足 $f \circ s = \text{id}_Y$。对 $s \circ f: X \to X$，利用同伦提升于纤维化 $f$ 上：$f \circ (s \circ f) = f$，而 $\text{id}_X$ 也是 $f$ 的提升。由提升的唯一性（在同伦意义下），$s \circ f \simeq \text{id}_X$。

因此 $f$ 为同伦等价，同伦逆为 $s$。

---

### (b) 胞腔逼近定理

**定理的陈述**

**胞腔逼近定理**：设 $X, Y$ 为 CW 复形，$A \subset X$ 为子复形。设 $f: X \to Y$ 连续且在 $A$ 上为胞腔映射（即 $f(A^{(n)}) \subset Y^{(n)}$）。则存在**胞腔映射** $g: X \to Y$（即 $g(X^{(n)}) \subset Y^{(n)}$ 对所有 $n$），使得 $g|_A = f|_A$ 且 $g \simeq f \; \text{rel } A$。

**证明**

**归纳构造**

假设已在 $X^{(n)} \cup A$ 上定义了 $g_n$，$g_n \simeq f|_{X^{(n)} \cup A} \; \text{rel } A$，且 $g_n$ 为胞腔映射。

对 $(n+1)$-胞腔 $e^{n+1}_\alpha$，其特征映射为 $\Phi_\alpha: (D^{n+1}, S^n) \to (X^{(n+1)}, X^{(n)})$。复合映射

$$
g_n \circ \Phi_\alpha|_{S^n}: S^n \longrightarrow Y^{(n)}
$$

需扩张至 $D^{n+1} \to Y^{(n+1)}$。

**关键观察**：$Y$ 的 $(n+1)$-骨架具有如下性质：对任意映射 $h: S^n \to Y^{(n)}$，若 $h$ 在 $Y$ 中可缩（即 $[h] = 0 \in \pi_n(Y)$），则 $h$ 在 $Y^{(n+1)}$ 中可缩。这是因为 $Y$ 的 $(n+1)$-骨架到 $Y$ 的包含诱导 $\pi_n(Y^{(n+1)}) \to \pi_n(Y)$ 的同构（由胞腔逼近的诱导同构性质）。

具体构造：令 $H: S^n \times [0,1] \to Y$ 为 $g_n \circ \Phi_\alpha|_{S^n}$ 到 $f \circ \Phi_\alpha|_{S^n}$ 的同伦（由归纳假设）。因 $f \circ \Phi_\alpha: D^{n+1} \to Y$，其在边界上的限制可扩张，故 $f \circ \Phi_\alpha|_{S^n}$ 在 $Y$ 中可缩。因此 $g_n \circ \Phi_\alpha|_{S^n}$ 也在 $Y$ 中可缩。

由上述观察，存在同伦 $K: S^n \times [0,1] \to Y^{(n+1)}$ 使得 $K(\cdot, 0) = g_n \circ \Phi_\alpha|_{S^n}$ 且 $K(\cdot, 1)$ 为常值映射。将此同伦与常值映射的锥形（cone）粘合，得到扩张 $\tilde{g}: D^{n+1} \to Y^{(n+1)}$。

对所有 $(n+1)$-胞腔执行此操作，定义 $g_{n+1}: X^{(n+1)} \cup A \to Y^{(n+1)}$。由同伦扩张性质（homotopy extension property），$g_{n+1} \simeq f|_{X^{(n+1)} \cup A} \; \text{rel } A$。

**极限过程**

取 $g = \bigcup_n g_n: X \to Y$。由同伦扩张的相容性，所有局部同伦可粘合为整体同伦 $g \simeq f \; \text{rel } A$。

---

### (c) 非 CW 空间的反例

**弱同伦等价 ≠ 同伦等价**

Whitehead 定理要求空间为 CW 复形。对一般拓扑空间，弱同伦等价未必是同伦等价。

**经典反例：拓扑学家的正弦曲线（Warsaw Circle）**

定义**拓扑学家的正弦曲线**：

$$
S = \{(x, \sin(1/x)) : 0 < x \leq 1\} \cup \{(0, y) : -1 \leq y \leq 1\} \subset \mathbb{R}^2.
$$

其闭包加上从 $(0, -1)$ 到 $(1, \sin 1)$ 的弧段构成**Warsaw 圆** $W$。 Warsaw 圆是道路连通、单连通的（$\pi_1(W) = 0$），且所有高阶同伦群为零（因可收缩于平面中的任意邻域内）。

包含映射 $i: W \hookrightarrow D^2$（单位圆盘）诱导同伦群同构（两边均平凡）。但 $W$ 不是可缩的：存在映射 $W \to W$（恒等）不能同伦于常值映射，因为 $W$ 的拓扑结构导致"无穷振荡"无法连续压平。

严格证明：$W$ 的**Čech 上同调** $\check{H}^1(W; \mathbb{Z}) \neq 0$，而可缩空间的 Čech 上同调必为零。因此 $W$ 与单点空间弱同伦等价但不同伦等价。

**另一个反例：伪圆（Pseudocircle）**

设 $X \subset \mathbb{R}^2$ 为两相交正弦曲线的并：

$$
X = \{(x, \sin(1/x))\} \cup \{(0, y)\} \cup \{(-x, \sin(1/x))\}.
$$

$X$ 具有与 $S^1$ 相同的弱同伦型（$\pi_1(X) \cong \mathbb{Z}$，高阶群为零），但 $X$ 不同胚于 $S^1$，也不是 CW 复形。包含 $X \hookrightarrow S^1$（适当定义）为弱同伦等价但非同伦等价。

**Čech 同伦与弱同伦型的区别**

弱同伦型仅由同伦群决定，而同伦型需要映射自身的同伦类信息。对 CW 复形，Whitehead 定理保证两者一致；对病态空间，Čech 同伦群或 shape 理论更能反映全局性质。

**应用：模型范畴与局部化**

在 Quillen 的模型范畴框架中，CW 复形构成的空间范畴具有**胞腔模型结构**，其中弱等价恰为弱同伦等价，纤维化为 Serre 纤维化，余纤维化为相对 CW 包含。Whitehead 定理等价于：在此模型结构中，每个对象 fibrant 且 cofibrant（对 CW 复形而言），故弱等价即同伦等价。

对一般空间，需通过**CW 逼近**（CW approximation）：任意空间 $X$ 存在 CW 复形 $X'$ 和弱同伦等价 $X' \to X$。例如，Warsaw 圆的 CW 逼近为单点（因其弱同伦型为点），但 $X' \to W$ 不是同伦等价。

---
