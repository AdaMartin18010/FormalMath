---
title: Ext与群扩张
description: 深入探讨Ext^1与群扩张分类之间的精确对应，建立群上同调与群论结构的桥梁。
msc_primary:
  - 20J06
msc_secondary:
  - 18G15
  - 20E22
processed_at: '2026-04-20'
references:
  textbooks:
    - id: weibel_ha
      type: textbook
      title: An Introduction to Homological Algebra
      authors:
        - Charles A. Weibel
      publisher: Cambridge University Press
      year: 1994
      msc: 18-01
    - id: brown_cohomology
      type: textbook
      title: Cohomology of Groups
      authors:
        - Kenneth S. Brown
      publisher: Springer
      year: 1982
      msc: 20-01
  databases:
    - id: nlab
      type: database
      name: nLab
      entry_url: "https://ncatlab.org/nlab/show/{entry}"
---

# Ext与群扩张

## 引言

群扩张（group extension）是群论中的基本构造，描述如何通过两个给定的群"拼接"出更大的群。给定群 $Q$（商）和 $N$（核），一个 $Q$ 由 $N$ 的扩张是短正合列
$$1 \longrightarrow N \longrightarrow E \longrightarrow Q \longrightarrow 1.$$

Schreier在1926年建立了因子组理论，证明了扩张的等价类可用2-上闭链描述。而同调代数的视角更为深刻：将 $N$ 视为 $Q$-模（通过共轭作用），扩张的等价类与 $\operatorname{Ext}^1_{\mathbb{Z}Q}(\mathbb{Z}, N)$ 一一对应。这一对应不仅是群论与同调代数之间的优美桥梁，也是理解非Abel群结构的核心工具。

本教程严格建立Ext与群扩张的对应，详细证明Schreier定理，并通过具体分类例子展示理论的应用。

---

## 1. 群扩张的定义与等价

### 1.1 基本定义

**定义 1.1（群扩张）**。设 $Q, N$ 为群。一个 **$Q$ 由 $N$ 的扩张**（extension of $Q$ by $N$）是指一个短正合列
$$1 \longrightarrow N \xrightarrow{\iota} E \xrightarrow{\pi} Q \longrightarrow 1. \tag{E}$$
即 $\iota$ 为单射，$\pi$ 为满射，$\ker\pi = \operatorname{im}\iota$。常将 $N$ 等同于其在 $E$ 中的像，视 $N$ 为 $E$ 的正规子群。

**定义 1.2（扩张的等价）**。两个扩张 $1 \to N \to E \to Q \to 1$ 和 $1 \to N \to E' \to Q \to 1$ 称为 **等价**，如果存在同态 $\phi: E \to E'$ 使得下图交换：
$$\begin{array}{ccccccccc}
1 & \to & N & \to & E & \to & Q & \to & 1 \\
  &     & \downarrow^{\mathrm{id}} & & \downarrow^{\phi} & & \downarrow^{\mathrm{id}} & & \\
1 & \to & N & \to & E' & \to & Q & \to & 1
\end{array}$$
由五引理，$\phi$ 必为同构。

### 1.2 $Q$-模结构

设 (E) 为扩张。对 $q \in Q$，选取提升 $\tilde{q} \in E$（即 $\pi(\tilde{q}) = q$）。共轭作用
$$q \cdot n := \tilde{q} n \tilde{q}^{-1} \in N$$
不依赖于提升的选择（因 $N$ 正规），且给出 $Q$ 在 $N$ 上的作用。当 $N$ 为Abel群时，这一作用使 $N$ 成为 **$\mathbb{Z}Q$-模**。

**本节以下假设 $N$ 为Abel群，从而 $N$ 是 $\mathbb{Z}Q$-模。**

---

## 2. Schreier因子组理论

### 2.1 截面的选取与因子组

**定义 2.1（截面）**。映射 $s: Q \to E$ 称为 **截面**（section），若 $\pi \circ s = \mathrm{id}_Q$。一般不要求 $s$ 为同态。

给定截面 $s$，每个 $e \in E$ 可唯一写为 $e = n \cdot s(q)$（$n \in N, q \in Q$）。但 $s$ 通常不保持乘法，定义 **因子组**（factor set）$f: Q \times Q \to N$ 为
$$s(q)s(q') = f(q,q') s(qq'). \tag{F}$$

### 2.2 因子组的上闭链条件

**定理 2.1**。因子组 $f$ 满足 **2-上闭链条件**：
$$q \cdot f(q', q'') - f(qq', q'') + f(q, q'q'') - f(q, q') = 0 \quad \forall q,q',q'' \in Q. \tag{Cocycle}$$
这里 $N$ 的群运算写为加法（因 $N$ 为Abel群），$q \cdot n$ 为 $Q$-模作用。

**证明**：由结合律 $(s(q)s(q'))s(q'') = s(q)(s(q')s(q''))$。左端：
$$[f(q,q')s(qq')]s(q'') = f(q,q')f(qq',q'')s(qq'q'').$$
右端：
$$s(q)[f(q',q'')s(q'q'')] = (s(q)f(q',q'')s(q)^{-1})s(q)f(q',q'')s(q'q'') = (q \cdot f(q',q''))f(q,q'q'')s(qq'q'').$$
比较 $N$ 分量即得 (Cocycle)。∎

### 2.3 因子的上边缘

**定义 2.2**。若截面 $s$ 为同态（即 $s(qq') = s(q)s(q')$），则称扩张 **分裂**（splits）。此时 $E \cong N \rtimes Q$（半直积）。

设 $s, s'$ 为两个截面，$s'(q) = g(q)s(q)$（$g: Q \to N$）。设 $f, f'$ 为对应的因子组。

**定理 2.2**。$f' - f = dg$，其中上边缘
$$dg(q,q') = q \cdot g(q') - g(qq') + g(q). \tag{Coboundary}$$

**证明**：由 $s'(q)s'(q') = f'(q,q')s'(qq')$ 和 $s'(q) = g(q)s(q)$：
$$g(q)s(q)g(q')s(q') = g(q)(q \cdot g(q'))s(q)s(q') = g(q)(q \cdot g(q'))f(q,q')s(qq').$$
另一方面，右端为 $f'(q,q')g(qq')s(qq')$。比较得
$$f'(q,q') = f(q,q') + g(q)(q \cdot g(q'))g(qq')^{-1}.$$
转写为加法即 $f' = f + dg$。∎

---

## 3. Ext与群扩张的精确对应

### 3.1 群上同调与Ext

回顾群上同调的定义：
$$H^n(Q, N) := \operatorname{Ext}^n_{\mathbb{Z}Q}(\mathbb{Z}, N).$$
特别地，$H^2(Q, N)$ 由2-上闭链模去2-上边缘定义。

### 3.2 主定理

**定理 3.1（Schreier定理）**。设 $Q$ 为群，$N$ 为 $\mathbb{Z}Q$-模。则存在自然Abel群同构
$$\operatorname{Ext}^1_{\mathbb{Z}Q}(\mathbb{Z}, N) \cong H^2(Q, N) \cong \{\text{扩张 } 1 \to N \to E \to Q \to 1\}/\sim.$$
群运算对应于扩张的 **Baer和**。

**证明**：由定理2.1和2.2，因子组 $f$ 恰为2-上闭链，而不同的截面选择导致相差上边缘。因此扩张的等价类与 $H^2(Q,N)$ 的元素一一对应。

**Baer和的构造**：给定两个扩张 $E_1, E_2$，考虑纤维积（pullback）
$$P = \{(e_1, e_2) \in E_1 \times E_2 : \pi_1(e_1) = \pi_2(e_2)\}.$$
定义对角同态 $\nabla: N \to N \times N$，$n \mapsto (n, n^{-1})$。令 $E = P / \nabla(N)$。则 $1 \to N \to E \to Q \to 1$ 为Baer和，对应于 $H^2$ 中的加法。∎

**推论 3.1**。扩张分裂当且仅当其对应的 $\operatorname{Ext}^1$（或 $H^2$）类为零。

---

## 4. 分裂扩张与半直积

### 4.1 半直积的刻画

**定理 4.1**。短正合列 $1 \to N \to E \to Q \to 1$ 分裂当且仅当 $E \cong N \rtimes_\varphi Q$，其中 $\varphi: Q \to \operatorname{Aut}(N)$ 为同态，半直积乘法为
$$(n, q)(n', q') = (n \cdot \varphi(q)(n'), qq').$$

**证明**：若分裂，截面 $s: Q \to E$ 为同态。每个 $e \in E$ 唯一写为 $e = n s(q)$。由 $s(q)n s(q)^{-1} = \varphi(q)(n)$，乘法表恰给出半直积结构。反之，半直积的投影 $(n,q) \mapsto q$ 有截面 $q \mapsto (1,q)$ 为同态。∎

---

## 5. 具体例子

### 例子 5.1：$Q = \mathbb{Z}/2\mathbb{Z}$，$N = \mathbb{Z}/3\mathbb{Z}$ 的扩张分类

$Q = \{1, \tau\}$，$\tau^2 = 1$。$N = \mathbb{Z}/3\mathbb{Z} = \{0,1,2\}$。$Q$-模结构由 $\tau$ 的自同构决定：$\operatorname{Aut}(\mathbb{Z}/3) \cong \mathbb{Z}/2$。有两种可能：

**情形A：平凡作用**（$\tau \cdot n = n$）。此时 $H^2(Q, N)$ 由2-上闭链 $f: Q \times Q \to N$ 模上边缘计算。标准结果（可用Bar分解）：$H^2(\mathbb{Z}/2, \mathbb{Z}/3) = 0$（因 $|Q|$ 与 $|N|$ 互素，由Schur-Zassenhaus定理）。唯一扩张为直积 $E = \mathbb{Z}/6$。

**情形B：非平凡作用**（$\tau \cdot n = -n = 2n$）。此时 $H^2(\mathbb{Z}/2, \mathbb{Z}/3) = 0$ 同样成立（可由Hochschild-Serre谱序列或直接计算验证）。唯一扩张为半直积 $\mathbb{Z}/3 \rtimes \mathbb{Z}/2 \cong S_3$（三次对称群）。

### 例子 5.2：$Q = \mathbb{Z}/2\mathbb{Z} \times \mathbb{Z}/2\mathbb{Z}$，$N = \mathbb{Z}/2\mathbb{Z}$（平凡作用）

$Q = \{1, a, b, ab\}$，$a^2=b^2=(ab)^2=1$。计算 $H^2(Q, \mathbb{Z}/2)$。

用Künneth公式（对平凡模）：
$$H^2(\mathbb{Z}/2 \times \mathbb{Z}/2, \mathbb{Z}/2) \cong H^2(\mathbb{Z}/2)^{\oplus 2} \oplus (H^1(\mathbb{Z}/2) \otimes H^1(\mathbb{Z}/2)) \cong \mathbb{Z}/2 \oplus \mathbb{Z}/2 \oplus \mathbb{Z}/2 = (\mathbb{Z}/2)^3.$$

故共有8个等价类的扩张（含分裂的直积）。其中：
- 分裂扩张：$E = (\mathbb{Z}/2)^3$。
- 三个含 $\mathbb{Z}/4$ 因子的扩张：$\mathbb{Z}/4 \times \mathbb{Z}/2$（三种方式）。
- 四元数群 $Q_8$：$1 \to \mathbb{Z}/2 \to Q_8 \to (\mathbb{Z}/2)^2 \to 1$，其中中心 $Z(Q_8) = \mathbb{Z}/2$。
- 二面体群 $D_8$：$1 \to \mathbb{Z}/2 \to D_8 \to (\mathbb{Z}/2)^2 \to 1$。

实际上 $(\mathbb{Z}/2)^3$、$\mathbb{Z}/4 \times \mathbb{Z}/2$、$D_8$、$Q_8$ 恰为8阶群的全部类型，其中8个扩张类对应于这些群的中心扩张结构。

### 例子 5.3：用Schreier理论构造 $D_8$

$D_8 = \langle r, s \mid r^4 = s^2 = 1, srs = r^{-1} \rangle$。令 $N = \langle r^2 \rangle \cong \mathbb{Z}/2$，$Q = D_8/N \cong (\mathbb{Z}/2)^2 = \{1, \bar{r}, \bar{s}, \bar{r}\bar{s}\}$。

取截面：$s(1)=1$，$s(\bar{r})=r$，$s(\bar{s})=s$，$s(\bar{r}\bar{s})=rs$。计算因子组：
$$f(\bar{r}, \bar{r}) = s(\bar{r})s(\bar{r})s(\bar{r}^2)^{-1} = r \cdot r \cdot 1^{-1} = r^2 \in N.$$
其余 $f$ 值类似计算。所得 $[f] \in H^2(Q, N)$ 是非零元，对应非分裂扩张 $D_8$。

---

## 6. 与已有文档的关联

- [07-左导出函子Ext](07-左导出函子Ext.md)：Ext函子的定义与基本性质。
- [17-群上同调](17-群上同调.md)：$H^2(Q,N)$ 的定义与Bar分解计算。
- [10-Ext与模扩张](10-Ext与模扩张.md)：模扩张的Baer和理论，是群扩张的Abel类比。
- [02-长正合列](02-长正合列.md)：Ext长正合序列在扩张分类中的应用。

---

## 参考文献

1. K. S. Brown, *Cohomology of Groups*, Springer, 1982. (Ch. IV)
2. C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge Univ. Press, 1994. (Ch. 6)
3. S. Mac Lane, *Homology*, Springer, 1963. (Ch. IV)
4. O. Schreier, "Über die Erweiterung von Gruppen I", *Monatsh. Math. Phys.*, 34:165–180, 1926.

---

**适用**：docs/15-同调代数/
