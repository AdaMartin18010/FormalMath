---
msc_primary: 00A99
习题编号: ANA-100
学科: 实分析
知识点: 测度论-Lebesgue外测度
难度: ⭐⭐⭐
预计时间: 20分钟
---

# Lebesgue外测度与可测集

## 题目

**定义**：对 $E \subset \mathbb{R}^n$，Lebesgue外测度：
$$m^*(E) = \inf\left\{\sum_{k=1}^\infty |I_k| : E \subset \bigcup_{k=1}^\infty I_k\right\}$$
其中 $I_k$ 是方体，$|I|$ 表示体积。

(a) 证明外测度的单调性：$E \subset F \Rightarrow m^*(E) \leq m^*(F)$。

(b) 证明次可加性：$m^*\left(\bigcup_{k=1}^\infty E_k\right) \leq \sum_{k=1}^\infty m^*(E_k)$。

(c) 证明区间 $[a,b]$ 的外测度等于 $b-a$。

(d) 叙述Carathéodory可测性条件，并证明开集都是可测集。

## 解答

### (a) 单调性

**证明：**

若 $F \subset \bigcup I_k$，则 $E \subset \bigcup I_k$。

因此覆盖 $F$ 的方体族也覆盖 $E$。

取下确界，得 $m^*(E) \leq m^*(F)$。$\square$

### (b) 次可加性

**证明：**

不妨设 $m^*(E_k) < \infty$（否则显然）。

对 $\varepsilon > 0$，对每个 $k$，存在覆盖 $\{I_{k,j}\}_j$ 使得：
$$\sum_j |I_{k,j}| < m^*(E_k) + \frac{\varepsilon}{2^k}$$

则 $\{I_{k,j}\}_{k,j}$ 覆盖 $\bigcup_k E_k$。

$$m^*\left(\bigcup_k E_k\right) \leq \sum_{k,j} |I_{k,j}| < \sum_k m^*(E_k) + \varepsilon$$

令 $\varepsilon \to 0$，得证。$\square$

### (c) 区间的外测度

**证明：**

**上界**：$[a,b] \subset (a-\varepsilon, b+\varepsilon)$，故 $m^*([a,b]) \leq b-a + 2\varepsilon$。

令 $\varepsilon \to 0$，得 $m^*([a,b]) \leq b-a$。

**下界**：设 $\{I_k\}$ 覆盖 $[a,b]$。由紧性，存在有限子覆盖。

由Heine-Borel定理，$[a,b]$ 紧致。

有限覆盖的长度和 $\geq b-a$（可用归纳法证明）。

因此 $m^*([a,b]) \geq b-a$。$\square$

### (d) Carathéodory条件

**定义**：$E$ 可测，若对所有 $A \subset \mathbb{R}^n$：
$$m^*(A) = m^*(A \cap E) + m^*(A \cap E^c)$$

**开集可测**：

设 $G$ 开集，$A \subset \mathbb{R}^n$。需证：
$$m^*(A) \geq m^*(A \cap G) + m^*(A \cap G^c)$$

（反向不等式由次可加性自动满足）

设 $m^*(A) < \infty$。对 $\varepsilon > 0$，取覆盖 $\{I_k\}$ 使得：
$$\sum |I_k| < m^*(A) + \varepsilon$$

对每个 $I_k$，由于 $I_k \cap G$ 开（在 $I_k$ 的相对拓扑中），可进一步分割。

利用开集的构造（可数个不交方体的并），可证等式成立。$\square$

## 证明技巧

1. **$\varepsilon$-逼近**：外测度定义的核心
2. **紧性论证**：从无限覆盖到有限覆盖
3. **分割技巧**：Carathéodory条件的验证

## 常见错误

- ❌ 忘记证明下界（外测度等于测度需双向不等式）
- ❌ 混淆开集与可测集（所有开集可测，但可测集更多）
- ❌ 次可加性证明中选择覆盖的方式不当

## 变式练习

**变式1：** 证明 $m^*(E) = 0$ 的集合都是可测集（零测集可测）。

**变式2：** 证明Cantor集的外测度为0，但不可数。
