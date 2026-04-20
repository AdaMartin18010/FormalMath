---
msc_primary: 00A99
习题编号: AG-050
学科: 代数几何
知识点: 代数几何-Bridgeland稳定性
难度: ⭐⭐⭐⭐⭐
预计时间: 60分钟
---

# Bridgeland 稳定性

## 题目

**(a)** 定义 stability condition 并证明其满足 Harder-Narasimhan 性质与支撑性质。

**(b)** 证明稳定性流形 $\operatorname{Stab}(\mathcal{D})$ 的复流形结构。

**(c)** 讨论 $\mathbb{P}^1$ 的稳定性流形与 wall-crossing 现象。

## 解答

### (a) 稳定性条件

**三角范畴**：$(\mathcal{D}, [1])$ 是 $
$ \mathbb{C}$-线性的 triangulated category（如 $D^b\operatorname{Coh}(X)$）。

**Heart**：abelian 子范畴 $\mathcal{A} \subset \mathcal{D}$，使得：
- 对 $E \in \mathcal{D}$，存在 distinguished triangle $A \to E \to B \to A[1]$，$A \in \mathcal{A}, B \in \mathcal{A}[-1]$
- $\operatorname{Hom}(\mathcal{A}, \mathcal{A}[k]) = 0$ 对 $k < 0$

**中心荷**：群同态 $Z: K(\mathcal{D}) \to \mathbb{C}$，使得 $Z(E) \in \mathbb{H} = \{r e^{i\pi\phi} : r > 0, \phi \in (0, 1]\}$ 对 $0 \neq E \in \mathcal{A}$。

**相位**：$\phi(E) = \frac{1}{\pi} \arg Z(E) \in (0, 1]$。

**半稳定对象**：$E \in \mathcal{A}$ 是 **(semi)stable**，若对所有 proper 子对象 $F \subset E$：

$$
\phi(F) \; (\leq) \; \phi(E)
$$

**稳定性条件**：$(Z, \mathcal{A})$ 满足 **Harder-Narasimhan 性质**：每个 $E \in \mathcal{A}$ 有唯一滤过：

$$
0 = E_0 \subset E_1 \subset \cdots \subset E_n = E$$

使得 $F_i = E_i/E_{i-1}$ semi-stable，$\phi(F_1) > \phi(F_2) > \cdots > \phi(F_n)$。

**支撑性质**：存在范数 $\| \cdot \|$ 在 $K(\mathcal{D}) \otimes \mathbb{R}$ 上，使得对 semi-stable $E$：

$$
\|E\| \leq C |Z(E)|
$$

对某常数 $C$。

---

### (b) 稳定性流形

**定义**：$\operatorname{Stab}(\mathcal{D})$ 是所有稳定性条件 $(Z, \mathcal{A})$ 的集合。

**Bridgeland 定理（2007）**：$\operatorname{Stab}(\mathcal{D})$ 是有限维复流形，局部同胚于 $\operatorname{Hom}(K(\mathcal{D}), \mathbb{C})$。

*证明概要*：

1. **拓扑**：在 $(Z, \mathcal{A})$ 附近，$Z'$ 接近 $Z$ 时，可"倾斜"（tilt）heart 得到新稳定性条件。

2. **Tilting**：对 heart $\mathcal{A}$ 和 torsion pair $(\mathcal{T}, \mathcal{F})$，倾斜 heart：
   $$\mathcal{A}^\sharp = \{E \in \mathcal{D} : H^0(E) \in \mathcal{T}, H^{-1}(E) \in \mathcal{F}, H^i(E) = 0 \text{ otherwise}\}$$

3. **局部同胚**：固定 heart，$(Z, \mathcal{A})$ 附近的小扰动 $Z'$ 对应同一 heart 上的新稳定性条件。支撑性质保证 HN 性质保持。

4. **维数**：$\dim_\mathbb{C} \operatorname{Stab}(\mathcal{D}) = \operatorname{rank} K(\mathcal{D})$。

---

### (c) $\mathbb{P}^1$ 的稳定性流形

**$D^b(\mathbb{P}^1)$ 的生成元**：$\mathcal{O}$ 和 $\mathcal{O}(-1)$，$K(\mathcal{D}) \cong \mathbb{Z}^2$。

**经典 slope stability**：对凝聚层，$\mu(E) = \deg(E)/\operatorname{rank}(E)$。

**Bridgeland stability**：

**例 1**：heart = $\operatorname{Coh}(\mathbb{P}^1)$，$Z(E) = -\deg(E) + i \cdot \operatorname{rank}(E)$。

Semi-stable：半稳定层（slope-semistable）。

**例 2**：倾斜 heart。对 $t \in \mathbb{R}$，$\mathcal{A}_t = \langle \mathcal{O}(n)[1] : n < t, \mathcal{O}(m) : m \geq t \rangle$。

**定理**：$\operatorname{Stab}(\mathbb{P}^1) \cong \mathbb{C}^2$（由 Okada 证明）。

**Wall-crossing**：在 $\operatorname{Stab}$ 中，对象的稳定性只在 codimension-1 的 "walls" 上改变。

对 $\mathbb{P}^1$，wall-crossing 对应欧拉特征的突变：

$$\chi(E, F) = \dim \operatorname{Hom}(E, F) - \dim \operatorname{Ext}^1(E, F)$$

**Gaiotto-Moore-Neitzke 公式**： wall-crossing 时 BPS 谱的突变由 Kontsevich-Soibelman 的 motivic Donaldson-Thomas 不变量控制。

---

## 常见错误

- **Heart 非唯一**：同一三角范畴可有多个 heart（通过倾斜），稳定性条件依赖 heart 的选择。
- **支撑性质的必要性**：无支撑性质时，稳定性流形可能不 Hausdorff。
- **$\mathbb{P}^1$ vs 高维**：$\operatorname{Stab}(\mathbb{P}^1)$ 完全已知，但 $K3$ 曲面或 Calabi-Yau 3-fold 的稳定性流形仍有许多未解决问题。

## 参考文献

- Bridgeland, *Stability conditions on triangulated categories*.
- Huybrechts, *Introduction to Stability Conditions*.
- Macrì & Schmidt, *Lectures on Bridgeland Stability*.
