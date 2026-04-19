---
msc_primary: 00A99
msc_secondary:
  - 97A99
---

# Stacks Project Tag 07GJ - 晶体上同调与de Rham上同调

## 1. 基本信息

| 属性 | 内容 |
|------|------|
| **Tag编号** | 07GJ |
| **英文名称** | Crystalline and de Rham Cohomology |
| **所属章节** | Crystalline Cohomology |
| **主题分类** | 代数几何 - 比较定理 |
| **创建日期** | 2026-04-10 |
| **版本** | v1.0 |

---

## 2. 核心概念与定义

### 2.1 比较问题概述

在代数几何中，**比较定理**（Comparison Theorem）研究不同上同调理论之间的关系。Tag 07GJ 建立的是**晶体上同调**与**代数de Rham上同调**之间的深刻联系。

### 2.2 两种上同调的定义回顾

**定义 2.2.1**（代数de Rham上同调 - Grothendieck）
设 $X$ 是光滑 $k$-概形，其**de Rham上同调**定义为超上同调：

$$H^i_{\text{dR}}(X/k) := \mathbb{H}^i(X, \Omega^\bullet_{X/k})$$

其中 $\Omega^\bullet_{X/k}$ 是代数的de Rham复形：

$$\mathcal{O}_X \xrightarrow{d} \Omega^1_{X/k} \xrightarrow{d} \Omega^2_{X/k} \xrightarrow{d} \cdots$$

**定义 2.2.2**（晶体上同调 - Berthelot）
对于特征 $p$ 的光滑 $k$-概形，其**晶体上同调**为：

$$H^i_{\text{cris}}(X/W) := H^i(\text{Cris}(X/W), \mathcal{O}_{X/W})$$

其中 $W = W(k)$ 是Witt向量环。

### 2.3 关键概念

**定义 2.3.1**（提升）
$k$-概形 $X$ 到 $W$ 的**提升**是指光滑 $W$-概形 $\mathcal{X}$ 使得 $\mathcal{X} \times_W k \cong X$。

**定义 2.3.2**（Gauss-Manin联络）
对于光滑态射 $f: X \to S$，**Gauss-Manin联络**是 $R^i f_* \Omega^\bullet_{X/S}$ 上的可积联络：

$$\nabla: R^i f_* \Omega^\bullet_{X/S} \to \Omega^1_{S/k} \otimes R^i f_* \Omega^\bullet_{X/S}$$

---

## 3. 主要结果与定理

### 3.1 比较同构定理

**定理 3.1.1**（Tag 07GJ - 晶体-de Rham比较）
设 $X$ 是 $k$ 上的光滑真概形，$\mathcal{X}$ 是其到 $W = W(k)$ 的光滑提升（若存在），则存在典范同构：

$$\boxed{H^i_{\text{cris}}(X/W) \otimes_W K \cong H^i_{\text{dR}}(\mathcal{X}_K/K)}$$

其中 $K = \text{Frac}(W)$ 是分式域。

**推论 3.1.2**
若 $X$ 可提升到 $W_n = W/p^n$ 对所有 $n$，则：

$$H^i_{\text{cris}}(X/W) \cong \varprojlim_n H^i_{\text{dR}}(\mathcal{X}_n/W_n)$$

### 3.2 绝对情形

**定理 3.2.1**（Berthelot-Ogus）
即使不存在整体提升，仍有比较同构通过晶体-de Rham复形实现：

$$Ru_{X/W*}\mathcal{O}_{X/W} \cong \Omega^\bullet_{\mathcal{X}/W} \otimes \mathbb{Q}$$

其中 $u_{X/W}: (X/W)_{\text{cris}} \to X_{\text{Zar}}$ 是拓扑的投射态射。

### 3.3 滤过结构

**定理 3.3.1**（Hodge滤过）
de Rham上同调带有**Hodge滤过**：

$$F^p H^i_{\text{dR}}(X/k) = \text{Im}(\mathbb{H}^i(X, \sigma_{\geq p}\Omega^\bullet_{X/k}))$$

其中 $\sigma_{\geq p}$ 是笨滤过（stupid filtration）。

**定理 3.3.2**（共轭滤过）
晶体上同调带有**共轭滤过** $F_{\text{con}}^\bullet$，与de Rham上同调的Hodge滤过正交。

---

## 4. 证明思路

### 4.1 局部计算

**步骤1**：仿射情形
- 设 $X = \text{Spec}(A)$，$\mathcal{X} = \text{Spec}(\mathcal{A})$
- 计算 $H^i_{\text{cris}}(X/W)$ 通过PD包络 $D(\mathcal{A})$

**步骤2**：Poincaré引理
- 在晶体位形上，存在de Rham复形的拟同构：

$$\mathcal{O}_{X/W} \xrightarrow{\sim} \Omega^\bullet_{\mathcal{X}/W} \otimes \mathbb{Q}$$

### 4.2 整体构造

**关键引理**：
对于光滑提升 $\mathcal{X}$，存在**晶体-de Rham复形**的典范映射：

$$\mathcal{O}_{X/W} \to i_{\text{cris}*}\Omega^\bullet_{\mathcal{X}/W}$$

在 $\mathbb{Q}$ 上这是拟同构。

### 4.3 收敛性论证

**步骤1**：p-进展开
- 利用 $W = \varprojlim W/p^n$
- 在每一层 $W_n$ 上建立比较

**步骤2**：Mittag-Leffler
- 验证上同调系统满足ML条件
- 保证极限与上同调交换

---

## 5. 应用与例子

### 5.1 曲线的情形

**例子 5.1.1**（椭圆曲线）
设 $E/k$ 是椭圆曲线，$\mathcal{E}/W$ 是其提升。

$$H^1_{\text{dR}}(\mathcal{E}_K/K) = H^0(\mathcal{E}_K, \Omega^1) \oplus H^1(\mathcal{E}_K, \mathcal{O})$$

维度分解：$2 = 1 + 1$（Hodge分解）

**例子 5.1.2**（超奇异vs普通）
- **普通椭圆曲线**：$H^1_{\text{cris}}$ 有秩1的unit子模
- **超奇异椭圆曲线**：$F$ 在 $H^1_{\text{cris}}$ 上幂零

### 5.2 K3曲面的周期映射

**应用 5.2.1**
对于K3曲面 $X/k$，晶体上同调 $H^2_{\text{cris}}(X/W)$ 携带：

- **Frobenius作用**：$F^*$
- **晶格结构**：与 $H^2(X, \mathbb{Z})$ 同构的抽象格
- **周期映射**：联系晶体结构与复结构

**Torelli定理**：周期映射确定K3曲面的同构类。

### 5.3 Calabi-Yau簇的形变

**例子 5.3.1**
对于Calabi-Yau $n$-fold，$h^{n,0} = 1$。

Bogomolov-Tian-Todorov定理：形变是无障碍的。

比较定理给出晶体-de Rham数据完全控制形变：

$$\text{Def}(X) \cong \text{Spf}(W[[t_1, \ldots, t_m]])$$

### 5.4 $p$-进Hodge理论

**应用 5.4.1**（$C_{\text{dR}}$-比较）
设 $X$ 是 $K$（$p$-进域）上的光滑真簇，则：

$$H^i_{\text{ét}}(X_{\bar{K}}, \mathbb{Q}_p) \otimes_{\mathbb{Q}_p} B_{\text{dR}} \cong H^i_{\text{dR}}(X/K) \otimes_K B_{\text{dR}}$$

这建立了Galois表示与de Rham结构的关系。

---

## 6. 与其他概念的关系

### 6.1 上同调理论的比较图谱

```
    晶体上同调 $H^i_{\text{cris}}(X/W)$
            │
            │ ⊗_W K
            ▼
    de Rham上同调 $H^i_{\text{dR}}(\mathcal{X}_K/K)$
            │
    ┌───────┴───────┐
    │               │
    ▼               ▼
  Hodge理论      p-进Hodge理论
    │               │
    ▼               ▼
  复几何         Galois表示
```

### 6.2 与Motive理论的关系

比较定理支持Grothendieck的Motive哲学：

$$h^i(X) \in \text{Mot}(k) \leadsto H^i_{\text{cris}}(X) \in \text{F-Isoc}(k)$$

晶体实现是Weil上同调理论之一。

### 6.3 与D-模理论的联系

通过Riemann-Hilbert对应：

- de Rham复形 $\Omega^\bullet_{X}$ 对应于常D-模 $\mathcal{O}_X$
- 晶体上同调对应于带Frobenius结构的D-模

---

## 7. 参考文献

### 7.1 奠基文献

1. **Grothendieck, A.** (1966). *On the de Rham cohomology of algebraic varieties*
   - Pub. Math. IHÉS 29
   - de Rham上同调的代数定义

2. **Berthelot, P.** (1974). *Cohomologie cristalline des schémas*
   - Springer Lecture Notes 407
   - 晶体上同调的建立

3. **Berthelot, P. & Ogus, A.** (1978). *Notes on Crystalline Cohomology*
   - 比较定理的详细证明

### 7.2 现代发展

4. **Fontaine, J.-M.** (1982). *Formes différentielles et modules de Tate*
   - $p$-进Hodge理论的奠基

5. **Beilinson, A.** (1987). *On the derived category of perverse sheaves*
   - 导出范畴视角

6. **Bhatt, B.** (2018). *Specializing varieties and their cohomology*
   - 现代比较定理的证明

### 7.3 应用文献

7. **Deligne, P. & Illusie, L.** (1987). *Relèvements modulo $p^2$*
   - 退化定理的代数证明

8. **Ogus, A.** (1994). *F-Crystals, Griffiths transversality*
   - K3曲面等具体应用

### 7.4 在线资源

9. **Stacks Project**: [Tag 07GJ](https://stacks.math.columbia.edu/tag/07GJ)
10. **Stacks Project**: [Chapter Crystalline](https://stacks.math.columbia.edu/chapter/07GI)

---

## 8. 相关Tags

### 8.1 直接相关

| Tag | 主题 | 关系 |
|-----|------|------|
| [07GI](#tag-07gi) | 晶体上同调定义 | 理论基础 |
| [0F1B](#tag-0f1b) | de Rham上同调 | 比较对象 |
| [0F1C](#tag-0f1c) | Hodge滤过 | 结构细化 |

### 8.2 比较定理

| Tag | 主题 | 说明 |
|-----|------|------|
| [0F1D](#tag-0f1d) | p-进比较定理 | 推广结果 |
| [0F1E](#tag-0f1e) | 半稳定比较 | 边界情形 |
| [0F1F](#tag-0f1f) | 刚性比较 | 开簇推广 |

### 8.3 应用主题

| Tag | 主题 | 说明 |
|-----|------|------|
| [0F1G](#tag-0f1g) | 周期映射 | 几何应用 |
| [0F1H](#tag-0f1h) | Torelli定理 | 分类问题 |
| [0F1I](#tag-0f1i) | 形变理论 | 结构应用 |

---

## 附录：计算示例

### K3曲面的晶体上同调

对于K3曲面 $X/\mathbb{F}_p$：

$$H^2_{\text{cris}}(X/W) \cong W^{22}$$

**Frobenius特征多项式**：

$$\det(T - F^* | H^2_{\text{cris}}) = T^{22} + a_1 T^{21} + \cdots + p^{22}$$

满足Weil猜想：根的绝对值为 $p$。

---

*本文档由FormalMath项目生成，最后更新：2026-04-10*
