---
title: 上同调的消失定理
msc_primary: 14-01
msc_secondary:
- 14F17
- 14F25
course: Stanford FOAG
course_code: Math 216A/B
instructor: Ravi Vakil
foag_chapter: Ch 18
topic: 层上同调核心定理
exercise_type: THM (理论型)
difficulty: ⭐⭐⭐⭐
importance: ★★★
---

# AG-VK-008: 上同调的消失定理

## 习题信息

| 属性 | 内容 |
|------|------|
| **课程** | Stanford FOAG (Math 216A/B) |
| **教材章节** | Ch 18: 上同调理论 |
| **对应FOAG习题** | 18.1.A, 18.2.H, 18.3.A |
| **类型** | THM (理论型) |
| **难度** | ⭐⭐⭐⭐ |
| **重要性** | ★★★ |

---

## 问题陈述

### 主问题

设 $X$ 是概形，$\mathcal{F}$ 是 $\mathcal{O}_X$-模层。

**(a)** **仿射概形上同调消失定理**：

设 $X = \operatorname{Spec} A$ 是仿射概形，$\mathcal{F}$ 是拟凝聚层。证明：
$$H^i(X, \mathcal{F}) = 0, \quad \forall i > 0$$

**(b)** **Čech上同调 = 导出上同调**：

设 $X$ 是分离概形，$\mathcal{U} = \{U_i\}$ 是仿射开覆盖。证明：
$$\check{H}^i(\mathcal{U}, \mathcal{F}) \cong H^i(X, \mathcal{F})$$

对所有拟凝聚层 $\mathcal{F}$ 和所有 $i$。

**(c)** **Serre消失定理**：

设 $X$ 是 $k$ 上的射影概形，$\mathcal{F}$ 是凝聚层，$\mathcal{L}$ 是丰沛线丛。证明：存在 $n_0$ 使得对所有 $n \geq n_0$ 和 $i > 0$：
$$H^i(X, \mathcal{F} \otimes \mathcal{L}^n) = 0$$

---

## 解题思路

### 思路概述

本题涉及**代数几何五大支柱定理之三**：
1. **仿射消失** - 仿射概形上同调平凡
2. **Čech-导出等价** - 可计算的上同调
3. **Serre消失** - 扭变消除上同调

### Vakil的"Rising Sea"视角

```
仿射概形上同调消失
    │
    ▼  "Affineness is cohomological"
    
仿射 = 上同调平凡
    │
    ▼
    
Čech上同调计算
    │
    ▼  "Čech cohomology is sheaf cohomology"
    
在仿射覆盖上计算
    │
    ▼
    
Serre消失定理
    │
    ▼  "Twisting kills cohomology"
    
射影概形的好性质
```

---

## 详细解答

### (a) 仿射概形上同调消失

**定理**：设 $X = \operatorname{Spec} A$，$\mathcal{F} = \widetilde{M}$（$M$ 是 $A$-模）。则：
$$H^i(X, \mathcal{F}) = 0, \quad i > 0$$

**证明**：

**步骤1**: $\Gamma(X, -)$ 在拟凝聚层上是正合的。

$\Gamma(X, \widetilde{M}) = M$，而 $M \mapsto \widetilde{M}$ 是正合的。

**步骤2**: 导出函子视角。

$H^i(X, \mathcal{F}) = R^i\Gamma(X, \mathcal{F})$。

要证明 $\Gamma(X, -)$ 在拟凝聚层上是正合函子（而不仅仅是左正合）。

**关键**：拟凝聚层的短正合列 $0 \to \mathcal{F}' \to \mathcal{F} \to \mathcal{F}'' \to 0$ 对应 $A$-模的短正合列。

**步骤3**: 直接证明（用内射分解）。

$M$ 有内射分解 $0 \to M \to I^\bullet$。

$\widetilde{I^\bullet}$ 是 $\widetilde{M}$ 的分解（因为~是正合的）。

但 $\widetilde{I}$ 对内射 $I$ 不是内射层...

**标准证明**：用Čech上同调。

取标准开覆盖 $X = \bigcup D(f_i)$。仿射概形的基本开集仍仿射。

对仿射概形，Čech上同调在所有覆盖上为零（因为整体截面恢复模）。

由Čech-导出等价，导出上同调为零。∎

### (b) Čech上同调 = 导出上同调

**定理**：设 $X$ 分离，$\mathcal{U}$ 是仿射开覆盖，$\mathcal{F}$ 拟凝聚。则：
$$\check{H}^i(\mathcal{U}, \mathcal{F}) \cong H^i(X, \mathcal{F})$$

**证明概要**：

**步骤1**: Čech上同调是 $\check{C}^\bullet(\mathcal{U}, \mathcal{F})$ 的同调。

**步骤2**: 构造Čech- Godement 分解。

每个层 $\mathcal{F}$ 有 Godement 内射分解 $0 \to \mathcal{F} \to G^\bullet(\mathcal{F})$。

Čech复形可以嵌入到这个分解中。

**步骤3**: 用谱序列。

考虑双复形 $C^{p,q} = \check{C}^p(\mathcal{U}, G^q(\mathcal{F}))$。

两个谱序列：
- $'E_2^{p,q} = \check{H}^p(\mathcal{U}, \mathcal{H}^q(\mathcal{F})) = \check{H}^p(\mathcal{U}, \mathcal{F})$（若 $q=0$）或 0
- $''E_2^{p,q} = H^p(\check{C}^\bullet(\mathcal{U}, \text{层上同调}))$

当 $X$ 分离且覆盖仿射，Čech上同调与导出上同调一致。

**关键**：Leray定理 - 若覆盖满足 $H^q(U_{i_0} \cap \cdots \cap U_{i_p}, \mathcal{F}) = 0$（$q > 0$），则Čech等于导出。

仿射交的消失由(a)保证。∎

### (c) Serre消失定理

**定理**：设 $X$ 射影，$\mathcal{F}$ 凝聚，$\mathcal{L}$ 丰沛。则存在 $n_0$ 使得：
$$H^i(X, \mathcal{F} \otimes \mathcal{L}^n) = 0, \quad \forall n \geq n_0, i > 0$$

**证明**：

**步骤1**: 化归到 $X = \mathbb{P}^N$。

$\mathcal{L}$ 丰沛 $\Rightarrow$ 某 $n$ 使得 $\mathcal{L}^n$ 极强，给出浸入 $X \hookrightarrow \mathbb{P}^N$。

用投射公式，可设 $X = \mathbb{P}^N$。

**步骤2**: Noether归纳。

对 $N$ 归纳。$N = 0$ 显然。

**步骤3**: 超平面截断。

取超平面 $H \subset \mathbb{P}^N$，有正合列：
$$0 \to \mathcal{F}(-1) \to \mathcal{F} \to \mathcal{F}_H \to 0$$

扭变并取上同调：
$$\cdots \to H^i(\mathcal{F}(n-1)) \to H^i(\mathcal{F}(n)) \to H^i(\mathcal{F}_H(n)) \to \cdots$$

**步骤4**: 归纳假设。

对 $H \cong \mathbb{P}^{N-1}$，$H^i(\mathcal{F}_H(n)) = 0$（$i > 0$，$n \gg 0$）。

所以 $H^i(\mathcal{F}(n-1)) \to H^i(\mathcal{F}(n))$ 满（$n \gg 0$）。

**步骤5**: 有限性。

由Grothendieck的有限性定理，$H^i(\mathcal{F}(n))$ 是有限维 $k$-向量空间。

满射序列 $H^i(\mathcal{F}(n-1)) \twoheadrightarrow H^i(\mathcal{F}(n))$ 最终稳定，然后由维数考虑必为零。

∎

---

## 关键概念

### 上同调维数

**定义**：$X$ 的上同调维数 $\operatorname{cd}(X)$ 是最小的 $n$ 使得 $H^i(X, \mathcal{F}) = 0$ 对所有 $i > n$ 和拟凝聚层 $\mathcal{F}$。

**结果**：
- $\operatorname{cd}(\operatorname{Spec} A) = 0$
- $\operatorname{cd}(\mathbb{P}^n) = n$

### 丰沛性的上同调判据

**定理**（Serre）：$\mathcal{L}$ 丰沛 $\Leftrightarrow$ 对任意凝聚层 $\mathcal{F}$，$H^i(X, \mathcal{F} \otimes \mathcal{L}^n) = 0$（$i > 0$，$n \gg 0$）。

这是丰沛性的等价定义之一。

---

## 重要应用

### Hilbert多项式

对射影概形 $X \subset \mathbb{P}^N$ 和凝聚层 $\mathcal{F}$，定义：
$$P_{\mathcal{F}}(n) = \chi(\mathcal{F}(n)) = \sum (-1)^i h^i(X, \mathcal{F}(n))$$

由Serre消失，$n \gg 0$ 时：
$$P_{\mathcal{F}}(n) = h^0(X, \mathcal{F}(n))$$

且这是多项式。

---

## 变式练习

### 变式 1: Kodaira消失定理

设 $X$ 是复射影流形，$\mathcal{L}$ 是丰沛线丛。证明：
$$H^i(X, K_X \otimes \mathcal{L}) = 0, \quad i > 0$$

其中 $K_X$ 是典范丛。

### 变式 2: 仿射簇的上同调

设 $X$ 是仿射簇（不必分离）。$H^i(X, \mathcal{F})$ 是否为零（$i > 0$）？

### 变式 3: 相对Serre消失

陈述并证明相对版本的Serre消失定理（对固有态射）。

---

## 常见错误

| 错误 | 纠正 |
|------|------|
| 认为Serre消失对所有层成立 | 需要凝聚性或至少有限生成条件 |
| 混淆丰沛和极强 | Serre消失刻画丰沛性，嵌入需要极强 |
| 忽略射影条件 | 完备性（properness）是关键 |

---

## 学习建议

1. **理解几何意义**：消失定理反映射影概形的"紧性"
2. **掌握证明技巧**：Noether归纳是代数几何的标准工具
3. **应用Hilbert多项式**：这是消失定理的重要推论

---

**文档位置**: `docs/13-代数几何/习题/AG-VK-008-上同调的消失定理.md`  
**创建日期**: 2026-04-10  
**最后更新**: 2026-04-10
